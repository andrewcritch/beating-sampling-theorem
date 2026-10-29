import BstLean.Part261Checker
import BstLean.Part259Data20
import BstLean.Part259Data21
import BstLean.Part259Data22
import BstLean.Part259Data23
import BstLean.Part259Data24

namespace BstLean.Part261
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part259

noncomputable def tp12325 : ℝ := (1155705051 / 5000000000)
noncomputable def tm12325 : ℝ := (-((6078361007 / 10000000000)))
noncomputable def ep12325 : ℝ := (50901411326936467 / 100000000000000000000)
noncomputable def em12325 : ℝ := (9958157630834759 / 20000000000000000000)
noncomputable def bp12325 : ℝ := (4564848036836081059 / 10000000000000000000)
noncomputable def bm12325 : ℝ := (5804533872328594911 / 12500000000000000000)

theorem positive12325 :
    Eplus aL (agent12325.root+dsL) scalar12325.worldRadius world12325.frame
      agent12325.frame tp12325 ≤ -ep12325 := by
  apply positive_check (eT := (115701705571403668617 / 100000000000000000000)) (y := (37232215350884509783 / 100000000000000000000)) (u := (7255501915408247791 / 5000000000000000000))
  · norm_num [world12325, agent12325, scalar12325, tp12325, tm12325, ep12325, em12325, dsL]
  · norm_num [world12325, agent12325, scalar12325, tp12325, tm12325, ep12325, em12325, dsL]
  · norm_num [world12325, agent12325, scalar12325, tp12325, tm12325, ep12325, em12325, dsL]
  · norm_num [world12325, agent12325, scalar12325, tp12325, tm12325, ep12325, em12325, dsL]
  · norm_num [world12325, agent12325, scalar12325, tp12325, tm12325, ep12325, em12325, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12325, agent12325, tp12325, tm12325, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12325, agent12325, scalar12325, tp12325, tm12325, ep12325, em12325, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12325, agent12325, tp12325, tm12325, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12325, agent12325, scalar12325, tp12325, tm12325, ep12325, em12325, dsL]

theorem negative12325 :
    Eminus aL (agent12325.root+dsL) scalar12325.worldRadius world12325.frame
      agent12325.frame tm12325 ≤ -em12325 := by
  apply negative_check (lo := (17036256979498819001 / 25000000000000000000)) (hi := (13629005583599055201 / 20000000000000000000))
    (y := (-((70855879401109267067 / 100000000000000000000)))) (u := (12308831721474930881 / 25000000000000000000))
  · norm_num [world12325, agent12325, scalar12325, tp12325, tm12325, ep12325, em12325, dsL]
  · norm_num [world12325, agent12325, scalar12325, tp12325, tm12325, ep12325, em12325, dsL]
  · norm_num [world12325, agent12325, scalar12325, tp12325, tm12325, ep12325, em12325, dsL]
  · norm_num [world12325, agent12325, scalar12325, tp12325, tm12325, ep12325, em12325, dsL]
  · norm_num [world12325, agent12325, scalar12325, tp12325, tm12325, ep12325, em12325, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12325, agent12325, tp12325, tm12325, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12325, agent12325, tp12325, tm12325, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12325, agent12325, scalar12325, tp12325, tm12325, ep12325, em12325, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12325, agent12325, tp12325, tm12325, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12325, agent12325, scalar12325, tp12325, tm12325, ep12325, em12325, dsL]

theorem tails12325 :
    exp (-((12325:ℝ)*ep12325)) ≤ scalar12325.upperTail ∧
    exp (-((12325:ℝ)*em12325)) ≤ scalar12325.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12325:ℝ)) (by norm_num [ep12325]) ?_)
      (show bp12325^8 ≤ scalar12325.upperTail by norm_num [bp12325, scalar12325])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12325, bp12325, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12325:ℝ)) (by norm_num [em12325]) ?_)
      (show bm12325^8 ≤ scalar12325.lowerTail by norm_num [bm12325, scalar12325])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12325, bm12325, Finset.sum_range_succ, Nat.factorial]

theorem guards12325 :
    agent12325.root+dsL+scalar12325.worldRadius < √(1/100/aL) ∧
    2*(agent12325.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12325, agent12325, scalar12325, tp12325, tm12325, ep12325, em12325, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12325, agent12325, scalar12325, tp12325, tm12325, ep12325, em12325, dsL]

noncomputable def master12325 : MasterCertificate 12325 world12325 agent12325 :=
  master scalar12325 dsL tp12325 tm12325 ep12325 em12325
    (by norm_num [dsL]) (by norm_num [tp12325]) (by norm_num [tm12325])
    (by norm_num [ep12325]) (by norm_num [em12325])
    positive12325 negative12325 tails12325.1 tails12325.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12325.1 guards12325.2

theorem preserves12325 : master12325.toScalarCertificate = scalar12325 := rfl

noncomputable def tp12326 : ℝ := (28893877 / 125000000)
noncomputable def tm12326 : ℝ := (-((3039291733 / 5000000000)))
noncomputable def ep12326 : ℝ := (50904433424067837 / 100000000000000000000)
noncomputable def em12326 : ℝ := (24896715578925467 / 50000000000000000000)
noncomputable def bp12326 : ℝ := (11410862662986639047 / 25000000000000000000)
noncomputable def bm12326 : ℝ := (46431490120086742259 / 100000000000000000000)

theorem positive12326 :
    Eplus aL (agent12326.root+dsL) scalar12326.worldRadius world12326.frame
      agent12326.frame tp12326 ≤ -ep12326 := by
  apply positive_check (eT := (115702042454278463497 / 100000000000000000000)) (y := (37233031576541723787 / 100000000000000000000)) (u := (7255561136918131257 / 5000000000000000000))
  · norm_num [world12326, agent12326, scalar12326, tp12326, tm12326, ep12326, em12326, dsL]
  · norm_num [world12326, agent12326, scalar12326, tp12326, tm12326, ep12326, em12326, dsL]
  · norm_num [world12326, agent12326, scalar12326, tp12326, tm12326, ep12326, em12326, dsL]
  · norm_num [world12326, agent12326, scalar12326, tp12326, tm12326, ep12326, em12326, dsL]
  · norm_num [world12326, agent12326, scalar12326, tp12326, tm12326, ep12326, em12326, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12326, agent12326, tp12326, tm12326, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12326, agent12326, scalar12326, tp12326, tm12326, ep12326, em12326, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12326, agent12326, tp12326, tm12326, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12326, agent12326, scalar12326, tp12326, tm12326, ep12326, em12326, dsL]

theorem negative12326 :
    Eminus aL (agent12326.root+dsL) scalar12326.worldRadius world12326.frame
      agent12326.frame tm12326 ≤ -em12326 := by
  apply negative_check (lo := (68144680995045519281 / 100000000000000000000)) (hi := (34072340497522759641 / 50000000000000000000))
    (y := (-((2834236810751934631 / 4000000000000000000)))) (u := (393882454116508133 / 800000000000000000))
  · norm_num [world12326, agent12326, scalar12326, tp12326, tm12326, ep12326, em12326, dsL]
  · norm_num [world12326, agent12326, scalar12326, tp12326, tm12326, ep12326, em12326, dsL]
  · norm_num [world12326, agent12326, scalar12326, tp12326, tm12326, ep12326, em12326, dsL]
  · norm_num [world12326, agent12326, scalar12326, tp12326, tm12326, ep12326, em12326, dsL]
  · norm_num [world12326, agent12326, scalar12326, tp12326, tm12326, ep12326, em12326, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12326, agent12326, tp12326, tm12326, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12326, agent12326, tp12326, tm12326, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12326, agent12326, scalar12326, tp12326, tm12326, ep12326, em12326, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12326, agent12326, tp12326, tm12326, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12326, agent12326, scalar12326, tp12326, tm12326, ep12326, em12326, dsL]

theorem tails12326 :
    exp (-((12326:ℝ)*ep12326)) ≤ scalar12326.upperTail ∧
    exp (-((12326:ℝ)*em12326)) ≤ scalar12326.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12326:ℝ)) (by norm_num [ep12326]) ?_)
      (show bp12326^8 ≤ scalar12326.upperTail by norm_num [bp12326, scalar12326])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12326, bp12326, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12326:ℝ)) (by norm_num [em12326]) ?_)
      (show bm12326^8 ≤ scalar12326.lowerTail by norm_num [bm12326, scalar12326])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12326, bm12326, Finset.sum_range_succ, Nat.factorial]

theorem guards12326 :
    agent12326.root+dsL+scalar12326.worldRadius < √(1/100/aL) ∧
    2*(agent12326.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12326, agent12326, scalar12326, tp12326, tm12326, ep12326, em12326, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12326, agent12326, scalar12326, tp12326, tm12326, ep12326, em12326, dsL]

noncomputable def master12326 : MasterCertificate 12326 world12326 agent12326 :=
  master scalar12326 dsL tp12326 tm12326 ep12326 em12326
    (by norm_num [dsL]) (by norm_num [tp12326]) (by norm_num [tm12326])
    (by norm_num [ep12326]) (by norm_num [em12326])
    positive12326 negative12326 tails12326.1 tails12326.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12326.1 guards12326.2

theorem preserves12326 : master12326.toScalarCertificate = scalar12326 := rfl

noncomputable def tp12327 : ℝ := (72237819 / 312500000)
noncomputable def tm12327 : ℝ := (-((1519701469 / 2500000000)))
noncomputable def ep12327 : ℝ := (2036298178394241 / 4000000000000000000)
noncomputable def em12327 : ℝ := (49796073145594751 / 100000000000000000000)
noncomputable def bp12327 : ℝ := (5704802736410617659 / 12500000000000000000)
noncomputable def bm12327 : ℝ := (4642671017377027441 / 10000000000000000000)

theorem positive12327 :
    Eplus aL (agent12327.root+dsL) scalar12327.worldRadius world12327.frame
      agent12327.frame tp12327 ≤ -ep12327 := by
  apply positive_check (eT := (28925594824139310591 / 25000000000000000000)) (y := (37233848071430409303 / 100000000000000000000)) (u := (145112407568916226797 / 100000000000000000000))
  · norm_num [world12327, agent12327, scalar12327, tp12327, tm12327, ep12327, em12327, dsL]
  · norm_num [world12327, agent12327, scalar12327, tp12327, tm12327, ep12327, em12327, dsL]
  · norm_num [world12327, agent12327, scalar12327, tp12327, tm12327, ep12327, em12327, dsL]
  · norm_num [world12327, agent12327, scalar12327, tp12327, tm12327, ep12327, em12327, dsL]
  · norm_num [world12327, agent12327, scalar12327, tp12327, tm12327, ep12327, em12327, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12327, agent12327, tp12327, tm12327, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12327, agent12327, scalar12327, tp12327, tm12327, ep12327, em12327, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12327, agent12327, tp12327, tm12327, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12327, agent12327, scalar12327, tp12327, tm12327, ep12327, em12327, dsL]

theorem negative12327 :
    Eminus aL (agent12327.root+dsL) scalar12327.worldRadius world12327.frame
      agent12327.frame tm12327 ≤ -em12327 := by
  apply negative_check (lo := (34072167113856797297 / 50000000000000000000)) (hi := (13628866845542718919 / 20000000000000000000))
    (y := (-((1771399036901114231 / 2500000000000000000)))) (u := (6154410809506702411 / 12500000000000000000))
  · norm_num [world12327, agent12327, scalar12327, tp12327, tm12327, ep12327, em12327, dsL]
  · norm_num [world12327, agent12327, scalar12327, tp12327, tm12327, ep12327, em12327, dsL]
  · norm_num [world12327, agent12327, scalar12327, tp12327, tm12327, ep12327, em12327, dsL]
  · norm_num [world12327, agent12327, scalar12327, tp12327, tm12327, ep12327, em12327, dsL]
  · norm_num [world12327, agent12327, scalar12327, tp12327, tm12327, ep12327, em12327, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12327, agent12327, tp12327, tm12327, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12327, agent12327, tp12327, tm12327, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12327, agent12327, scalar12327, tp12327, tm12327, ep12327, em12327, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12327, agent12327, tp12327, tm12327, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12327, agent12327, scalar12327, tp12327, tm12327, ep12327, em12327, dsL]

theorem tails12327 :
    exp (-((12327:ℝ)*ep12327)) ≤ scalar12327.upperTail ∧
    exp (-((12327:ℝ)*em12327)) ≤ scalar12327.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12327:ℝ)) (by norm_num [ep12327]) ?_)
      (show bp12327^8 ≤ scalar12327.upperTail by norm_num [bp12327, scalar12327])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12327, bp12327, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12327:ℝ)) (by norm_num [em12327]) ?_)
      (show bm12327^8 ≤ scalar12327.lowerTail by norm_num [bm12327, scalar12327])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12327, bm12327, Finset.sum_range_succ, Nat.factorial]

theorem guards12327 :
    agent12327.root+dsL+scalar12327.worldRadius < √(1/100/aL) ∧
    2*(agent12327.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12327, agent12327, scalar12327, tp12327, tm12327, ep12327, em12327, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12327, agent12327, scalar12327, tp12327, tm12327, ep12327, em12327, dsL]

noncomputable def master12327 : MasterCertificate 12327 world12327 agent12327 :=
  master scalar12327 dsL tp12327 tm12327 ep12327 em12327
    (by norm_num [dsL]) (by norm_num [tp12327]) (by norm_num [tm12327])
    (by norm_num [ep12327]) (by norm_num [em12327])
    positive12327 negative12327 tails12327.1 tails12327.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12327.1 guards12327.2

theorem preserves12327 : master12327.toScalarCertificate = scalar12327 := rfl

noncomputable def tp12328 : ℝ := (115585507 / 500000000)
noncomputable def tm12328 : ℝ := (-((1215805623 / 2000000000)))
noncomputable def ep12328 : ℝ := (50910473294149687 / 100000000000000000000)
noncomputable def em12328 : ℝ := (1991948524332071 / 4000000000000000000)
noncomputable def bp12328 : ℝ := (5704174361016290127 / 12500000000000000000)
noncomputable def bm12328 : ℝ := (46421931861550061303 / 100000000000000000000)

theorem positive12328 :
    Eplus aL (agent12328.root+dsL) scalar12328.worldRadius world12328.frame
      agent12328.frame tp12328 ≤ -ep12328 := by
  apply positive_check (eT := (1446283941555210881 / 1250000000000000000)) (y := (37234663046735100267 / 100000000000000000000)) (u := (36278397551005260361 / 25000000000000000000))
  · norm_num [world12328, agent12328, scalar12328, tp12328, tm12328, ep12328, em12328, dsL]
  · norm_num [world12328, agent12328, scalar12328, tp12328, tm12328, ep12328, em12328, dsL]
  · norm_num [world12328, agent12328, scalar12328, tp12328, tm12328, ep12328, em12328, dsL]
  · norm_num [world12328, agent12328, scalar12328, tp12328, tm12328, ep12328, em12328, dsL]
  · norm_num [world12328, agent12328, scalar12328, tp12328, tm12328, ep12328, em12328, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12328, agent12328, tp12328, tm12328, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12328, agent12328, scalar12328, tp12328, tm12328, ep12328, em12328, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12328, agent12328, tp12328, tm12328, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12328, agent12328, scalar12328, tp12328, tm12328, ep12328, em12328, dsL]

theorem negative12328 :
    Eminus aL (agent12328.root+dsL) scalar12328.worldRadius world12328.frame
      agent12328.frame tm12328 ≤ -em12328 := by
  apply negative_check (lo := (68143988140544822051 / 100000000000000000000)) (hi := (17035997035136205513 / 25000000000000000000))
    (y := (-((17714000430586648483 / 25000000000000000000)))) (u := (12308816665168877223 / 25000000000000000000))
  · norm_num [world12328, agent12328, scalar12328, tp12328, tm12328, ep12328, em12328, dsL]
  · norm_num [world12328, agent12328, scalar12328, tp12328, tm12328, ep12328, em12328, dsL]
  · norm_num [world12328, agent12328, scalar12328, tp12328, tm12328, ep12328, em12328, dsL]
  · norm_num [world12328, agent12328, scalar12328, tp12328, tm12328, ep12328, em12328, dsL]
  · norm_num [world12328, agent12328, scalar12328, tp12328, tm12328, ep12328, em12328, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12328, agent12328, tp12328, tm12328, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12328, agent12328, tp12328, tm12328, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12328, agent12328, scalar12328, tp12328, tm12328, ep12328, em12328, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12328, agent12328, tp12328, tm12328, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12328, agent12328, scalar12328, tp12328, tm12328, ep12328, em12328, dsL]

theorem tails12328 :
    exp (-((12328:ℝ)*ep12328)) ≤ scalar12328.upperTail ∧
    exp (-((12328:ℝ)*em12328)) ≤ scalar12328.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12328:ℝ)) (by norm_num [ep12328]) ?_)
      (show bp12328^8 ≤ scalar12328.upperTail by norm_num [bp12328, scalar12328])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12328, bp12328, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12328:ℝ)) (by norm_num [em12328]) ?_)
      (show bm12328^8 ≤ scalar12328.lowerTail by norm_num [bm12328, scalar12328])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12328, bm12328, Finset.sum_range_succ, Nat.factorial]

theorem guards12328 :
    agent12328.root+dsL+scalar12328.worldRadius < √(1/100/aL) ∧
    2*(agent12328.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12328, agent12328, scalar12328, tp12328, tm12328, ep12328, em12328, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12328, agent12328, scalar12328, tp12328, tm12328, ep12328, em12328, dsL]

noncomputable def master12328 : MasterCertificate 12328 world12328 agent12328 :=
  master scalar12328 dsL tp12328 tm12328 ep12328 em12328
    (by norm_num [dsL]) (by norm_num [tp12328]) (by norm_num [tm12328])
    (by norm_num [ep12328]) (by norm_num [em12328])
    positive12328 negative12328 tails12328.1 tails12328.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12328.1 guards12328.2

theorem preserves12328 : master12328.toScalarCertificate = scalar12328 := rfl

noncomputable def tp12329 : ℝ := (462362007 / 2000000000)
noncomputable def tm12329 : ℝ := (-((1519812563 / 2500000000)))
noncomputable def ep12329 : ℝ := (2545674577339003 / 5000000000000000000)
noncomputable def em12329 : ℝ := (9960270499784261 / 20000000000000000000)
noncomputable def bp12329 : ℝ := (22814184251675604099 / 50000000000000000000)
noncomputable def bm12329 : ℝ := (2901072134000831437 / 6250000000000000000)

theorem positive12329 :
    Eplus aL (agent12329.root+dsL) scalar12329.worldRadius world12329.frame
      agent12329.frame tp12329 ≤ -ep12329 := by
  apply positive_check (eT := (28925762778653346037 / 25000000000000000000)) (y := (7447095555133888807 / 20000000000000000000)) (u := (29022954498248862031 / 20000000000000000000))
  · norm_num [world12329, agent12329, scalar12329, tp12329, tm12329, ep12329, em12329, dsL]
  · norm_num [world12329, agent12329, scalar12329, tp12329, tm12329, ep12329, em12329, dsL]
  · norm_num [world12329, agent12329, scalar12329, tp12329, tm12329, ep12329, em12329, dsL]
  · norm_num [world12329, agent12329, scalar12329, tp12329, tm12329, ep12329, em12329, dsL]
  · norm_num [world12329, agent12329, scalar12329, tp12329, tm12329, ep12329, em12329, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12329, agent12329, tp12329, tm12329, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12329, agent12329, scalar12329, tp12329, tm12329, ep12329, em12329, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12329, agent12329, tp12329, tm12329, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12329, agent12329, scalar12329, tp12329, tm12329, ep12329, em12329, dsL]

theorem negative12329 :
    Eminus aL (agent12329.root+dsL) scalar12329.worldRadius world12329.frame
      agent12329.frame tm12329 ≤ -em12329 := by
  apply negative_check (lo := (34071821218406555727 / 50000000000000000000)) (hi := (13628728487362622291 / 20000000000000000000))
    (y := (-((14171208385608853803 / 20000000000000000000)))) (u := (9847049373059405043 / 20000000000000000000))
  · norm_num [world12329, agent12329, scalar12329, tp12329, tm12329, ep12329, em12329, dsL]
  · norm_num [world12329, agent12329, scalar12329, tp12329, tm12329, ep12329, em12329, dsL]
  · norm_num [world12329, agent12329, scalar12329, tp12329, tm12329, ep12329, em12329, dsL]
  · norm_num [world12329, agent12329, scalar12329, tp12329, tm12329, ep12329, em12329, dsL]
  · norm_num [world12329, agent12329, scalar12329, tp12329, tm12329, ep12329, em12329, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12329, agent12329, tp12329, tm12329, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12329, agent12329, tp12329, tm12329, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12329, agent12329, scalar12329, tp12329, tm12329, ep12329, em12329, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12329, agent12329, tp12329, tm12329, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12329, agent12329, scalar12329, tp12329, tm12329, ep12329, em12329, dsL]

theorem tails12329 :
    exp (-((12329:ℝ)*ep12329)) ≤ scalar12329.upperTail ∧
    exp (-((12329:ℝ)*em12329)) ≤ scalar12329.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12329:ℝ)) (by norm_num [ep12329]) ?_)
      (show bp12329^8 ≤ scalar12329.upperTail by norm_num [bp12329, scalar12329])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12329, bp12329, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12329:ℝ)) (by norm_num [em12329]) ?_)
      (show bm12329^8 ≤ scalar12329.lowerTail by norm_num [bm12329, scalar12329])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12329, bm12329, Finset.sum_range_succ, Nat.factorial]

theorem guards12329 :
    agent12329.root+dsL+scalar12329.worldRadius < √(1/100/aL) ∧
    2*(agent12329.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12329, agent12329, scalar12329, tp12329, tm12329, ep12329, em12329, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12329, agent12329, scalar12329, tp12329, tm12329, ep12329, em12329, dsL]

noncomputable def master12329 : MasterCertificate 12329 world12329 agent12329 :=
  master scalar12329 dsL tp12329 tm12329 ep12329 em12329
    (by norm_num [dsL]) (by norm_num [tp12329]) (by norm_num [tm12329])
    (by norm_num [ep12329]) (by norm_num [em12329])
    positive12329 negative12329 tails12329.1 tails12329.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12329.1 guards12329.2

theorem preserves12329 : master12329.toScalarCertificate = scalar12329 := rfl

noncomputable def tp12330 : ℝ := (2311910017 / 10000000000)
noncomputable def tm12330 : ℝ := (-((607947227 / 1000000000)))
noncomputable def ep12330 : ℝ := (2036660309338057 / 4000000000000000000)
noncomputable def em12330 : ℝ := (24901995003726463 / 50000000000000000000)
noncomputable def bp12330 : ℝ := (11405835945169163091 / 25000000000000000000)
noncomputable def bm12330 : ℝ := (11603094489565196897 / 25000000000000000000)

theorem positive12330 :
    Eplus aL (agent12330.root+dsL) scalar12330.worldRadius world12330.frame
      agent12330.frame tp12330 ≤ -ep12330 := by
  apply positive_check (eT := (115703387572292913973 / 100000000000000000000)) (y := (37236294348780707849 / 100000000000000000000)) (u := (566859208844902439 / 390625000000000000))
  · norm_num [world12330, agent12330, scalar12330, tp12330, tm12330, ep12330, em12330, dsL]
  · norm_num [world12330, agent12330, scalar12330, tp12330, tm12330, ep12330, em12330, dsL]
  · norm_num [world12330, agent12330, scalar12330, tp12330, tm12330, ep12330, em12330, dsL]
  · norm_num [world12330, agent12330, scalar12330, tp12330, tm12330, ep12330, em12330, dsL]
  · norm_num [world12330, agent12330, scalar12330, tp12330, tm12330, ep12330, em12330, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12330, agent12330, tp12330, tm12330, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12330, agent12330, scalar12330, tp12330, tm12330, ep12330, em12330, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12330, agent12330, tp12330, tm12330, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12330, agent12330, scalar12330, tp12330, tm12330, ep12330, em12330, dsL]

theorem negative12330 :
    Eminus aL (agent12330.root+dsL) scalar12330.worldRadius world12330.frame
      agent12330.frame tm12330 ≤ -em12330 := by
  apply negative_check (lo := (34071648594820052551 / 50000000000000000000)) (hi := (68143297189640105103 / 100000000000000000000))
    (y := (-((2834243255374704109 / 4000000000000000000)))) (u := (3077201714930166273 / 6250000000000000000))
  · norm_num [world12330, agent12330, scalar12330, tp12330, tm12330, ep12330, em12330, dsL]
  · norm_num [world12330, agent12330, scalar12330, tp12330, tm12330, ep12330, em12330, dsL]
  · norm_num [world12330, agent12330, scalar12330, tp12330, tm12330, ep12330, em12330, dsL]
  · norm_num [world12330, agent12330, scalar12330, tp12330, tm12330, ep12330, em12330, dsL]
  · norm_num [world12330, agent12330, scalar12330, tp12330, tm12330, ep12330, em12330, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12330, agent12330, tp12330, tm12330, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12330, agent12330, tp12330, tm12330, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12330, agent12330, scalar12330, tp12330, tm12330, ep12330, em12330, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12330, agent12330, tp12330, tm12330, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12330, agent12330, scalar12330, tp12330, tm12330, ep12330, em12330, dsL]

theorem tails12330 :
    exp (-((12330:ℝ)*ep12330)) ≤ scalar12330.upperTail ∧
    exp (-((12330:ℝ)*em12330)) ≤ scalar12330.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12330:ℝ)) (by norm_num [ep12330]) ?_)
      (show bp12330^8 ≤ scalar12330.upperTail by norm_num [bp12330, scalar12330])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12330, bp12330, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12330:ℝ)) (by norm_num [em12330]) ?_)
      (show bm12330^8 ≤ scalar12330.lowerTail by norm_num [bm12330, scalar12330])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12330, bm12330, Finset.sum_range_succ, Nat.factorial]

theorem guards12330 :
    agent12330.root+dsL+scalar12330.worldRadius < √(1/100/aL) ∧
    2*(agent12330.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12330, agent12330, scalar12330, tp12330, tm12330, ep12330, em12330, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12330, agent12330, scalar12330, tp12330, tm12330, ep12330, em12330, dsL]

noncomputable def master12330 : MasterCertificate 12330 world12330 agent12330 :=
  master scalar12330 dsL tp12330 tm12330 ep12330 em12330
    (by norm_num [dsL]) (by norm_num [tp12330]) (by norm_num [tm12330])
    (by norm_num [ep12330]) (by norm_num [em12330])
    positive12330 negative12330 tails12330.1 tails12330.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12330.1 guards12330.2

theorem preserves12330 : master12330.toScalarCertificate = scalar12330 := rfl

noncomputable def tp12331 : ℝ := (11560049 / 50000000)
noncomputable def tm12331 : ℝ := (-((1519923567 / 2500000000)))
noncomputable def ep12331 : ℝ := (25459761436299399 / 50000000000000000000)
noncomputable def em12331 : ℝ := (9961325302401803 / 20000000000000000000)
noncomputable def bp12331 : ℝ := (45618320003920935723 / 100000000000000000000)
noncomputable def bm12331 : ℝ := (23203801338060631857 / 50000000000000000000)

theorem positive12331 :
    Eplus aL (agent12331.root+dsL) scalar12331.worldRadius world12331.frame
      agent12331.frame tp12331 ≤ -ep12331 := by
  apply positive_check (eT := (7231482663107947393 / 6250000000000000000)) (y := (37237107919238516983 / 100000000000000000000)) (u := (72558569044828561913 / 50000000000000000000))
  · norm_num [world12331, agent12331, scalar12331, tp12331, tm12331, ep12331, em12331, dsL]
  · norm_num [world12331, agent12331, scalar12331, tp12331, tm12331, ep12331, em12331, dsL]
  · norm_num [world12331, agent12331, scalar12331, tp12331, tm12331, ep12331, em12331, dsL]
  · norm_num [world12331, agent12331, scalar12331, tp12331, tm12331, ep12331, em12331, dsL]
  · norm_num [world12331, agent12331, scalar12331, tp12331, tm12331, ep12331, em12331, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12331, agent12331, tp12331, tm12331, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12331, agent12331, scalar12331, tp12331, tm12331, ep12331, em12331, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12331, agent12331, tp12331, tm12331, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12331, agent12331, scalar12331, tp12331, tm12331, ep12331, em12331, dsL]

theorem negative12331 :
    Eminus aL (agent12331.root+dsL) scalar12331.worldRadius world12331.frame
      agent12331.frame tm12331 ≤ -em12331 := by
  apply negative_check (lo := (8517868996670414081 / 12500000000000000000)) (hi := (68142951973363312649 / 100000000000000000000))
    (y := (-((70856121456829914489 / 100000000000000000000)))) (u := (6154400963639831739 / 12500000000000000000))
  · norm_num [world12331, agent12331, scalar12331, tp12331, tm12331, ep12331, em12331, dsL]
  · norm_num [world12331, agent12331, scalar12331, tp12331, tm12331, ep12331, em12331, dsL]
  · norm_num [world12331, agent12331, scalar12331, tp12331, tm12331, ep12331, em12331, dsL]
  · norm_num [world12331, agent12331, scalar12331, tp12331, tm12331, ep12331, em12331, dsL]
  · norm_num [world12331, agent12331, scalar12331, tp12331, tm12331, ep12331, em12331, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12331, agent12331, tp12331, tm12331, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12331, agent12331, tp12331, tm12331, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12331, agent12331, scalar12331, tp12331, tm12331, ep12331, em12331, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12331, agent12331, tp12331, tm12331, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12331, agent12331, scalar12331, tp12331, tm12331, ep12331, em12331, dsL]

theorem tails12331 :
    exp (-((12331:ℝ)*ep12331)) ≤ scalar12331.upperTail ∧
    exp (-((12331:ℝ)*em12331)) ≤ scalar12331.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12331:ℝ)) (by norm_num [ep12331]) ?_)
      (show bp12331^8 ≤ scalar12331.upperTail by norm_num [bp12331, scalar12331])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12331, bp12331, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12331:ℝ)) (by norm_num [em12331]) ?_)
      (show bm12331^8 ≤ scalar12331.lowerTail by norm_num [bm12331, scalar12331])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12331, bm12331, Finset.sum_range_succ, Nat.factorial]

theorem guards12331 :
    agent12331.root+dsL+scalar12331.worldRadius < √(1/100/aL) ∧
    2*(agent12331.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12331, agent12331, scalar12331, tp12331, tm12331, ep12331, em12331, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12331, agent12331, scalar12331, tp12331, tm12331, ep12331, em12331, dsL]

noncomputable def master12331 : MasterCertificate 12331 world12331 agent12331 :=
  master scalar12331 dsL tp12331 tm12331 ep12331 em12331
    (by norm_num [dsL]) (by norm_num [tp12331]) (by norm_num [tm12331])
    (by norm_num [ep12331]) (by norm_num [em12331])
    positive12331 negative12331 tails12331.1 tails12331.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12331.1 guards12331.2

theorem preserves12331 : master12331.toScalarCertificate = scalar12331 := rfl

noncomputable def tp12332 : ℝ := (36126713 / 156250000)
noncomputable def tm12332 : ℝ := (-((6079916069 / 10000000000)))
noncomputable def ep12332 : ℝ := (50922536746424181 / 100000000000000000000)
noncomputable def em12332 : ℝ := (24904630929703033 / 50000000000000000000)
noncomputable def bp12332 : ℝ := (11403324331553174763 / 25000000000000000000)
noncomputable def bm12332 : ℝ := (23201414203581873249 / 50000000000000000000)

theorem positive12332 :
    Eplus aL (agent12332.root+dsL) scalar12332.worldRadius world12332.frame
      agent12332.frame tp12332 ≤ -ep12332 := by
  apply positive_check (eT := (57852029018630908821 / 50000000000000000000)) (y := (37237922729597238431 / 100000000000000000000)) (u := (72559160261973925231 / 50000000000000000000))
  · norm_num [world12332, agent12332, scalar12332, tp12332, tm12332, ep12332, em12332, dsL]
  · norm_num [world12332, agent12332, scalar12332, tp12332, tm12332, ep12332, em12332, dsL]
  · norm_num [world12332, agent12332, scalar12332, tp12332, tm12332, ep12332, em12332, dsL]
  · norm_num [world12332, agent12332, scalar12332, tp12332, tm12332, ep12332, em12332, dsL]
  · norm_num [world12332, agent12332, scalar12332, tp12332, tm12332, ep12332, em12332, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12332, agent12332, tp12332, tm12332, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12332, agent12332, scalar12332, tp12332, tm12332, ep12332, em12332, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12332, agent12332, tp12332, tm12332, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12332, agent12332, scalar12332, tp12332, tm12332, ep12332, em12332, dsL]

theorem negative12332 :
    Eminus aL (agent12332.root+dsL) scalar12332.worldRadius world12332.frame
      agent12332.frame tm12332 ≤ -em12332 := by
  apply negative_check (lo := (34071303774460880923 / 50000000000000000000)) (hi := (68142607548921761847 / 100000000000000000000))
    (y := (-((4428510035806218693 / 6250000000000000000)))) (u := (49235188450244312949 / 100000000000000000000))
  · norm_num [world12332, agent12332, scalar12332, tp12332, tm12332, ep12332, em12332, dsL]
  · norm_num [world12332, agent12332, scalar12332, tp12332, tm12332, ep12332, em12332, dsL]
  · norm_num [world12332, agent12332, scalar12332, tp12332, tm12332, ep12332, em12332, dsL]
  · norm_num [world12332, agent12332, scalar12332, tp12332, tm12332, ep12332, em12332, dsL]
  · norm_num [world12332, agent12332, scalar12332, tp12332, tm12332, ep12332, em12332, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12332, agent12332, tp12332, tm12332, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12332, agent12332, tp12332, tm12332, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12332, agent12332, scalar12332, tp12332, tm12332, ep12332, em12332, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12332, agent12332, tp12332, tm12332, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12332, agent12332, scalar12332, tp12332, tm12332, ep12332, em12332, dsL]

theorem tails12332 :
    exp (-((12332:ℝ)*ep12332)) ≤ scalar12332.upperTail ∧
    exp (-((12332:ℝ)*em12332)) ≤ scalar12332.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12332:ℝ)) (by norm_num [ep12332]) ?_)
      (show bp12332^8 ≤ scalar12332.upperTail by norm_num [bp12332, scalar12332])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12332, bp12332, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12332:ℝ)) (by norm_num [em12332]) ?_)
      (show bm12332^8 ≤ scalar12332.lowerTail by norm_num [bm12332, scalar12332])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12332, bm12332, Finset.sum_range_succ, Nat.factorial]

theorem guards12332 :
    agent12332.root+dsL+scalar12332.worldRadius < √(1/100/aL) ∧
    2*(agent12332.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12332, agent12332, scalar12332, tp12332, tm12332, ep12332, em12332, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12332, agent12332, scalar12332, tp12332, tm12332, ep12332, em12332, dsL]

noncomputable def master12332 : MasterCertificate 12332 world12332 agent12332 :=
  master scalar12332 dsL tp12332 tm12332 ep12332 em12332
    (by norm_num [dsL]) (by norm_num [tp12332]) (by norm_num [tm12332])
    (by norm_num [ep12332]) (by norm_num [em12332])
    positive12332 negative12332 tails12332.1 tails12332.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12332.1 guards12332.2

theorem preserves12332 : master12332.toScalarCertificate = scalar12332 := rfl

noncomputable def tp12333 : ℝ := (1156104689 / 5000000000)
noncomputable def tm12333 : ℝ := (-((3040068917 / 5000000000)))
noncomputable def ep12333 : ℝ := (12731387275549057 / 25000000000000000000)
noncomputable def em12333 : ℝ := (12452973941737341 / 25000000000000000000)
noncomputable def bp12333 : ℝ := (4560827592522471547 / 10000000000000000000)
noncomputable def bm12333 : ℝ := (11599513838396242881 / 25000000000000000000)

theorem positive12333 :
    Eplus aL (agent12333.root+dsL) scalar12333.worldRadius world12333.frame
      agent12333.frame tp12333 ≤ -ep12333 := by
  apply positive_check (eT := (28926098217368005653 / 25000000000000000000)) (y := (37238736541130563579 / 100000000000000000000)) (u := (72559750759191385023 / 50000000000000000000))
  · norm_num [world12333, agent12333, scalar12333, tp12333, tm12333, ep12333, em12333, dsL]
  · norm_num [world12333, agent12333, scalar12333, tp12333, tm12333, ep12333, em12333, dsL]
  · norm_num [world12333, agent12333, scalar12333, tp12333, tm12333, ep12333, em12333, dsL]
  · norm_num [world12333, agent12333, scalar12333, tp12333, tm12333, ep12333, em12333, dsL]
  · norm_num [world12333, agent12333, scalar12333, tp12333, tm12333, ep12333, em12333, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12333, agent12333, tp12333, tm12333, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12333, agent12333, scalar12333, tp12333, tm12333, ep12333, em12333, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12333, agent12333, tp12333, tm12333, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12333, agent12333, scalar12333, tp12333, tm12333, ep12333, em12333, dsL]

theorem negative12333 :
    Eminus aL (agent12333.root+dsL) scalar12333.worldRadius world12333.frame
      agent12333.frame tm12333 ≤ -em12333 := by
  apply negative_check (lo := (34071131612060457539 / 50000000000000000000)) (hi := (68142263224120915079 / 100000000000000000000))
    (y := (-((553564062691657839 / 781250000000000000)))) (u := (24617584513081217923 / 50000000000000000000))
  · norm_num [world12333, agent12333, scalar12333, tp12333, tm12333, ep12333, em12333, dsL]
  · norm_num [world12333, agent12333, scalar12333, tp12333, tm12333, ep12333, em12333, dsL]
  · norm_num [world12333, agent12333, scalar12333, tp12333, tm12333, ep12333, em12333, dsL]
  · norm_num [world12333, agent12333, scalar12333, tp12333, tm12333, ep12333, em12333, dsL]
  · norm_num [world12333, agent12333, scalar12333, tp12333, tm12333, ep12333, em12333, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12333, agent12333, tp12333, tm12333, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12333, agent12333, tp12333, tm12333, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12333, agent12333, scalar12333, tp12333, tm12333, ep12333, em12333, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12333, agent12333, tp12333, tm12333, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12333, agent12333, scalar12333, tp12333, tm12333, ep12333, em12333, dsL]

theorem tails12333 :
    exp (-((12333:ℝ)*ep12333)) ≤ scalar12333.upperTail ∧
    exp (-((12333:ℝ)*em12333)) ≤ scalar12333.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12333:ℝ)) (by norm_num [ep12333]) ?_)
      (show bp12333^8 ≤ scalar12333.upperTail by norm_num [bp12333, scalar12333])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12333, bp12333, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12333:ℝ)) (by norm_num [em12333]) ?_)
      (show bm12333^8 ≤ scalar12333.lowerTail by norm_num [bm12333, scalar12333])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12333, bm12333, Finset.sum_range_succ, Nat.factorial]

theorem guards12333 :
    agent12333.root+dsL+scalar12333.worldRadius < √(1/100/aL) ∧
    2*(agent12333.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12333, agent12333, scalar12333, tp12333, tm12333, ep12333, em12333, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12333, agent12333, scalar12333, tp12333, tm12333, ep12333, em12333, dsL]

noncomputable def master12333 : MasterCertificate 12333 world12333 agent12333 :=
  master scalar12333 dsL tp12333 tm12333 ep12333 em12333
    (by norm_num [dsL]) (by norm_num [tp12333]) (by norm_num [tm12333])
    (by norm_num [ep12333]) (by norm_num [em12333])
    positive12333 negative12333 tails12333.1 tails12333.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12333.1 guards12333.2

theorem preserves12333 : master12333.toScalarCertificate = scalar12333 := rfl

noncomputable def tp12334 : ℝ := (2312309107 / 10000000000)
noncomputable def tm12334 : ℝ := (-((380022473 / 625000000)))
noncomputable def ep12334 : ℝ := (2546427986797507 / 5000000000000000000)
noncomputable def em12334 : ℝ := (49814528086942897 / 100000000000000000000)
noncomputable def bp12334 : ℝ := (11400813986080483393 / 25000000000000000000)
noncomputable def bm12334 : ℝ := (2319664181050186189 / 5000000000000000000)

theorem positive12334 :
    Eplus aL (agent12334.root+dsL) scalar12334.worldRadius world12334.frame
      agent12334.frame tp12334 ≤ -ep12334 := by
  apply positive_check (eT := (57852363805011396051 / 50000000000000000000)) (y := (37239550397151151391 / 100000000000000000000)) (u := (72560341293494508443 / 50000000000000000000))
  · norm_num [world12334, agent12334, scalar12334, tp12334, tm12334, ep12334, em12334, dsL]
  · norm_num [world12334, agent12334, scalar12334, tp12334, tm12334, ep12334, em12334, dsL]
  · norm_num [world12334, agent12334, scalar12334, tp12334, tm12334, ep12334, em12334, dsL]
  · norm_num [world12334, agent12334, scalar12334, tp12334, tm12334, ep12334, em12334, dsL]
  · norm_num [world12334, agent12334, scalar12334, tp12334, tm12334, ep12334, em12334, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12334, agent12334, tp12334, tm12334, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12334, agent12334, scalar12334, tp12334, tm12334, ep12334, em12334, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12334, agent12334, tp12334, tm12334, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12334, agent12334, scalar12334, tp12334, tm12334, ep12334, em12334, dsL]

theorem negative12334 :
    Eminus aL (agent12334.root+dsL) scalar12334.worldRadius world12334.frame
      agent12334.frame tm12334 ≤ -em12334 := by
  apply negative_check (lo := (68141918977485250027 / 100000000000000000000)) (hi := (17035479744371312507 / 25000000000000000000))
    (y := (-((70856239570634725113 / 100000000000000000000)))) (u := (24617574777787932973 / 50000000000000000000))
  · norm_num [world12334, agent12334, scalar12334, tp12334, tm12334, ep12334, em12334, dsL]
  · norm_num [world12334, agent12334, scalar12334, tp12334, tm12334, ep12334, em12334, dsL]
  · norm_num [world12334, agent12334, scalar12334, tp12334, tm12334, ep12334, em12334, dsL]
  · norm_num [world12334, agent12334, scalar12334, tp12334, tm12334, ep12334, em12334, dsL]
  · norm_num [world12334, agent12334, scalar12334, tp12334, tm12334, ep12334, em12334, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12334, agent12334, tp12334, tm12334, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12334, agent12334, tp12334, tm12334, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12334, agent12334, scalar12334, tp12334, tm12334, ep12334, em12334, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12334, agent12334, tp12334, tm12334, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12334, agent12334, scalar12334, tp12334, tm12334, ep12334, em12334, dsL]

theorem tails12334 :
    exp (-((12334:ℝ)*ep12334)) ≤ scalar12334.upperTail ∧
    exp (-((12334:ℝ)*em12334)) ≤ scalar12334.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12334:ℝ)) (by norm_num [ep12334]) ?_)
      (show bp12334^8 ≤ scalar12334.upperTail by norm_num [bp12334, scalar12334])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12334, bp12334, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12334:ℝ)) (by norm_num [em12334]) ?_)
      (show bm12334^8 ≤ scalar12334.lowerTail by norm_num [bm12334, scalar12334])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12334, bm12334, Finset.sum_range_succ, Nat.factorial]

theorem guards12334 :
    agent12334.root+dsL+scalar12334.worldRadius < √(1/100/aL) ∧
    2*(agent12334.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12334, agent12334, scalar12334, tp12334, tm12334, ep12334, em12334, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12334, agent12334, scalar12334, tp12334, tm12334, ep12334, em12334, dsL]

noncomputable def master12334 : MasterCertificate 12334 world12334 agent12334 :=
  master scalar12334 dsL tp12334 tm12334 ep12334 em12334
    (by norm_num [dsL]) (by norm_num [tp12334]) (by norm_num [tm12334])
    (by norm_num [ep12334]) (by norm_num [em12334])
    positive12334 negative12334 tails12334.1 tails12334.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12334.1 guards12334.2

theorem preserves12334 : master12334.toScalarCertificate = scalar12334 := rfl

noncomputable def tp12335 : ℝ := (578102187 / 2500000000)
noncomputable def tm12335 : ℝ := (-((6080580997 / 10000000000)))
noncomputable def ep12335 : ℝ := (636644612107471 / 1250000000000000000)
noncomputable def em12335 : ℝ := (12454289776702093 / 25000000000000000000)
noncomputable def bp12335 : ℝ := (11399559289457208857 / 25000000000000000000)
noncomputable def bm12335 : ℝ := (23194256501905185553 / 50000000000000000000)

theorem positive12335 :
    Eplus aL (agent12335.root+dsL) scalar12335.worldRadius world12335.frame
      agent12335.frame tp12335 ≤ -ep12335 := by
  apply positive_check (eT := (115705061740698036263 / 100000000000000000000)) (y := (3724036327135281411 / 10000000000000000000)) (u := (72560931120186792941 / 50000000000000000000))
  · norm_num [world12335, agent12335, scalar12335, tp12335, tm12335, ep12335, em12335, dsL]
  · norm_num [world12335, agent12335, scalar12335, tp12335, tm12335, ep12335, em12335, dsL]
  · norm_num [world12335, agent12335, scalar12335, tp12335, tm12335, ep12335, em12335, dsL]
  · norm_num [world12335, agent12335, scalar12335, tp12335, tm12335, ep12335, em12335, dsL]
  · norm_num [world12335, agent12335, scalar12335, tp12335, tm12335, ep12335, em12335, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12335, agent12335, tp12335, tm12335, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12335, agent12335, scalar12335, tp12335, tm12335, ep12335, em12335, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12335, agent12335, tp12335, tm12335, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12335, agent12335, scalar12335, tp12335, tm12335, ep12335, em12335, dsL]

theorem negative12335 :
    Eminus aL (agent12335.root+dsL) scalar12335.worldRadius world12335.frame
      agent12335.frame tm12335 ≤ -em12335 := by
  apply negative_check (lo := (545132607894455331 / 800000000000000000)) (hi := (8517696998350864547 / 12500000000000000000))
    (y := (-((70856277412451219991 / 100000000000000000000)))) (u := (4923513092410444539 / 10000000000000000000))
  · norm_num [world12335, agent12335, scalar12335, tp12335, tm12335, ep12335, em12335, dsL]
  · norm_num [world12335, agent12335, scalar12335, tp12335, tm12335, ep12335, em12335, dsL]
  · norm_num [world12335, agent12335, scalar12335, tp12335, tm12335, ep12335, em12335, dsL]
  · norm_num [world12335, agent12335, scalar12335, tp12335, tm12335, ep12335, em12335, dsL]
  · norm_num [world12335, agent12335, scalar12335, tp12335, tm12335, ep12335, em12335, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12335, agent12335, tp12335, tm12335, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12335, agent12335, tp12335, tm12335, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12335, agent12335, scalar12335, tp12335, tm12335, ep12335, em12335, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12335, agent12335, tp12335, tm12335, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12335, agent12335, scalar12335, tp12335, tm12335, ep12335, em12335, dsL]

theorem tails12335 :
    exp (-((12335:ℝ)*ep12335)) ≤ scalar12335.upperTail ∧
    exp (-((12335:ℝ)*em12335)) ≤ scalar12335.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12335:ℝ)) (by norm_num [ep12335]) ?_)
      (show bp12335^8 ≤ scalar12335.upperTail by norm_num [bp12335, scalar12335])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12335, bp12335, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12335:ℝ)) (by norm_num [em12335]) ?_)
      (show bm12335^8 ≤ scalar12335.lowerTail by norm_num [bm12335, scalar12335])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12335, bm12335, Finset.sum_range_succ, Nat.factorial]

theorem guards12335 :
    agent12335.root+dsL+scalar12335.worldRadius < √(1/100/aL) ∧
    2*(agent12335.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12335, agent12335, scalar12335, tp12335, tm12335, ep12335, em12335, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12335, agent12335, scalar12335, tp12335, tm12335, ep12335, em12335, dsL]

noncomputable def master12335 : MasterCertificate 12335 world12335 agent12335 :=
  master scalar12335 dsL tp12335 tm12335 ep12335 em12335
    (by norm_num [dsL]) (by norm_num [tp12335]) (by norm_num [tm12335])
    (by norm_num [ep12335]) (by norm_num [em12335])
    positive12335 negative12335 tails12335.1 tails12335.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12335.1 guards12335.2

theorem preserves12335 : master12335.toScalarCertificate = scalar12335 := rfl

noncomputable def tp12336 : ℝ := (2312508401 / 10000000000)
noncomputable def tm12336 : ℝ := (-((1216160489 / 2000000000)))
noncomputable def ep12336 : ℝ := (25467288646987459 / 50000000000000000000)
noncomputable def em12336 : ℝ := (49819789269790101 / 100000000000000000000)
noncomputable def bp12336 : ℝ := (45593219218522051273 / 100000000000000000000)
noncomputable def bm12336 : ℝ := (23191871592481507533 / 50000000000000000000)

theorem positive12336 :
    Eplus aL (agent12336.root+dsL) scalar12336.worldRadius world12336.frame
      agent12336.frame tp12336 ≤ -ep12336 := by
  apply positive_check (eT := (23141079198276443323 / 20000000000000000000)) (y := (4655147080582885039 / 12500000000000000000)) (u := (145123042627668881467 / 100000000000000000000))
  · norm_num [world12336, agent12336, scalar12336, tp12336, tm12336, ep12336, em12336, dsL]
  · norm_num [world12336, agent12336, scalar12336, tp12336, tm12336, ep12336, em12336, dsL]
  · norm_num [world12336, agent12336, scalar12336, tp12336, tm12336, ep12336, em12336, dsL]
  · norm_num [world12336, agent12336, scalar12336, tp12336, tm12336, ep12336, em12336, dsL]
  · norm_num [world12336, agent12336, scalar12336, tp12336, tm12336, ep12336, em12336, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12336, agent12336, tp12336, tm12336, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12336, agent12336, scalar12336, tp12336, tm12336, ep12336, em12336, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12336, agent12336, tp12336, tm12336, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12336, agent12336, scalar12336, tp12336, tm12336, ep12336, em12336, dsL]

theorem negative12336 :
    Eminus aL (agent12336.root+dsL) scalar12336.worldRadius world12336.frame
      agent12336.frame tm12336 ≤ -em12336 := by
  apply negative_check (lo := (68141232859343359641 / 100000000000000000000)) (hi := (34070616429671679821 / 50000000000000000000))
    (y := (-((70856315956823069481 / 100000000000000000000)))) (u := (24617555973368079387 / 50000000000000000000))
  · norm_num [world12336, agent12336, scalar12336, tp12336, tm12336, ep12336, em12336, dsL]
  · norm_num [world12336, agent12336, scalar12336, tp12336, tm12336, ep12336, em12336, dsL]
  · norm_num [world12336, agent12336, scalar12336, tp12336, tm12336, ep12336, em12336, dsL]
  · norm_num [world12336, agent12336, scalar12336, tp12336, tm12336, ep12336, em12336, dsL]
  · norm_num [world12336, agent12336, scalar12336, tp12336, tm12336, ep12336, em12336, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12336, agent12336, tp12336, tm12336, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12336, agent12336, tp12336, tm12336, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12336, agent12336, scalar12336, tp12336, tm12336, ep12336, em12336, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12336, agent12336, tp12336, tm12336, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12336, agent12336, scalar12336, tp12336, tm12336, ep12336, em12336, dsL]

theorem tails12336 :
    exp (-((12336:ℝ)*ep12336)) ≤ scalar12336.upperTail ∧
    exp (-((12336:ℝ)*em12336)) ≤ scalar12336.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12336:ℝ)) (by norm_num [ep12336]) ?_)
      (show bp12336^8 ≤ scalar12336.upperTail by norm_num [bp12336, scalar12336])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12336, bp12336, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12336:ℝ)) (by norm_num [em12336]) ?_)
      (show bm12336^8 ≤ scalar12336.lowerTail by norm_num [bm12336, scalar12336])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12336, bm12336, Finset.sum_range_succ, Nat.factorial]

theorem guards12336 :
    agent12336.root+dsL+scalar12336.worldRadius < √(1/100/aL) ∧
    2*(agent12336.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12336, agent12336, scalar12336, tp12336, tm12336, ep12336, em12336, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12336, agent12336, scalar12336, tp12336, tm12336, ep12336, em12336, dsL]

noncomputable def master12336 : MasterCertificate 12336 world12336 agent12336 :=
  master scalar12336 dsL tp12336 tm12336 ep12336 em12336
    (by norm_num [dsL]) (by norm_num [tp12336]) (by norm_num [tm12336])
    (by norm_num [ep12336]) (by norm_num [em12336])
    positive12336 negative12336 tails12336.1 tails12336.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12336.1 guards12336.2

theorem preserves12336 : master12336.toScalarCertificate = scalar12336 := rfl

noncomputable def tp12337 : ℝ := (1156303967 / 5000000000)
noncomputable def tm12337 : ℝ := (-((1520255941 / 2500000000)))
noncomputable def ep12337 : ℝ := (203750334249157 / 400000000000000000)
noncomputable def em12337 : ℝ := (9964483511711699 / 20000000000000000000)
noncomputable def bp12337 : ℝ := (11397050733683469713 / 25000000000000000000)
noncomputable def bm12337 : ℝ := (1159474372302038987 / 2500000000000000000)

theorem positive12337 :
    Eplus aL (agent12337.root+dsL) scalar12337.worldRadius world12337.frame
      agent12337.frame tp12337 ≤ -ep12337 := by
  apply positive_check (eT := (7231608087415227963 / 6250000000000000000)) (y := (1862099413922447723 / 5000000000000000000)) (u := (72562110250046967491 / 50000000000000000000))
  · norm_num [world12337, agent12337, scalar12337, tp12337, tm12337, ep12337, em12337, dsL]
  · norm_num [world12337, agent12337, scalar12337, tp12337, tm12337, ep12337, em12337, dsL]
  · norm_num [world12337, agent12337, scalar12337, tp12337, tm12337, ep12337, em12337, dsL]
  · norm_num [world12337, agent12337, scalar12337, tp12337, tm12337, ep12337, em12337, dsL]
  · norm_num [world12337, agent12337, scalar12337, tp12337, tm12337, ep12337, em12337, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12337, agent12337, tp12337, tm12337, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12337, agent12337, scalar12337, tp12337, tm12337, ep12337, em12337, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12337, agent12337, tp12337, tm12337, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12337, agent12337, scalar12337, tp12337, tm12337, ep12337, em12337, dsL]

theorem negative12337 :
    Eminus aL (agent12337.root+dsL) scalar12337.worldRadius world12337.frame
      agent12337.frame tm12337 ≤ -em12337 := by
  apply negative_check (lo := (6814089023124663029 / 10000000000000000000)) (hi := (68140890231246630291 / 100000000000000000000))
    (y := (-((70856353654691651173 / 100000000000000000000)))) (u := (49235093386151859517 / 100000000000000000000))
  · norm_num [world12337, agent12337, scalar12337, tp12337, tm12337, ep12337, em12337, dsL]
  · norm_num [world12337, agent12337, scalar12337, tp12337, tm12337, ep12337, em12337, dsL]
  · norm_num [world12337, agent12337, scalar12337, tp12337, tm12337, ep12337, em12337, dsL]
  · norm_num [world12337, agent12337, scalar12337, tp12337, tm12337, ep12337, em12337, dsL]
  · norm_num [world12337, agent12337, scalar12337, tp12337, tm12337, ep12337, em12337, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12337, agent12337, tp12337, tm12337, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12337, agent12337, tp12337, tm12337, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12337, agent12337, scalar12337, tp12337, tm12337, ep12337, em12337, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12337, agent12337, tp12337, tm12337, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12337, agent12337, scalar12337, tp12337, tm12337, ep12337, em12337, dsL]

theorem tails12337 :
    exp (-((12337:ℝ)*ep12337)) ≤ scalar12337.upperTail ∧
    exp (-((12337:ℝ)*em12337)) ≤ scalar12337.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12337:ℝ)) (by norm_num [ep12337]) ?_)
      (show bp12337^8 ≤ scalar12337.upperTail by norm_num [bp12337, scalar12337])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12337, bp12337, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12337:ℝ)) (by norm_num [em12337]) ?_)
      (show bm12337^8 ≤ scalar12337.lowerTail by norm_num [bm12337, scalar12337])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12337, bm12337, Finset.sum_range_succ, Nat.factorial]

theorem guards12337 :
    agent12337.root+dsL+scalar12337.worldRadius < √(1/100/aL) ∧
    2*(agent12337.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12337, agent12337, scalar12337, tp12337, tm12337, ep12337, em12337, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12337, agent12337, scalar12337, tp12337, tm12337, ep12337, em12337, dsL]

noncomputable def master12337 : MasterCertificate 12337 world12337 agent12337 :=
  master scalar12337 dsL tp12337 tm12337 ep12337 em12337
    (by norm_num [dsL]) (by norm_num [tp12337]) (by norm_num [tm12337])
    (by norm_num [ep12337]) (by norm_num [em12337])
    positive12337 negative12337 tails12337.1 tails12337.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12337.1 guards12337.2

theorem preserves12337 : master12337.toScalarCertificate = scalar12337 := rfl

noncomputable def tp12338 : ℝ := (1156353747 / 5000000000)
noncomputable def tm12338 : ℝ := (-((6081244877 / 10000000000)))
noncomputable def ep12338 : ℝ := (25470294321311399 / 50000000000000000000)
noncomputable def em12338 : ℝ := (4982504469650939 / 10000000000000000000)
noncomputable def bp12338 : ℝ := (22791593847710220473 / 50000000000000000000)
noncomputable def bm12338 : ℝ := (2898387975484059257 / 6250000000000000000)

theorem positive12338 :
    Eplus aL (agent12338.root+dsL) scalar12338.worldRadius world12338.frame
      agent12338.frame tp12338 ≤ -ep12338 := by
  apply positive_check (eT := (28926515758859766071 / 25000000000000000000)) (y := (37242800970506850341 / 100000000000000000000)) (u := (72562699958950266741 / 50000000000000000000))
  · norm_num [world12338, agent12338, scalar12338, tp12338, tm12338, ep12338, em12338, dsL]
  · norm_num [world12338, agent12338, scalar12338, tp12338, tm12338, ep12338, em12338, dsL]
  · norm_num [world12338, agent12338, scalar12338, tp12338, tm12338, ep12338, em12338, dsL]
  · norm_num [world12338, agent12338, scalar12338, tp12338, tm12338, ep12338, em12338, dsL]
  · norm_num [world12338, agent12338, scalar12338, tp12338, tm12338, ep12338, em12338, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12338, agent12338, tp12338, tm12338, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12338, agent12338, scalar12338, tp12338, tm12338, ep12338, em12338, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12338, agent12338, tp12338, tm12338, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12338, agent12338, scalar12338, tp12338, tm12338, ep12338, em12338, dsL]

theorem negative12338 :
    Eminus aL (agent12338.root+dsL) scalar12338.worldRadius world12338.frame
      agent12338.frame tm12338 ≤ -em12338 := by
  apply negative_check (lo := (34070274216711379379 / 50000000000000000000)) (hi := (68140548433422758759 / 100000000000000000000))
    (y := (-((17714097618507588853 / 25000000000000000000)))) (u := (49235075258119401633 / 100000000000000000000))
  · norm_num [world12338, agent12338, scalar12338, tp12338, tm12338, ep12338, em12338, dsL]
  · norm_num [world12338, agent12338, scalar12338, tp12338, tm12338, ep12338, em12338, dsL]
  · norm_num [world12338, agent12338, scalar12338, tp12338, tm12338, ep12338, em12338, dsL]
  · norm_num [world12338, agent12338, scalar12338, tp12338, tm12338, ep12338, em12338, dsL]
  · norm_num [world12338, agent12338, scalar12338, tp12338, tm12338, ep12338, em12338, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12338, agent12338, tp12338, tm12338, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12338, agent12338, tp12338, tm12338, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12338, agent12338, scalar12338, tp12338, tm12338, ep12338, em12338, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12338, agent12338, tp12338, tm12338, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12338, agent12338, scalar12338, tp12338, tm12338, ep12338, em12338, dsL]

theorem tails12338 :
    exp (-((12338:ℝ)*ep12338)) ≤ scalar12338.upperTail ∧
    exp (-((12338:ℝ)*em12338)) ≤ scalar12338.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12338:ℝ)) (by norm_num [ep12338]) ?_)
      (show bp12338^8 ≤ scalar12338.upperTail by norm_num [bp12338, scalar12338])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12338, bp12338, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12338:ℝ)) (by norm_num [em12338]) ?_)
      (show bm12338^8 ≤ scalar12338.lowerTail by norm_num [bm12338, scalar12338])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12338, bm12338, Finset.sum_range_succ, Nat.factorial]

theorem guards12338 :
    agent12338.root+dsL+scalar12338.worldRadius < √(1/100/aL) ∧
    2*(agent12338.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12338, agent12338, scalar12338, tp12338, tm12338, ep12338, em12338, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12338, agent12338, scalar12338, tp12338, tm12338, ep12338, em12338, dsL]

noncomputable def master12338 : MasterCertificate 12338 world12338 agent12338 :=
  master scalar12338 dsL tp12338 tm12338 ep12338 em12338
    (by norm_num [dsL]) (by norm_num [tp12338]) (by norm_num [tm12338])
    (by norm_num [ep12338]) (by norm_num [em12338])
    positive12338 negative12338 tails12338.1 tails12338.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12338.1 guards12338.2

theorem preserves12338 : master12338.toScalarCertificate = scalar12338 := rfl

noncomputable def tp12339 : ℝ := (2312807017 / 10000000000)
noncomputable def tm12339 : ℝ := (-((3040733039 / 5000000000)))
noncomputable def ep12339 : ℝ := (3183974559166747 / 6250000000000000000)
noncomputable def em12339 : ℝ := (1557114722594537 / 3125000000000000000)
noncomputable def bp12339 : ℝ := (45578173211147366387 / 100000000000000000000)
noncomputable def bm12339 : ℝ := (23184720508850431353 / 50000000000000000000)

theorem positive12339 :
    Eplus aL (agent12339.root+dsL) scalar12339.worldRadius world12339.frame
      agent12339.frame tp12339 ≤ -ep12339 := by
  apply positive_check (eT := (115706396434637396591 / 100000000000000000000)) (y := (37243613264194729513 / 100000000000000000000)) (u := (72563289383575714269 / 50000000000000000000))
  · norm_num [world12339, agent12339, scalar12339, tp12339, tm12339, ep12339, em12339, dsL]
  · norm_num [world12339, agent12339, scalar12339, tp12339, tm12339, ep12339, em12339, dsL]
  · norm_num [world12339, agent12339, scalar12339, tp12339, tm12339, ep12339, em12339, dsL]
  · norm_num [world12339, agent12339, scalar12339, tp12339, tm12339, ep12339, em12339, dsL]
  · norm_num [world12339, agent12339, scalar12339, tp12339, tm12339, ep12339, em12339, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12339, agent12339, tp12339, tm12339, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12339, agent12339, scalar12339, tp12339, tm12339, ep12339, em12339, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12339, agent12339, tp12339, tm12339, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12339, agent12339, scalar12339, tp12339, tm12339, ep12339, em12339, dsL]

theorem negative12339 :
    Eminus aL (agent12339.root+dsL) scalar12339.worldRadius world12339.frame
      agent12339.frame tm12339 ≤ -em12339 := by
  apply negative_check (lo := (34070103101092697079 / 50000000000000000000)) (hi := (68140206202185394159 / 100000000000000000000))
    (y := (-((17714107194592224579 / 25000000000000000000)))) (u := (49235056398953104849 / 100000000000000000000))
  · norm_num [world12339, agent12339, scalar12339, tp12339, tm12339, ep12339, em12339, dsL]
  · norm_num [world12339, agent12339, scalar12339, tp12339, tm12339, ep12339, em12339, dsL]
  · norm_num [world12339, agent12339, scalar12339, tp12339, tm12339, ep12339, em12339, dsL]
  · norm_num [world12339, agent12339, scalar12339, tp12339, tm12339, ep12339, em12339, dsL]
  · norm_num [world12339, agent12339, scalar12339, tp12339, tm12339, ep12339, em12339, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12339, agent12339, tp12339, tm12339, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12339, agent12339, tp12339, tm12339, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12339, agent12339, scalar12339, tp12339, tm12339, ep12339, em12339, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12339, agent12339, tp12339, tm12339, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12339, agent12339, scalar12339, tp12339, tm12339, ep12339, em12339, dsL]

theorem tails12339 :
    exp (-((12339:ℝ)*ep12339)) ≤ scalar12339.upperTail ∧
    exp (-((12339:ℝ)*em12339)) ≤ scalar12339.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12339:ℝ)) (by norm_num [ep12339]) ?_)
      (show bp12339^8 ≤ scalar12339.upperTail by norm_num [bp12339, scalar12339])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12339, bp12339, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12339:ℝ)) (by norm_num [em12339]) ?_)
      (show bm12339^8 ≤ scalar12339.lowerTail by norm_num [bm12339, scalar12339])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12339, bm12339, Finset.sum_range_succ, Nat.factorial]

theorem guards12339 :
    agent12339.root+dsL+scalar12339.worldRadius < √(1/100/aL) ∧
    2*(agent12339.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12339, agent12339, scalar12339, tp12339, tm12339, ep12339, em12339, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12339, agent12339, scalar12339, tp12339, tm12339, ep12339, em12339, dsL]

noncomputable def master12339 : MasterCertificate 12339 world12339 agent12339 :=
  master scalar12339 dsL tp12339 tm12339 ep12339 em12339
    (by norm_num [dsL]) (by norm_num [tp12339]) (by norm_num [tm12339])
    (by norm_num [ep12339]) (by norm_num [em12339])
    positive12339 negative12339 tails12339.1 tails12339.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12339.1 guards12339.2

theorem preserves12339 : master12339.toScalarCertificate = scalar12339 := rfl

noncomputable def tp12340 : ℝ := (578226609 / 2500000000)
noncomputable def tm12340 : ℝ := (-((6081687087 / 10000000000)))
noncomputable def ep12340 : ℝ := (50946595053114257 / 100000000000000000000)
noncomputable def em12340 : ℝ := (12457573882068113 / 25000000000000000000)
noncomputable def bp12340 : ℝ := (45573160481052444817 / 100000000000000000000)
noncomputable def bm12340 : ℝ := (46364676058719920851 / 100000000000000000000)

theorem positive12340 :
    Eplus aL (agent12340.root+dsL) scalar12340.worldRadius world12340.frame
      agent12340.frame tp12340 ≤ -ep12340 := by
  apply positive_check (eT := (115706729107250771303 / 100000000000000000000)) (y := (7448884848989756749 / 20000000000000000000)) (u := (145127755720546673801 / 100000000000000000000))
  · norm_num [world12340, agent12340, scalar12340, tp12340, tm12340, ep12340, em12340, dsL]
  · norm_num [world12340, agent12340, scalar12340, tp12340, tm12340, ep12340, em12340, dsL]
  · norm_num [world12340, agent12340, scalar12340, tp12340, tm12340, ep12340, em12340, dsL]
  · norm_num [world12340, agent12340, scalar12340, tp12340, tm12340, ep12340, em12340, dsL]
  · norm_num [world12340, agent12340, scalar12340, tp12340, tm12340, ep12340, em12340, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12340, agent12340, tp12340, tm12340, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12340, agent12340, scalar12340, tp12340, tm12340, ep12340, em12340, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12340, agent12340, tp12340, tm12340, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12340, agent12340, scalar12340, tp12340, tm12340, ep12340, em12340, dsL]

theorem negative12340 :
    Eminus aL (agent12340.root+dsL) scalar12340.worldRadius world12340.frame
      agent12340.frame tm12340 ≤ -em12340 := by
  apply negative_check (lo := (34069932370516407383 / 50000000000000000000)) (hi := (68139864741032814767 / 100000000000000000000))
    (y := (-((70856465918601003359 / 100000000000000000000)))) (u := (24617519056471138481 / 50000000000000000000))
  · norm_num [world12340, agent12340, scalar12340, tp12340, tm12340, ep12340, em12340, dsL]
  · norm_num [world12340, agent12340, scalar12340, tp12340, tm12340, ep12340, em12340, dsL]
  · norm_num [world12340, agent12340, scalar12340, tp12340, tm12340, ep12340, em12340, dsL]
  · norm_num [world12340, agent12340, scalar12340, tp12340, tm12340, ep12340, em12340, dsL]
  · norm_num [world12340, agent12340, scalar12340, tp12340, tm12340, ep12340, em12340, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12340, agent12340, tp12340, tm12340, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12340, agent12340, tp12340, tm12340, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12340, agent12340, scalar12340, tp12340, tm12340, ep12340, em12340, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12340, agent12340, tp12340, tm12340, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12340, agent12340, scalar12340, tp12340, tm12340, ep12340, em12340, dsL]

theorem tails12340 :
    exp (-((12340:ℝ)*ep12340)) ≤ scalar12340.upperTail ∧
    exp (-((12340:ℝ)*em12340)) ≤ scalar12340.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12340:ℝ)) (by norm_num [ep12340]) ?_)
      (show bp12340^8 ≤ scalar12340.upperTail by norm_num [bp12340, scalar12340])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12340, bp12340, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12340:ℝ)) (by norm_num [em12340]) ?_)
      (show bm12340^8 ≤ scalar12340.lowerTail by norm_num [bm12340, scalar12340])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12340, bm12340, Finset.sum_range_succ, Nat.factorial]

theorem guards12340 :
    agent12340.root+dsL+scalar12340.worldRadius < √(1/100/aL) ∧
    2*(agent12340.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12340, agent12340, scalar12340, tp12340, tm12340, ep12340, em12340, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12340, agent12340, scalar12340, tp12340, tm12340, ep12340, em12340, dsL]

noncomputable def master12340 : MasterCertificate 12340 world12340 agent12340 :=
  master scalar12340 dsL tp12340 tm12340 ep12340 em12340
    (by norm_num [dsL]) (by norm_num [tp12340]) (by norm_num [tm12340])
    (by norm_num [ep12340]) (by norm_num [em12340])
    positive12340 negative12340 tails12340.1 tails12340.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12340.1 guards12340.2

theorem preserves12340 : master12340.toScalarCertificate = scalar12340 := rfl

noncomputable def tp12341 : ℝ := (2313005827 / 10000000000)
noncomputable def tm12341 : ℝ := (-((6081907957 / 10000000000)))
noncomputable def ep12341 : ℝ := (3184349766057811 / 6250000000000000000)
noncomputable def em12341 : ℝ := (24916459540394699 / 50000000000000000000)
noncomputable def bp12341 : ℝ := (45568148594764943051 / 100000000000000000000)
noncomputable def bm12341 : ℝ := (46359911895060060411 / 100000000000000000000)

theorem positive12341 :
    Eplus aL (agent12341.root+dsL) scalar12341.worldRadius world12341.frame
      agent12341.frame tp12341 ≤ -ep12341 := by
  apply positive_check (eT := (28926765401991834617 / 25000000000000000000)) (y := (9311308757975198413 / 25000000000000000000)) (u := (18141116550277998139 / 12500000000000000000))
  · norm_num [world12341, agent12341, scalar12341, tp12341, tm12341, ep12341, em12341, dsL]
  · norm_num [world12341, agent12341, scalar12341, tp12341, tm12341, ep12341, em12341, dsL]
  · norm_num [world12341, agent12341, scalar12341, tp12341, tm12341, ep12341, em12341, dsL]
  · norm_num [world12341, agent12341, scalar12341, tp12341, tm12341, ep12341, em12341, dsL]
  · norm_num [world12341, agent12341, scalar12341, tp12341, tm12341, ep12341, em12341, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12341, agent12341, tp12341, tm12341, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12341, agent12341, scalar12341, tp12341, tm12341, ep12341, em12341, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12341, agent12341, tp12341, tm12341, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12341, agent12341, scalar12341, tp12341, tm12341, ep12341, em12341, dsL]

theorem negative12341 :
    Eminus aL (agent12341.root+dsL) scalar12341.worldRadius world12341.frame
      agent12341.frame tm12341 ≤ -em12341 := by
  apply negative_check (lo := (13627904764427930889 / 20000000000000000000)) (hi := (34069761911069827223 / 50000000000000000000))
    (y := (-((70856502249730729909 / 100000000000000000000)))) (u := (1538594382040623707 / 3125000000000000000))
  · norm_num [world12341, agent12341, scalar12341, tp12341, tm12341, ep12341, em12341, dsL]
  · norm_num [world12341, agent12341, scalar12341, tp12341, tm12341, ep12341, em12341, dsL]
  · norm_num [world12341, agent12341, scalar12341, tp12341, tm12341, ep12341, em12341, dsL]
  · norm_num [world12341, agent12341, scalar12341, tp12341, tm12341, ep12341, em12341, dsL]
  · norm_num [world12341, agent12341, scalar12341, tp12341, tm12341, ep12341, em12341, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12341, agent12341, tp12341, tm12341, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12341, agent12341, tp12341, tm12341, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12341, agent12341, scalar12341, tp12341, tm12341, ep12341, em12341, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12341, agent12341, tp12341, tm12341, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12341, agent12341, scalar12341, tp12341, tm12341, ep12341, em12341, dsL]

theorem tails12341 :
    exp (-((12341:ℝ)*ep12341)) ≤ scalar12341.upperTail ∧
    exp (-((12341:ℝ)*em12341)) ≤ scalar12341.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12341:ℝ)) (by norm_num [ep12341]) ?_)
      (show bp12341^8 ≤ scalar12341.upperTail by norm_num [bp12341, scalar12341])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12341, bp12341, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12341:ℝ)) (by norm_num [em12341]) ?_)
      (show bm12341^8 ≤ scalar12341.lowerTail by norm_num [bm12341, scalar12341])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12341, bm12341, Finset.sum_range_succ, Nat.factorial]

theorem guards12341 :
    agent12341.root+dsL+scalar12341.worldRadius < √(1/100/aL) ∧
    2*(agent12341.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12341, agent12341, scalar12341, tp12341, tm12341, ep12341, em12341, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12341, agent12341, scalar12341, tp12341, tm12341, ep12341, em12341, dsL]

noncomputable def master12341 : MasterCertificate 12341 world12341 agent12341 :=
  master scalar12341 dsL tp12341 tm12341 ep12341 em12341
    (by norm_num [dsL]) (by norm_num [tp12341]) (by norm_num [tm12341])
    (by norm_num [ep12341]) (by norm_num [em12341])
    positive12341 negative12341 tails12341.1 tails12341.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12341.1 guards12341.2

theorem preserves12341 : master12341.toScalarCertificate = scalar12341 := rfl

noncomputable def tp12342 : ℝ := (2313105197 / 10000000000)
noncomputable def tm12342 : ℝ := (-((3041064331 / 5000000000)))
noncomputable def ep12342 : ℝ := (50952595593348101 / 100000000000000000000)
noncomputable def em12342 : ℝ := (49835540901112859 / 100000000000000000000)
noncomputable def bp12342 : ℝ := (45563138230430554587 / 100000000000000000000)
noncomputable def bm12342 : ℝ := (4635514915566782537 / 10000000000000000000)

theorem positive12342 :
    Eplus aL (agent12342.root+dsL) scalar12342.worldRadius world12342.frame
      agent12342.frame tp12342 ≤ -ep12342 := by
  apply positive_check (eT := (115707393987894334901 / 100000000000000000000)) (y := (18623023021981968451 / 50000000000000000000)) (u := (18141263677518218797 / 12500000000000000000))
  · norm_num [world12342, agent12342, scalar12342, tp12342, tm12342, ep12342, em12342, dsL]
  · norm_num [world12342, agent12342, scalar12342, tp12342, tm12342, ep12342, em12342, dsL]
  · norm_num [world12342, agent12342, scalar12342, tp12342, tm12342, ep12342, em12342, dsL]
  · norm_num [world12342, agent12342, scalar12342, tp12342, tm12342, ep12342, em12342, dsL]
  · norm_num [world12342, agent12342, scalar12342, tp12342, tm12342, ep12342, em12342, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12342, agent12342, tp12342, tm12342, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12342, agent12342, scalar12342, tp12342, tm12342, ep12342, em12342, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12342, agent12342, tp12342, tm12342, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12342, agent12342, scalar12342, tp12342, tm12342, ep12342, em12342, dsL]

theorem negative12342 :
    Eminus aL (agent12342.root+dsL) scalar12342.worldRadius world12342.frame
      agent12342.frame tm12342 ≤ -em12342 := by
  apply negative_check (lo := (68139183557186277037 / 100000000000000000000)) (hi := (34069591778593138519 / 50000000000000000000))
    (y := (-((7085653808676732701 / 10000000000000000000)))) (u := (49235002580930903503 / 100000000000000000000))
  · norm_num [world12342, agent12342, scalar12342, tp12342, tm12342, ep12342, em12342, dsL]
  · norm_num [world12342, agent12342, scalar12342, tp12342, tm12342, ep12342, em12342, dsL]
  · norm_num [world12342, agent12342, scalar12342, tp12342, tm12342, ep12342, em12342, dsL]
  · norm_num [world12342, agent12342, scalar12342, tp12342, tm12342, ep12342, em12342, dsL]
  · norm_num [world12342, agent12342, scalar12342, tp12342, tm12342, ep12342, em12342, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12342, agent12342, tp12342, tm12342, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12342, agent12342, tp12342, tm12342, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12342, agent12342, scalar12342, tp12342, tm12342, ep12342, em12342, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12342, agent12342, tp12342, tm12342, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12342, agent12342, scalar12342, tp12342, tm12342, ep12342, em12342, dsL]

theorem tails12342 :
    exp (-((12342:ℝ)*ep12342)) ≤ scalar12342.upperTail ∧
    exp (-((12342:ℝ)*em12342)) ≤ scalar12342.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12342:ℝ)) (by norm_num [ep12342]) ?_)
      (show bp12342^8 ≤ scalar12342.upperTail by norm_num [bp12342, scalar12342])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12342, bp12342, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12342:ℝ)) (by norm_num [em12342]) ?_)
      (show bm12342^8 ≤ scalar12342.lowerTail by norm_num [bm12342, scalar12342])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12342, bm12342, Finset.sum_range_succ, Nat.factorial]

theorem guards12342 :
    agent12342.root+dsL+scalar12342.worldRadius < √(1/100/aL) ∧
    2*(agent12342.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12342, agent12342, scalar12342, tp12342, tm12342, ep12342, em12342, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12342, agent12342, scalar12342, tp12342, tm12342, ep12342, em12342, dsL]

noncomputable def master12342 : MasterCertificate 12342 world12342 agent12342 :=
  master scalar12342 dsL tp12342 tm12342 ep12342 em12342
    (by norm_num [dsL]) (by norm_num [tp12342]) (by norm_num [tm12342])
    (by norm_num [ep12342]) (by norm_num [em12342])
    positive12342 negative12342 tails12342.1 tails12342.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12342.1 guards12342.2

theorem preserves12342 : master12342.toScalarCertificate = scalar12342 := rfl

noncomputable def tp12343 : ℝ := (2313204543 / 10000000000)
noncomputable def tm12343 : ℝ := (-((3041174721 / 5000000000)))
noncomputable def ep12343 : ℝ := (6369449252800637 / 12500000000000000000)
noncomputable def em12343 : ℝ := (24919080932362337 / 50000000000000000000)
noncomputable def bp12343 : ℝ := (22779064356591801713 / 50000000000000000000)
noncomputable def bm12343 : ℝ := (185401548857695427 / 400000000000000000)

theorem positive12343 :
    Eplus aL (agent12343.root+dsL) scalar12343.worldRadius world12343.frame
      agent12343.frame tp12343 ≤ -ep12343 := by
  apply positive_check (eT := (23141545245031251099 / 20000000000000000000)) (y := (7449371386241949279 / 20000000000000000000)) (u := (145131286266464309601 / 100000000000000000000))
  · norm_num [world12343, agent12343, scalar12343, tp12343, tm12343, ep12343, em12343, dsL]
  · norm_num [world12343, agent12343, scalar12343, tp12343, tm12343, ep12343, em12343, dsL]
  · norm_num [world12343, agent12343, scalar12343, tp12343, tm12343, ep12343, em12343, dsL]
  · norm_num [world12343, agent12343, scalar12343, tp12343, tm12343, ep12343, em12343, dsL]
  · norm_num [world12343, agent12343, scalar12343, tp12343, tm12343, ep12343, em12343, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12343, agent12343, tp12343, tm12343, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12343, agent12343, scalar12343, tp12343, tm12343, ep12343, em12343, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12343, agent12343, tp12343, tm12343, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12343, agent12343, scalar12343, tp12343, tm12343, ep12343, em12343, dsL]

theorem negative12343 :
    Eminus aL (agent12343.root+dsL) scalar12343.worldRadius world12343.frame
      agent12343.frame tm12343 ≤ -em12343 := by
  apply negative_check (lo := (68138842914674215643 / 100000000000000000000)) (hi := (17034710728668553911 / 25000000000000000000))
    (y := (-((7085657515965333433 / 10000000000000000000)))) (u := (123087460820244761 / 250000000000000000))
  · norm_num [world12343, agent12343, scalar12343, tp12343, tm12343, ep12343, em12343, dsL]
  · norm_num [world12343, agent12343, scalar12343, tp12343, tm12343, ep12343, em12343, dsL]
  · norm_num [world12343, agent12343, scalar12343, tp12343, tm12343, ep12343, em12343, dsL]
  · norm_num [world12343, agent12343, scalar12343, tp12343, tm12343, ep12343, em12343, dsL]
  · norm_num [world12343, agent12343, scalar12343, tp12343, tm12343, ep12343, em12343, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12343, agent12343, tp12343, tm12343, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12343, agent12343, tp12343, tm12343, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12343, agent12343, scalar12343, tp12343, tm12343, ep12343, em12343, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12343, agent12343, tp12343, tm12343, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12343, agent12343, scalar12343, tp12343, tm12343, ep12343, em12343, dsL]

theorem tails12343 :
    exp (-((12343:ℝ)*ep12343)) ≤ scalar12343.upperTail ∧
    exp (-((12343:ℝ)*em12343)) ≤ scalar12343.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12343:ℝ)) (by norm_num [ep12343]) ?_)
      (show bp12343^8 ≤ scalar12343.upperTail by norm_num [bp12343, scalar12343])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12343, bp12343, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12343:ℝ)) (by norm_num [em12343]) ?_)
      (show bm12343^8 ≤ scalar12343.lowerTail by norm_num [bm12343, scalar12343])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12343, bm12343, Finset.sum_range_succ, Nat.factorial]

theorem guards12343 :
    agent12343.root+dsL+scalar12343.worldRadius < √(1/100/aL) ∧
    2*(agent12343.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12343, agent12343, scalar12343, tp12343, tm12343, ep12343, em12343, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12343, agent12343, scalar12343, tp12343, tm12343, ep12343, em12343, dsL]

noncomputable def master12343 : MasterCertificate 12343 world12343 agent12343 :=
  master scalar12343 dsL tp12343 tm12343 ep12343 em12343
    (by norm_num [dsL]) (by norm_num [tp12343]) (by norm_num [tm12343])
    (by norm_num [ep12343]) (by norm_num [em12343])
    positive12343 negative12343 tails12343.1 tails12343.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12343.1 guards12343.2

theorem preserves12343 : master12343.toScalarCertificate = scalar12343 := rfl

noncomputable def tp12344 : ℝ := (144581487 / 625000000)
noncomputable def tm12344 : ℝ := (-((760321247 / 1250000000)))
noncomputable def ep12344 : ℝ := (50958590738307831 / 100000000000000000000)
noncomputable def em12344 : ℝ := (49840781248717809 / 100000000000000000000)
noncomputable def bp12344 : ℝ := (45553120609396928193 / 100000000000000000000)
noncomputable def bm12344 : ℝ := (46345626588291825611 / 100000000000000000000)

theorem positive12344 :
    Eplus aL (agent12344.root+dsL) scalar12344.worldRadius world12344.frame
      agent12344.frame tp12344 ≤ -ep12344 := by
  apply positive_check (eT := (115708057786986271123 / 100000000000000000000)) (y := (7449533295478713597 / 20000000000000000000)) (u := (72566230588004761113 / 50000000000000000000))
  · norm_num [world12344, agent12344, scalar12344, tp12344, tm12344, ep12344, em12344, dsL]
  · norm_num [world12344, agent12344, scalar12344, tp12344, tm12344, ep12344, em12344, dsL]
  · norm_num [world12344, agent12344, scalar12344, tp12344, tm12344, ep12344, em12344, dsL]
  · norm_num [world12344, agent12344, scalar12344, tp12344, tm12344, ep12344, em12344, dsL]
  · norm_num [world12344, agent12344, scalar12344, tp12344, tm12344, ep12344, em12344, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12344, agent12344, tp12344, tm12344, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12344, agent12344, scalar12344, tp12344, tm12344, ep12344, em12344, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12344, agent12344, tp12344, tm12344, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12344, agent12344, scalar12344, tp12344, tm12344, ep12344, em12344, dsL]

theorem negative12344 :
    Eminus aL (agent12344.root+dsL) scalar12344.worldRadius world12344.frame
      agent12344.frame tm12344 ≤ -em12344 := by
  apply negative_check (lo := (13627700654839945243 / 20000000000000000000)) (hi := (8517312909274965777 / 12500000000000000000))
    (y := (-((70856610269839318387 / 100000000000000000000)))) (u := (49234967041606372243 / 100000000000000000000))
  · norm_num [world12344, agent12344, scalar12344, tp12344, tm12344, ep12344, em12344, dsL]
  · norm_num [world12344, agent12344, scalar12344, tp12344, tm12344, ep12344, em12344, dsL]
  · norm_num [world12344, agent12344, scalar12344, tp12344, tm12344, ep12344, em12344, dsL]
  · norm_num [world12344, agent12344, scalar12344, tp12344, tm12344, ep12344, em12344, dsL]
  · norm_num [world12344, agent12344, scalar12344, tp12344, tm12344, ep12344, em12344, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12344, agent12344, tp12344, tm12344, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12344, agent12344, tp12344, tm12344, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12344, agent12344, scalar12344, tp12344, tm12344, ep12344, em12344, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12344, agent12344, tp12344, tm12344, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12344, agent12344, scalar12344, tp12344, tm12344, ep12344, em12344, dsL]

theorem tails12344 :
    exp (-((12344:ℝ)*ep12344)) ≤ scalar12344.upperTail ∧
    exp (-((12344:ℝ)*em12344)) ≤ scalar12344.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12344:ℝ)) (by norm_num [ep12344]) ?_)
      (show bp12344^8 ≤ scalar12344.upperTail by norm_num [bp12344, scalar12344])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12344, bp12344, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12344:ℝ)) (by norm_num [em12344]) ?_)
      (show bm12344^8 ≤ scalar12344.lowerTail by norm_num [bm12344, scalar12344])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12344, bm12344, Finset.sum_range_succ, Nat.factorial]

theorem guards12344 :
    agent12344.root+dsL+scalar12344.worldRadius < √(1/100/aL) ∧
    2*(agent12344.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12344, agent12344, scalar12344, tp12344, tm12344, ep12344, em12344, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12344, agent12344, scalar12344, tp12344, tm12344, ep12344, em12344, dsL]

noncomputable def master12344 : MasterCertificate 12344 world12344 agent12344 :=
  master scalar12344 dsL tp12344 tm12344 ep12344 em12344
    (by norm_num [dsL]) (by norm_num [tp12344]) (by norm_num [tm12344])
    (by norm_num [ep12344]) (by norm_num [em12344])
    positive12344 negative12344 tails12344.1 tails12344.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12344.1 guards12344.2

theorem preserves12344 : master12344.toScalarCertificate = scalar12344 := rfl

noncomputable def tp12345 : ℝ := (1156701509 / 5000000000)
noncomputable def tm12345 : ℝ := (-((1520697613 / 2500000000)))
noncomputable def ep12345 : ℝ := (50961585595985421 / 100000000000000000000)
noncomputable def em12345 : ℝ := (4984339890847497 / 10000000000000000000)
noncomputable def bp12345 : ℝ := (45548114020983241823 / 100000000000000000000)
noncomputable def bm12345 : ℝ := (11585216845164239239 / 25000000000000000000)

theorem positive12345 :
    Eplus aL (agent12345.root+dsL) scalar12345.worldRadius world12345.frame
      agent12345.frame tp12345 ≤ -ep12345 := by
  apply positive_check (eT := (115708389213455760153 / 100000000000000000000)) (y := (37248476213732584313 / 100000000000000000000)) (u := (36283409092761339337 / 25000000000000000000))
  · norm_num [world12345, agent12345, scalar12345, tp12345, tm12345, ep12345, em12345, dsL]
  · norm_num [world12345, agent12345, scalar12345, tp12345, tm12345, ep12345, em12345, dsL]
  · norm_num [world12345, agent12345, scalar12345, tp12345, tm12345, ep12345, em12345, dsL]
  · norm_num [world12345, agent12345, scalar12345, tp12345, tm12345, ep12345, em12345, dsL]
  · norm_num [world12345, agent12345, scalar12345, tp12345, tm12345, ep12345, em12345, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12345, agent12345, tp12345, tm12345, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12345, agent12345, scalar12345, tp12345, tm12345, ep12345, em12345, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12345, agent12345, tp12345, tm12345, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12345, agent12345, scalar12345, tp12345, tm12345, ep12345, em12345, dsL]

theorem negative12345 :
    Eminus aL (agent12345.root+dsL) scalar12345.worldRadius world12345.frame
      agent12345.frame tm12345 ≤ -em12345 := by
  apply negative_check (lo := (2725526553110265663 / 4000000000000000000)) (hi := (8517270478469580197 / 12500000000000000000))
    (y := (-((70856645907943086109 / 100000000000000000000)))) (u := (9846989899040170911 / 20000000000000000000))
  · norm_num [world12345, agent12345, scalar12345, tp12345, tm12345, ep12345, em12345, dsL]
  · norm_num [world12345, agent12345, scalar12345, tp12345, tm12345, ep12345, em12345, dsL]
  · norm_num [world12345, agent12345, scalar12345, tp12345, tm12345, ep12345, em12345, dsL]
  · norm_num [world12345, agent12345, scalar12345, tp12345, tm12345, ep12345, em12345, dsL]
  · norm_num [world12345, agent12345, scalar12345, tp12345, tm12345, ep12345, em12345, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12345, agent12345, tp12345, tm12345, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12345, agent12345, tp12345, tm12345, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12345, agent12345, scalar12345, tp12345, tm12345, ep12345, em12345, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12345, agent12345, tp12345, tm12345, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12345, agent12345, scalar12345, tp12345, tm12345, ep12345, em12345, dsL]

theorem tails12345 :
    exp (-((12345:ℝ)*ep12345)) ≤ scalar12345.upperTail ∧
    exp (-((12345:ℝ)*em12345)) ≤ scalar12345.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12345:ℝ)) (by norm_num [ep12345]) ?_)
      (show bp12345^8 ≤ scalar12345.upperTail by norm_num [bp12345, scalar12345])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12345, bp12345, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12345:ℝ)) (by norm_num [em12345]) ?_)
      (show bm12345^8 ≤ scalar12345.lowerTail by norm_num [bm12345, scalar12345])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12345, bm12345, Finset.sum_range_succ, Nat.factorial]

theorem guards12345 :
    agent12345.root+dsL+scalar12345.worldRadius < √(1/100/aL) ∧
    2*(agent12345.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12345, agent12345, scalar12345, tp12345, tm12345, ep12345, em12345, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12345, agent12345, scalar12345, tp12345, tm12345, ep12345, em12345, dsL]

noncomputable def master12345 : MasterCertificate 12345 world12345 agent12345 :=
  master scalar12345 dsL tp12345 tm12345 ep12345 em12345
    (by norm_num [dsL]) (by norm_num [tp12345]) (by norm_num [tm12345])
    (by norm_num [ep12345]) (by norm_num [em12345])
    positive12345 negative12345 tails12345.1 tails12345.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12345.1 guards12345.2

theorem preserves12345 : master12345.toScalarCertificate = scalar12345 := rfl

noncomputable def tp12346 : ℝ := (1156751117 / 5000000000)
noncomputable def tm12346 : ℝ := (-((6083010907 / 10000000000)))
noncomputable def ep12346 : ℝ := (25482289773132907 / 50000000000000000000)
noncomputable def em12346 : ℝ := (12461503927898953 / 25000000000000000000)
noncomputable def bp12346 : ℝ := (45543108279597517151 / 100000000000000000000)
noncomputable def bm12346 : ℝ := (23168054485538685539 / 50000000000000000000)

theorem positive12346 :
    Eplus aL (agent12346.root+dsL) scalar12346.worldRadius world12346.frame
      agent12346.frame tp12346 ≤ -ep12346 := by
  apply positive_check (eT := (4628348823976929121 / 4000000000000000000)) (y := (18624643033584722157 / 50000000000000000000)) (u := (14513481174554694713 / 10000000000000000000))
  · norm_num [world12346, agent12346, scalar12346, tp12346, tm12346, ep12346, em12346, dsL]
  · norm_num [world12346, agent12346, scalar12346, tp12346, tm12346, ep12346, em12346, dsL]
  · norm_num [world12346, agent12346, scalar12346, tp12346, tm12346, ep12346, em12346, dsL]
  · norm_num [world12346, agent12346, scalar12346, tp12346, tm12346, ep12346, em12346, dsL]
  · norm_num [world12346, agent12346, scalar12346, tp12346, tm12346, ep12346, em12346, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12346, agent12346, tp12346, tm12346, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12346, agent12346, scalar12346, tp12346, tm12346, ep12346, em12346, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12346, agent12346, tp12346, tm12346, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12346, agent12346, scalar12346, tp12346, tm12346, ep12346, em12346, dsL]

theorem negative12346 :
    Eminus aL (agent12346.root+dsL) scalar12346.worldRadius world12346.frame
      agent12346.frame tm12346 ≤ -em12346 := by
  apply negative_check (lo := (68137824416356780201 / 100000000000000000000)) (hi := (34068912208178390101 / 50000000000000000000))
    (y := (-((70856681863596051047 / 100000000000000000000)))) (u := (49234931792456459167 / 100000000000000000000))
  · norm_num [world12346, agent12346, scalar12346, tp12346, tm12346, ep12346, em12346, dsL]
  · norm_num [world12346, agent12346, scalar12346, tp12346, tm12346, ep12346, em12346, dsL]
  · norm_num [world12346, agent12346, scalar12346, tp12346, tm12346, ep12346, em12346, dsL]
  · norm_num [world12346, agent12346, scalar12346, tp12346, tm12346, ep12346, em12346, dsL]
  · norm_num [world12346, agent12346, scalar12346, tp12346, tm12346, ep12346, em12346, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12346, agent12346, tp12346, tm12346, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12346, agent12346, tp12346, tm12346, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12346, agent12346, scalar12346, tp12346, tm12346, ep12346, em12346, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12346, agent12346, tp12346, tm12346, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12346, agent12346, scalar12346, tp12346, tm12346, ep12346, em12346, dsL]

theorem tails12346 :
    exp (-((12346:ℝ)*ep12346)) ≤ scalar12346.upperTail ∧
    exp (-((12346:ℝ)*em12346)) ≤ scalar12346.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12346:ℝ)) (by norm_num [ep12346]) ?_)
      (show bp12346^8 ≤ scalar12346.upperTail by norm_num [bp12346, scalar12346])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12346, bp12346, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12346:ℝ)) (by norm_num [em12346]) ?_)
      (show bm12346^8 ≤ scalar12346.lowerTail by norm_num [bm12346, scalar12346])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12346, bm12346, Finset.sum_range_succ, Nat.factorial]

theorem guards12346 :
    agent12346.root+dsL+scalar12346.worldRadius < √(1/100/aL) ∧
    2*(agent12346.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12346, agent12346, scalar12346, tp12346, tm12346, ep12346, em12346, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12346, agent12346, scalar12346, tp12346, tm12346, ep12346, em12346, dsL]

noncomputable def master12346 : MasterCertificate 12346 world12346 agent12346 :=
  master scalar12346 dsL tp12346 tm12346 ep12346 em12346
    (by norm_num [dsL]) (by norm_num [tp12346]) (by norm_num [tm12346])
    (by norm_num [ep12346]) (by norm_num [em12346])
    positive12346 negative12346 tails12346.1 tails12346.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12346.1 guards12346.2

theorem preserves12346 : master12346.toScalarCertificate = scalar12346 := rfl

noncomputable def tp12347 : ℝ := (231360139 / 1000000000)
noncomputable def tm12347 : ℝ := (-((6083231037 / 10000000000)))
noncomputable def ep12347 : ℝ := (10193514422730531 / 20000000000000000000)
noncomputable def em12347 : ℝ := (24924315612128949 / 50000000000000000000)
noncomputable def bp12347 : ℝ := (45538103719426496437 / 100000000000000000000)
noncomputable def bm12347 : ℝ := (11582837917442078937 / 25000000000000000000)

theorem positive12347 :
    Eplus aL (agent12347.root+dsL) scalar12347.worldRadius world12347.frame
      agent12347.frame tp12347 ≤ -ep12347 := by
  apply positive_check (eT := (11570905158003871763 / 10000000000000000000)) (y := (3725009532136029379 / 10000000000000000000)) (u := (145135986259845776149 / 100000000000000000000))
  · norm_num [world12347, agent12347, scalar12347, tp12347, tm12347, ep12347, em12347, dsL]
  · norm_num [world12347, agent12347, scalar12347, tp12347, tm12347, ep12347, em12347, dsL]
  · norm_num [world12347, agent12347, scalar12347, tp12347, tm12347, ep12347, em12347, dsL]
  · norm_num [world12347, agent12347, scalar12347, tp12347, tm12347, ep12347, em12347, dsL]
  · norm_num [world12347, agent12347, scalar12347, tp12347, tm12347, ep12347, em12347, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12347, agent12347, tp12347, tm12347, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12347, agent12347, scalar12347, tp12347, tm12347, ep12347, em12347, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12347, agent12347, tp12347, tm12347, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12347, agent12347, scalar12347, tp12347, tm12347, ep12347, em12347, dsL]

theorem negative12347 :
    Eminus aL (agent12347.root+dsL) scalar12347.worldRadius world12347.frame
      agent12347.frame tm12347 ≤ -em12347 := by
  apply negative_check (lo := (68137486346310478073 / 100000000000000000000)) (hi := (34068743173155239037 / 50000000000000000000))
    (y := (-((3542835775667179701 / 5000000000000000000)))) (u := (49234915225028995499 / 100000000000000000000))
  · norm_num [world12347, agent12347, scalar12347, tp12347, tm12347, ep12347, em12347, dsL]
  · norm_num [world12347, agent12347, scalar12347, tp12347, tm12347, ep12347, em12347, dsL]
  · norm_num [world12347, agent12347, scalar12347, tp12347, tm12347, ep12347, em12347, dsL]
  · norm_num [world12347, agent12347, scalar12347, tp12347, tm12347, ep12347, em12347, dsL]
  · norm_num [world12347, agent12347, scalar12347, tp12347, tm12347, ep12347, em12347, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12347, agent12347, tp12347, tm12347, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12347, agent12347, tp12347, tm12347, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12347, agent12347, scalar12347, tp12347, tm12347, ep12347, em12347, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12347, agent12347, tp12347, tm12347, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12347, agent12347, scalar12347, tp12347, tm12347, ep12347, em12347, dsL]

theorem tails12347 :
    exp (-((12347:ℝ)*ep12347)) ≤ scalar12347.upperTail ∧
    exp (-((12347:ℝ)*em12347)) ≤ scalar12347.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12347:ℝ)) (by norm_num [ep12347]) ?_)
      (show bp12347^8 ≤ scalar12347.upperTail by norm_num [bp12347, scalar12347])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12347, bp12347, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12347:ℝ)) (by norm_num [em12347]) ?_)
      (show bm12347^8 ≤ scalar12347.lowerTail by norm_num [bm12347, scalar12347])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12347, bm12347, Finset.sum_range_succ, Nat.factorial]

theorem guards12347 :
    agent12347.root+dsL+scalar12347.worldRadius < √(1/100/aL) ∧
    2*(agent12347.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12347, agent12347, scalar12347, tp12347, tm12347, ep12347, em12347, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12347, agent12347, scalar12347, tp12347, tm12347, ep12347, em12347, dsL]

noncomputable def master12347 : MasterCertificate 12347 world12347 agent12347 :=
  master scalar12347 dsL tp12347 tm12347 ep12347 em12347
    (by norm_num [dsL]) (by norm_num [tp12347]) (by norm_num [tm12347])
    (by norm_num [ep12347]) (by norm_num [em12347])
    positive12347 negative12347 tails12347.1 tails12347.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12347.1 guards12347.2

theorem preserves12347 : master12347.toScalarCertificate = scalar12347 := rfl

noncomputable def tp12348 : ℝ := (1156850249 / 5000000000)
noncomputable def tm12348 : ℝ := (-((3041725607 / 5000000000)))
noncomputable def ep12348 : ℝ := (10194112593537339 / 20000000000000000000)
noncomputable def em12348 : ℝ := (49851245163666709 / 100000000000000000000)
noncomputable def bp12348 : ℝ := (9106620114537138313 / 20000000000000000000)
noncomputable def bm12348 : ℝ := (23163297839462723447 / 50000000000000000000)

theorem positive12348 :
    Eplus aL (agent12348.root+dsL) scalar12348.worldRadius world12348.frame
      agent12348.frame tp12348 ≤ -ep12348 := by
  apply positive_check (eT := (115709382242876257447 / 100000000000000000000)) (y := (37250904182872939247 / 100000000000000000000)) (u := (72568580106863727301 / 50000000000000000000))
  · norm_num [world12348, agent12348, scalar12348, tp12348, tm12348, ep12348, em12348, dsL]
  · norm_num [world12348, agent12348, scalar12348, tp12348, tm12348, ep12348, em12348, dsL]
  · norm_num [world12348, agent12348, scalar12348, tp12348, tm12348, ep12348, em12348, dsL]
  · norm_num [world12348, agent12348, scalar12348, tp12348, tm12348, ep12348, em12348, dsL]
  · norm_num [world12348, agent12348, scalar12348, tp12348, tm12348, ep12348, em12348, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12348, agent12348, tp12348, tm12348, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12348, agent12348, scalar12348, tp12348, tm12348, ep12348, em12348, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12348, agent12348, tp12348, tm12348, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12348, agent12348, scalar12348, tp12348, tm12348, ep12348, em12348, dsL]

theorem negative12348 :
    Eminus aL (agent12348.root+dsL) scalar12348.worldRadius world12348.frame
      agent12348.frame tm12348 ≤ -em12348 := by
  apply negative_check (lo := (13627429603808565369 / 20000000000000000000)) (hi := (34068574009521413423 / 50000000000000000000))
    (y := (-((35428375204307129117 / 50000000000000000000)))) (u := (49234898044375064047 / 100000000000000000000))
  · norm_num [world12348, agent12348, scalar12348, tp12348, tm12348, ep12348, em12348, dsL]
  · norm_num [world12348, agent12348, scalar12348, tp12348, tm12348, ep12348, em12348, dsL]
  · norm_num [world12348, agent12348, scalar12348, tp12348, tm12348, ep12348, em12348, dsL]
  · norm_num [world12348, agent12348, scalar12348, tp12348, tm12348, ep12348, em12348, dsL]
  · norm_num [world12348, agent12348, scalar12348, tp12348, tm12348, ep12348, em12348, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12348, agent12348, tp12348, tm12348, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12348, agent12348, tp12348, tm12348, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12348, agent12348, scalar12348, tp12348, tm12348, ep12348, em12348, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12348, agent12348, tp12348, tm12348, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12348, agent12348, scalar12348, tp12348, tm12348, ep12348, em12348, dsL]

theorem tails12348 :
    exp (-((12348:ℝ)*ep12348)) ≤ scalar12348.upperTail ∧
    exp (-((12348:ℝ)*em12348)) ≤ scalar12348.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12348:ℝ)) (by norm_num [ep12348]) ?_)
      (show bp12348^8 ≤ scalar12348.upperTail by norm_num [bp12348, scalar12348])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12348, bp12348, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12348:ℝ)) (by norm_num [em12348]) ?_)
      (show bm12348^8 ≤ scalar12348.lowerTail by norm_num [bm12348, scalar12348])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12348, bm12348, Finset.sum_range_succ, Nat.factorial]

theorem guards12348 :
    agent12348.root+dsL+scalar12348.worldRadius < √(1/100/aL) ∧
    2*(agent12348.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12348, agent12348, scalar12348, tp12348, tm12348, ep12348, em12348, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12348, agent12348, scalar12348, tp12348, tm12348, ep12348, em12348, dsL]

noncomputable def master12348 : MasterCertificate 12348 world12348 agent12348 :=
  master scalar12348 dsL tp12348 tm12348 ep12348 em12348
    (by norm_num [dsL]) (by norm_num [tp12348]) (by norm_num [tm12348])
    (by norm_num [ep12348]) (by norm_num [em12348])
    positive12348 negative12348 tails12348.1 tails12348.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12348.1 guards12348.2

theorem preserves12348 : master12348.toScalarCertificate = scalar12348 := rfl

noncomputable def tp12349 : ℝ := (46275991 / 200000000)
noncomputable def tm12349 : ℝ := (-((6083671229 / 10000000000)))
noncomputable def ep12349 : ℝ := (50973552914309763 / 100000000000000000000)
noncomputable def em12349 : ℝ := (6231732280816919 / 12500000000000000000)
noncomputable def bp12349 : ℝ := (22764049136460138649 / 50000000000000000000)
noncomputable def bm12349 : ℝ := (11580460121510856843 / 25000000000000000000)

theorem positive12349 :
    Eplus aL (agent12349.root+dsL) scalar12349.worldRadius world12349.frame
      agent12349.frame tp12349 ≤ -ep12349 := by
  apply positive_check (eT := (23141942505912688277 / 20000000000000000000)) (y := (18625856182588064027 / 50000000000000000000)) (u := (9071145824456971561 / 6250000000000000000))
  · norm_num [world12349, agent12349, scalar12349, tp12349, tm12349, ep12349, em12349, dsL]
  · norm_num [world12349, agent12349, scalar12349, tp12349, tm12349, ep12349, em12349, dsL]
  · norm_num [world12349, agent12349, scalar12349, tp12349, tm12349, ep12349, em12349, dsL]
  · norm_num [world12349, agent12349, scalar12349, tp12349, tm12349, ep12349, em12349, dsL]
  · norm_num [world12349, agent12349, scalar12349, tp12349, tm12349, ep12349, em12349, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12349, agent12349, tp12349, tm12349, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12349, agent12349, scalar12349, tp12349, tm12349, ep12349, em12349, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12349, agent12349, tp12349, tm12349, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12349, agent12349, scalar12349, tp12349, tm12349, ep12349, em12349, dsL]

theorem negative12349 :
    Eminus aL (agent12349.root+dsL) scalar12349.worldRadius world12349.frame
      agent12349.frame tm12349 ≤ -em12349 := by
  apply negative_check (lo := (68136810332652169033 / 100000000000000000000)) (hi := (34068405166326084517 / 50000000000000000000))
    (y := (-((70856784273383235143 / 100000000000000000000)))) (u := (49234881371093408487 / 100000000000000000000))
  · norm_num [world12349, agent12349, scalar12349, tp12349, tm12349, ep12349, em12349, dsL]
  · norm_num [world12349, agent12349, scalar12349, tp12349, tm12349, ep12349, em12349, dsL]
  · norm_num [world12349, agent12349, scalar12349, tp12349, tm12349, ep12349, em12349, dsL]
  · norm_num [world12349, agent12349, scalar12349, tp12349, tm12349, ep12349, em12349, dsL]
  · norm_num [world12349, agent12349, scalar12349, tp12349, tm12349, ep12349, em12349, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12349, agent12349, tp12349, tm12349, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12349, agent12349, tp12349, tm12349, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12349, agent12349, scalar12349, tp12349, tm12349, ep12349, em12349, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12349, agent12349, tp12349, tm12349, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12349, agent12349, scalar12349, tp12349, tm12349, ep12349, em12349, dsL]

theorem tails12349 :
    exp (-((12349:ℝ)*ep12349)) ≤ scalar12349.upperTail ∧
    exp (-((12349:ℝ)*em12349)) ≤ scalar12349.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12349:ℝ)) (by norm_num [ep12349]) ?_)
      (show bp12349^8 ≤ scalar12349.upperTail by norm_num [bp12349, scalar12349])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12349, bp12349, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12349:ℝ)) (by norm_num [em12349]) ?_)
      (show bm12349^8 ≤ scalar12349.lowerTail by norm_num [bm12349, scalar12349])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12349, bm12349, Finset.sum_range_succ, Nat.factorial]

theorem guards12349 :
    agent12349.root+dsL+scalar12349.worldRadius < √(1/100/aL) ∧
    2*(agent12349.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12349, agent12349, scalar12349, tp12349, tm12349, ep12349, em12349, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12349, agent12349, scalar12349, tp12349, tm12349, ep12349, em12349, dsL]

noncomputable def master12349 : MasterCertificate 12349 world12349 agent12349 :=
  master scalar12349 dsL tp12349 tm12349 ep12349 em12349
    (by norm_num [dsL]) (by norm_num [tp12349]) (by norm_num [tm12349])
    (by norm_num [ep12349]) (by norm_num [em12349])
    positive12349 negative12349 tails12349.1 tails12349.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12349.1 guards12349.2

theorem preserves12349 : master12349.toScalarCertificate = scalar12349 := rfl

end BstLean.Part261
