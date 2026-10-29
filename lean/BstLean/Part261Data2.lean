import BstLean.Part261Checker
import BstLean.Part259Data10
import BstLean.Part259Data11
import BstLean.Part259Data12
import BstLean.Part259Data13
import BstLean.Part259Data14

namespace BstLean.Part261
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part259

noncomputable def tp12275 : ℝ := (2306363841 / 10000000000)
noncomputable def tm12275 : ℝ := (-((303357009 / 500000000)))
noncomputable def ep12275 : ℝ := (634359180165853 / 1250000000000000000)
noncomputable def em12275 : ℝ := (49657217589882251 / 100000000000000000000)
noncomputable def bp12275 : ℝ := (9180267832867336227 / 20000000000000000000)
noncomputable def bm12275 : ℝ := (186706266534872967 / 400000000000000000)

theorem positive12275 :
    Eplus aL (agent12275.root+dsL) scalar12275.worldRadius world12275.frame
      agent12275.frame tp12275 ≤ -ep12275 := by
  apply positive_check (eT := (28921146509819178611 / 25000000000000000000)) (y := (18595409541225336271 / 50000000000000000000)) (u := (18131247574858173983 / 12500000000000000000))
  · norm_num [world12275, agent12275, scalar12275, tp12275, tm12275, ep12275, em12275, dsL]
  · norm_num [world12275, agent12275, scalar12275, tp12275, tm12275, ep12275, em12275, dsL]
  · norm_num [world12275, agent12275, scalar12275, tp12275, tm12275, ep12275, em12275, dsL]
  · norm_num [world12275, agent12275, scalar12275, tp12275, tm12275, ep12275, em12275, dsL]
  · norm_num [world12275, agent12275, scalar12275, tp12275, tm12275, ep12275, em12275, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12275, agent12275, tp12275, tm12275, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12275, agent12275, scalar12275, tp12275, tm12275, ep12275, em12275, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12275, agent12275, tp12275, tm12275, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12275, agent12275, scalar12275, tp12275, tm12275, ep12275, em12275, dsL]

theorem negative12275 :
    Eminus aL (agent12275.root+dsL) scalar12275.worldRadius world12275.frame
      agent12275.frame tm12275 ≤ -em12275 := by
  apply negative_check (lo := (34081362484720752093 / 50000000000000000000)) (hi := (68162724969441504187 / 100000000000000000000))
    (y := (-((7085309434951267387 / 10000000000000000000)))) (u := (24618349067126072793 / 50000000000000000000))
  · norm_num [world12275, agent12275, scalar12275, tp12275, tm12275, ep12275, em12275, dsL]
  · norm_num [world12275, agent12275, scalar12275, tp12275, tm12275, ep12275, em12275, dsL]
  · norm_num [world12275, agent12275, scalar12275, tp12275, tm12275, ep12275, em12275, dsL]
  · norm_num [world12275, agent12275, scalar12275, tp12275, tm12275, ep12275, em12275, dsL]
  · norm_num [world12275, agent12275, scalar12275, tp12275, tm12275, ep12275, em12275, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12275, agent12275, tp12275, tm12275, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12275, agent12275, tp12275, tm12275, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12275, agent12275, scalar12275, tp12275, tm12275, ep12275, em12275, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12275, agent12275, tp12275, tm12275, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12275, agent12275, scalar12275, tp12275, tm12275, ep12275, em12275, dsL]

theorem tails12275 :
    exp (-((12275:ℝ)*ep12275)) ≤ scalar12275.upperTail ∧
    exp (-((12275:ℝ)*em12275)) ≤ scalar12275.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12275:ℝ)) (by norm_num [ep12275]) ?_)
      (show bp12275^8 ≤ scalar12275.upperTail by norm_num [bp12275, scalar12275])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12275, bp12275, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12275:ℝ)) (by norm_num [em12275]) ?_)
      (show bm12275^8 ≤ scalar12275.lowerTail by norm_num [bm12275, scalar12275])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12275, bm12275, Finset.sum_range_succ, Nat.factorial]

theorem guards12275 :
    agent12275.root+dsL+scalar12275.worldRadius < √(1/100/aL) ∧
    2*(agent12275.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12275, agent12275, scalar12275, tp12275, tm12275, ep12275, em12275, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12275, agent12275, scalar12275, tp12275, tm12275, ep12275, em12275, dsL]

noncomputable def master12275 : MasterCertificate 12275 world12275 agent12275 :=
  master scalar12275 dsL tp12275 tm12275 ep12275 em12275
    (by norm_num [dsL]) (by norm_num [tp12275]) (by norm_num [tm12275])
    (by norm_num [ep12275]) (by norm_num [em12275])
    positive12275 negative12275 tails12275.1 tails12275.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12275.1 guards12275.2

theorem preserves12275 : master12275.toScalarCertificate = scalar12275 := rfl

noncomputable def tp12276 : ℝ := (144154113 / 625000000)
noncomputable def tm12276 : ℝ := (-((3033683597 / 5000000000)))
noncomputable def ep12276 : ℝ := (50751822435318831 / 100000000000000000000)
noncomputable def em12276 : ℝ := (24829960465789369 / 50000000000000000000)
noncomputable def bp12276 : ℝ := (45896252585592994429 / 100000000000000000000)
noncomputable def bm12276 : ℝ := (46671733324778431637 / 100000000000000000000)

theorem positive12276 :
    Eplus aL (agent12276.root+dsL) scalar12276.worldRadius world12276.frame
      agent12276.frame tp12276 ≤ -ep12276 := by
  apply positive_check (eT := (115684935248575690803 / 100000000000000000000)) (y := (37191656087627748353 / 100000000000000000000)) (u := (145051194679793304849 / 100000000000000000000))
  · norm_num [world12276, agent12276, scalar12276, tp12276, tm12276, ep12276, em12276, dsL]
  · norm_num [world12276, agent12276, scalar12276, tp12276, tm12276, ep12276, em12276, dsL]
  · norm_num [world12276, agent12276, scalar12276, tp12276, tm12276, ep12276, em12276, dsL]
  · norm_num [world12276, agent12276, scalar12276, tp12276, tm12276, ep12276, em12276, dsL]
  · norm_num [world12276, agent12276, scalar12276, tp12276, tm12276, ep12276, em12276, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12276, agent12276, tp12276, tm12276, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12276, agent12276, scalar12276, tp12276, tm12276, ep12276, em12276, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12276, agent12276, tp12276, tm12276, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12276, agent12276, scalar12276, tp12276, tm12276, ep12276, em12276, dsL]

theorem negative12276 :
    Eminus aL (agent12276.root+dsL) scalar12276.worldRadius world12276.frame
      agent12276.frame tm12276 ≤ -em12276 := by
  apply negative_check (lo := (68162361194897331501 / 100000000000000000000)) (hi := (34081180597448665751 / 50000000000000000000))
    (y := (-((35426579800623637749 / 50000000000000000000)))) (u := (4923666600646303439 / 10000000000000000000))
  · norm_num [world12276, agent12276, scalar12276, tp12276, tm12276, ep12276, em12276, dsL]
  · norm_num [world12276, agent12276, scalar12276, tp12276, tm12276, ep12276, em12276, dsL]
  · norm_num [world12276, agent12276, scalar12276, tp12276, tm12276, ep12276, em12276, dsL]
  · norm_num [world12276, agent12276, scalar12276, tp12276, tm12276, ep12276, em12276, dsL]
  · norm_num [world12276, agent12276, scalar12276, tp12276, tm12276, ep12276, em12276, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12276, agent12276, tp12276, tm12276, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12276, agent12276, tp12276, tm12276, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12276, agent12276, scalar12276, tp12276, tm12276, ep12276, em12276, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12276, agent12276, tp12276, tm12276, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12276, agent12276, scalar12276, tp12276, tm12276, ep12276, em12276, dsL]

theorem tails12276 :
    exp (-((12276:ℝ)*ep12276)) ≤ scalar12276.upperTail ∧
    exp (-((12276:ℝ)*em12276)) ≤ scalar12276.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12276:ℝ)) (by norm_num [ep12276]) ?_)
      (show bp12276^8 ≤ scalar12276.upperTail by norm_num [bp12276, scalar12276])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12276, bp12276, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12276:ℝ)) (by norm_num [em12276]) ?_)
      (show bm12276^8 ≤ scalar12276.lowerTail by norm_num [bm12276, scalar12276])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12276, bm12276, Finset.sum_range_succ, Nat.factorial]

theorem guards12276 :
    agent12276.root+dsL+scalar12276.worldRadius < √(1/100/aL) ∧
    2*(agent12276.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12276, agent12276, scalar12276, tp12276, tm12276, ep12276, em12276, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12276, agent12276, scalar12276, tp12276, tm12276, ep12276, em12276, dsL]

noncomputable def master12276 : MasterCertificate 12276 world12276 agent12276 :=
  master scalar12276 dsL tp12276 tm12276 ep12276 em12276
    (by norm_num [dsL]) (by norm_num [tp12276]) (by norm_num [tm12276])
    (by norm_num [ep12276]) (by norm_num [em12276])
    positive12276 negative12276 tails12276.1 tails12276.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12276.1 guards12276.2

theorem preserves12276 : master12276.toScalarCertificate = scalar12276 := rfl

noncomputable def tp12277 : ℝ := (576641927 / 2500000000)
noncomputable def tm12277 : ℝ := (-((6067593987 / 10000000000)))
noncomputable def ep12277 : ℝ := (50754908090978617 / 100000000000000000000)
noncomputable def em12277 : ℝ := (24831311036095303 / 50000000000000000000)
noncomputable def bp12277 : ℝ := (45891167882786669427 / 100000000000000000000)
noncomputable def bm12277 : ℝ := (1866676071090567851 / 4000000000000000000)

theorem positive12277 :
    Eplus aL (agent12277.root+dsL) scalar12277.worldRadius world12277.frame
      agent12277.frame tp12277 ≤ -ep12277 := by
  apply positive_check (eT := (723033025003146593 / 625000000000000000)) (y := (37192492476009070603 / 100000000000000000000)) (u := (29010481575241217121 / 20000000000000000000))
  · norm_num [world12277, agent12277, scalar12277, tp12277, tm12277, ep12277, em12277, dsL]
  · norm_num [world12277, agent12277, scalar12277, tp12277, tm12277, ep12277, em12277, dsL]
  · norm_num [world12277, agent12277, scalar12277, tp12277, tm12277, ep12277, em12277, dsL]
  · norm_num [world12277, agent12277, scalar12277, tp12277, tm12277, ep12277, em12277, dsL]
  · norm_num [world12277, agent12277, scalar12277, tp12277, tm12277, ep12277, em12277, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12277, agent12277, tp12277, tm12277, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12277, agent12277, scalar12277, tp12277, tm12277, ep12277, em12277, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12277, agent12277, tp12277, tm12277, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12277, agent12277, scalar12277, tp12277, tm12277, ep12277, em12277, dsL]

theorem negative12277 :
    Eminus aL (agent12277.root+dsL) scalar12277.worldRadius world12277.frame
      agent12277.frame tm12277 ≤ -em12277 := by
  apply negative_check (lo := (68161998317174947889 / 100000000000000000000)) (hi := (6816199831717494789 / 10000000000000000000))
    (y := (-((70853223299638248329 / 100000000000000000000)))) (u := (6154579330438626057 / 12500000000000000000))
  · norm_num [world12277, agent12277, scalar12277, tp12277, tm12277, ep12277, em12277, dsL]
  · norm_num [world12277, agent12277, scalar12277, tp12277, tm12277, ep12277, em12277, dsL]
  · norm_num [world12277, agent12277, scalar12277, tp12277, tm12277, ep12277, em12277, dsL]
  · norm_num [world12277, agent12277, scalar12277, tp12277, tm12277, ep12277, em12277, dsL]
  · norm_num [world12277, agent12277, scalar12277, tp12277, tm12277, ep12277, em12277, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12277, agent12277, tp12277, tm12277, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12277, agent12277, tp12277, tm12277, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12277, agent12277, scalar12277, tp12277, tm12277, ep12277, em12277, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12277, agent12277, tp12277, tm12277, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12277, agent12277, scalar12277, tp12277, tm12277, ep12277, em12277, dsL]

theorem tails12277 :
    exp (-((12277:ℝ)*ep12277)) ≤ scalar12277.upperTail ∧
    exp (-((12277:ℝ)*em12277)) ≤ scalar12277.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12277:ℝ)) (by norm_num [ep12277]) ?_)
      (show bp12277^8 ≤ scalar12277.upperTail by norm_num [bp12277, scalar12277])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12277, bp12277, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12277:ℝ)) (by norm_num [em12277]) ?_)
      (show bm12277^8 ≤ scalar12277.lowerTail by norm_num [bm12277, scalar12277])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12277, bm12277, Finset.sum_range_succ, Nat.factorial]

theorem guards12277 :
    agent12277.root+dsL+scalar12277.worldRadius < √(1/100/aL) ∧
    2*(agent12277.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12277, agent12277, scalar12277, tp12277, tm12277, ep12277, em12277, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12277, agent12277, scalar12277, tp12277, tm12277, ep12277, em12277, dsL]

noncomputable def master12277 : MasterCertificate 12277 world12277 agent12277 :=
  master scalar12277 dsL tp12277 tm12277 ep12277 em12277
    (by norm_num [dsL]) (by norm_num [tp12277]) (by norm_num [tm12277])
    (by norm_num [ep12277]) (by norm_num [em12277])
    positive12277 negative12277 tails12277.1 tails12277.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12277.1 guards12277.2

theorem preserves12277 : master12277.toScalarCertificate = scalar12277 := rfl

noncomputable def tp12278 : ℝ := (2306669599 / 10000000000)
noncomputable def tm12278 : ℝ := (-((3033910319 / 5000000000)))
noncomputable def ep12278 : ℝ := (12689498350564021 / 25000000000000000000)
noncomputable def em12278 : ℝ := (49665322901577649 / 100000000000000000000)
noncomputable def bp12278 : ℝ := (45886083631853746601 / 100000000000000000000)
noncomputable def bm12278 : ℝ := (11665517659425365503 / 25000000000000000000)

theorem positive12278 :
    Eplus aL (agent12278.root+dsL) scalar12278.worldRadius world12278.frame
      agent12278.frame tp12278 ≤ -ep12278 := by
  apply positive_check (eT := (4627425308758566901 / 4000000000000000000)) (y := (7438665782145455917 / 20000000000000000000)) (u := (283307853808553271 / 195312500000000000))
  · norm_num [world12278, agent12278, scalar12278, tp12278, tm12278, ep12278, em12278, dsL]
  · norm_num [world12278, agent12278, scalar12278, tp12278, tm12278, ep12278, em12278, dsL]
  · norm_num [world12278, agent12278, scalar12278, tp12278, tm12278, ep12278, em12278, dsL]
  · norm_num [world12278, agent12278, scalar12278, tp12278, tm12278, ep12278, em12278, dsL]
  · norm_num [world12278, agent12278, scalar12278, tp12278, tm12278, ep12278, em12278, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12278, agent12278, tp12278, tm12278, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12278, agent12278, scalar12278, tp12278, tm12278, ep12278, em12278, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12278, agent12278, tp12278, tm12278, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12278, agent12278, scalar12278, tp12278, tm12278, ep12278, em12278, dsL]

theorem negative12278 :
    Eminus aL (agent12278.root+dsL) scalar12278.worldRadius world12278.frame
      agent12278.frame tm12278 ≤ -em12278 := by
  apply negative_check (lo := (68161635995998394017 / 100000000000000000000)) (hi := (34080817997999197009 / 50000000000000000000))
    (y := (-((70853286424468578551 / 100000000000000000000)))) (u := (49236603562976739197 / 100000000000000000000))
  · norm_num [world12278, agent12278, scalar12278, tp12278, tm12278, ep12278, em12278, dsL]
  · norm_num [world12278, agent12278, scalar12278, tp12278, tm12278, ep12278, em12278, dsL]
  · norm_num [world12278, agent12278, scalar12278, tp12278, tm12278, ep12278, em12278, dsL]
  · norm_num [world12278, agent12278, scalar12278, tp12278, tm12278, ep12278, em12278, dsL]
  · norm_num [world12278, agent12278, scalar12278, tp12278, tm12278, ep12278, em12278, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12278, agent12278, tp12278, tm12278, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12278, agent12278, tp12278, tm12278, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12278, agent12278, scalar12278, tp12278, tm12278, ep12278, em12278, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12278, agent12278, tp12278, tm12278, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12278, agent12278, scalar12278, tp12278, tm12278, ep12278, em12278, dsL]

theorem tails12278 :
    exp (-((12278:ℝ)*ep12278)) ≤ scalar12278.upperTail ∧
    exp (-((12278:ℝ)*em12278)) ≤ scalar12278.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12278:ℝ)) (by norm_num [ep12278]) ?_)
      (show bp12278^8 ≤ scalar12278.upperTail by norm_num [bp12278, scalar12278])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12278, bp12278, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12278:ℝ)) (by norm_num [em12278]) ?_)
      (show bm12278^8 ≤ scalar12278.lowerTail by norm_num [bm12278, scalar12278])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12278, bm12278, Finset.sum_range_succ, Nat.factorial]

theorem guards12278 :
    agent12278.root+dsL+scalar12278.worldRadius < √(1/100/aL) ∧
    2*(agent12278.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12278, agent12278, scalar12278, tp12278, tm12278, ep12278, em12278, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12278, agent12278, scalar12278, tp12278, tm12278, ep12278, em12278, dsL]

noncomputable def master12278 : MasterCertificate 12278 world12278 agent12278 :=
  master scalar12278 dsL tp12278 tm12278 ep12278 em12278
    (by norm_num [dsL]) (by norm_num [tp12278]) (by norm_num [tm12278])
    (by norm_num [ep12278]) (by norm_num [em12278])
    positive12278 negative12278 tails12278.1 tails12278.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12278.1 guards12278.2

theorem preserves12278 : master12278.toScalarCertificate = scalar12278 := rfl

noncomputable def tp12279 : ℝ := (115338573 / 500000000)
noncomputable def tm12279 : ℝ := (-((758505907 / 1250000000)))
noncomputable def ep12279 : ℝ := (50761076816434831 / 100000000000000000000)
noncomputable def em12279 : ℝ := (4966802196470471 / 10000000000000000000)
noncomputable def bp12279 : ℝ := (45881000926275850821 / 100000000000000000000)
noncomputable def bm12279 : ℝ := (46657240948116335457 / 100000000000000000000)

theorem positive12279 :
    Eplus aL (agent12279.root+dsL) scalar12279.worldRadius world12279.frame
      agent12279.frame tp12279 ≤ -ep12279 := by
  apply positive_check (eT := (115685981250435315537 / 100000000000000000000)) (y := (37194165321550654533 / 100000000000000000000)) (u := (29010966879848027493 / 20000000000000000000))
  · norm_num [world12279, agent12279, scalar12279, tp12279, tm12279, ep12279, em12279, dsL]
  · norm_num [world12279, agent12279, scalar12279, tp12279, tm12279, ep12279, em12279, dsL]
  · norm_num [world12279, agent12279, scalar12279, tp12279, tm12279, ep12279, em12279, dsL]
  · norm_num [world12279, agent12279, scalar12279, tp12279, tm12279, ep12279, em12279, dsL]
  · norm_num [world12279, agent12279, scalar12279, tp12279, tm12279, ep12279, em12279, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12279, agent12279, tp12279, tm12279, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12279, agent12279, scalar12279, tp12279, tm12279, ep12279, em12279, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12279, agent12279, tp12279, tm12279, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12279, agent12279, scalar12279, tp12279, tm12279, ep12279, em12279, dsL]

theorem negative12279 :
    Eminus aL (agent12279.root+dsL) scalar12279.worldRadius world12279.frame
      agent12279.frame tm12279 ≤ -em12279 := by
  apply negative_check (lo := (266254975633329467 / 390625000000000000)) (hi := (68161273762132343553 / 100000000000000000000))
    (y := (-((70853349924103039239 / 100000000000000000000)))) (u := (49236572297923382447 / 100000000000000000000))
  · norm_num [world12279, agent12279, scalar12279, tp12279, tm12279, ep12279, em12279, dsL]
  · norm_num [world12279, agent12279, scalar12279, tp12279, tm12279, ep12279, em12279, dsL]
  · norm_num [world12279, agent12279, scalar12279, tp12279, tm12279, ep12279, em12279, dsL]
  · norm_num [world12279, agent12279, scalar12279, tp12279, tm12279, ep12279, em12279, dsL]
  · norm_num [world12279, agent12279, scalar12279, tp12279, tm12279, ep12279, em12279, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12279, agent12279, tp12279, tm12279, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12279, agent12279, tp12279, tm12279, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12279, agent12279, scalar12279, tp12279, tm12279, ep12279, em12279, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12279, agent12279, tp12279, tm12279, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12279, agent12279, scalar12279, tp12279, tm12279, ep12279, em12279, dsL]

theorem tails12279 :
    exp (-((12279:ℝ)*ep12279)) ≤ scalar12279.upperTail ∧
    exp (-((12279:ℝ)*em12279)) ≤ scalar12279.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12279:ℝ)) (by norm_num [ep12279]) ?_)
      (show bp12279^8 ≤ scalar12279.upperTail by norm_num [bp12279, scalar12279])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12279, bp12279, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12279:ℝ)) (by norm_num [em12279]) ?_)
      (show bm12279^8 ≤ scalar12279.lowerTail by norm_num [bm12279, scalar12279])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12279, bm12279, Finset.sum_range_succ, Nat.factorial]

theorem guards12279 :
    agent12279.root+dsL+scalar12279.worldRadius < √(1/100/aL) ∧
    2*(agent12279.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12279, agent12279, scalar12279, tp12279, tm12279, ep12279, em12279, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12279, agent12279, scalar12279, tp12279, tm12279, ep12279, em12279, dsL]

noncomputable def master12279 : MasterCertificate 12279 world12279 agent12279 :=
  master scalar12279 dsL tp12279 tm12279 ep12279 em12279
    (by norm_num [dsL]) (by norm_num [tp12279]) (by norm_num [tm12279])
    (by norm_num [ep12279]) (by norm_num [em12279])
    positive12279 negative12279 tails12279.1 tails12279.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12279.1 guards12279.2

theorem preserves12279 : master12279.toScalarCertificate = scalar12279 := rfl

noncomputable def tp12280 : ℝ := (2306873193 / 10000000000)
noncomputable def tm12280 : ℝ := (-((30341369 / 50000000)))
noncomputable def ep12280 : ℝ := (10152831922212471 / 20000000000000000000)
noncomputable def em12280 : ℝ := (24835360210672797 / 50000000000000000000)
noncomputable def bp12280 : ℝ := (11468979716586893739 / 25000000000000000000)
noncomputable def bm12280 : ℝ := (46652411877940234487 / 100000000000000000000)

theorem positive12280 :
    Eplus aL (agent12280.root+dsL) scalar12280.worldRadius world12280.frame
      agent12280.frame tp12280 ≤ -ep12280 := by
  apply positive_check (eT := (115686328878854741221 / 100000000000000000000)) (y := (9298749978821735187 / 25000000000000000000)) (u := (9066002813928381329 / 6250000000000000000))
  · norm_num [world12280, agent12280, scalar12280, tp12280, tm12280, ep12280, em12280, dsL]
  · norm_num [world12280, agent12280, scalar12280, tp12280, tm12280, ep12280, em12280, dsL]
  · norm_num [world12280, agent12280, scalar12280, tp12280, tm12280, ep12280, em12280, dsL]
  · norm_num [world12280, agent12280, scalar12280, tp12280, tm12280, ep12280, em12280, dsL]
  · norm_num [world12280, agent12280, scalar12280, tp12280, tm12280, ep12280, em12280, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12280, agent12280, tp12280, tm12280, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12280, agent12280, scalar12280, tp12280, tm12280, ep12280, em12280, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12280, agent12280, tp12280, tm12280, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12280, agent12280, scalar12280, tp12280, tm12280, ep12280, em12280, dsL]

theorem negative12280 :
    Eminus aL (agent12280.root+dsL) scalar12280.worldRadius world12280.frame
      agent12280.frame tm12280 ≤ -em12280 := by
  apply negative_check (lo := (17040227948007914391 / 25000000000000000000)) (hi := (13632182358406331513 / 20000000000000000000))
    (y := (-((35426706831411319253 / 50000000000000000000)))) (u := (24618270457586313333 / 50000000000000000000))
  · norm_num [world12280, agent12280, scalar12280, tp12280, tm12280, ep12280, em12280, dsL]
  · norm_num [world12280, agent12280, scalar12280, tp12280, tm12280, ep12280, em12280, dsL]
  · norm_num [world12280, agent12280, scalar12280, tp12280, tm12280, ep12280, em12280, dsL]
  · norm_num [world12280, agent12280, scalar12280, tp12280, tm12280, ep12280, em12280, dsL]
  · norm_num [world12280, agent12280, scalar12280, tp12280, tm12280, ep12280, em12280, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12280, agent12280, tp12280, tm12280, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12280, agent12280, tp12280, tm12280, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12280, agent12280, scalar12280, tp12280, tm12280, ep12280, em12280, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12280, agent12280, tp12280, tm12280, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12280, agent12280, scalar12280, tp12280, tm12280, ep12280, em12280, dsL]

theorem tails12280 :
    exp (-((12280:ℝ)*ep12280)) ≤ scalar12280.upperTail ∧
    exp (-((12280:ℝ)*em12280)) ≤ scalar12280.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12280:ℝ)) (by norm_num [ep12280]) ?_)
      (show bp12280^8 ≤ scalar12280.upperTail by norm_num [bp12280, scalar12280])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12280, bp12280, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12280:ℝ)) (by norm_num [em12280]) ?_)
      (show bm12280^8 ≤ scalar12280.lowerTail by norm_num [bm12280, scalar12280])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12280, bm12280, Finset.sum_range_succ, Nat.factorial]

theorem guards12280 :
    agent12280.root+dsL+scalar12280.worldRadius < √(1/100/aL) ∧
    2*(agent12280.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12280, agent12280, scalar12280, tp12280, tm12280, ep12280, em12280, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12280, agent12280, scalar12280, tp12280, tm12280, ep12280, em12280, dsL]

noncomputable def master12280 : MasterCertificate 12280 world12280 agent12280 :=
  master scalar12280 dsL tp12280 tm12280 ep12280 em12280
    (by norm_num [dsL]) (by norm_num [tp12280]) (by norm_num [tm12280])
    (by norm_num [ep12280]) (by norm_num [em12280])
    positive12280 negative12280 tails12280.1 tails12280.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12280.1 guards12280.2

theorem preserves12280 : master12280.toScalarCertificate = scalar12280 := rfl

noncomputable def tp12281 : ℝ := (1153487501 / 5000000000)
noncomputable def tm12281 : ℝ := (-((6068500183 / 10000000000)))
noncomputable def ep12281 : ℝ := (5076724017439151 / 10000000000000000000)
noncomputable def em12281 : ℝ := (12418354206417051 / 25000000000000000000)
noncomputable def bp12281 : ℝ := (5733854823379653933 / 12500000000000000000)
noncomputable def bm12281 : ℝ := (9329516892509783553 / 20000000000000000000)

theorem positive12281 :
    Eplus aL (agent12281.root+dsL) scalar12281.worldRadius world12281.frame
      agent12281.frame tp12281 ≤ -ep12281 := by
  apply positive_check (eT := (57843338547442895977 / 50000000000000000000)) (y := (37195836320558596147 / 100000000000000000000)) (u := (72528629142167705833 / 50000000000000000000))
  · norm_num [world12281, agent12281, scalar12281, tp12281, tm12281, ep12281, em12281, dsL]
  · norm_num [world12281, agent12281, scalar12281, tp12281, tm12281, ep12281, em12281, dsL]
  · norm_num [world12281, agent12281, scalar12281, tp12281, tm12281, ep12281, em12281, dsL]
  · norm_num [world12281, agent12281, scalar12281, tp12281, tm12281, ep12281, em12281, dsL]
  · norm_num [world12281, agent12281, scalar12281, tp12281, tm12281, ep12281, em12281, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12281, agent12281, tp12281, tm12281, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12281, agent12281, scalar12281, tp12281, tm12281, ep12281, em12281, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12281, agent12281, tp12281, tm12281, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12281, agent12281, scalar12281, tp12281, tm12281, ep12281, em12281, dsL]

theorem negative12281 :
    Eminus aL (agent12281.root+dsL) scalar12281.worldRadius world12281.frame
      agent12281.frame tm12281 ≤ -em12281 := by
  apply negative_check (lo := (68160550460295073457 / 100000000000000000000)) (hi := (34080275230147536729 / 50000000000000000000))
    (y := (-((70853476546076775521 / 100000000000000000000)))) (u := (49236509953643209513 / 100000000000000000000))
  · norm_num [world12281, agent12281, scalar12281, tp12281, tm12281, ep12281, em12281, dsL]
  · norm_num [world12281, agent12281, scalar12281, tp12281, tm12281, ep12281, em12281, dsL]
  · norm_num [world12281, agent12281, scalar12281, tp12281, tm12281, ep12281, em12281, dsL]
  · norm_num [world12281, agent12281, scalar12281, tp12281, tm12281, ep12281, em12281, dsL]
  · norm_num [world12281, agent12281, scalar12281, tp12281, tm12281, ep12281, em12281, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12281, agent12281, tp12281, tm12281, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12281, agent12281, tp12281, tm12281, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12281, agent12281, scalar12281, tp12281, tm12281, ep12281, em12281, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12281, agent12281, tp12281, tm12281, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12281, agent12281, scalar12281, tp12281, tm12281, ep12281, em12281, dsL]

theorem tails12281 :
    exp (-((12281:ℝ)*ep12281)) ≤ scalar12281.upperTail ∧
    exp (-((12281:ℝ)*em12281)) ≤ scalar12281.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12281:ℝ)) (by norm_num [ep12281]) ?_)
      (show bp12281^8 ≤ scalar12281.upperTail by norm_num [bp12281, scalar12281])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12281, bp12281, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12281:ℝ)) (by norm_num [em12281]) ?_)
      (show bm12281^8 ≤ scalar12281.lowerTail by norm_num [bm12281, scalar12281])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12281, bm12281, Finset.sum_range_succ, Nat.factorial]

theorem guards12281 :
    agent12281.root+dsL+scalar12281.worldRadius < √(1/100/aL) ∧
    2*(agent12281.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12281, agent12281, scalar12281, tp12281, tm12281, ep12281, em12281, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12281, agent12281, scalar12281, tp12281, tm12281, ep12281, em12281, dsL]

noncomputable def master12281 : MasterCertificate 12281 world12281 agent12281 :=
  master scalar12281 dsL tp12281 tm12281 ep12281 em12281
    (by norm_num [dsL]) (by norm_num [tp12281]) (by norm_num [tm12281])
    (by norm_num [ep12281]) (by norm_num [em12281])
    positive12281 negative12281 tails12281.1 tails12281.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12281.1 guards12281.2

theorem preserves12281 : master12281.toScalarCertificate = scalar12281 := rfl

noncomputable def tp12282 : ℝ := (461415339 / 2000000000)
noncomputable def tm12282 : ℝ := (-((3034363237 / 5000000000)))
noncomputable def ep12282 : ℝ := (50770319314537543 / 100000000000000000000)
noncomputable def em12282 : ℝ := (49676111902569033 / 100000000000000000000)
noncomputable def bp12282 : ℝ := (11466439879806013857 / 25000000000000000000)
noncomputable def bm12282 : ℝ := (46642758182805071183 / 100000000000000000000)

theorem positive12282 :
    Eplus aL (agent12282.root+dsL) scalar12282.worldRadius world12282.frame
      agent12282.frame tp12282 ≤ -ep12282 := by
  apply positive_check (eT := (115687024495593879933 / 100000000000000000000)) (y := (18598335581742525623 / 50000000000000000000)) (u := (2266538582650789019 / 1562500000000000000))
  · norm_num [world12282, agent12282, scalar12282, tp12282, tm12282, ep12282, em12282, dsL]
  · norm_num [world12282, agent12282, scalar12282, tp12282, tm12282, ep12282, em12282, dsL]
  · norm_num [world12282, agent12282, scalar12282, tp12282, tm12282, ep12282, em12282, dsL]
  · norm_num [world12282, agent12282, scalar12282, tp12282, tm12282, ep12282, em12282, dsL]
  · norm_num [world12282, agent12282, scalar12282, tp12282, tm12282, ep12282, em12282, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12282, agent12282, tp12282, tm12282, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12282, agent12282, scalar12282, tp12282, tm12282, ep12282, em12282, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12282, agent12282, tp12282, tm12282, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12282, agent12282, scalar12282, tp12282, tm12282, ep12282, em12282, dsL]

theorem negative12282 :
    Eminus aL (agent12282.root+dsL) scalar12282.worldRadius world12282.frame
      agent12282.frame tm12282 ≤ -em12282 := by
  apply negative_check (lo := (34080094734879594023 / 50000000000000000000)) (hi := (68160189469759188047 / 100000000000000000000))
    (y := (-((35426769682540377227 / 50000000000000000000)))) (u := (49236479023767777567 / 100000000000000000000))
  · norm_num [world12282, agent12282, scalar12282, tp12282, tm12282, ep12282, em12282, dsL]
  · norm_num [world12282, agent12282, scalar12282, tp12282, tm12282, ep12282, em12282, dsL]
  · norm_num [world12282, agent12282, scalar12282, tp12282, tm12282, ep12282, em12282, dsL]
  · norm_num [world12282, agent12282, scalar12282, tp12282, tm12282, ep12282, em12282, dsL]
  · norm_num [world12282, agent12282, scalar12282, tp12282, tm12282, ep12282, em12282, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12282, agent12282, tp12282, tm12282, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12282, agent12282, tp12282, tm12282, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12282, agent12282, scalar12282, tp12282, tm12282, ep12282, em12282, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12282, agent12282, tp12282, tm12282, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12282, agent12282, scalar12282, tp12282, tm12282, ep12282, em12282, dsL]

theorem tails12282 :
    exp (-((12282:ℝ)*ep12282)) ≤ scalar12282.upperTail ∧
    exp (-((12282:ℝ)*em12282)) ≤ scalar12282.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12282:ℝ)) (by norm_num [ep12282]) ?_)
      (show bp12282^8 ≤ scalar12282.upperTail by norm_num [bp12282, scalar12282])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12282, bp12282, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12282:ℝ)) (by norm_num [em12282]) ?_)
      (show bm12282^8 ≤ scalar12282.lowerTail by norm_num [bm12282, scalar12282])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12282, bm12282, Finset.sum_range_succ, Nat.factorial]

theorem guards12282 :
    agent12282.root+dsL+scalar12282.worldRadius < √(1/100/aL) ∧
    2*(agent12282.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12282, agent12282, scalar12282, tp12282, tm12282, ep12282, em12282, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12282, agent12282, scalar12282, tp12282, tm12282, ep12282, em12282, dsL]

noncomputable def master12282 : MasterCertificate 12282 world12282 agent12282 :=
  master scalar12282 dsL tp12282 tm12282 ep12282 em12282
    (by norm_num [dsL]) (by norm_num [tp12282]) (by norm_num [tm12282])
    (by norm_num [ep12282]) (by norm_num [em12282])
    positive12282 negative12282 tails12282.1 tails12282.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12282.1 guards12282.2

theorem preserves12282 : master12282.toScalarCertificate = scalar12282 := rfl

noncomputable def tp12283 : ℝ := (1153589173 / 5000000000)
noncomputable def tm12283 : ℝ := (-((379309537 / 625000000)))
noncomputable def ep12283 : ℝ := (50773397166795461 / 100000000000000000000)
noncomputable def em12283 : ℝ := (49678805794717449 / 100000000000000000000)
noncomputable def bp12283 : ℝ := (45860681567609210679 / 100000000000000000000)
noncomputable def bm12283 : ℝ := (23318966468265433391 / 50000000000000000000)

theorem positive12283 :
    Eplus aL (agent12283.root+dsL) scalar12283.worldRadius world12283.frame
      agent12283.frame tp12283 ≤ -ep12283 := by
  apply positive_check (eT := (7230460726355664801 / 6250000000000000000)) (y := (37197505576323528851 / 100000000000000000000)) (u := (145059679681191373337 / 100000000000000000000))
  · norm_num [world12283, agent12283, scalar12283, tp12283, tm12283, ep12283, em12283, dsL]
  · norm_num [world12283, agent12283, scalar12283, tp12283, tm12283, ep12283, em12283, dsL]
  · norm_num [world12283, agent12283, scalar12283, tp12283, tm12283, ep12283, em12283, dsL]
  · norm_num [world12283, agent12283, scalar12283, tp12283, tm12283, ep12283, em12283, dsL]
  · norm_num [world12283, agent12283, scalar12283, tp12283, tm12283, ep12283, em12283, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12283, agent12283, tp12283, tm12283, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12283, agent12283, scalar12283, tp12283, tm12283, ep12283, em12283, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12283, agent12283, tp12283, tm12283, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12283, agent12283, scalar12283, tp12283, tm12283, ep12283, em12283, dsL]

theorem negative12283 :
    Eminus aL (agent12283.root+dsL) scalar12283.worldRadius world12283.frame
      agent12283.frame tm12283 ≤ -em12283 := by
  apply negative_check (lo := (8519978646145589523 / 12500000000000000000)) (hi := (13631965833832943237 / 20000000000000000000))
    (y := (-((17713400264570809783 / 25000000000000000000)))) (u := (24618224324108223467 / 50000000000000000000))
  · norm_num [world12283, agent12283, scalar12283, tp12283, tm12283, ep12283, em12283, dsL]
  · norm_num [world12283, agent12283, scalar12283, tp12283, tm12283, ep12283, em12283, dsL]
  · norm_num [world12283, agent12283, scalar12283, tp12283, tm12283, ep12283, em12283, dsL]
  · norm_num [world12283, agent12283, scalar12283, tp12283, tm12283, ep12283, em12283, dsL]
  · norm_num [world12283, agent12283, scalar12283, tp12283, tm12283, ep12283, em12283, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12283, agent12283, tp12283, tm12283, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12283, agent12283, tp12283, tm12283, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12283, agent12283, scalar12283, tp12283, tm12283, ep12283, em12283, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12283, agent12283, tp12283, tm12283, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12283, agent12283, scalar12283, tp12283, tm12283, ep12283, em12283, dsL]

theorem tails12283 :
    exp (-((12283:ℝ)*ep12283)) ≤ scalar12283.upperTail ∧
    exp (-((12283:ℝ)*em12283)) ≤ scalar12283.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12283:ℝ)) (by norm_num [ep12283]) ?_)
      (show bp12283^8 ≤ scalar12283.upperTail by norm_num [bp12283, scalar12283])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12283, bp12283, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12283:ℝ)) (by norm_num [em12283]) ?_)
      (show bm12283^8 ≤ scalar12283.lowerTail by norm_num [bm12283, scalar12283])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12283, bm12283, Finset.sum_range_succ, Nat.factorial]

theorem guards12283 :
    agent12283.root+dsL+scalar12283.worldRadius < √(1/100/aL) ∧
    2*(agent12283.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12283, agent12283, scalar12283, tp12283, tm12283, ep12283, em12283, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12283, agent12283, scalar12283, tp12283, tm12283, ep12283, em12283, dsL]

noncomputable def master12283 : MasterCertificate 12283 world12283 agent12283 :=
  master scalar12283 dsL tp12283 tm12283 ep12283 em12283
    (by norm_num [dsL]) (by norm_num [tp12283]) (by norm_num [tm12283])
    (by norm_num [ep12283]) (by norm_num [em12283])
    positive12283 negative12283 tails12283.1 tails12283.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12283.1 guards12283.2

theorem preserves12283 : master12283.toScalarCertificate = scalar12283 := rfl

noncomputable def tp12284 : ℝ := (36051249 / 156250000)
noncomputable def tm12284 : ℝ := (-((758647343 / 1250000000)))
noncomputable def ep12284 : ℝ := (25388236899676687 / 50000000000000000000)
noncomputable def em12284 : ℝ := (2484074925346911 / 5000000000000000000)
noncomputable def bp12284 : ℝ := (45855604684155824209 / 100000000000000000000)
noncomputable def bm12284 : ℝ := (46633108720261273249 / 100000000000000000000)

theorem positive12284 :
    Eplus aL (agent12284.root+dsL) scalar12284.worldRadius world12284.frame
      agent12284.frame tp12284 ≤ -ep12284 := by
  apply positive_check (eT := (57843859167188691537 / 50000000000000000000)) (y := (9299584882588210617 / 25000000000000000000)) (u := (18132611177159912309 / 12500000000000000000))
  · norm_num [world12284, agent12284, scalar12284, tp12284, tm12284, ep12284, em12284, dsL]
  · norm_num [world12284, agent12284, scalar12284, tp12284, tm12284, ep12284, em12284, dsL]
  · norm_num [world12284, agent12284, scalar12284, tp12284, tm12284, ep12284, em12284, dsL]
  · norm_num [world12284, agent12284, scalar12284, tp12284, tm12284, ep12284, em12284, dsL]
  · norm_num [world12284, agent12284, scalar12284, tp12284, tm12284, ep12284, em12284, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12284, agent12284, tp12284, tm12284, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12284, agent12284, scalar12284, tp12284, tm12284, ep12284, em12284, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12284, agent12284, tp12284, tm12284, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12284, agent12284, scalar12284, tp12284, tm12284, ep12284, em12284, dsL]

theorem negative12284 :
    Eminus aL (agent12284.root+dsL) scalar12284.worldRadius world12284.frame
      agent12284.frame tm12284 ≤ -em12284 := by
  apply negative_check (lo := (6815946866733322909 / 10000000000000000000)) (hi := (68159468667333229091 / 100000000000000000000))
    (y := (-((70853664182523984117 / 100000000000000000000)))) (u := (19694567027236751 / 40000000000000000))
  · norm_num [world12284, agent12284, scalar12284, tp12284, tm12284, ep12284, em12284, dsL]
  · norm_num [world12284, agent12284, scalar12284, tp12284, tm12284, ep12284, em12284, dsL]
  · norm_num [world12284, agent12284, scalar12284, tp12284, tm12284, ep12284, em12284, dsL]
  · norm_num [world12284, agent12284, scalar12284, tp12284, tm12284, ep12284, em12284, dsL]
  · norm_num [world12284, agent12284, scalar12284, tp12284, tm12284, ep12284, em12284, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12284, agent12284, tp12284, tm12284, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12284, agent12284, tp12284, tm12284, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12284, agent12284, scalar12284, tp12284, tm12284, ep12284, em12284, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12284, agent12284, tp12284, tm12284, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12284, agent12284, scalar12284, tp12284, tm12284, ep12284, em12284, dsL]

theorem tails12284 :
    exp (-((12284:ℝ)*ep12284)) ≤ scalar12284.upperTail ∧
    exp (-((12284:ℝ)*em12284)) ≤ scalar12284.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12284:ℝ)) (by norm_num [ep12284]) ?_)
      (show bp12284^8 ≤ scalar12284.upperTail by norm_num [bp12284, scalar12284])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12284, bp12284, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12284:ℝ)) (by norm_num [em12284]) ?_)
      (show bm12284^8 ≤ scalar12284.lowerTail by norm_num [bm12284, scalar12284])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12284, bm12284, Finset.sum_range_succ, Nat.factorial]

theorem guards12284 :
    agent12284.root+dsL+scalar12284.worldRadius < √(1/100/aL) ∧
    2*(agent12284.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12284, agent12284, scalar12284, tp12284, tm12284, ep12284, em12284, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12284, agent12284, scalar12284, tp12284, tm12284, ep12284, em12284, dsL]

noncomputable def master12284 : MasterCertificate 12284 world12284 agent12284 :=
  master scalar12284 dsL tp12284 tm12284 ep12284 em12284
    (by norm_num [dsL]) (by norm_num [tp12284]) (by norm_num [tm12284])
    (by norm_num [ep12284]) (by norm_num [em12284])
    positive12284 negative12284 tails12284.1 tails12284.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12284.1 guards12284.2

theorem preserves12284 : master12284.toScalarCertificate = scalar12284 := rfl

noncomputable def tp12285 : ℝ := (2307381463 / 10000000000)
noncomputable def tm12285 : ℝ := (-((3034702327 / 5000000000)))
noncomputable def ep12285 : ℝ := (5077954834024409 / 10000000000000000000)
noncomputable def em12285 : ℝ := (9936837862667057 / 20000000000000000000)
noncomputable def bp12285 : ℝ := (11462632370697155561 / 25000000000000000000)
noncomputable def bm12285 : ℝ := (91070871198737643 / 195312500000000000)

theorem positive12285 :
    Eplus aL (agent12285.root+dsL) scalar12285.worldRadius world12285.frame
      agent12285.frame tp12285 ≤ -ep12285 := by
  apply positive_check (eT := (115688064619050789583 / 100000000000000000000)) (y := (37199172737288813571 / 100000000000000000000)) (u := (145062098079706627211 / 100000000000000000000))
  · norm_num [world12285, agent12285, scalar12285, tp12285, tm12285, ep12285, em12285, dsL]
  · norm_num [world12285, agent12285, scalar12285, tp12285, tm12285, ep12285, em12285, dsL]
  · norm_num [world12285, agent12285, scalar12285, tp12285, tm12285, ep12285, em12285, dsL]
  · norm_num [world12285, agent12285, scalar12285, tp12285, tm12285, ep12285, em12285, dsL]
  · norm_num [world12285, agent12285, scalar12285, tp12285, tm12285, ep12285, em12285, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12285, agent12285, tp12285, tm12285, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12285, agent12285, scalar12285, tp12285, tm12285, ep12285, em12285, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12285, agent12285, tp12285, tm12285, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12285, agent12285, scalar12285, tp12285, tm12285, ep12285, em12285, dsL]

theorem negative12285 :
    Eminus aL (agent12285.root+dsL) scalar12285.worldRadius world12285.frame
      agent12285.frame tm12285 ≤ -em12285 := by
  apply negative_check (lo := (68159109152412157291 / 100000000000000000000)) (hi := (17039777288103039323 / 25000000000000000000))
    (y := (-((14170745077830370193 / 20000000000000000000)))) (u := (12309096858037556057 / 25000000000000000000))
  · norm_num [world12285, agent12285, scalar12285, tp12285, tm12285, ep12285, em12285, dsL]
  · norm_num [world12285, agent12285, scalar12285, tp12285, tm12285, ep12285, em12285, dsL]
  · norm_num [world12285, agent12285, scalar12285, tp12285, tm12285, ep12285, em12285, dsL]
  · norm_num [world12285, agent12285, scalar12285, tp12285, tm12285, ep12285, em12285, dsL]
  · norm_num [world12285, agent12285, scalar12285, tp12285, tm12285, ep12285, em12285, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12285, agent12285, tp12285, tm12285, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12285, agent12285, tp12285, tm12285, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12285, agent12285, scalar12285, tp12285, tm12285, ep12285, em12285, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12285, agent12285, tp12285, tm12285, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12285, agent12285, scalar12285, tp12285, tm12285, ep12285, em12285, dsL]

theorem tails12285 :
    exp (-((12285:ℝ)*ep12285)) ≤ scalar12285.upperTail ∧
    exp (-((12285:ℝ)*em12285)) ≤ scalar12285.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12285:ℝ)) (by norm_num [ep12285]) ?_)
      (show bp12285^8 ≤ scalar12285.upperTail by norm_num [bp12285, scalar12285])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12285, bp12285, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12285:ℝ)) (by norm_num [em12285]) ?_)
      (show bm12285^8 ≤ scalar12285.lowerTail by norm_num [bm12285, scalar12285])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12285, bm12285, Finset.sum_range_succ, Nat.factorial]

theorem guards12285 :
    agent12285.root+dsL+scalar12285.worldRadius < √(1/100/aL) ∧
    2*(agent12285.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12285, agent12285, scalar12285, tp12285, tm12285, ep12285, em12285, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12285, agent12285, scalar12285, tp12285, tm12285, ep12285, em12285, dsL]

noncomputable def master12285 : MasterCertificate 12285 world12285 agent12285 :=
  master scalar12285 dsL tp12285 tm12285 ep12285 em12285
    (by norm_num [dsL]) (by norm_num [tp12285]) (by norm_num [tm12285])
    (by norm_num [ep12285]) (by norm_num [em12285])
    positive12285 negative12285 tails12285.1 tails12285.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12285.1 guards12285.2

theorem preserves12285 : master12285.toScalarCertificate = scalar12285 := rfl

noncomputable def tp12286 : ℝ := (461496613 / 2000000000)
noncomputable def tm12286 : ℝ := (-((1213926087 / 2000000000)))
noncomputable def ep12286 : ℝ := (25391311033700537 / 50000000000000000000)
noncomputable def em12286 : ℝ := (12421719843510759 / 25000000000000000000)
noncomputable def bp12286 : ℝ := (22922727531838225729 / 50000000000000000000)
noncomputable def bm12286 : ℝ := (11655866026571100621 / 25000000000000000000)

theorem positive12286 :
    Eplus aL (agent12286.root+dsL) scalar12286.worldRadius world12286.frame
      agent12286.frame tp12286 ≤ -ep12286 := by
  apply positive_check (eT := (23137682296799858073 / 20000000000000000000)) (y := (744000149855123343 / 2000000000000000000)) (u := (14506330899855550399 / 10000000000000000000))
  · norm_num [world12286, agent12286, scalar12286, tp12286, tm12286, ep12286, em12286, dsL]
  · norm_num [world12286, agent12286, scalar12286, tp12286, tm12286, ep12286, em12286, dsL]
  · norm_num [world12286, agent12286, scalar12286, tp12286, tm12286, ep12286, em12286, dsL]
  · norm_num [world12286, agent12286, scalar12286, tp12286, tm12286, ep12286, em12286, dsL]
  · norm_num [world12286, agent12286, scalar12286, tp12286, tm12286, ep12286, em12286, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12286, agent12286, tp12286, tm12286, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12286, agent12286, scalar12286, tp12286, tm12286, ep12286, em12286, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12286, agent12286, tp12286, tm12286, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12286, agent12286, scalar12286, tp12286, tm12286, ep12286, em12286, dsL]

theorem negative12286 :
    Eminus aL (agent12286.root+dsL) scalar12286.worldRadius world12286.frame
      agent12286.frame tm12286 ≤ -em12286 := by
  apply negative_check (lo := (6815875013792259631 / 10000000000000000000)) (hi := (68158750137922596311 / 100000000000000000000))
    (y := (-((14170757203580039319 / 20000000000000000000)))) (u := (1969454303230153711 / 4000000000000000000))
  · norm_num [world12286, agent12286, scalar12286, tp12286, tm12286, ep12286, em12286, dsL]
  · norm_num [world12286, agent12286, scalar12286, tp12286, tm12286, ep12286, em12286, dsL]
  · norm_num [world12286, agent12286, scalar12286, tp12286, tm12286, ep12286, em12286, dsL]
  · norm_num [world12286, agent12286, scalar12286, tp12286, tm12286, ep12286, em12286, dsL]
  · norm_num [world12286, agent12286, scalar12286, tp12286, tm12286, ep12286, em12286, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12286, agent12286, tp12286, tm12286, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12286, agent12286, tp12286, tm12286, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12286, agent12286, scalar12286, tp12286, tm12286, ep12286, em12286, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12286, agent12286, tp12286, tm12286, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12286, agent12286, scalar12286, tp12286, tm12286, ep12286, em12286, dsL]

theorem tails12286 :
    exp (-((12286:ℝ)*ep12286)) ≤ scalar12286.upperTail ∧
    exp (-((12286:ℝ)*em12286)) ≤ scalar12286.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12286:ℝ)) (by norm_num [ep12286]) ?_)
      (show bp12286^8 ≤ scalar12286.upperTail by norm_num [bp12286, scalar12286])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12286, bp12286, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12286:ℝ)) (by norm_num [em12286]) ?_)
      (show bm12286^8 ≤ scalar12286.lowerTail by norm_num [bm12286, scalar12286])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12286, bm12286, Finset.sum_range_succ, Nat.factorial]

theorem guards12286 :
    agent12286.root+dsL+scalar12286.worldRadius < √(1/100/aL) ∧
    2*(agent12286.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12286, agent12286, scalar12286, tp12286, tm12286, ep12286, em12286, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12286, agent12286, scalar12286, tp12286, tm12286, ep12286, em12286, dsL]

noncomputable def master12286 : MasterCertificate 12286 world12286 agent12286 :=
  master scalar12286 dsL tp12286 tm12286 ep12286 em12286
    (by norm_num [dsL]) (by norm_num [tp12286]) (by norm_num [tm12286])
    (by norm_num [ep12286]) (by norm_num [em12286])
    positive12286 negative12286 tails12286.1 tails12286.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12286.1 guards12286.2

theorem preserves12286 : master12286.toScalarCertificate = scalar12286 := rfl

noncomputable def tp12287 : ℝ := (2307584519 / 10000000000)
noncomputable def tm12287 : ℝ := (-((1517464023 / 2500000000)))
noncomputable def ep12287 : ℝ := (25392846883145921 / 50000000000000000000)
noncomputable def em12287 : ℝ := (49689567529677319 / 100000000000000000000)
noncomputable def bp12287 : ℝ := (11460095570479141873 / 25000000000000000000)
noncomputable def bm12287 : ℝ := (46618643707987694137 / 100000000000000000000)

theorem positive12287 :
    Eplus aL (agent12287.root+dsL) scalar12287.worldRadius world12287.frame
      agent12287.frame tp12287 ≤ -ep12287 := by
  apply positive_check (eT := (57844378649956512757 / 50000000000000000000)) (y := (9300210082223901469 / 25000000000000000000)) (u := (72532258571624417729 / 50000000000000000000))
  · norm_num [world12287, agent12287, scalar12287, tp12287, tm12287, ep12287, em12287, dsL]
  · norm_num [world12287, agent12287, scalar12287, tp12287, tm12287, ep12287, em12287, dsL]
  · norm_num [world12287, agent12287, scalar12287, tp12287, tm12287, ep12287, em12287, dsL]
  · norm_num [world12287, agent12287, scalar12287, tp12287, tm12287, ep12287, em12287, dsL]
  · norm_num [world12287, agent12287, scalar12287, tp12287, tm12287, ep12287, em12287, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12287, agent12287, tp12287, tm12287, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12287, agent12287, scalar12287, tp12287, tm12287, ep12287, em12287, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12287, agent12287, tp12287, tm12287, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12287, agent12287, scalar12287, tp12287, tm12287, ep12287, em12287, dsL]

theorem negative12287 :
    Eminus aL (agent12287.root+dsL) scalar12287.worldRadius world12287.frame
      agent12287.frame tm12287 ≤ -em12287 := by
  apply negative_check (lo := (68158391602283766281 / 100000000000000000000)) (hi := (34079195801141883141 / 50000000000000000000))
    (y := (-((14170769286625774087 / 20000000000000000000)))) (u := (49236327834504805327 / 100000000000000000000))
  · norm_num [world12287, agent12287, scalar12287, tp12287, tm12287, ep12287, em12287, dsL]
  · norm_num [world12287, agent12287, scalar12287, tp12287, tm12287, ep12287, em12287, dsL]
  · norm_num [world12287, agent12287, scalar12287, tp12287, tm12287, ep12287, em12287, dsL]
  · norm_num [world12287, agent12287, scalar12287, tp12287, tm12287, ep12287, em12287, dsL]
  · norm_num [world12287, agent12287, scalar12287, tp12287, tm12287, ep12287, em12287, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12287, agent12287, tp12287, tm12287, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12287, agent12287, tp12287, tm12287, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12287, agent12287, scalar12287, tp12287, tm12287, ep12287, em12287, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12287, agent12287, tp12287, tm12287, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12287, agent12287, scalar12287, tp12287, tm12287, ep12287, em12287, dsL]

theorem tails12287 :
    exp (-((12287:ℝ)*ep12287)) ≤ scalar12287.upperTail ∧
    exp (-((12287:ℝ)*em12287)) ≤ scalar12287.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12287:ℝ)) (by norm_num [ep12287]) ?_)
      (show bp12287^8 ≤ scalar12287.upperTail by norm_num [bp12287, scalar12287])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12287, bp12287, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12287:ℝ)) (by norm_num [em12287]) ?_)
      (show bm12287^8 ≤ scalar12287.lowerTail by norm_num [bm12287, scalar12287])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12287, bm12287, Finset.sum_range_succ, Nat.factorial]

theorem guards12287 :
    agent12287.root+dsL+scalar12287.worldRadius < √(1/100/aL) ∧
    2*(agent12287.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12287, agent12287, scalar12287, tp12287, tm12287, ep12287, em12287, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12287, agent12287, scalar12287, tp12287, tm12287, ep12287, em12287, dsL]

noncomputable def master12287 : MasterCertificate 12287 world12287 agent12287 :=
  master scalar12287 dsL tp12287 tm12287 ep12287 em12287
    (by norm_num [dsL]) (by norm_num [tp12287]) (by norm_num [tm12287])
    (by norm_num [ep12287]) (by norm_num [em12287])
    positive12287 negative12287 tails12287.1 tails12287.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12287.1 guards12287.2

theorem preserves12287 : master12287.toScalarCertificate = scalar12287 := rfl

noncomputable def tp12288 : ℝ := (461537193 / 2000000000)
noncomputable def tm12288 : ℝ := (-((3035040937 / 5000000000)))
noncomputable def ep12288 : ℝ := (12697191212580057 / 25000000000000000000)
noncomputable def em12288 : ℝ := (49692255083161289 / 100000000000000000000)
noncomputable def bp12288 : ℝ := (45835310142359119047 / 100000000000000000000)
noncomputable def bm12288 : ℝ := (5826727990742670121 / 12500000000000000000)

theorem positive12288 :
    Eplus aL (agent12288.root+dsL) scalar12288.worldRadius world12288.frame
      agent12288.frame tp12288 ≤ -ep12288 := by
  apply positive_check (eT := (28922275772422349907 / 25000000000000000000)) (y := (2325104589133900229 / 6250000000000000000)) (u := (36266431419195339793 / 25000000000000000000))
  · norm_num [world12288, agent12288, scalar12288, tp12288, tm12288, ep12288, em12288, dsL]
  · norm_num [world12288, agent12288, scalar12288, tp12288, tm12288, ep12288, em12288, dsL]
  · norm_num [world12288, agent12288, scalar12288, tp12288, tm12288, ep12288, em12288, dsL]
  · norm_num [world12288, agent12288, scalar12288, tp12288, tm12288, ep12288, em12288, dsL]
  · norm_num [world12288, agent12288, scalar12288, tp12288, tm12288, ep12288, em12288, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12288, agent12288, tp12288, tm12288, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12288, agent12288, scalar12288, tp12288, tm12288, ep12288, em12288, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12288, agent12288, tp12288, tm12288, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12288, agent12288, scalar12288, tp12288, tm12288, ep12288, em12288, dsL]

theorem negative12288 :
    Eminus aL (agent12288.root+dsL) scalar12288.worldRadius world12288.frame
      agent12288.frame tm12288 ≤ -em12288 := by
  apply negative_check (lo := (68158032473696423029 / 100000000000000000000)) (hi := (6815803247369642303 / 10000000000000000000))
    (y := (-((70853908991538413173 / 100000000000000000000)))) (u := (49236297033050829263 / 100000000000000000000))
  · norm_num [world12288, agent12288, scalar12288, tp12288, tm12288, ep12288, em12288, dsL]
  · norm_num [world12288, agent12288, scalar12288, tp12288, tm12288, ep12288, em12288, dsL]
  · norm_num [world12288, agent12288, scalar12288, tp12288, tm12288, ep12288, em12288, dsL]
  · norm_num [world12288, agent12288, scalar12288, tp12288, tm12288, ep12288, em12288, dsL]
  · norm_num [world12288, agent12288, scalar12288, tp12288, tm12288, ep12288, em12288, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12288, agent12288, tp12288, tm12288, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12288, agent12288, tp12288, tm12288, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12288, agent12288, scalar12288, tp12288, tm12288, ep12288, em12288, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12288, agent12288, tp12288, tm12288, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12288, agent12288, scalar12288, tp12288, tm12288, ep12288, em12288, dsL]

theorem tails12288 :
    exp (-((12288:ℝ)*ep12288)) ≤ scalar12288.upperTail ∧
    exp (-((12288:ℝ)*em12288)) ≤ scalar12288.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12288:ℝ)) (by norm_num [ep12288]) ?_)
      (show bp12288^8 ≤ scalar12288.upperTail by norm_num [bp12288, scalar12288])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12288, bp12288, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12288:ℝ)) (by norm_num [em12288]) ?_)
      (show bm12288^8 ≤ scalar12288.lowerTail by norm_num [bm12288, scalar12288])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12288, bm12288, Finset.sum_range_succ, Nat.factorial]

theorem guards12288 :
    agent12288.root+dsL+scalar12288.worldRadius < √(1/100/aL) ∧
    2*(agent12288.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12288, agent12288, scalar12288, tp12288, tm12288, ep12288, em12288, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12288, agent12288, scalar12288, tp12288, tm12288, ep12288, em12288, dsL]

noncomputable def master12288 : MasterCertificate 12288 world12288 agent12288 :=
  master scalar12288 dsL tp12288 tm12288 ep12288 em12288
    (by norm_num [dsL]) (by norm_num [tp12288]) (by norm_num [tm12288])
    (by norm_num [ep12288]) (by norm_num [em12288])
    positive12288 negative12288 tails12288.1 tails12288.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12288.1 guards12288.2

theorem preserves12288 : master12288.toScalarCertificate = scalar12288 := rfl

noncomputable def tp12289 : ℝ := (1153893679 / 5000000000)
noncomputable def tm12289 : ℝ := (-((1517576811 / 2500000000)))
noncomputable def ep12289 : ℝ := (50791833847107907 / 100000000000000000000)
noncomputable def em12289 : ℝ := (4969494073477261 / 10000000000000000000)
noncomputable def bp12289 : ℝ := (45830239681589529281 / 100000000000000000000)
noncomputable def bm12289 : ℝ := (4660900569072811897 / 10000000000000000000)

theorem positive12289 :
    Eplus aL (agent12289.root+dsL) scalar12289.worldRadius world12289.frame
      agent12289.frame tp12289 ≤ -ep12289 := by
  apply positive_check (eT := (14461181065571864959 / 12500000000000000000)) (y := (37202505949050544353 / 100000000000000000000)) (u := (36266733346801676227 / 25000000000000000000))
  · norm_num [world12289, agent12289, scalar12289, tp12289, tm12289, ep12289, em12289, dsL]
  · norm_num [world12289, agent12289, scalar12289, tp12289, tm12289, ep12289, em12289, dsL]
  · norm_num [world12289, agent12289, scalar12289, tp12289, tm12289, ep12289, em12289, dsL]
  · norm_num [world12289, agent12289, scalar12289, tp12289, tm12289, ep12289, em12289, dsL]
  · norm_num [world12289, agent12289, scalar12289, tp12289, tm12289, ep12289, em12289, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12289, agent12289, tp12289, tm12289, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12289, agent12289, scalar12289, tp12289, tm12289, ep12289, em12289, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12289, agent12289, tp12289, tm12289, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12289, agent12289, scalar12289, tp12289, tm12289, ep12289, em12289, dsL]

theorem negative12289 :
    Eminus aL (agent12289.root+dsL) scalar12289.worldRadius world12289.frame
      agent12289.frame tm12289 ≤ -em12289 := by
  apply negative_check (lo := (68157675063568019511 / 100000000000000000000)) (hi := (8519709382946002439 / 12500000000000000000))
    (y := (-((35426984001673711751 / 50000000000000000000)))) (u := (49236267977829833367 / 100000000000000000000))
  · norm_num [world12289, agent12289, scalar12289, tp12289, tm12289, ep12289, em12289, dsL]
  · norm_num [world12289, agent12289, scalar12289, tp12289, tm12289, ep12289, em12289, dsL]
  · norm_num [world12289, agent12289, scalar12289, tp12289, tm12289, ep12289, em12289, dsL]
  · norm_num [world12289, agent12289, scalar12289, tp12289, tm12289, ep12289, em12289, dsL]
  · norm_num [world12289, agent12289, scalar12289, tp12289, tm12289, ep12289, em12289, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12289, agent12289, tp12289, tm12289, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12289, agent12289, tp12289, tm12289, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12289, agent12289, scalar12289, tp12289, tm12289, ep12289, em12289, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12289, agent12289, tp12289, tm12289, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12289, agent12289, scalar12289, tp12289, tm12289, ep12289, em12289, dsL]

theorem tails12289 :
    exp (-((12289:ℝ)*ep12289)) ≤ scalar12289.upperTail ∧
    exp (-((12289:ℝ)*em12289)) ≤ scalar12289.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12289:ℝ)) (by norm_num [ep12289]) ?_)
      (show bp12289^8 ≤ scalar12289.upperTail by norm_num [bp12289, scalar12289])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12289, bp12289, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12289:ℝ)) (by norm_num [em12289]) ?_)
      (show bm12289^8 ≤ scalar12289.lowerTail by norm_num [bm12289, scalar12289])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12289, bm12289, Finset.sum_range_succ, Nat.factorial]

theorem guards12289 :
    agent12289.root+dsL+scalar12289.worldRadius < √(1/100/aL) ∧
    2*(agent12289.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12289, agent12289, scalar12289, tp12289, tm12289, ep12289, em12289, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12289, agent12289, scalar12289, tp12289, tm12289, ep12289, em12289, dsL]

noncomputable def master12289 : MasterCertificate 12289 world12289 agent12289 :=
  master scalar12289 dsL tp12289 tm12289 ep12289 em12289
    (by norm_num [dsL]) (by norm_num [tp12289]) (by norm_num [tm12289])
    (by norm_num [ep12289]) (by norm_num [em12289])
    positive12289 negative12289 tails12289.1 tails12289.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12289.1 guards12289.2

theorem preserves12289 : master12289.toScalarCertificate = scalar12289 := rfl

noncomputable def tp12290 : ℝ := (1153944349 / 5000000000)
noncomputable def tm12290 : ℝ := (-((6070532749 / 10000000000)))
noncomputable def ep12290 : ℝ := (10158980285024343 / 20000000000000000000)
noncomputable def em12290 : ℝ := (24848812531521637 / 50000000000000000000)
noncomputable def bp12290 : ℝ := (22912585214470035501 / 50000000000000000000)
noncomputable def bm12290 : ℝ := (23302094294049872903 / 50000000000000000000)

theorem positive12290 :
    Eplus aL (agent12290.root+dsL) scalar12290.worldRadius world12290.frame
      agent12290.frame tp12290 ≤ -ep12290 := by
  apply positive_check (eT := (115689793604548945357 / 100000000000000000000)) (y := (37203338000308534907 / 100000000000000000000)) (u := (72534070211736227367 / 50000000000000000000))
  · norm_num [world12290, agent12290, scalar12290, tp12290, tm12290, ep12290, em12290, dsL]
  · norm_num [world12290, agent12290, scalar12290, tp12290, tm12290, ep12290, em12290, dsL]
  · norm_num [world12290, agent12290, scalar12290, tp12290, tm12290, ep12290, em12290, dsL]
  · norm_num [world12290, agent12290, scalar12290, tp12290, tm12290, ep12290, em12290, dsL]
  · norm_num [world12290, agent12290, scalar12290, tp12290, tm12290, ep12290, em12290, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12290, agent12290, tp12290, tm12290, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12290, agent12290, scalar12290, tp12290, tm12290, ep12290, em12290, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12290, agent12290, tp12290, tm12290, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12290, agent12290, scalar12290, tp12290, tm12290, ep12290, em12290, dsL]

theorem negative12290 :
    Eminus aL (agent12290.root+dsL) scalar12290.worldRadius world12290.frame
      agent12290.frame tm12290 ≤ -em12290 := by
  apply negative_check (lo := (34078658508735850559 / 50000000000000000000)) (hi := (68157317017471701119 / 100000000000000000000))
    (y := (-((35427014561603735931 / 50000000000000000000)))) (u := (24618118942350474361 / 50000000000000000000))
  · norm_num [world12290, agent12290, scalar12290, tp12290, tm12290, ep12290, em12290, dsL]
  · norm_num [world12290, agent12290, scalar12290, tp12290, tm12290, ep12290, em12290, dsL]
  · norm_num [world12290, agent12290, scalar12290, tp12290, tm12290, ep12290, em12290, dsL]
  · norm_num [world12290, agent12290, scalar12290, tp12290, tm12290, ep12290, em12290, dsL]
  · norm_num [world12290, agent12290, scalar12290, tp12290, tm12290, ep12290, em12290, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12290, agent12290, tp12290, tm12290, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12290, agent12290, tp12290, tm12290, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12290, agent12290, scalar12290, tp12290, tm12290, ep12290, em12290, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12290, agent12290, tp12290, tm12290, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12290, agent12290, scalar12290, tp12290, tm12290, ep12290, em12290, dsL]

theorem tails12290 :
    exp (-((12290:ℝ)*ep12290)) ≤ scalar12290.upperTail ∧
    exp (-((12290:ℝ)*em12290)) ≤ scalar12290.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12290:ℝ)) (by norm_num [ep12290]) ?_)
      (show bp12290^8 ≤ scalar12290.upperTail by norm_num [bp12290, scalar12290])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12290, bp12290, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12290:ℝ)) (by norm_num [em12290]) ?_)
      (show bm12290^8 ≤ scalar12290.lowerTail by norm_num [bm12290, scalar12290])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12290, bm12290, Finset.sum_range_succ, Nat.factorial]

theorem guards12290 :
    agent12290.root+dsL+scalar12290.worldRadius < √(1/100/aL) ∧
    2*(agent12290.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12290, agent12290, scalar12290, tp12290, tm12290, ep12290, em12290, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12290, agent12290, scalar12290, tp12290, tm12290, ep12290, em12290, dsL]

noncomputable def master12290 : MasterCertificate 12290 world12290 agent12290 :=
  master scalar12290 dsL tp12290 tm12290 ep12290 em12290
    (by norm_num [dsL]) (by norm_num [tp12290]) (by norm_num [tm12290])
    (by norm_num [ep12290]) (by norm_num [em12290])
    positive12290 negative12290 tails12290.1 tails12290.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12290.1 guards12290.2

theorem preserves12290 : master12290.toScalarCertificate = scalar12290 := rfl

noncomputable def tp12291 : ℝ := (576997497 / 2500000000)
noncomputable def tm12291 : ℝ := (-((6070758083 / 10000000000)))
noncomputable def ep12291 : ℝ := (25398983799117139 / 50000000000000000000)
noncomputable def em12291 : ℝ := (49700308073694119 / 100000000000000000000)
noncomputable def bp12291 : ℝ := (45820102374611820659 / 100000000000000000000)
noncomputable def bm12291 : ℝ := (9319874522788697057 / 20000000000000000000)

theorem positive12291 :
    Eplus aL (agent12291.root+dsL) scalar12291.worldRadius world12291.frame
      agent12291.frame tp12291 ≤ -ep12291 := by
  apply positive_check (eT := (11569013835158776587 / 10000000000000000000)) (y := (9301042382727639641 / 25000000000000000000)) (u := (145069346714469195001 / 100000000000000000000))
  · norm_num [world12291, agent12291, scalar12291, tp12291, tm12291, ep12291, em12291, dsL]
  · norm_num [world12291, agent12291, scalar12291, tp12291, tm12291, ep12291, em12291, dsL]
  · norm_num [world12291, agent12291, scalar12291, tp12291, tm12291, ep12291, em12291, dsL]
  · norm_num [world12291, agent12291, scalar12291, tp12291, tm12291, ep12291, em12291, dsL]
  · norm_num [world12291, agent12291, scalar12291, tp12291, tm12291, ep12291, em12291, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12291, agent12291, tp12291, tm12291, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12291, agent12291, scalar12291, tp12291, tm12291, ep12291, em12291, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12291, agent12291, tp12291, tm12291, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12291, agent12291, scalar12291, tp12291, tm12291, ep12291, em12291, dsL]

theorem negative12291 :
    Eminus aL (agent12291.root+dsL) scalar12291.worldRadius world12291.frame
      agent12291.frame tm12291 ≤ -em12291 := by
  apply negative_check (lo := (6815695965242448451 / 10000000000000000000)) (hi := (68156959652424484511 / 100000000000000000000))
    (y := (-((8856761126370185963 / 12500000000000000000)))) (u := (4923620839823274707 / 10000000000000000000))
  · norm_num [world12291, agent12291, scalar12291, tp12291, tm12291, ep12291, em12291, dsL]
  · norm_num [world12291, agent12291, scalar12291, tp12291, tm12291, ep12291, em12291, dsL]
  · norm_num [world12291, agent12291, scalar12291, tp12291, tm12291, ep12291, em12291, dsL]
  · norm_num [world12291, agent12291, scalar12291, tp12291, tm12291, ep12291, em12291, dsL]
  · norm_num [world12291, agent12291, scalar12291, tp12291, tm12291, ep12291, em12291, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12291, agent12291, tp12291, tm12291, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12291, agent12291, tp12291, tm12291, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12291, agent12291, scalar12291, tp12291, tm12291, ep12291, em12291, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12291, agent12291, tp12291, tm12291, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12291, agent12291, scalar12291, tp12291, tm12291, ep12291, em12291, dsL]

theorem tails12291 :
    exp (-((12291:ℝ)*ep12291)) ≤ scalar12291.upperTail ∧
    exp (-((12291:ℝ)*em12291)) ≤ scalar12291.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12291:ℝ)) (by norm_num [ep12291]) ?_)
      (show bp12291^8 ≤ scalar12291.upperTail by norm_num [bp12291, scalar12291])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12291, bp12291, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12291:ℝ)) (by norm_num [em12291]) ?_)
      (show bm12291^8 ≤ scalar12291.lowerTail by norm_num [bm12291, scalar12291])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12291, bm12291, Finset.sum_range_succ, Nat.factorial]

theorem guards12291 :
    agent12291.root+dsL+scalar12291.worldRadius < √(1/100/aL) ∧
    2*(agent12291.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12291, agent12291, scalar12291, tp12291, tm12291, ep12291, em12291, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12291, agent12291, scalar12291, tp12291, tm12291, ep12291, em12291, dsL]

noncomputable def master12291 : MasterCertificate 12291 world12291 agent12291 :=
  master scalar12291 dsL tp12291 tm12291 ep12291 em12291
    (by norm_num [dsL]) (by norm_num [tp12291]) (by norm_num [tm12291])
    (by norm_num [ep12291]) (by norm_num [em12291])
    positive12291 negative12291 tails12291.1 tails12291.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12291.1 guards12291.2

theorem preserves12291 : master12291.toScalarCertificate = scalar12291 := rfl

noncomputable def tp12292 : ℝ := (577022813 / 2500000000)
noncomputable def tm12292 : ℝ := (-((6070983237 / 10000000000)))
noncomputable def ep12292 : ℝ := (25400516404140391 / 50000000000000000000)
noncomputable def em12292 : ℝ := (24851495095220931 / 50000000000000000000)
noncomputable def bp12292 : ℝ := (45815035207543574483 / 100000000000000000000)
noncomputable def bm12292 : ℝ := (46594557464893059951 / 100000000000000000000)

theorem positive12292 :
    Eplus aL (agent12292.root+dsL) scalar12292.worldRadius world12292.frame
      agent12292.frame tp12292 ≤ -ep12292 := by
  apply positive_check (eT := (115690482941000519843 / 100000000000000000000)) (y := (4650625138774797359 / 12500000000000000000)) (u := (145070553086125410219 / 100000000000000000000))
  · norm_num [world12292, agent12292, scalar12292, tp12292, tm12292, ep12292, em12292, dsL]
  · norm_num [world12292, agent12292, scalar12292, tp12292, tm12292, ep12292, em12292, dsL]
  · norm_num [world12292, agent12292, scalar12292, tp12292, tm12292, ep12292, em12292, dsL]
  · norm_num [world12292, agent12292, scalar12292, tp12292, tm12292, ep12292, em12292, dsL]
  · norm_num [world12292, agent12292, scalar12292, tp12292, tm12292, ep12292, em12292, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12292, agent12292, tp12292, tm12292, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12292, agent12292, scalar12292, tp12292, tm12292, ep12292, em12292, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12292, agent12292, tp12292, tm12292, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12292, agent12292, scalar12292, tp12292, tm12292, ep12292, em12292, dsL]

theorem negative12292 :
    Eminus aL (agent12292.root+dsL) scalar12292.worldRadius world12292.frame
      agent12292.frame tm12292 ≤ -em12292 := by
  apply negative_check (lo := (17039150751792504971 / 25000000000000000000)) (hi := (13631320601434003977 / 20000000000000000000))
    (y := (-((70854148525535207657 / 100000000000000000000)))) (u := (49236179095521922687 / 100000000000000000000))
  · norm_num [world12292, agent12292, scalar12292, tp12292, tm12292, ep12292, em12292, dsL]
  · norm_num [world12292, agent12292, scalar12292, tp12292, tm12292, ep12292, em12292, dsL]
  · norm_num [world12292, agent12292, scalar12292, tp12292, tm12292, ep12292, em12292, dsL]
  · norm_num [world12292, agent12292, scalar12292, tp12292, tm12292, ep12292, em12292, dsL]
  · norm_num [world12292, agent12292, scalar12292, tp12292, tm12292, ep12292, em12292, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12292, agent12292, tp12292, tm12292, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12292, agent12292, tp12292, tm12292, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12292, agent12292, scalar12292, tp12292, tm12292, ep12292, em12292, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12292, agent12292, tp12292, tm12292, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12292, agent12292, scalar12292, tp12292, tm12292, ep12292, em12292, dsL]

theorem tails12292 :
    exp (-((12292:ℝ)*ep12292)) ≤ scalar12292.upperTail ∧
    exp (-((12292:ℝ)*em12292)) ≤ scalar12292.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12292:ℝ)) (by norm_num [ep12292]) ?_)
      (show bp12292^8 ≤ scalar12292.upperTail by norm_num [bp12292, scalar12292])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12292, bp12292, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12292:ℝ)) (by norm_num [em12292]) ?_)
      (show bm12292^8 ≤ scalar12292.lowerTail by norm_num [bm12292, scalar12292])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12292, bm12292, Finset.sum_range_succ, Nat.factorial]

theorem guards12292 :
    agent12292.root+dsL+scalar12292.worldRadius < √(1/100/aL) ∧
    2*(agent12292.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12292, agent12292, scalar12292, tp12292, tm12292, ep12292, em12292, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12292, agent12292, scalar12292, tp12292, tm12292, ep12292, em12292, dsL]

noncomputable def master12292 : MasterCertificate 12292 world12292 agent12292 :=
  master scalar12292 dsL tp12292 tm12292 ep12292 em12292
    (by norm_num [dsL]) (by norm_num [tp12292]) (by norm_num [tm12292])
    (by norm_num [ep12292]) (by norm_num [em12292])
    positive12292 negative12292 tails12292.1 tails12292.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12292.1 guards12292.2

theorem preserves12292 : master12292.toScalarCertificate = scalar12292 := rfl

noncomputable def tp12293 : ℝ := (1154096237 / 5000000000)
noncomputable def tm12293 : ℝ := (-((3035604129 / 5000000000)))
noncomputable def ep12293 : ℝ := (12701023951181169 / 25000000000000000000)
noncomputable def em12293 : ℝ := (49705670264270143 / 100000000000000000000)
noncomputable def bp12293 : ℝ := (22904984904008687433 / 50000000000000000000)
noncomputable def bm12293 : ℝ := (9317948792708722249 / 20000000000000000000)

theorem positive12293 :
    Eplus aL (agent12293.root+dsL) scalar12293.worldRadius world12293.frame
      agent12293.frame tp12293 ≤ -ep12293 := by
  apply positive_check (eT := (1807669175873793671 / 1562500000000000000)) (y := (37205832354230419903 / 100000000000000000000)) (u := (145071758981452147077 / 100000000000000000000))
  · norm_num [world12293, agent12293, scalar12293, tp12293, tm12293, ep12293, em12293, dsL]
  · norm_num [world12293, agent12293, scalar12293, tp12293, tm12293, ep12293, em12293, dsL]
  · norm_num [world12293, agent12293, scalar12293, tp12293, tm12293, ep12293, em12293, dsL]
  · norm_num [world12293, agent12293, scalar12293, tp12293, tm12293, ep12293, em12293, dsL]
  · norm_num [world12293, agent12293, scalar12293, tp12293, tm12293, ep12293, em12293, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12293, agent12293, tp12293, tm12293, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12293, agent12293, scalar12293, tp12293, tm12293, ep12293, em12293, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12293, agent12293, tp12293, tm12293, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12293, agent12293, scalar12293, tp12293, tm12293, ep12293, em12293, dsL]

theorem negative12293 :
    Eminus aL (agent12293.root+dsL) scalar12293.worldRadius world12293.frame
      agent12293.frame tm12293 ≤ -em12293 := by
  apply negative_check (lo := (6815624687935556047 / 10000000000000000000)) (hi := (68156246879355560471 / 100000000000000000000))
    (y := (-((70854207041216871811 / 100000000000000000000)))) (u := (49236150284644529 / 100000000000000000))
  · norm_num [world12293, agent12293, scalar12293, tp12293, tm12293, ep12293, em12293, dsL]
  · norm_num [world12293, agent12293, scalar12293, tp12293, tm12293, ep12293, em12293, dsL]
  · norm_num [world12293, agent12293, scalar12293, tp12293, tm12293, ep12293, em12293, dsL]
  · norm_num [world12293, agent12293, scalar12293, tp12293, tm12293, ep12293, em12293, dsL]
  · norm_num [world12293, agent12293, scalar12293, tp12293, tm12293, ep12293, em12293, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12293, agent12293, tp12293, tm12293, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12293, agent12293, tp12293, tm12293, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12293, agent12293, scalar12293, tp12293, tm12293, ep12293, em12293, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12293, agent12293, tp12293, tm12293, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12293, agent12293, scalar12293, tp12293, tm12293, ep12293, em12293, dsL]

theorem tails12293 :
    exp (-((12293:ℝ)*ep12293)) ≤ scalar12293.upperTail ∧
    exp (-((12293:ℝ)*em12293)) ≤ scalar12293.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12293:ℝ)) (by norm_num [ep12293]) ?_)
      (show bp12293^8 ≤ scalar12293.upperTail by norm_num [bp12293, scalar12293])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12293, bp12293, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12293:ℝ)) (by norm_num [em12293]) ?_)
      (show bm12293^8 ≤ scalar12293.lowerTail by norm_num [bm12293, scalar12293])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12293, bm12293, Finset.sum_range_succ, Nat.factorial]

theorem guards12293 :
    agent12293.root+dsL+scalar12293.worldRadius < √(1/100/aL) ∧
    2*(agent12293.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12293, agent12293, scalar12293, tp12293, tm12293, ep12293, em12293, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12293, agent12293, scalar12293, tp12293, tm12293, ep12293, em12293, dsL]

noncomputable def master12293 : MasterCertificate 12293 world12293 agent12293 :=
  master scalar12293 dsL tp12293 tm12293 ep12293 em12293
    (by norm_num [dsL]) (by norm_num [tp12293]) (by norm_num [tm12293])
    (by norm_num [ep12293]) (by norm_num [em12293])
    positive12293 negative12293 tails12293.1 tails12293.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12293.1 guards12293.2

theorem preserves12293 : master12293.toScalarCertificate = scalar12293 := rfl

noncomputable def tp12294 : ℝ := (2308293597 / 10000000000)
noncomputable def tm12294 : ℝ := (-((758929159 / 1250000000)))
noncomputable def ep12294 : ℝ := (50807157851967403 / 100000000000000000000)
noncomputable def em12294 : ℝ := (24854174724973733 / 50000000000000000000)
noncomputable def bp12294 : ℝ := (45804905285930190439 / 100000000000000000000)
noncomputable def bm12294 : ℝ := (46584931283152387903 / 100000000000000000000)

theorem positive12294 :
    Eplus aL (agent12294.root+dsL) scalar12294.worldRadius world12294.frame
      agent12294.frame tp12294 ≤ -ep12294 := by
  apply positive_check (eT := (115691170879961252881 / 100000000000000000000)) (y := (18603331140670173783 / 50000000000000000000)) (u := (36268240744076229 / 25000000000000000))
  · norm_num [world12294, agent12294, scalar12294, tp12294, tm12294, ep12294, em12294, dsL]
  · norm_num [world12294, agent12294, scalar12294, tp12294, tm12294, ep12294, em12294, dsL]
  · norm_num [world12294, agent12294, scalar12294, tp12294, tm12294, ep12294, em12294, dsL]
  · norm_num [world12294, agent12294, scalar12294, tp12294, tm12294, ep12294, em12294, dsL]
  · norm_num [world12294, agent12294, scalar12294, tp12294, tm12294, ep12294, em12294, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12294, agent12294, tp12294, tm12294, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12294, agent12294, scalar12294, tp12294, tm12294, ep12294, em12294, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12294, agent12294, tp12294, tm12294, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12294, agent12294, scalar12294, tp12294, tm12294, ep12294, em12294, dsL]

theorem negative12294 :
    Eminus aL (agent12294.root+dsL) scalar12294.worldRadius world12294.frame
      agent12294.frame tm12294 ≤ -em12294 := by
  apply negative_check (lo := (68155890726707513701 / 100000000000000000000)) (hi := (34077945363353756851 / 50000000000000000000))
    (y := (-((4428391651931314211 / 6250000000000000000)))) (u := (9847224208691813543 / 20000000000000000000))
  · norm_num [world12294, agent12294, scalar12294, tp12294, tm12294, ep12294, em12294, dsL]
  · norm_num [world12294, agent12294, scalar12294, tp12294, tm12294, ep12294, em12294, dsL]
  · norm_num [world12294, agent12294, scalar12294, tp12294, tm12294, ep12294, em12294, dsL]
  · norm_num [world12294, agent12294, scalar12294, tp12294, tm12294, ep12294, em12294, dsL]
  · norm_num [world12294, agent12294, scalar12294, tp12294, tm12294, ep12294, em12294, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12294, agent12294, tp12294, tm12294, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12294, agent12294, tp12294, tm12294, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12294, agent12294, scalar12294, tp12294, tm12294, ep12294, em12294, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12294, agent12294, tp12294, tm12294, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12294, agent12294, scalar12294, tp12294, tm12294, ep12294, em12294, dsL]

theorem tails12294 :
    exp (-((12294:ℝ)*ep12294)) ≤ scalar12294.upperTail ∧
    exp (-((12294:ℝ)*em12294)) ≤ scalar12294.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12294:ℝ)) (by norm_num [ep12294]) ?_)
      (show bp12294^8 ≤ scalar12294.upperTail by norm_num [bp12294, scalar12294])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12294, bp12294, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12294:ℝ)) (by norm_num [em12294]) ?_)
      (show bm12294^8 ≤ scalar12294.lowerTail by norm_num [bm12294, scalar12294])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12294, bm12294, Finset.sum_range_succ, Nat.factorial]

theorem guards12294 :
    agent12294.root+dsL+scalar12294.worldRadius < √(1/100/aL) ∧
    2*(agent12294.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12294, agent12294, scalar12294, tp12294, tm12294, ep12294, em12294, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12294, agent12294, scalar12294, tp12294, tm12294, ep12294, em12294, dsL]

noncomputable def master12294 : MasterCertificate 12294 world12294 agent12294 :=
  master scalar12294 dsL tp12294 tm12294 ep12294 em12294
    (by norm_num [dsL]) (by norm_num [tp12294]) (by norm_num [tm12294])
    (by norm_num [ep12294]) (by norm_num [em12294])
    positive12294 negative12294 tails12294.1 tails12294.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12294.1 guards12294.2

theorem preserves12294 : master12294.toScalarCertificate = scalar12294 := rfl

noncomputable def tp12295 : ℝ := (2308394757 / 10000000000)
noncomputable def tm12295 : ℝ := (-((1517914503 / 2500000000)))
noncomputable def ep12295 : ℝ := (2032408734167257 / 4000000000000000000)
noncomputable def em12295 : ℝ := (24855513585684091 / 50000000000000000000)
noncomputable def bp12295 : ℝ := (11449960515168177377 / 25000000000000000000)
noncomputable def bm12295 : ℝ := (9316023967228865703 / 20000000000000000000)

theorem positive12295 :
    Eplus aL (agent12295.root+dsL) scalar12295.worldRadius world12295.frame
      agent12295.frame tp12295 ≤ -ep12295 := by
  apply positive_check (eT := (57845757403325703341 / 50000000000000000000)) (y := (372074933441611713 / 1000000000000000000)) (u := (145074168628773137217 / 100000000000000000000))
  · norm_num [world12295, agent12295, scalar12295, tp12295, tm12295, ep12295, em12295, dsL]
  · norm_num [world12295, agent12295, scalar12295, tp12295, tm12295, ep12295, em12295, dsL]
  · norm_num [world12295, agent12295, scalar12295, tp12295, tm12295, ep12295, em12295, dsL]
  · norm_num [world12295, agent12295, scalar12295, tp12295, tm12295, ep12295, em12295, dsL]
  · norm_num [world12295, agent12295, scalar12295, tp12295, tm12295, ep12295, em12295, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12295, agent12295, tp12295, tm12295, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12295, agent12295, scalar12295, tp12295, tm12295, ep12295, em12295, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12295, agent12295, tp12295, tm12295, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12295, agent12295, scalar12295, tp12295, tm12295, ep12295, em12295, dsL]

theorem negative12295 :
    Eminus aL (agent12295.root+dsL) scalar12295.worldRadius world12295.frame
      agent12295.frame tm12295 ≤ -em12295 := by
  apply negative_check (lo := (34077767849122313539 / 50000000000000000000)) (hi := (68155535698244627079 / 100000000000000000000))
    (y := (-((3542716194337784019 / 5000000000000000000)))) (u := (2461804637721652553 / 5000000000000000000))
  · norm_num [world12295, agent12295, scalar12295, tp12295, tm12295, ep12295, em12295, dsL]
  · norm_num [world12295, agent12295, scalar12295, tp12295, tm12295, ep12295, em12295, dsL]
  · norm_num [world12295, agent12295, scalar12295, tp12295, tm12295, ep12295, em12295, dsL]
  · norm_num [world12295, agent12295, scalar12295, tp12295, tm12295, ep12295, em12295, dsL]
  · norm_num [world12295, agent12295, scalar12295, tp12295, tm12295, ep12295, em12295, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12295, agent12295, tp12295, tm12295, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12295, agent12295, tp12295, tm12295, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12295, agent12295, scalar12295, tp12295, tm12295, ep12295, em12295, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12295, agent12295, tp12295, tm12295, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12295, agent12295, scalar12295, tp12295, tm12295, ep12295, em12295, dsL]

theorem tails12295 :
    exp (-((12295:ℝ)*ep12295)) ≤ scalar12295.upperTail ∧
    exp (-((12295:ℝ)*em12295)) ≤ scalar12295.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12295:ℝ)) (by norm_num [ep12295]) ?_)
      (show bp12295^8 ≤ scalar12295.upperTail by norm_num [bp12295, scalar12295])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12295, bp12295, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12295:ℝ)) (by norm_num [em12295]) ?_)
      (show bm12295^8 ≤ scalar12295.lowerTail by norm_num [bm12295, scalar12295])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12295, bm12295, Finset.sum_range_succ, Nat.factorial]

theorem guards12295 :
    agent12295.root+dsL+scalar12295.worldRadius < √(1/100/aL) ∧
    2*(agent12295.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12295, agent12295, scalar12295, tp12295, tm12295, ep12295, em12295, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12295, agent12295, scalar12295, tp12295, tm12295, ep12295, em12295, dsL]

noncomputable def master12295 : MasterCertificate 12295 world12295 agent12295 :=
  master scalar12295 dsL tp12295 tm12295 ep12295 em12295
    (by norm_num [dsL]) (by norm_num [tp12295]) (by norm_num [tm12295])
    (by norm_num [ep12295]) (by norm_num [em12295])
    positive12295 negative12295 tails12295.1 tails12295.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12295.1 guards12295.2

theorem preserves12295 : master12295.toScalarCertificate = scalar12295 := rfl

noncomputable def tp12296 : ℝ := (577123953 / 2500000000)
noncomputable def tm12296 : ℝ := (-((6071882923 / 10000000000)))
noncomputable def ep12296 : ℝ := (10162655448624807 / 20000000000000000000)
noncomputable def em12296 : ℝ := (24856851714989883 / 50000000000000000000)
noncomputable def bp12296 : ℝ := (45794780180237689911 / 100000000000000000000)
noncomputable def bm12296 : ℝ := (4657530962145950537 / 10000000000000000000)

theorem positive12296 :
    Eplus aL (agent12296.root+dsL) scalar12296.worldRadius world12296.frame
      agent12296.frame tp12296 ≤ -ep12296 := by
  apply positive_check (eT := (57845928999320578999 / 50000000000000000000)) (y := (37208322883140626417 / 100000000000000000000)) (u := (145075372080542577199 / 100000000000000000000))
  · norm_num [world12296, agent12296, scalar12296, tp12296, tm12296, ep12296, em12296, dsL]
  · norm_num [world12296, agent12296, scalar12296, tp12296, tm12296, ep12296, em12296, dsL]
  · norm_num [world12296, agent12296, scalar12296, tp12296, tm12296, ep12296, em12296, dsL]
  · norm_num [world12296, agent12296, scalar12296, tp12296, tm12296, ep12296, em12296, dsL]
  · norm_num [world12296, agent12296, scalar12296, tp12296, tm12296, ep12296, em12296, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12296, agent12296, tp12296, tm12296, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12296, agent12296, scalar12296, tp12296, tm12296, ep12296, em12296, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12296, agent12296, tp12296, tm12296, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12296, agent12296, scalar12296, tp12296, tm12296, ep12296, em12296, dsL]

theorem negative12296 :
    Eminus aL (agent12296.root+dsL) scalar12296.worldRadius world12296.frame
      agent12296.frame tm12296 ≤ -em12296 := by
  apply negative_check (lo := (68155179878939671631 / 100000000000000000000)) (hi := (4259698742433729477 / 6250000000000000000))
    (y := (-((70854383504775893081 / 100000000000000000000)))) (u := (49236063400858070789 / 100000000000000000000))
  · norm_num [world12296, agent12296, scalar12296, tp12296, tm12296, ep12296, em12296, dsL]
  · norm_num [world12296, agent12296, scalar12296, tp12296, tm12296, ep12296, em12296, dsL]
  · norm_num [world12296, agent12296, scalar12296, tp12296, tm12296, ep12296, em12296, dsL]
  · norm_num [world12296, agent12296, scalar12296, tp12296, tm12296, ep12296, em12296, dsL]
  · norm_num [world12296, agent12296, scalar12296, tp12296, tm12296, ep12296, em12296, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12296, agent12296, tp12296, tm12296, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12296, agent12296, tp12296, tm12296, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12296, agent12296, scalar12296, tp12296, tm12296, ep12296, em12296, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12296, agent12296, tp12296, tm12296, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12296, agent12296, scalar12296, tp12296, tm12296, ep12296, em12296, dsL]

theorem tails12296 :
    exp (-((12296:ℝ)*ep12296)) ≤ scalar12296.upperTail ∧
    exp (-((12296:ℝ)*em12296)) ≤ scalar12296.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12296:ℝ)) (by norm_num [ep12296]) ?_)
      (show bp12296^8 ≤ scalar12296.upperTail by norm_num [bp12296, scalar12296])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12296, bp12296, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12296:ℝ)) (by norm_num [em12296]) ?_)
      (show bm12296^8 ≤ scalar12296.lowerTail by norm_num [bm12296, scalar12296])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12296, bm12296, Finset.sum_range_succ, Nat.factorial]

theorem guards12296 :
    agent12296.root+dsL+scalar12296.worldRadius < √(1/100/aL) ∧
    2*(agent12296.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12296, agent12296, scalar12296, tp12296, tm12296, ep12296, em12296, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12296, agent12296, scalar12296, tp12296, tm12296, ep12296, em12296, dsL]

noncomputable def master12296 : MasterCertificate 12296 world12296 agent12296 :=
  master scalar12296 dsL tp12296 tm12296 ep12296 em12296
    (by norm_num [dsL]) (by norm_num [tp12296]) (by norm_num [tm12296])
    (by norm_num [ep12296]) (by norm_num [em12296])
    positive12296 negative12296 tails12296.1 tails12296.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12296.1 guards12296.2

theorem preserves12296 : master12296.toScalarCertificate = scalar12296 := rfl

noncomputable def tp12297 : ℝ := (1154298411 / 5000000000)
noncomputable def tm12297 : ℝ := (-((6072107501 / 10000000000)))
noncomputable def ep12297 : ℝ := (50816335047399517 / 100000000000000000000)
noncomputable def em12297 : ℝ := (49716378657771759 / 100000000000000000000)
noncomputable def bp12297 : ℝ := (45789719272524355791 / 100000000000000000000)
noncomputable def bm12297 : ℝ := (11642625082458975191 / 25000000000000000000)

theorem positive12297 :
    Eplus aL (agent12297.root+dsL) scalar12297.worldRadius world12297.frame
      agent12297.frame tp12297 ≤ -ep12297 := by
  apply positive_check (eT := (115692200894296253469 / 100000000000000000000)) (y := (37209152190124018899 / 100000000000000000000)) (u := (72538287602861608721 / 50000000000000000000))
  · norm_num [world12297, agent12297, scalar12297, tp12297, tm12297, ep12297, em12297, dsL]
  · norm_num [world12297, agent12297, scalar12297, tp12297, tm12297, ep12297, em12297, dsL]
  · norm_num [world12297, agent12297, scalar12297, tp12297, tm12297, ep12297, em12297, dsL]
  · norm_num [world12297, agent12297, scalar12297, tp12297, tm12297, ep12297, em12297, dsL]
  · norm_num [world12297, agent12297, scalar12297, tp12297, tm12297, ep12297, em12297, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12297, agent12297, tp12297, tm12297, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12297, agent12297, scalar12297, tp12297, tm12297, ep12297, em12297, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12297, agent12297, tp12297, tm12297, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12297, agent12297, scalar12297, tp12297, tm12297, ep12297, em12297, dsL]

theorem negative12297 :
    Eminus aL (agent12297.root+dsL) scalar12297.worldRadius world12297.frame
      agent12297.frame tm12297 ≤ -em12297 := by
  apply negative_check (lo := (68154825437638751609 / 100000000000000000000)) (hi := (6815482543763875161 / 10000000000000000000))
    (y := (-((4428402572493417883 / 6250000000000000000)))) (u := (24618017506877705657 / 50000000000000000000))
  · norm_num [world12297, agent12297, scalar12297, tp12297, tm12297, ep12297, em12297, dsL]
  · norm_num [world12297, agent12297, scalar12297, tp12297, tm12297, ep12297, em12297, dsL]
  · norm_num [world12297, agent12297, scalar12297, tp12297, tm12297, ep12297, em12297, dsL]
  · norm_num [world12297, agent12297, scalar12297, tp12297, tm12297, ep12297, em12297, dsL]
  · norm_num [world12297, agent12297, scalar12297, tp12297, tm12297, ep12297, em12297, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12297, agent12297, tp12297, tm12297, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12297, agent12297, tp12297, tm12297, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12297, agent12297, scalar12297, tp12297, tm12297, ep12297, em12297, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12297, agent12297, tp12297, tm12297, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12297, agent12297, scalar12297, tp12297, tm12297, ep12297, em12297, dsL]

theorem tails12297 :
    exp (-((12297:ℝ)*ep12297)) ≤ scalar12297.upperTail ∧
    exp (-((12297:ℝ)*em12297)) ≤ scalar12297.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12297:ℝ)) (by norm_num [ep12297]) ?_)
      (show bp12297^8 ≤ scalar12297.upperTail by norm_num [bp12297, scalar12297])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12297, bp12297, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12297:ℝ)) (by norm_num [em12297]) ?_)
      (show bm12297^8 ≤ scalar12297.lowerTail by norm_num [bm12297, scalar12297])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12297, bm12297, Finset.sum_range_succ, Nat.factorial]

theorem guards12297 :
    agent12297.root+dsL+scalar12297.worldRadius < √(1/100/aL) ∧
    2*(agent12297.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12297, agent12297, scalar12297, tp12297, tm12297, ep12297, em12297, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12297, agent12297, scalar12297, tp12297, tm12297, ep12297, em12297, dsL]

noncomputable def master12297 : MasterCertificate 12297 world12297 agent12297 :=
  master scalar12297 dsL tp12297 tm12297 ep12297 em12297
    (by norm_num [dsL]) (by norm_num [tp12297]) (by norm_num [tm12297])
    (by norm_num [ep12297]) (by norm_num [em12297])
    positive12297 negative12297 tails12297.1 tails12297.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12297.1 guards12297.2

theorem preserves12297 : master12297.toScalarCertificate = scalar12297 := rfl

noncomputable def tp12298 : ℝ := (1154348903 / 5000000000)
noncomputable def tm12298 : ℝ := (-((151808299 / 250000000)))
noncomputable def ep12298 : ℝ := (25409695488405523 / 50000000000000000000)
noncomputable def em12298 : ℝ := (9943810426562647 / 20000000000000000000)
noncomputable def bp12298 : ℝ := (11446164973420029137 / 25000000000000000000)
noncomputable def bm12298 : ℝ := (46565692478050768271 / 100000000000000000000)

theorem positive12298 :
    Eplus aL (agent12298.root+dsL) scalar12298.worldRadius world12298.frame
      agent12298.frame tp12298 ≤ -ep12298 := by
  apply positive_check (eT := (23138508726475834157 / 20000000000000000000)) (y := (4651247679918673829 / 12500000000000000000)) (u := (145077778257087446907 / 100000000000000000000))
  · norm_num [world12298, agent12298, scalar12298, tp12298, tm12298, ep12298, em12298, dsL]
  · norm_num [world12298, agent12298, scalar12298, tp12298, tm12298, ep12298, em12298, dsL]
  · norm_num [world12298, agent12298, scalar12298, tp12298, tm12298, ep12298, em12298, dsL]
  · norm_num [world12298, agent12298, scalar12298, tp12298, tm12298, ep12298, em12298, dsL]
  · norm_num [world12298, agent12298, scalar12298, tp12298, tm12298, ep12298, em12298, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12298, agent12298, tp12298, tm12298, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12298, agent12298, scalar12298, tp12298, tm12298, ep12298, em12298, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12298, agent12298, tp12298, tm12298, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12298, agent12298, scalar12298, tp12298, tm12298, ep12298, em12298, dsL]

theorem negative12298 :
    Eminus aL (agent12298.root+dsL) scalar12298.worldRadius world12298.frame
      agent12298.frame tm12298 ≤ -em12298 := by
  apply negative_check (lo := (8519308931677919333 / 12500000000000000000)) (hi := (13630894290684670933 / 20000000000000000000))
    (y := (-((70854497952356809731 / 100000000000000000000)))) (u := (49236007051406815217 / 100000000000000000000))
  · norm_num [world12298, agent12298, scalar12298, tp12298, tm12298, ep12298, em12298, dsL]
  · norm_num [world12298, agent12298, scalar12298, tp12298, tm12298, ep12298, em12298, dsL]
  · norm_num [world12298, agent12298, scalar12298, tp12298, tm12298, ep12298, em12298, dsL]
  · norm_num [world12298, agent12298, scalar12298, tp12298, tm12298, ep12298, em12298, dsL]
  · norm_num [world12298, agent12298, scalar12298, tp12298, tm12298, ep12298, em12298, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12298, agent12298, tp12298, tm12298, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12298, agent12298, tp12298, tm12298, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12298, agent12298, scalar12298, tp12298, tm12298, ep12298, em12298, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12298, agent12298, tp12298, tm12298, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12298, agent12298, scalar12298, tp12298, tm12298, ep12298, em12298, dsL]

theorem tails12298 :
    exp (-((12298:ℝ)*ep12298)) ≤ scalar12298.upperTail ∧
    exp (-((12298:ℝ)*em12298)) ≤ scalar12298.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12298:ℝ)) (by norm_num [ep12298]) ?_)
      (show bp12298^8 ≤ scalar12298.upperTail by norm_num [bp12298, scalar12298])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12298, bp12298, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12298:ℝ)) (by norm_num [em12298]) ?_)
      (show bm12298^8 ≤ scalar12298.lowerTail by norm_num [bm12298, scalar12298])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12298, bm12298, Finset.sum_range_succ, Nat.factorial]

theorem guards12298 :
    agent12298.root+dsL+scalar12298.worldRadius < √(1/100/aL) ∧
    2*(agent12298.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12298, agent12298, scalar12298, tp12298, tm12298, ep12298, em12298, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12298, agent12298, scalar12298, tp12298, tm12298, ep12298, em12298, dsL]

noncomputable def master12298 : MasterCertificate 12298 world12298 agent12298 :=
  master scalar12298 dsL tp12298 tm12298 ep12298 em12298
    (by norm_num [dsL]) (by norm_num [tp12298]) (by norm_num [tm12298])
    (by norm_num [ep12298]) (by norm_num [em12298])
    positive12298 negative12298 tails12298.1 tails12298.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12298.1 guards12298.2

theorem preserves12298 : master12298.toScalarCertificate = scalar12298 := rfl

noncomputable def tp12299 : ℝ := (2308798777 / 10000000000)
noncomputable def tm12299 : ℝ := (-((3036278203 / 5000000000)))
noncomputable def ep12299 : ℝ := (25411222881314357 / 50000000000000000000)
noncomputable def em12299 : ℝ := (12430431145076369 / 25000000000000000000)
noncomputable def bp12299 : ℝ := (45779601528972710361 / 100000000000000000000)
noncomputable def bm12299 : ℝ := (9312177109391294459 / 20000000000000000000)

theorem positive12299 :
    Eplus aL (agent12299.root+dsL) scalar12299.worldRadius world12299.frame
      agent12299.frame tp12299 ≤ -ep12299 := by
  apply positive_check (eT := (115692886307867930417 / 100000000000000000000)) (y := (37210810709913523619 / 100000000000000000000)) (u := (145078981349386069311 / 100000000000000000000))
  · norm_num [world12299, agent12299, scalar12299, tp12299, tm12299, ep12299, em12299, dsL]
  · norm_num [world12299, agent12299, scalar12299, tp12299, tm12299, ep12299, em12299, dsL]
  · norm_num [world12299, agent12299, scalar12299, tp12299, tm12299, ep12299, em12299, dsL]
  · norm_num [world12299, agent12299, scalar12299, tp12299, tm12299, ep12299, em12299, dsL]
  · norm_num [world12299, agent12299, scalar12299, tp12299, tm12299, ep12299, em12299, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12299, agent12299, tp12299, tm12299, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12299, agent12299, scalar12299, tp12299, tm12299, ep12299, em12299, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12299, agent12299, tp12299, tm12299, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12299, agent12299, scalar12299, tp12299, tm12299, ep12299, em12299, dsL]

theorem negative12299 :
    Eminus aL (agent12299.root+dsL) scalar12299.worldRadius world12299.frame
      agent12299.frame tm12299 ≤ -em12299 := by
  apply negative_check (lo := (68154117470121361907 / 100000000000000000000)) (hi := (17038529367530340477 / 25000000000000000000))
    (y := (-((17713638817853681199 / 25000000000000000000)))) (u := (6154497353724938317 / 12500000000000000000))
  · norm_num [world12299, agent12299, scalar12299, tp12299, tm12299, ep12299, em12299, dsL]
  · norm_num [world12299, agent12299, scalar12299, tp12299, tm12299, ep12299, em12299, dsL]
  · norm_num [world12299, agent12299, scalar12299, tp12299, tm12299, ep12299, em12299, dsL]
  · norm_num [world12299, agent12299, scalar12299, tp12299, tm12299, ep12299, em12299, dsL]
  · norm_num [world12299, agent12299, scalar12299, tp12299, tm12299, ep12299, em12299, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12299, agent12299, tp12299, tm12299, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12299, agent12299, tp12299, tm12299, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12299, agent12299, scalar12299, tp12299, tm12299, ep12299, em12299, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12299, agent12299, tp12299, tm12299, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12299, agent12299, scalar12299, tp12299, tm12299, ep12299, em12299, dsL]

theorem tails12299 :
    exp (-((12299:ℝ)*ep12299)) ≤ scalar12299.upperTail ∧
    exp (-((12299:ℝ)*em12299)) ≤ scalar12299.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12299:ℝ)) (by norm_num [ep12299]) ?_)
      (show bp12299^8 ≤ scalar12299.upperTail by norm_num [bp12299, scalar12299])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12299, bp12299, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12299:ℝ)) (by norm_num [em12299]) ?_)
      (show bm12299^8 ≤ scalar12299.lowerTail by norm_num [bm12299, scalar12299])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12299, bm12299, Finset.sum_range_succ, Nat.factorial]

theorem guards12299 :
    agent12299.root+dsL+scalar12299.worldRadius < √(1/100/aL) ∧
    2*(agent12299.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12299, agent12299, scalar12299, tp12299, tm12299, ep12299, em12299, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12299, agent12299, scalar12299, tp12299, tm12299, ep12299, em12299, dsL]

noncomputable def master12299 : MasterCertificate 12299 world12299 agent12299 :=
  master scalar12299 dsL tp12299 tm12299 ep12299 em12299
    (by norm_num [dsL]) (by norm_num [tp12299]) (by norm_num [tm12299])
    (by norm_num [ep12299]) (by norm_num [em12299])
    positive12299 negative12299 tails12299.1 tails12299.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12299.1 guards12299.2

theorem preserves12299 : master12299.toScalarCertificate = scalar12299 := rfl

end BstLean.Part261
