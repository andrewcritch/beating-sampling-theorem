import BstLean.Part261Checker
import BstLean.Part259Data15
import BstLean.Part259Data16
import BstLean.Part259Data17
import BstLean.Part259Data18
import BstLean.Part259Data19

namespace BstLean.Part261
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part259

noncomputable def tp12300 : ℝ := (288612461 / 1250000000)
noncomputable def tm12300 : ℝ := (-((6072780789 / 10000000000)))
noncomputable def ep12300 : ℝ := (50825498998587987 / 100000000000000000000)
noncomputable def em12300 : ℝ := (49724395565805383 / 100000000000000000000)
noncomputable def bp12300 : ℝ := (45774544464308150847 / 100000000000000000000)
noncomputable def bm12300 : ℝ := (2909754990470250273 / 6250000000000000000)

theorem positive12300 :
    Eplus aL (agent12300.root+dsL) scalar12300.worldRadius world12300.frame
      agent12300.frame tp12300 ≤ -ep12300 := by
  apply positive_check (eT := (23138645715489987073 / 20000000000000000000)) (y := (37211639536292378887 / 100000000000000000000)) (u := (18135022975904600573 / 12500000000000000000))
  · norm_num [world12300, agent12300, scalar12300, tp12300, tm12300, ep12300, em12300, dsL]
  · norm_num [world12300, agent12300, scalar12300, tp12300, tm12300, ep12300, em12300, dsL]
  · norm_num [world12300, agent12300, scalar12300, tp12300, tm12300, ep12300, em12300, dsL]
  · norm_num [world12300, agent12300, scalar12300, tp12300, tm12300, ep12300, em12300, dsL]
  · norm_num [world12300, agent12300, scalar12300, tp12300, tm12300, ep12300, em12300, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12300, agent12300, tp12300, tm12300, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12300, agent12300, scalar12300, tp12300, tm12300, ep12300, em12300, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12300, agent12300, tp12300, tm12300, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12300, agent12300, scalar12300, tp12300, tm12300, ep12300, em12300, dsL]

theorem negative12300 :
    Eminus aL (agent12300.root+dsL) scalar12300.worldRadius world12300.frame
      agent12300.frame tm12300 ≤ -em12300 := by
  apply negative_check (lo := (68153763702902628787 / 100000000000000000000)) (hi := (17038440925725657197 / 25000000000000000000))
    (y := (-((70854613084967908837 / 100000000000000000000)))) (u := (49235950364738928419 / 100000000000000000000))
  · norm_num [world12300, agent12300, scalar12300, tp12300, tm12300, ep12300, em12300, dsL]
  · norm_num [world12300, agent12300, scalar12300, tp12300, tm12300, ep12300, em12300, dsL]
  · norm_num [world12300, agent12300, scalar12300, tp12300, tm12300, ep12300, em12300, dsL]
  · norm_num [world12300, agent12300, scalar12300, tp12300, tm12300, ep12300, em12300, dsL]
  · norm_num [world12300, agent12300, scalar12300, tp12300, tm12300, ep12300, em12300, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12300, agent12300, tp12300, tm12300, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12300, agent12300, tp12300, tm12300, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12300, agent12300, scalar12300, tp12300, tm12300, ep12300, em12300, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12300, agent12300, tp12300, tm12300, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12300, agent12300, scalar12300, tp12300, tm12300, ep12300, em12300, dsL]

theorem tails12300 :
    exp (-((12300:ℝ)*ep12300)) ≤ scalar12300.upperTail ∧
    exp (-((12300:ℝ)*em12300)) ≤ scalar12300.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12300:ℝ)) (by norm_num [ep12300]) ?_)
      (show bp12300^8 ≤ scalar12300.upperTail by norm_num [bp12300, scalar12300])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12300, bp12300, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12300:ℝ)) (by norm_num [em12300]) ?_)
      (show bm12300^8 ≤ scalar12300.lowerTail by norm_num [bm12300, scalar12300])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12300, bm12300, Finset.sum_range_succ, Nat.factorial]

theorem guards12300 :
    agent12300.root+dsL+scalar12300.worldRadius < √(1/100/aL) ∧
    2*(agent12300.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12300, agent12300, scalar12300, tp12300, tm12300, ep12300, em12300, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12300, agent12300, scalar12300, tp12300, tm12300, ep12300, em12300, dsL]

noncomputable def master12300 : MasterCertificate 12300 world12300 agent12300 :=
  master scalar12300 dsL tp12300 tm12300 ep12300 em12300
    (by norm_num [dsL]) (by norm_num [tp12300]) (by norm_num [tm12300])
    (by norm_num [ep12300]) (by norm_num [em12300])
    positive12300 negative12300 tails12300.1 tails12300.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12300.1 guards12300.2

theorem preserves12300 : master12300.toScalarCertificate = scalar12300 := rfl

noncomputable def tp12301 : ℝ := (1154500259 / 5000000000)
noncomputable def tm12301 : ℝ := (-((759125617 / 1250000000)))
noncomputable def ep12301 : ℝ := (12707137708491359 / 25000000000000000000)
noncomputable def em12301 : ℝ := (49727065237728281 / 100000000000000000000)
noncomputable def bp12301 : ℝ := (22884744297294868329 / 50000000000000000000)
noncomputable def bm12301 : ℝ := (23275637636748155579 / 50000000000000000000)

theorem positive12301 :
    Eplus aL (agent12301.root+dsL) scalar12301.worldRadius world12301.frame
      agent12301.frame tp12301 ≤ -ep12301 := by
  apply positive_check (eT := (115693570287774485349 / 100000000000000000000)) (y := (9303116826000566651 / 25000000000000000000)) (u := (36270346184780565741 / 25000000000000000000))
  · norm_num [world12301, agent12301, scalar12301, tp12301, tm12301, ep12301, em12301, dsL]
  · norm_num [world12301, agent12301, scalar12301, tp12301, tm12301, ep12301, em12301, dsL]
  · norm_num [world12301, agent12301, scalar12301, tp12301, tm12301, ep12301, em12301, dsL]
  · norm_num [world12301, agent12301, scalar12301, tp12301, tm12301, ep12301, em12301, dsL]
  · norm_num [world12301, agent12301, scalar12301, tp12301, tm12301, ep12301, em12301, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12301, agent12301, tp12301, tm12301, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12301, agent12301, scalar12301, tp12301, tm12301, ep12301, em12301, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12301, agent12301, tp12301, tm12301, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12301, agent12301, scalar12301, tp12301, tm12301, ep12301, em12301, dsL]

theorem negative12301 :
    Eminus aL (agent12301.root+dsL) scalar12301.worldRadius world12301.frame
      agent12301.frame tm12301 ≤ -em12301 := by
  apply negative_check (lo := (17038352724027355723 / 25000000000000000000)) (hi := (68153410896109422893 / 100000000000000000000))
    (y := (-((14170933808447297543 / 20000000000000000000)))) (u := (49235922813653653877 / 100000000000000000000))
  · norm_num [world12301, agent12301, scalar12301, tp12301, tm12301, ep12301, em12301, dsL]
  · norm_num [world12301, agent12301, scalar12301, tp12301, tm12301, ep12301, em12301, dsL]
  · norm_num [world12301, agent12301, scalar12301, tp12301, tm12301, ep12301, em12301, dsL]
  · norm_num [world12301, agent12301, scalar12301, tp12301, tm12301, ep12301, em12301, dsL]
  · norm_num [world12301, agent12301, scalar12301, tp12301, tm12301, ep12301, em12301, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12301, agent12301, tp12301, tm12301, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12301, agent12301, tp12301, tm12301, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12301, agent12301, scalar12301, tp12301, tm12301, ep12301, em12301, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12301, agent12301, tp12301, tm12301, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12301, agent12301, scalar12301, tp12301, tm12301, ep12301, em12301, dsL]

theorem tails12301 :
    exp (-((12301:ℝ)*ep12301)) ≤ scalar12301.upperTail ∧
    exp (-((12301:ℝ)*em12301)) ≤ scalar12301.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12301:ℝ)) (by norm_num [ep12301]) ?_)
      (show bp12301^8 ≤ scalar12301.upperTail by norm_num [bp12301, scalar12301])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12301, bp12301, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12301:ℝ)) (by norm_num [em12301]) ?_)
      (show bm12301^8 ≤ scalar12301.lowerTail by norm_num [bm12301, scalar12301])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12301, bm12301, Finset.sum_range_succ, Nat.factorial]

theorem guards12301 :
    agent12301.root+dsL+scalar12301.worldRadius < √(1/100/aL) ∧
    2*(agent12301.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12301, agent12301, scalar12301, tp12301, tm12301, ep12301, em12301, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12301, agent12301, scalar12301, tp12301, tm12301, ep12301, em12301, dsL]

noncomputable def master12301 : MasterCertificate 12301 world12301 agent12301 :=
  master scalar12301 dsL tp12301 tm12301 ep12301 em12301
    (by norm_num [dsL]) (by norm_num [tp12301]) (by norm_num [tm12301])
    (by norm_num [ep12301]) (by norm_num [em12301])
    positive12301 negative12301 tails12301.1 tails12301.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12301.1 guards12301.2

theorem preserves12301 : master12301.toScalarCertificate = scalar12301 := rfl

noncomputable def tp12302 : ℝ := (14431883 / 62500000)
noncomputable def tm12302 : ℝ := (-((1518307263 / 2500000000)))
noncomputable def ep12302 : ℝ := (50831600911082007 / 100000000000000000000)
noncomputable def em12302 : ℝ := (49729733296138957 / 100000000000000000000)
noncomputable def bp12302 : ℝ := (22882217085749628693 / 50000000000000000000)
noncomputable def bm12302 : ℝ := (46546472039540761219 / 100000000000000000000)

theorem positive12302 :
    Eplus aL (agent12302.root+dsL) scalar12302.worldRadius world12302.frame
      agent12302.frame tp12302 ≤ -ep12302 := by
  apply positive_check (eT := (14461738941726461519 / 12500000000000000000)) (y := (18606647168984384633 / 50000000000000000000)) (u := (145082584616414817459 / 100000000000000000000))
  · norm_num [world12302, agent12302, scalar12302, tp12302, tm12302, ep12302, em12302, dsL]
  · norm_num [world12302, agent12302, scalar12302, tp12302, tm12302, ep12302, em12302, dsL]
  · norm_num [world12302, agent12302, scalar12302, tp12302, tm12302, ep12302, em12302, dsL]
  · norm_num [world12302, agent12302, scalar12302, tp12302, tm12302, ep12302, em12302, dsL]
  · norm_num [world12302, agent12302, scalar12302, tp12302, tm12302, ep12302, em12302, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12302, agent12302, tp12302, tm12302, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12302, agent12302, scalar12302, tp12302, tm12302, ep12302, em12302, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12302, agent12302, tp12302, tm12302, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12302, agent12302, scalar12302, tp12302, tm12302, ep12302, em12302, dsL]

theorem negative12302 :
    Eminus aL (agent12302.root+dsL) scalar12302.worldRadius world12302.frame
      agent12302.frame tm12302 ≤ -em12302 := by
  apply negative_check (lo := (34076529083823410813 / 50000000000000000000)) (hi := (68153058167646821627 / 100000000000000000000))
    (y := (-((35427362755578969223 / 50000000000000000000)))) (u := (12308973752666731179 / 25000000000000000000))
  · norm_num [world12302, agent12302, scalar12302, tp12302, tm12302, ep12302, em12302, dsL]
  · norm_num [world12302, agent12302, scalar12302, tp12302, tm12302, ep12302, em12302, dsL]
  · norm_num [world12302, agent12302, scalar12302, tp12302, tm12302, ep12302, em12302, dsL]
  · norm_num [world12302, agent12302, scalar12302, tp12302, tm12302, ep12302, em12302, dsL]
  · norm_num [world12302, agent12302, scalar12302, tp12302, tm12302, ep12302, em12302, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12302, agent12302, tp12302, tm12302, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12302, agent12302, tp12302, tm12302, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12302, agent12302, scalar12302, tp12302, tm12302, ep12302, em12302, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12302, agent12302, tp12302, tm12302, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12302, agent12302, scalar12302, tp12302, tm12302, ep12302, em12302, dsL]

theorem tails12302 :
    exp (-((12302:ℝ)*ep12302)) ≤ scalar12302.upperTail ∧
    exp (-((12302:ℝ)*em12302)) ≤ scalar12302.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12302:ℝ)) (by norm_num [ep12302]) ?_)
      (show bp12302^8 ≤ scalar12302.upperTail by norm_num [bp12302, scalar12302])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12302, bp12302, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12302:ℝ)) (by norm_num [em12302]) ?_)
      (show bm12302^8 ≤ scalar12302.lowerTail by norm_num [bm12302, scalar12302])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12302, bm12302, Finset.sum_range_succ, Nat.factorial]

theorem guards12302 :
    agent12302.root+dsL+scalar12302.worldRadius < √(1/100/aL) ∧
    2*(agent12302.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12302, agent12302, scalar12302, tp12302, tm12302, ep12302, em12302, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12302, agent12302, scalar12302, tp12302, tm12302, ep12302, em12302, dsL]

noncomputable def master12302 : MasterCertificate 12302 world12302 agent12302 :=
  master scalar12302 dsL tp12302 tm12302 ep12302 em12302
    (by norm_num [dsL]) (by norm_num [tp12302]) (by norm_num [tm12302])
    (by norm_num [ep12302]) (by norm_num [em12302])
    positive12302 negative12302 tails12302.1 tails12302.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12302.1 guards12302.2

theorem preserves12302 : master12302.toScalarCertificate = scalar12302 := rfl

noncomputable def tp12303 : ℝ := (1154601069 / 5000000000)
noncomputable def tm12303 : ℝ := (-((388701 / 640000)))
noncomputable def ep12303 : ℝ := (25417325268342833 / 50000000000000000000)
noncomputable def em12303 : ℝ := (9946480183930903 / 20000000000000000000)
noncomputable def bp12303 : ℝ := (45759380275395097867 / 100000000000000000000)
noncomputable def bm12303 : ℝ := (11635417325507021123 / 25000000000000000000)

theorem positive12303 :
    Eplus aL (agent12303.root+dsL) scalar12303.worldRadius world12303.frame
      agent12303.frame tp12303 ≤ -ep12303 := by
  apply positive_check (eT := (11569425351340081687 / 10000000000000000000)) (y := (37214123282510204901 / 100000000000000000000)) (u := (145083787275565250769 / 100000000000000000000))
  · norm_num [world12303, agent12303, scalar12303, tp12303, tm12303, ep12303, em12303, dsL]
  · norm_num [world12303, agent12303, scalar12303, tp12303, tm12303, ep12303, em12303, dsL]
  · norm_num [world12303, agent12303, scalar12303, tp12303, tm12303, ep12303, em12303, dsL]
  · norm_num [world12303, agent12303, scalar12303, tp12303, tm12303, ep12303, em12303, dsL]
  · norm_num [world12303, agent12303, scalar12303, tp12303, tm12303, ep12303, em12303, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12303, agent12303, tp12303, tm12303, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12303, agent12303, scalar12303, tp12303, tm12303, ep12303, em12303, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12303, agent12303, tp12303, tm12303, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12303, agent12303, scalar12303, tp12303, tm12303, ep12303, em12303, dsL]

theorem negative12303 :
    Eminus aL (agent12303.root+dsL) scalar12303.worldRadius world12303.frame
      agent12303.frame tm12303 ≤ -em12303 := by
  apply negative_check (lo := (3407635278458221189 / 5000000000000000000)) (hi := (68152705569164423781 / 100000000000000000000))
    (y := (-((17713695556298895831 / 25000000000000000000)))) (u := (49235867087010811891 / 100000000000000000000))
  · norm_num [world12303, agent12303, scalar12303, tp12303, tm12303, ep12303, em12303, dsL]
  · norm_num [world12303, agent12303, scalar12303, tp12303, tm12303, ep12303, em12303, dsL]
  · norm_num [world12303, agent12303, scalar12303, tp12303, tm12303, ep12303, em12303, dsL]
  · norm_num [world12303, agent12303, scalar12303, tp12303, tm12303, ep12303, em12303, dsL]
  · norm_num [world12303, agent12303, scalar12303, tp12303, tm12303, ep12303, em12303, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12303, agent12303, tp12303, tm12303, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12303, agent12303, tp12303, tm12303, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12303, agent12303, scalar12303, tp12303, tm12303, ep12303, em12303, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12303, agent12303, tp12303, tm12303, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12303, agent12303, scalar12303, tp12303, tm12303, ep12303, em12303, dsL]

theorem tails12303 :
    exp (-((12303:ℝ)*ep12303)) ≤ scalar12303.upperTail ∧
    exp (-((12303:ℝ)*em12303)) ≤ scalar12303.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12303:ℝ)) (by norm_num [ep12303]) ?_)
      (show bp12303^8 ≤ scalar12303.upperTail by norm_num [bp12303, scalar12303])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12303, bp12303, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12303:ℝ)) (by norm_num [em12303]) ?_)
      (show bm12303^8 ≤ scalar12303.lowerTail by norm_num [bm12303, scalar12303])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12303, bm12303, Finset.sum_range_succ, Nat.factorial]

theorem guards12303 :
    agent12303.root+dsL+scalar12303.worldRadius < √(1/100/aL) ∧
    2*(agent12303.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12303, agent12303, scalar12303, tp12303, tm12303, ep12303, em12303, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12303, agent12303, scalar12303, tp12303, tm12303, ep12303, em12303, dsL]

noncomputable def master12303 : MasterCertificate 12303 world12303 agent12303 :=
  master scalar12303 dsL tp12303 tm12303 ep12303 em12303
    (by norm_num [dsL]) (by norm_num [tp12303]) (by norm_num [tm12303])
    (by norm_num [ep12303]) (by norm_num [em12303])
    positive12303 negative12303 tails12303.1 tails12303.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12303.1 guards12303.2

theorem preserves12303 : master12303.toScalarCertificate = scalar12303 := rfl

noncomputable def tp12304 : ℝ := (461860567 / 2000000000)
noncomputable def tm12304 : ℝ := (-((3036838453 / 5000000000)))
noncomputable def ep12304 : ℝ := (12709424565978113 / 25000000000000000000)
noncomputable def em12304 : ℝ := (49735066782967287 / 100000000000000000000)
noncomputable def bp12304 : ℝ := (915086558489276793 / 2000000000000000000)
noncomputable def bm12304 : ℝ := (11634217002388635943 / 25000000000000000000)

theorem positive12304 :
    Eplus aL (agent12304.root+dsL) scalar12304.worldRadius world12304.frame
      agent12304.frame tp12304 ≤ -ep12304 := by
  apply positive_check (eT := (115694594349437481793 / 100000000000000000000)) (y := (4651868754029864343 / 12500000000000000000)) (u := (36271246690085328801 / 25000000000000000000))
  · norm_num [world12304, agent12304, scalar12304, tp12304, tm12304, ep12304, em12304, dsL]
  · norm_num [world12304, agent12304, scalar12304, tp12304, tm12304, ep12304, em12304, dsL]
  · norm_num [world12304, agent12304, scalar12304, tp12304, tm12304, ep12304, em12304, dsL]
  · norm_num [world12304, agent12304, scalar12304, tp12304, tm12304, ep12304, em12304, dsL]
  · norm_num [world12304, agent12304, scalar12304, tp12304, tm12304, ep12304, em12304, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12304, agent12304, tp12304, tm12304, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12304, agent12304, scalar12304, tp12304, tm12304, ep12304, em12304, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12304, agent12304, tp12304, tm12304, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12304, agent12304, scalar12304, tp12304, tm12304, ep12304, em12304, dsL]

theorem negative12304 :
    Eminus aL (agent12304.root+dsL) scalar12304.worldRadius world12304.frame
      agent12304.frame tm12304 ≤ -em12304 := by
  apply negative_check (lo := (34076177085985291601 / 50000000000000000000)) (hi := (68152354171970583203 / 100000000000000000000))
    (y := (-((70854837237288818069 / 100000000000000000000)))) (u := (3077240000083572203 / 6250000000000000000))
  · norm_num [world12304, agent12304, scalar12304, tp12304, tm12304, ep12304, em12304, dsL]
  · norm_num [world12304, agent12304, scalar12304, tp12304, tm12304, ep12304, em12304, dsL]
  · norm_num [world12304, agent12304, scalar12304, tp12304, tm12304, ep12304, em12304, dsL]
  · norm_num [world12304, agent12304, scalar12304, tp12304, tm12304, ep12304, em12304, dsL]
  · norm_num [world12304, agent12304, scalar12304, tp12304, tm12304, ep12304, em12304, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12304, agent12304, tp12304, tm12304, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12304, agent12304, tp12304, tm12304, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12304, agent12304, scalar12304, tp12304, tm12304, ep12304, em12304, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12304, agent12304, tp12304, tm12304, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12304, agent12304, scalar12304, tp12304, tm12304, ep12304, em12304, dsL]

theorem tails12304 :
    exp (-((12304:ℝ)*ep12304)) ≤ scalar12304.upperTail ∧
    exp (-((12304:ℝ)*em12304)) ≤ scalar12304.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12304:ℝ)) (by norm_num [ep12304]) ?_)
      (show bp12304^8 ≤ scalar12304.upperTail by norm_num [bp12304, scalar12304])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12304, bp12304, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12304:ℝ)) (by norm_num [em12304]) ?_)
      (show bm12304^8 ≤ scalar12304.lowerTail by norm_num [bm12304, scalar12304])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12304, bm12304, Finset.sum_range_succ, Nat.factorial]

theorem guards12304 :
    agent12304.root+dsL+scalar12304.worldRadius < √(1/100/aL) ∧
    2*(agent12304.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12304, agent12304, scalar12304, tp12304, tm12304, ep12304, em12304, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12304, agent12304, scalar12304, tp12304, tm12304, ep12304, em12304, dsL]

noncomputable def master12304 : MasterCertificate 12304 world12304 agent12304 :=
  master scalar12304 dsL tp12304 tm12304 ep12304 em12304
    (by norm_num [dsL]) (by norm_num [tp12304]) (by norm_num [tm12304])
    (by norm_num [ep12304]) (by norm_num [em12304])
    positive12304 negative12304 tails12304.1 tails12304.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12304.1 guards12304.2

theorem preserves12304 : master12304.toScalarCertificate = scalar12304 := rfl

noncomputable def tp12305 : ℝ := (2309403499 / 10000000000)
noncomputable def tm12305 : ℝ := (-((3036950373 / 5000000000)))
noncomputable def ep12305 : ℝ := (12710186063988761 / 25000000000000000000)
noncomputable def em12305 : ℝ := (994754620928073 / 2000000000000000000)
noncomputable def bp12305 : ℝ := (9149855400761397669 / 20000000000000000000)
noncomputable def bm12305 : ℝ := (46532068047333289489 / 100000000000000000000)

theorem positive12305 :
    Eplus aL (agent12305.root+dsL) scalar12305.worldRadius world12305.frame
      agent12305.frame tp12305 ≤ -ep12305 := by
  apply positive_check (eT := (1807733359013754009 / 1562500000000000000)) (y := (18607888276607212199 / 50000000000000000000)) (u := (145086185923144864053 / 100000000000000000000))
  · norm_num [world12305, agent12305, scalar12305, tp12305, tm12305, ep12305, em12305, dsL]
  · norm_num [world12305, agent12305, scalar12305, tp12305, tm12305, ep12305, em12305, dsL]
  · norm_num [world12305, agent12305, scalar12305, tp12305, tm12305, ep12305, em12305, dsL]
  · norm_num [world12305, agent12305, scalar12305, tp12305, tm12305, ep12305, em12305, dsL]
  · norm_num [world12305, agent12305, scalar12305, tp12305, tm12305, ep12305, em12305, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12305, agent12305, tp12305, tm12305, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12305, agent12305, scalar12305, tp12305, tm12305, ep12305, em12305, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12305, agent12305, tp12305, tm12305, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12305, agent12305, scalar12305, tp12305, tm12305, ep12305, em12305, dsL]

theorem negative12305 :
    Eminus aL (agent12305.root+dsL) scalar12305.worldRadius world12305.frame
      agent12305.frame tm12305 ≤ -em12305 := by
  apply negative_check (lo := (68152002465812734517 / 100000000000000000000)) (hi := (34076001232906367259 / 50000000000000000000))
    (y := (-((70854893212789329497 / 100000000000000000000)))) (u := (49235812441336996919 / 100000000000000000000))
  · norm_num [world12305, agent12305, scalar12305, tp12305, tm12305, ep12305, em12305, dsL]
  · norm_num [world12305, agent12305, scalar12305, tp12305, tm12305, ep12305, em12305, dsL]
  · norm_num [world12305, agent12305, scalar12305, tp12305, tm12305, ep12305, em12305, dsL]
  · norm_num [world12305, agent12305, scalar12305, tp12305, tm12305, ep12305, em12305, dsL]
  · norm_num [world12305, agent12305, scalar12305, tp12305, tm12305, ep12305, em12305, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12305, agent12305, tp12305, tm12305, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12305, agent12305, tp12305, tm12305, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12305, agent12305, scalar12305, tp12305, tm12305, ep12305, em12305, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12305, agent12305, tp12305, tm12305, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12305, agent12305, scalar12305, tp12305, tm12305, ep12305, em12305, dsL]

theorem tails12305 :
    exp (-((12305:ℝ)*ep12305)) ≤ scalar12305.upperTail ∧
    exp (-((12305:ℝ)*em12305)) ≤ scalar12305.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12305:ℝ)) (by norm_num [ep12305]) ?_)
      (show bp12305^8 ≤ scalar12305.upperTail by norm_num [bp12305, scalar12305])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12305, bp12305, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12305:ℝ)) (by norm_num [em12305]) ?_)
      (show bm12305^8 ≤ scalar12305.lowerTail by norm_num [bm12305, scalar12305])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12305, bm12305, Finset.sum_range_succ, Nat.factorial]

theorem guards12305 :
    agent12305.root+dsL+scalar12305.worldRadius < √(1/100/aL) ∧
    2*(agent12305.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12305, agent12305, scalar12305, tp12305, tm12305, ep12305, em12305, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12305, agent12305, scalar12305, tp12305, tm12305, ep12305, em12305, dsL]

noncomputable def master12305 : MasterCertificate 12305 world12305 agent12305 :=
  master scalar12305 dsL tp12305 tm12305 ep12305 em12305
    (by norm_num [dsL]) (by norm_num [tp12305]) (by norm_num [tm12305])
    (by norm_num [ep12305]) (by norm_num [em12305])
    positive12305 negative12305 tails12305.1 tails12305.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12305.1 guards12305.2

theorem preserves12305 : master12305.toScalarCertificate = scalar12305 := rfl

noncomputable def tp12306 : ℝ := (144344009 / 625000000)
noncomputable def tm12306 : ℝ := (-((6074124441 / 10000000000)))
noncomputable def ep12306 : ℝ := (25421894425975087 / 50000000000000000000)
noncomputable def em12306 : ℝ := (6217549250039631 / 12500000000000000000)
noncomputable def bp12306 : ℝ := (45744227274734527657 / 100000000000000000000)
noncomputable def bm12306 : ℝ := (46527269207526389659 / 100000000000000000000)

theorem positive12306 :
    Eplus aL (agent12306.root+dsL) scalar12306.worldRadius world12306.frame
      agent12306.frame tp12306 ≤ -ep12306 := by
  apply positive_check (eT := (57847637748959937613 / 50000000000000000000)) (y := (37216603088724971013 / 100000000000000000000)) (u := (18135923139618536377 / 12500000000000000000))
  · norm_num [world12306, agent12306, scalar12306, tp12306, tm12306, ep12306, em12306, dsL]
  · norm_num [world12306, agent12306, scalar12306, tp12306, tm12306, ep12306, em12306, dsL]
  · norm_num [world12306, agent12306, scalar12306, tp12306, tm12306, ep12306, em12306, dsL]
  · norm_num [world12306, agent12306, scalar12306, tp12306, tm12306, ep12306, em12306, dsL]
  · norm_num [world12306, agent12306, scalar12306, tp12306, tm12306, ep12306, em12306, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12306, agent12306, tp12306, tm12306, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12306, agent12306, scalar12306, tp12306, tm12306, ep12306, em12306, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12306, agent12306, tp12306, tm12306, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12306, agent12306, scalar12306, tp12306, tm12306, ep12306, em12306, dsL]

theorem negative12306 :
    Eminus aL (agent12306.root+dsL) scalar12306.worldRadius world12306.frame
      agent12306.frame tm12306 ≤ -em12306 := by
  apply negative_check (lo := (68151651328462319207 / 100000000000000000000)) (hi := (8518956416057789901 / 12500000000000000000))
    (y := (-((70854948202161345209 / 100000000000000000000)))) (u := (49235785366880372631 / 100000000000000000000))
  · norm_num [world12306, agent12306, scalar12306, tp12306, tm12306, ep12306, em12306, dsL]
  · norm_num [world12306, agent12306, scalar12306, tp12306, tm12306, ep12306, em12306, dsL]
  · norm_num [world12306, agent12306, scalar12306, tp12306, tm12306, ep12306, em12306, dsL]
  · norm_num [world12306, agent12306, scalar12306, tp12306, tm12306, ep12306, em12306, dsL]
  · norm_num [world12306, agent12306, scalar12306, tp12306, tm12306, ep12306, em12306, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12306, agent12306, tp12306, tm12306, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12306, agent12306, tp12306, tm12306, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12306, agent12306, scalar12306, tp12306, tm12306, ep12306, em12306, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12306, agent12306, tp12306, tm12306, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12306, agent12306, scalar12306, tp12306, tm12306, ep12306, em12306, dsL]

theorem tails12306 :
    exp (-((12306:ℝ)*ep12306)) ≤ scalar12306.upperTail ∧
    exp (-((12306:ℝ)*em12306)) ≤ scalar12306.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12306:ℝ)) (by norm_num [ep12306]) ?_)
      (show bp12306^8 ≤ scalar12306.upperTail by norm_num [bp12306, scalar12306])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12306, bp12306, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12306:ℝ)) (by norm_num [em12306]) ?_)
      (show bm12306^8 ≤ scalar12306.lowerTail by norm_num [bm12306, scalar12306])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12306, bm12306, Finset.sum_range_succ, Nat.factorial]

theorem guards12306 :
    agent12306.root+dsL+scalar12306.worldRadius < √(1/100/aL) ∧
    2*(agent12306.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12306, agent12306, scalar12306, tp12306, tm12306, ep12306, em12306, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12306, agent12306, scalar12306, tp12306, tm12306, ep12306, em12306, dsL]

noncomputable def master12306 : MasterCertificate 12306 world12306 agent12306 :=
  master scalar12306 dsL tp12306 tm12306 ep12306 em12306
    (by norm_num [dsL]) (by norm_num [tp12306]) (by norm_num [tm12306])
    (by norm_num [ep12306]) (by norm_num [em12306])
    positive12306 negative12306 tails12306.1 tails12306.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12306.1 guards12306.2

theorem preserves12306 : master12306.toScalarCertificate = scalar12306 := rfl

noncomputable def tp12307 : ℝ := (288700591 / 1250000000)
noncomputable def tm12307 : ℝ := (-((3037173999 / 5000000000)))
noncomputable def ep12307 : ℝ := (25423416014297057 / 50000000000000000000)
noncomputable def em12307 : ℝ := (49743055637301261 / 100000000000000000000)
noncomputable def bp12307 : ℝ := (22869589376805927289 / 50000000000000000000)
noncomputable def bm12307 : ℝ := (2907654468463606683 / 6250000000000000000)

theorem positive12307 :
    Eplus aL (agent12307.root+dsL) scalar12307.worldRadius world12307.frame
      agent12307.frame tp12307 ≤ -ep12307 := by
  apply positive_check (eT := (115695615605891788137 / 100000000000000000000)) (y := (1860871455650553309 / 5000000000000000000)) (u := (29017716715787040831 / 20000000000000000000))
  · norm_num [world12307, agent12307, scalar12307, tp12307, tm12307, ep12307, em12307, dsL]
  · norm_num [world12307, agent12307, scalar12307, tp12307, tm12307, ep12307, em12307, dsL]
  · norm_num [world12307, agent12307, scalar12307, tp12307, tm12307, ep12307, em12307, dsL]
  · norm_num [world12307, agent12307, scalar12307, tp12307, tm12307, ep12307, em12307, dsL]
  · norm_num [world12307, agent12307, scalar12307, tp12307, tm12307, ep12307, em12307, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12307, agent12307, tp12307, tm12307, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12307, agent12307, scalar12307, tp12307, tm12307, ep12307, em12307, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12307, agent12307, tp12307, tm12307, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12307, agent12307, scalar12307, tp12307, tm12307, ep12307, em12307, dsL]

theorem negative12307 :
    Eminus aL (agent12307.root+dsL) scalar12307.worldRadius world12307.frame
      agent12307.frame tm12307 ≤ -em12307 := by
  apply negative_check (lo := (34075650364829320031 / 50000000000000000000)) (hi := (68151300729658640063 / 100000000000000000000))
    (y := (-((70855003090167209061 / 100000000000000000000)))) (u := (49235758342347029959 / 100000000000000000000))
  · norm_num [world12307, agent12307, scalar12307, tp12307, tm12307, ep12307, em12307, dsL]
  · norm_num [world12307, agent12307, scalar12307, tp12307, tm12307, ep12307, em12307, dsL]
  · norm_num [world12307, agent12307, scalar12307, tp12307, tm12307, ep12307, em12307, dsL]
  · norm_num [world12307, agent12307, scalar12307, tp12307, tm12307, ep12307, em12307, dsL]
  · norm_num [world12307, agent12307, scalar12307, tp12307, tm12307, ep12307, em12307, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12307, agent12307, tp12307, tm12307, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12307, agent12307, tp12307, tm12307, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12307, agent12307, scalar12307, tp12307, tm12307, ep12307, em12307, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12307, agent12307, tp12307, tm12307, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12307, agent12307, scalar12307, tp12307, tm12307, ep12307, em12307, dsL]

theorem tails12307 :
    exp (-((12307:ℝ)*ep12307)) ≤ scalar12307.upperTail ∧
    exp (-((12307:ℝ)*em12307)) ≤ scalar12307.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12307:ℝ)) (by norm_num [ep12307]) ?_)
      (show bp12307^8 ≤ scalar12307.upperTail by norm_num [bp12307, scalar12307])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12307, bp12307, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12307:ℝ)) (by norm_num [em12307]) ?_)
      (show bm12307^8 ≤ scalar12307.lowerTail by norm_num [bm12307, scalar12307])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12307, bm12307, Finset.sum_range_succ, Nat.factorial]

theorem guards12307 :
    agent12307.root+dsL+scalar12307.worldRadius < √(1/100/aL) ∧
    2*(agent12307.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12307, agent12307, scalar12307, tp12307, tm12307, ep12307, em12307, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12307, agent12307, scalar12307, tp12307, tm12307, ep12307, em12307, dsL]

noncomputable def master12307 : MasterCertificate 12307 world12307 agent12307 :=
  master scalar12307 dsL tp12307 tm12307 ep12307 em12307
    (by norm_num [dsL]) (by norm_num [tp12307]) (by norm_num [tm12307])
    (by norm_num [ep12307]) (by norm_num [em12307])
    positive12307 negative12307 tails12307.1 tails12307.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12307.1 guards12307.2

theorem preserves12307 : master12307.toScalarCertificate = scalar12307 := rfl

noncomputable def tp12308 : ℝ := (2309705281 / 10000000000)
noncomputable def tm12308 : ℝ := (-((6074571443 / 10000000000)))
noncomputable def ep12308 : ℝ := (50849874274504249 / 100000000000000000000)
noncomputable def em12308 : ℝ := (49745716396259437 / 100000000000000000000)
noncomputable def bp12308 : ℝ := (22867065548302348613 / 50000000000000000000)
noncomputable def bm12308 : ℝ := (5814709324609802021 / 12500000000000000000)

theorem positive12308 :
    Eplus aL (agent12308.root+dsL) scalar12308.worldRadius world12308.frame
      agent12308.frame tp12308 ≤ -ep12308 := by
  apply positive_check (eT := (115695955519844256419 / 100000000000000000000)) (y := (9304563723934982167 / 25000000000000000000)) (u := (145089781700346883253 / 100000000000000000000))
  · norm_num [world12308, agent12308, scalar12308, tp12308, tm12308, ep12308, em12308, dsL]
  · norm_num [world12308, agent12308, scalar12308, tp12308, tm12308, ep12308, em12308, dsL]
  · norm_num [world12308, agent12308, scalar12308, tp12308, tm12308, ep12308, em12308, dsL]
  · norm_num [world12308, agent12308, scalar12308, tp12308, tm12308, ep12308, em12308, dsL]
  · norm_num [world12308, agent12308, scalar12308, tp12308, tm12308, ep12308, em12308, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12308, agent12308, tp12308, tm12308, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12308, agent12308, scalar12308, tp12308, tm12308, ep12308, em12308, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12308, agent12308, tp12308, tm12308, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12308, agent12308, scalar12308, tp12308, tm12308, ep12308, em12308, dsL]

theorem negative12308 :
    Eminus aL (agent12308.root+dsL) scalar12308.worldRadius world12308.frame
      agent12308.frame tm12308 ≤ -em12308 := by
  apply negative_check (lo := (13630190111523102389 / 20000000000000000000)) (hi := (34075475278807755973 / 50000000000000000000))
    (y := (-((70855057434516112929 / 100000000000000000000)))) (u := (24617865792751000673 / 50000000000000000000))
  · norm_num [world12308, agent12308, scalar12308, tp12308, tm12308, ep12308, em12308, dsL]
  · norm_num [world12308, agent12308, scalar12308, tp12308, tm12308, ep12308, em12308, dsL]
  · norm_num [world12308, agent12308, scalar12308, tp12308, tm12308, ep12308, em12308, dsL]
  · norm_num [world12308, agent12308, scalar12308, tp12308, tm12308, ep12308, em12308, dsL]
  · norm_num [world12308, agent12308, scalar12308, tp12308, tm12308, ep12308, em12308, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12308, agent12308, tp12308, tm12308, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12308, agent12308, tp12308, tm12308, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12308, agent12308, scalar12308, tp12308, tm12308, ep12308, em12308, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12308, agent12308, tp12308, tm12308, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12308, agent12308, scalar12308, tp12308, tm12308, ep12308, em12308, dsL]

theorem tails12308 :
    exp (-((12308:ℝ)*ep12308)) ≤ scalar12308.upperTail ∧
    exp (-((12308:ℝ)*em12308)) ≤ scalar12308.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12308:ℝ)) (by norm_num [ep12308]) ?_)
      (show bp12308^8 ≤ scalar12308.upperTail by norm_num [bp12308, scalar12308])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12308, bp12308, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12308:ℝ)) (by norm_num [em12308]) ?_)
      (show bm12308^8 ≤ scalar12308.lowerTail by norm_num [bm12308, scalar12308])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12308, bm12308, Finset.sum_range_succ, Nat.factorial]

theorem guards12308 :
    agent12308.root+dsL+scalar12308.worldRadius < √(1/100/aL) ∧
    2*(agent12308.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12308, agent12308, scalar12308, tp12308, tm12308, ep12308, em12308, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12308, agent12308, scalar12308, tp12308, tm12308, ep12308, em12308, dsL]

noncomputable def master12308 : MasterCertificate 12308 world12308 agent12308 :=
  master scalar12308 dsL tp12308 tm12308 ep12308 em12308
    (by norm_num [dsL]) (by norm_num [tp12308]) (by norm_num [tm12308])
    (by norm_num [ep12308]) (by norm_num [em12308])
    positive12308 negative12308 tails12308.1 tails12308.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12308.1 guards12308.2

theorem preserves12308 : master12308.toScalarCertificate = scalar12308 := rfl

noncomputable def tp12309 : ℝ := (72181431 / 312500000)
noncomputable def tm12309 : ℝ := (-((6074794741 / 10000000000)))
noncomputable def ep12309 : ℝ := (25426457222941253 / 50000000000000000000)
noncomputable def em12309 : ℝ := (6218546908122629 / 12500000000000000000)
noncomputable def bp12309 : ℝ := (5716135638560609837 / 12500000000000000000)
noncomputable def bm12309 : ℝ := (46512879236309388909 / 100000000000000000000)

theorem positive12309 :
    Eplus aL (agent12309.root+dsL) scalar12309.worldRadius world12309.frame
      agent12309.frame tp12309 ≤ -ep12309 := by
  apply positive_check (eT := (115696295159494583929 / 100000000000000000000)) (y := (37219080292391002461 / 100000000000000000000)) (u := (145090979271488437443 / 100000000000000000000))
  · norm_num [world12309, agent12309, scalar12309, tp12309, tm12309, ep12309, em12309, dsL]
  · norm_num [world12309, agent12309, scalar12309, tp12309, tm12309, ep12309, em12309, dsL]
  · norm_num [world12309, agent12309, scalar12309, tp12309, tm12309, ep12309, em12309, dsL]
  · norm_num [world12309, agent12309, scalar12309, tp12309, tm12309, ep12309, em12309, dsL]
  · norm_num [world12309, agent12309, scalar12309, tp12309, tm12309, ep12309, em12309, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12309, agent12309, tp12309, tm12309, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12309, agent12309, scalar12309, tp12309, tm12309, ep12309, em12309, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12309, agent12309, tp12309, tm12309, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12309, agent12309, scalar12309, tp12309, tm12309, ep12309, em12309, dsL]

theorem negative12309 :
    Eminus aL (agent12309.root+dsL) scalar12309.worldRadius world12309.frame
      agent12309.frame tm12309 ≤ -em12309 := by
  apply negative_check (lo := (68150600962801842531 / 100000000000000000000)) (hi := (17037650240700460633 / 25000000000000000000))
    (y := (-((35427555383133859211 / 50000000000000000000)))) (u := (49235705327230933017 / 100000000000000000000))
  · norm_num [world12309, agent12309, scalar12309, tp12309, tm12309, ep12309, em12309, dsL]
  · norm_num [world12309, agent12309, scalar12309, tp12309, tm12309, ep12309, em12309, dsL]
  · norm_num [world12309, agent12309, scalar12309, tp12309, tm12309, ep12309, em12309, dsL]
  · norm_num [world12309, agent12309, scalar12309, tp12309, tm12309, ep12309, em12309, dsL]
  · norm_num [world12309, agent12309, scalar12309, tp12309, tm12309, ep12309, em12309, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12309, agent12309, tp12309, tm12309, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12309, agent12309, tp12309, tm12309, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12309, agent12309, scalar12309, tp12309, tm12309, ep12309, em12309, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12309, agent12309, tp12309, tm12309, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12309, agent12309, scalar12309, tp12309, tm12309, ep12309, em12309, dsL]

theorem tails12309 :
    exp (-((12309:ℝ)*ep12309)) ≤ scalar12309.upperTail ∧
    exp (-((12309:ℝ)*em12309)) ≤ scalar12309.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12309:ℝ)) (by norm_num [ep12309]) ?_)
      (show bp12309^8 ≤ scalar12309.upperTail by norm_num [bp12309, scalar12309])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12309, bp12309, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12309:ℝ)) (by norm_num [em12309]) ?_)
      (show bm12309^8 ≤ scalar12309.lowerTail by norm_num [bm12309, scalar12309])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12309, bm12309, Finset.sum_range_succ, Nat.factorial]

theorem guards12309 :
    agent12309.root+dsL+scalar12309.worldRadius < √(1/100/aL) ∧
    2*(agent12309.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12309, agent12309, scalar12309, tp12309, tm12309, ep12309, em12309, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12309, agent12309, scalar12309, tp12309, tm12309, ep12309, em12309, dsL]

noncomputable def master12309 : MasterCertificate 12309 world12309 agent12309 :=
  master scalar12309 dsL tp12309 tm12309 ep12309 em12309
    (by norm_num [dsL]) (by norm_num [tp12309]) (by norm_num [tm12309])
    (by norm_num [ep12309]) (by norm_num [em12309])
    positive12309 negative12309 tails12309.1 tails12309.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12309.1 guards12309.2

theorem preserves12309 : master12309.toScalarCertificate = scalar12309 := rfl

noncomputable def tp12310 : ℝ := (1154953119 / 5000000000)
noncomputable def tm12310 : ℝ := (-((6075018111 / 10000000000)))
noncomputable def ep12310 : ℝ := (50855953541655927 / 100000000000000000000)
noncomputable def em12310 : ℝ := (1243775827778999 / 2500000000000000000)
noncomputable def bp12310 : ℝ := (45724040086354854283 / 100000000000000000000)
noncomputable def bm12310 : ℝ := (2325404239635370411 / 5000000000000000000)

theorem positive12310 :
    Eplus aL (agent12310.root+dsL) scalar12310.worldRadius world12310.frame
      agent12310.frame tp12310 ≤ -ep12310 := by
  apply positive_check (eT := (28924158589219972527 / 25000000000000000000)) (y := (37219905109241120649 / 100000000000000000000)) (u := (145092176011268919063 / 100000000000000000000))
  · norm_num [world12310, agent12310, scalar12310, tp12310, tm12310, ep12310, em12310, dsL]
  · norm_num [world12310, agent12310, scalar12310, tp12310, tm12310, ep12310, em12310, dsL]
  · norm_num [world12310, agent12310, scalar12310, tp12310, tm12310, ep12310, em12310, dsL]
  · norm_num [world12310, agent12310, scalar12310, tp12310, tm12310, ep12310, em12310, dsL]
  · norm_num [world12310, agent12310, scalar12310, tp12310, tm12310, ep12310, em12310, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12310, agent12310, tp12310, tm12310, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12310, agent12310, scalar12310, tp12310, tm12310, ep12310, em12310, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12310, agent12310, tp12310, tm12310, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12310, agent12310, scalar12310, tp12310, tm12310, ep12310, em12310, dsL]

theorem negative12310 :
    Eminus aL (agent12310.root+dsL) scalar12310.worldRadius world12310.frame
      agent12310.frame tm12310 ≤ -em12310 := by
  apply negative_check (lo := (68150251003134074133 / 100000000000000000000)) (hi := (34075125501567037067 / 50000000000000000000))
    (y := (-((70855166009159502063 / 100000000000000000000)))) (u := (49235678128011033001 / 100000000000000000000))
  · norm_num [world12310, agent12310, scalar12310, tp12310, tm12310, ep12310, em12310, dsL]
  · norm_num [world12310, agent12310, scalar12310, tp12310, tm12310, ep12310, em12310, dsL]
  · norm_num [world12310, agent12310, scalar12310, tp12310, tm12310, ep12310, em12310, dsL]
  · norm_num [world12310, agent12310, scalar12310, tp12310, tm12310, ep12310, em12310, dsL]
  · norm_num [world12310, agent12310, scalar12310, tp12310, tm12310, ep12310, em12310, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12310, agent12310, tp12310, tm12310, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12310, agent12310, tp12310, tm12310, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12310, agent12310, scalar12310, tp12310, tm12310, ep12310, em12310, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12310, agent12310, tp12310, tm12310, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12310, agent12310, scalar12310, tp12310, tm12310, ep12310, em12310, dsL]

theorem tails12310 :
    exp (-((12310:ℝ)*ep12310)) ≤ scalar12310.upperTail ∧
    exp (-((12310:ℝ)*em12310)) ≤ scalar12310.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12310:ℝ)) (by norm_num [ep12310]) ?_)
      (show bp12310^8 ≤ scalar12310.upperTail by norm_num [bp12310, scalar12310])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12310, bp12310, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12310:ℝ)) (by norm_num [em12310]) ?_)
      (show bm12310^8 ≤ scalar12310.lowerTail by norm_num [bm12310, scalar12310])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12310, bm12310, Finset.sum_range_succ, Nat.factorial]

theorem guards12310 :
    agent12310.root+dsL+scalar12310.worldRadius < √(1/100/aL) ∧
    2*(agent12310.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12310, agent12310, scalar12310, tp12310, tm12310, ep12310, em12310, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12310, agent12310, scalar12310, tp12310, tm12310, ep12310, em12310, dsL]

noncomputable def master12310 : MasterCertificate 12310 world12310 agent12310 :=
  master scalar12310 dsL tp12310 tm12310 ep12310 em12310
    (by norm_num [dsL]) (by norm_num [tp12310]) (by norm_num [tm12310])
    (by norm_num [ep12310]) (by norm_num [em12310])
    positive12310 negative12310 tails12310.1 tails12310.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12310.1 guards12310.2

theorem preserves12310 : master12310.toScalarCertificate = scalar12310 := rfl

noncomputable def tp12311 : ℝ := (2310006603 / 10000000000)
noncomputable def tm12311 : ℝ := (-((189851289 / 312500000)))
noncomputable def ep12311 : ℝ := (50858990775831331 / 100000000000000000000)
noncomputable def em12311 : ℝ := (49753689216359413 / 100000000000000000000)
noncomputable def bp12311 : ℝ := (45718996583194106133 / 100000000000000000000)
noncomputable def bm12311 : ℝ := (1453227868131321829 / 3125000000000000000)

theorem positive12311 :
    Eplus aL (agent12311.root+dsL) scalar12311.worldRadius world12311.frame
      agent12311.frame tp12311 ≤ -ep12311 := by
  apply positive_check (eT := (23139394599028535463 / 20000000000000000000)) (y := (7444145782885342019 / 20000000000000000000)) (u := (90683357058163859 / 62500000000000000))
  · norm_num [world12311, agent12311, scalar12311, tp12311, tm12311, ep12311, em12311, dsL]
  · norm_num [world12311, agent12311, scalar12311, tp12311, tm12311, ep12311, em12311, dsL]
  · norm_num [world12311, agent12311, scalar12311, tp12311, tm12311, ep12311, em12311, dsL]
  · norm_num [world12311, agent12311, scalar12311, tp12311, tm12311, ep12311, em12311, dsL]
  · norm_num [world12311, agent12311, scalar12311, tp12311, tm12311, ep12311, em12311, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12311, agent12311, tp12311, tm12311, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12311, agent12311, scalar12311, tp12311, tm12311, ep12311, em12311, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12311, agent12311, tp12311, tm12311, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12311, agent12311, scalar12311, tp12311, tm12311, ep12311, em12311, dsL]

theorem negative12311 :
    Eminus aL (agent12311.root+dsL) scalar12311.worldRadius world12311.frame
      agent12311.frame tm12311 ≤ -em12311 := by
  apply negative_check (lo := (68149901990675802279 / 100000000000000000000)) (hi := (1703747549766895057 / 2500000000000000000))
    (y := (-((70855219295607344561 / 100000000000000000000)))) (u := (24617825946037038759 / 50000000000000000000))
  · norm_num [world12311, agent12311, scalar12311, tp12311, tm12311, ep12311, em12311, dsL]
  · norm_num [world12311, agent12311, scalar12311, tp12311, tm12311, ep12311, em12311, dsL]
  · norm_num [world12311, agent12311, scalar12311, tp12311, tm12311, ep12311, em12311, dsL]
  · norm_num [world12311, agent12311, scalar12311, tp12311, tm12311, ep12311, em12311, dsL]
  · norm_num [world12311, agent12311, scalar12311, tp12311, tm12311, ep12311, em12311, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12311, agent12311, tp12311, tm12311, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12311, agent12311, tp12311, tm12311, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12311, agent12311, scalar12311, tp12311, tm12311, ep12311, em12311, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12311, agent12311, tp12311, tm12311, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12311, agent12311, scalar12311, tp12311, tm12311, ep12311, em12311, dsL]

theorem tails12311 :
    exp (-((12311:ℝ)*ep12311)) ≤ scalar12311.upperTail ∧
    exp (-((12311:ℝ)*em12311)) ≤ scalar12311.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12311:ℝ)) (by norm_num [ep12311]) ?_)
      (show bp12311^8 ≤ scalar12311.upperTail by norm_num [bp12311, scalar12311])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12311, bp12311, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12311:ℝ)) (by norm_num [em12311]) ?_)
      (show bm12311^8 ≤ scalar12311.lowerTail by norm_num [bm12311, scalar12311])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12311, bm12311, Finset.sum_range_succ, Nat.factorial]

theorem guards12311 :
    agent12311.root+dsL+scalar12311.worldRadius < √(1/100/aL) ∧
    2*(agent12311.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12311, agent12311, scalar12311, tp12311, tm12311, ep12311, em12311, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12311, agent12311, scalar12311, tp12311, tm12311, ep12311, em12311, dsL]

noncomputable def master12311 : MasterCertificate 12311 world12311 agent12311 :=
  master scalar12311 dsL tp12311 tm12311 ep12311 em12311
    (by norm_num [dsL]) (by norm_num [tp12311]) (by norm_num [tm12311])
    (by norm_num [ep12311]) (by norm_num [em12311])
    positive12311 negative12311 tails12311.1 tails12311.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12311.1 guards12311.2

theorem preserves12311 : master12311.toScalarCertificate = scalar12311 := rfl

noncomputable def tp12312 : ℝ := (1155053501 / 5000000000)
noncomputable def tm12312 : ℝ := (-((189858257 / 312500000)))
noncomputable def ep12312 : ℝ := (25431013365307181 / 50000000000000000000)
noncomputable def em12312 : ℝ := (49756344151474713 / 100000000000000000000)
noncomputable def bp12312 : ℝ := (22856977094669121711 / 50000000000000000000)
noncomputable def bm12312 : ℝ := (23249249895108767369 / 50000000000000000000)

theorem positive12312 :
    Eplus aL (agent12312.root+dsL) scalar12312.worldRadius world12312.frame
      agent12312.frame tp12312 ≤ -ep12312 := by
  apply positive_check (eT := (14462163989267453579 / 12500000000000000000)) (y := (18610776851523710511 / 50000000000000000000)) (u := (145094568011613197863 / 100000000000000000000))
  · norm_num [world12312, agent12312, scalar12312, tp12312, tm12312, ep12312, em12312, dsL]
  · norm_num [world12312, agent12312, scalar12312, tp12312, tm12312, ep12312, em12312, dsL]
  · norm_num [world12312, agent12312, scalar12312, tp12312, tm12312, ep12312, em12312, dsL]
  · norm_num [world12312, agent12312, scalar12312, tp12312, tm12312, ep12312, em12312, dsL]
  · norm_num [world12312, agent12312, scalar12312, tp12312, tm12312, ep12312, em12312, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12312, agent12312, tp12312, tm12312, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12312, agent12312, scalar12312, tp12312, tm12312, ep12312, em12312, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12312, agent12312, tp12312, tm12312, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12312, agent12312, scalar12312, tp12312, tm12312, ep12312, em12312, dsL]

theorem negative12312 :
    Eminus aL (agent12312.root+dsL) scalar12312.worldRadius world12312.frame
      agent12312.frame tm12312 ≤ -em12312 := by
  apply negative_check (lo := (13629910723117744123 / 20000000000000000000)) (hi := (8518694201948590077 / 12500000000000000000))
    (y := (-((8856908996787328627 / 12500000000000000000)))) (u := (49235625955383846959 / 100000000000000000000))
  · norm_num [world12312, agent12312, scalar12312, tp12312, tm12312, ep12312, em12312, dsL]
  · norm_num [world12312, agent12312, scalar12312, tp12312, tm12312, ep12312, em12312, dsL]
  · norm_num [world12312, agent12312, scalar12312, tp12312, tm12312, ep12312, em12312, dsL]
  · norm_num [world12312, agent12312, scalar12312, tp12312, tm12312, ep12312, em12312, dsL]
  · norm_num [world12312, agent12312, scalar12312, tp12312, tm12312, ep12312, em12312, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12312, agent12312, tp12312, tm12312, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12312, agent12312, tp12312, tm12312, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12312, agent12312, scalar12312, tp12312, tm12312, ep12312, em12312, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12312, agent12312, tp12312, tm12312, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12312, agent12312, scalar12312, tp12312, tm12312, ep12312, em12312, dsL]

theorem tails12312 :
    exp (-((12312:ℝ)*ep12312)) ≤ scalar12312.upperTail ∧
    exp (-((12312:ℝ)*em12312)) ≤ scalar12312.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12312:ℝ)) (by norm_num [ep12312]) ?_)
      (show bp12312^8 ≤ scalar12312.upperTail by norm_num [bp12312, scalar12312])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12312, bp12312, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12312:ℝ)) (by norm_num [em12312]) ?_)
      (show bm12312^8 ≤ scalar12312.lowerTail by norm_num [bm12312, scalar12312])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12312, bm12312, Finset.sum_range_succ, Nat.factorial]

theorem guards12312 :
    agent12312.root+dsL+scalar12312.worldRadius < √(1/100/aL) ∧
    2*(agent12312.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12312, agent12312, scalar12312, tp12312, tm12312, ep12312, em12312, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12312, agent12312, scalar12312, tp12312, tm12312, ep12312, em12312, dsL]

noncomputable def master12312 : MasterCertificate 12312 world12312 agent12312 :=
  master scalar12312 dsL tp12312 tm12312 ep12312 em12312
    (by norm_num [dsL]) (by norm_num [tp12312]) (by norm_num [tm12312])
    (by norm_num [ep12312]) (by norm_num [em12312])
    positive12312 negative12312 tails12312.1 tails12312.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12312.1 guards12312.2

theorem preserves12312 : master12312.toScalarCertificate = scalar12312 := rfl

noncomputable def tp12313 : ℝ := (577551843 / 2500000000)
noncomputable def tm12313 : ℝ := (-((759460901 / 1250000000)))
noncomputable def ep12313 : ℝ := (6358132720488277 / 12500000000000000000)
noncomputable def em12313 : ℝ := (49758998216668233 / 100000000000000000000)
noncomputable def bp12313 : ℝ := (22854456326486273717 / 50000000000000000000)
noncomputable def bm12313 : ℝ := (2905856787996733457 / 6250000000000000000)

theorem positive12313 :
    Eplus aL (agent12313.root+dsL) scalar12313.worldRadius world12313.frame
      agent12313.frame tp12313 ≤ -ep12313 := by
  apply positive_check (eT := (7231103165861937593 / 6250000000000000000)) (y := (37222378284107700013 / 100000000000000000000)) (u := (145095764438873264759 / 100000000000000000000))
  · norm_num [world12313, agent12313, scalar12313, tp12313, tm12313, ep12313, em12313, dsL]
  · norm_num [world12313, agent12313, scalar12313, tp12313, tm12313, ep12313, em12313, dsL]
  · norm_num [world12313, agent12313, scalar12313, tp12313, tm12313, ep12313, em12313, dsL]
  · norm_num [world12313, agent12313, scalar12313, tp12313, tm12313, ep12313, em12313, dsL]
  · norm_num [world12313, agent12313, scalar12313, tp12313, tm12313, ep12313, em12313, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12313, agent12313, tp12313, tm12313, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12313, agent12313, scalar12313, tp12313, tm12313, ep12313, em12313, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12313, agent12313, tp12313, tm12313, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12313, agent12313, scalar12313, tp12313, tm12313, ep12313, em12313, dsL]

theorem negative12313 :
    Eminus aL (agent12313.root+dsL) scalar12313.worldRadius world12313.frame
      agent12313.frame tm12313 ≤ -em12313 := by
  apply negative_check (lo := (34074602575464320937 / 50000000000000000000)) (hi := (109038728241485827 / 160000000000000000))
    (y := (-((70855325256468732731 / 100000000000000000000)))) (u := (49235599721580862753 / 100000000000000000000))
  · norm_num [world12313, agent12313, scalar12313, tp12313, tm12313, ep12313, em12313, dsL]
  · norm_num [world12313, agent12313, scalar12313, tp12313, tm12313, ep12313, em12313, dsL]
  · norm_num [world12313, agent12313, scalar12313, tp12313, tm12313, ep12313, em12313, dsL]
  · norm_num [world12313, agent12313, scalar12313, tp12313, tm12313, ep12313, em12313, dsL]
  · norm_num [world12313, agent12313, scalar12313, tp12313, tm12313, ep12313, em12313, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12313, agent12313, tp12313, tm12313, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12313, agent12313, tp12313, tm12313, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12313, agent12313, scalar12313, tp12313, tm12313, ep12313, em12313, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12313, agent12313, tp12313, tm12313, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12313, agent12313, scalar12313, tp12313, tm12313, ep12313, em12313, dsL]

theorem tails12313 :
    exp (-((12313:ℝ)*ep12313)) ≤ scalar12313.upperTail ∧
    exp (-((12313:ℝ)*em12313)) ≤ scalar12313.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12313:ℝ)) (by norm_num [ep12313]) ?_)
      (show bp12313^8 ≤ scalar12313.upperTail by norm_num [bp12313, scalar12313])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12313, bp12313, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12313:ℝ)) (by norm_num [em12313]) ?_)
      (show bm12313^8 ≤ scalar12313.lowerTail by norm_num [bm12313, scalar12313])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12313, bm12313, Finset.sum_range_succ, Nat.factorial]

theorem guards12313 :
    agent12313.root+dsL+scalar12313.worldRadius < √(1/100/aL) ∧
    2*(agent12313.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12313, agent12313, scalar12313, tp12313, tm12313, ep12313, em12313, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12313, agent12313, scalar12313, tp12313, tm12313, ep12313, em12313, dsL]

noncomputable def master12313 : MasterCertificate 12313 world12313 agent12313 :=
  master scalar12313 dsL tp12313 tm12313 ep12313 em12313
    (by norm_num [dsL]) (by norm_num [tp12313]) (by norm_num [tm12313])
    (by norm_num [ep12313]) (by norm_num [em12313])
    positive12313 negative12313 tails12313.1 tails12313.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12313.1 guards12313.2

theorem preserves12313 : master12313.toScalarCertificate = scalar12313 := rfl

noncomputable def tp12314 : ℝ := (2310307649 / 10000000000)
noncomputable def tm12314 : ℝ := (-((1518977511 / 2500000000)))
noncomputable def ep12314 : ℝ := (25434047526170527 / 50000000000000000000)
noncomputable def em12314 : ℝ := (24880825340146527 / 50000000000000000000)
noncomputable def bp12314 : ℝ := (45703872553329187407 / 100000000000000000000)
noncomputable def bm12314 : ℝ := (9297783751389806631 / 20000000000000000000)

theorem positive12314 :
    Eplus aL (agent12314.root+dsL) scalar12314.worldRadius world12314.frame
      agent12314.frame tp12314 ≤ -ep12314 := by
  apply positive_check (eT := (57848994373362876761 / 50000000000000000000)) (y := (37223201697297445929 / 100000000000000000000)) (u := (145096959181454244353 / 100000000000000000000))
  · norm_num [world12314, agent12314, scalar12314, tp12314, tm12314, ep12314, em12314, dsL]
  · norm_num [world12314, agent12314, scalar12314, tp12314, tm12314, ep12314, em12314, dsL]
  · norm_num [world12314, agent12314, scalar12314, tp12314, tm12314, ep12314, em12314, dsL]
  · norm_num [world12314, agent12314, scalar12314, tp12314, tm12314, ep12314, em12314, dsL]
  · norm_num [world12314, agent12314, scalar12314, tp12314, tm12314, ep12314, em12314, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12314, agent12314, tp12314, tm12314, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12314, agent12314, scalar12314, tp12314, tm12314, ep12314, em12314, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12314, agent12314, tp12314, tm12314, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12314, agent12314, scalar12314, tp12314, tm12314, ep12314, em12314, dsL]

theorem negative12314 :
    Eminus aL (agent12314.root+dsL) scalar12314.worldRadius world12314.frame
      agent12314.frame tm12314 ≤ -em12314 := by
  apply negative_check (lo := (68148857267751319589 / 100000000000000000000)) (hi := (6814885726775131959 / 10000000000000000000))
    (y := (-((4428461120489608801 / 6250000000000000000)))) (u := (49235573788525249127 / 100000000000000000000))
  · norm_num [world12314, agent12314, scalar12314, tp12314, tm12314, ep12314, em12314, dsL]
  · norm_num [world12314, agent12314, scalar12314, tp12314, tm12314, ep12314, em12314, dsL]
  · norm_num [world12314, agent12314, scalar12314, tp12314, tm12314, ep12314, em12314, dsL]
  · norm_num [world12314, agent12314, scalar12314, tp12314, tm12314, ep12314, em12314, dsL]
  · norm_num [world12314, agent12314, scalar12314, tp12314, tm12314, ep12314, em12314, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12314, agent12314, tp12314, tm12314, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12314, agent12314, tp12314, tm12314, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12314, agent12314, scalar12314, tp12314, tm12314, ep12314, em12314, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12314, agent12314, tp12314, tm12314, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12314, agent12314, scalar12314, tp12314, tm12314, ep12314, em12314, dsL]

theorem tails12314 :
    exp (-((12314:ℝ)*ep12314)) ≤ scalar12314.upperTail ∧
    exp (-((12314:ℝ)*em12314)) ≤ scalar12314.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12314:ℝ)) (by norm_num [ep12314]) ?_)
      (show bp12314^8 ≤ scalar12314.upperTail by norm_num [bp12314, scalar12314])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12314, bp12314, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12314:ℝ)) (by norm_num [em12314]) ?_)
      (show bm12314^8 ≤ scalar12314.lowerTail by norm_num [bm12314, scalar12314])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12314, bm12314, Finset.sum_range_succ, Nat.factorial]

theorem guards12314 :
    agent12314.root+dsL+scalar12314.worldRadius < √(1/100/aL) ∧
    2*(agent12314.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12314, agent12314, scalar12314, tp12314, tm12314, ep12314, em12314, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12314, agent12314, scalar12314, tp12314, tm12314, ep12314, em12314, dsL]

noncomputable def master12314 : MasterCertificate 12314 world12314 agent12314 :=
  master scalar12314 dsL tp12314 tm12314 ep12314 em12314
    (by norm_num [dsL]) (by norm_num [tp12314]) (by norm_num [tm12314])
    (by norm_num [ep12314]) (by norm_num [em12314])
    positive12314 negative12314 tails12314.1 tails12314.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12314.1 guards12314.2

theorem preserves12314 : master12314.toScalarCertificate = scalar12314 := rfl

noncomputable def tp12315 : ℝ := (2310407881 / 10000000000)
noncomputable def tm12315 : ℝ := (-((3038066417 / 5000000000)))
noncomputable def ep12315 : ℝ := (50871126808916581 / 100000000000000000000)
noncomputable def em12315 : ℝ := (49764301691612977 / 100000000000000000000)
noncomputable def bp12315 : ℝ := (9139766748103132107 / 20000000000000000000)
noncomputable def bm12315 : ℝ := (46484130130382904973 / 100000000000000000000)

theorem positive12315 :
    Eplus aL (agent12315.root+dsL) scalar12315.worldRadius world12315.frame
      agent12315.frame tp12315 ≤ -ep12315 := by
  apply positive_check (eT := (115698326543518481323 / 100000000000000000000)) (y := (37224024823589899699 / 100000000000000000000)) (u := (36274538379397564613 / 25000000000000000000))
  · norm_num [world12315, agent12315, scalar12315, tp12315, tm12315, ep12315, em12315, dsL]
  · norm_num [world12315, agent12315, scalar12315, tp12315, tm12315, ep12315, em12315, dsL]
  · norm_num [world12315, agent12315, scalar12315, tp12315, tm12315, ep12315, em12315, dsL]
  · norm_num [world12315, agent12315, scalar12315, tp12315, tm12315, ep12315, em12315, dsL]
  · norm_num [world12315, agent12315, scalar12315, tp12315, tm12315, ep12315, em12315, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12315, agent12315, tp12315, tm12315, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12315, agent12315, scalar12315, tp12315, tm12315, ep12315, em12315, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12315, agent12315, tp12315, tm12315, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12315, agent12315, scalar12315, tp12315, tm12315, ep12315, em12315, dsL]

theorem negative12315 :
    Eminus aL (agent12315.root+dsL) scalar12315.worldRadius world12315.frame
      agent12315.frame tm12315 ≤ -em12315 := by
  apply negative_check (lo := (851856369090565239 / 1250000000000000000)) (hi := (68148509527245219121 / 100000000000000000000))
    (y := (-((35427715421820725513 / 50000000000000000000)))) (u := (9847109547026118271 / 20000000000000000000))
  · norm_num [world12315, agent12315, scalar12315, tp12315, tm12315, ep12315, em12315, dsL]
  · norm_num [world12315, agent12315, scalar12315, tp12315, tm12315, ep12315, em12315, dsL]
  · norm_num [world12315, agent12315, scalar12315, tp12315, tm12315, ep12315, em12315, dsL]
  · norm_num [world12315, agent12315, scalar12315, tp12315, tm12315, ep12315, em12315, dsL]
  · norm_num [world12315, agent12315, scalar12315, tp12315, tm12315, ep12315, em12315, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12315, agent12315, tp12315, tm12315, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12315, agent12315, tp12315, tm12315, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12315, agent12315, scalar12315, tp12315, tm12315, ep12315, em12315, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12315, agent12315, tp12315, tm12315, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12315, agent12315, scalar12315, tp12315, tm12315, ep12315, em12315, dsL]

theorem tails12315 :
    exp (-((12315:ℝ)*ep12315)) ≤ scalar12315.upperTail ∧
    exp (-((12315:ℝ)*em12315)) ≤ scalar12315.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12315:ℝ)) (by norm_num [ep12315]) ?_)
      (show bp12315^8 ≤ scalar12315.upperTail by norm_num [bp12315, scalar12315])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12315, bp12315, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12315:ℝ)) (by norm_num [em12315]) ?_)
      (show bm12315^8 ≤ scalar12315.lowerTail by norm_num [bm12315, scalar12315])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12315, bm12315, Finset.sum_range_succ, Nat.factorial]

theorem guards12315 :
    agent12315.root+dsL+scalar12315.worldRadius < √(1/100/aL) ∧
    2*(agent12315.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12315, agent12315, scalar12315, tp12315, tm12315, ep12315, em12315, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12315, agent12315, scalar12315, tp12315, tm12315, ep12315, em12315, dsL]

noncomputable def master12315 : MasterCertificate 12315 world12315 agent12315 :=
  master scalar12315 dsL tp12315 tm12315 ep12315 em12315
    (by norm_num [dsL]) (by norm_num [tp12315]) (by norm_num [tm12315])
    (by norm_num [ep12315]) (by norm_num [em12315])
    positive12315 negative12315 tails12315.1 tails12315.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12315.1 guards12315.2

theorem preserves12315 : master12315.toScalarCertificate = scalar12315 := rfl

noncomputable def tp12316 : ℝ := (1155254019 / 5000000000)
noncomputable def tm12316 : ℝ := (-((3038177713 / 5000000000)))
noncomputable def ep12316 : ℝ := (25437078880421369 / 50000000000000000000)
noncomputable def em12316 : ℝ := (49766951972533473 / 100000000000000000000)
noncomputable def bp12316 : ℝ := (22846897851465591123 / 50000000000000000000)
noncomputable def bm12316 : ℝ := (11619835552916670207 / 25000000000000000000)

theorem positive12316 :
    Eplus aL (agent12316.root+dsL) scalar12316.worldRadius world12316.frame
      agent12316.frame tp12316 ≤ -ep12316 := by
  apply positive_check (eT := (57849331912557518621 / 50000000000000000000)) (y := (72704779291918991 / 195312500000000000)) (u := (145099346481602251983 / 100000000000000000000))
  · norm_num [world12316, agent12316, scalar12316, tp12316, tm12316, ep12316, em12316, dsL]
  · norm_num [world12316, agent12316, scalar12316, tp12316, tm12316, ep12316, em12316, dsL]
  · norm_num [world12316, agent12316, scalar12316, tp12316, tm12316, ep12316, em12316, dsL]
  · norm_num [world12316, agent12316, scalar12316, tp12316, tm12316, ep12316, em12316, dsL]
  · norm_num [world12316, agent12316, scalar12316, tp12316, tm12316, ep12316, em12316, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12316, agent12316, tp12316, tm12316, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12316, agent12316, scalar12316, tp12316, tm12316, ep12316, em12316, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12316, agent12316, tp12316, tm12316, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12316, agent12316, scalar12316, tp12316, tm12316, ep12316, em12316, dsL]

theorem negative12316 :
    Eminus aL (agent12316.root+dsL) scalar12316.worldRadius world12316.frame
      agent12316.frame tm12316 ≤ -em12316 := by
  apply negative_check (lo := (13629632516632607531 / 20000000000000000000)) (hi := (8518520322895379707 / 12500000000000000000))
    (y := (-((35427741461980903321 / 50000000000000000000)))) (u := (24617761046553139641 / 50000000000000000000))
  · norm_num [world12316, agent12316, scalar12316, tp12316, tm12316, ep12316, em12316, dsL]
  · norm_num [world12316, agent12316, scalar12316, tp12316, tm12316, ep12316, em12316, dsL]
  · norm_num [world12316, agent12316, scalar12316, tp12316, tm12316, ep12316, em12316, dsL]
  · norm_num [world12316, agent12316, scalar12316, tp12316, tm12316, ep12316, em12316, dsL]
  · norm_num [world12316, agent12316, scalar12316, tp12316, tm12316, ep12316, em12316, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12316, agent12316, tp12316, tm12316, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12316, agent12316, tp12316, tm12316, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12316, agent12316, scalar12316, tp12316, tm12316, ep12316, em12316, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12316, agent12316, tp12316, tm12316, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12316, agent12316, scalar12316, tp12316, tm12316, ep12316, em12316, dsL]

theorem tails12316 :
    exp (-((12316:ℝ)*ep12316)) ≤ scalar12316.upperTail ∧
    exp (-((12316:ℝ)*em12316)) ≤ scalar12316.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12316:ℝ)) (by norm_num [ep12316]) ?_)
      (show bp12316^8 ≤ scalar12316.upperTail by norm_num [bp12316, scalar12316])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12316, bp12316, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12316:ℝ)) (by norm_num [em12316]) ?_)
      (show bm12316^8 ≤ scalar12316.lowerTail by norm_num [bm12316, scalar12316])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12316, bm12316, Finset.sum_range_succ, Nat.factorial]

theorem guards12316 :
    agent12316.root+dsL+scalar12316.worldRadius < √(1/100/aL) ∧
    2*(agent12316.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12316, agent12316, scalar12316, tp12316, tm12316, ep12316, em12316, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12316, agent12316, scalar12316, tp12316, tm12316, ep12316, em12316, dsL]

noncomputable def master12316 : MasterCertificate 12316 world12316 agent12316 :=
  master scalar12316 dsL tp12316 tm12316 ep12316 em12316
    (by norm_num [dsL]) (by norm_num [tp12316]) (by norm_num [tm12316])
    (by norm_num [ep12316]) (by norm_num [em12316])
    positive12316 negative12316 tails12316.1 tails12316.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12316.1 guards12316.2

theorem preserves12316 : master12316.toScalarCertificate = scalar12316 := rfl

noncomputable def tp12317 : ℝ := (2310608237 / 10000000000)
noncomputable def tm12317 : ℝ := (-((6076577721 / 10000000000)))
noncomputable def ep12317 : ℝ := (10175437371109307 / 20000000000000000000)
noncomputable def em12317 : ℝ := (79631360826271 / 160000000000000000)
noncomputable def bp12317 : ℝ := (45688759180996968947 / 100000000000000000000)
noncomputable def bm12317 : ℝ := (11618638930273023927 / 25000000000000000000)

theorem positive12317 :
    Eplus aL (agent12317.root+dsL) scalar12317.worldRadius world12317.frame
      agent12317.frame tp12317 ≤ -ep12317 := by
  apply positive_check (eT := (57849500722916778711 / 50000000000000000000)) (y := (3722567028869658631 / 10000000000000000000)) (u := (145100541076720009291 / 100000000000000000000))
  · norm_num [world12317, agent12317, scalar12317, tp12317, tm12317, ep12317, em12317, dsL]
  · norm_num [world12317, agent12317, scalar12317, tp12317, tm12317, ep12317, em12317, dsL]
  · norm_num [world12317, agent12317, scalar12317, tp12317, tm12317, ep12317, em12317, dsL]
  · norm_num [world12317, agent12317, scalar12317, tp12317, tm12317, ep12317, em12317, dsL]
  · norm_num [world12317, agent12317, scalar12317, tp12317, tm12317, ep12317, em12317, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12317, agent12317, tp12317, tm12317, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12317, agent12317, scalar12317, tp12317, tm12317, ep12317, em12317, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12317, agent12317, tp12317, tm12317, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12317, agent12317, scalar12317, tp12317, tm12317, ep12317, em12317, dsL]

theorem negative12317 :
    Eminus aL (agent12317.root+dsL) scalar12317.worldRadius world12317.frame
      agent12317.frame tm12317 ≤ -em12317 := by
  apply negative_check (lo := (68147816861241301823 / 100000000000000000000)) (hi := (1064809638456895341 / 1562500000000000000))
    (y := (-((3542776621727819073 / 5000000000000000000)))) (u := (49235497716312583517 / 100000000000000000000))
  · norm_num [world12317, agent12317, scalar12317, tp12317, tm12317, ep12317, em12317, dsL]
  · norm_num [world12317, agent12317, scalar12317, tp12317, tm12317, ep12317, em12317, dsL]
  · norm_num [world12317, agent12317, scalar12317, tp12317, tm12317, ep12317, em12317, dsL]
  · norm_num [world12317, agent12317, scalar12317, tp12317, tm12317, ep12317, em12317, dsL]
  · norm_num [world12317, agent12317, scalar12317, tp12317, tm12317, ep12317, em12317, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12317, agent12317, tp12317, tm12317, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12317, agent12317, tp12317, tm12317, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12317, agent12317, scalar12317, tp12317, tm12317, ep12317, em12317, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12317, agent12317, tp12317, tm12317, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12317, agent12317, scalar12317, tp12317, tm12317, ep12317, em12317, dsL]

theorem tails12317 :
    exp (-((12317:ℝ)*ep12317)) ≤ scalar12317.upperTail ∧
    exp (-((12317:ℝ)*em12317)) ≤ scalar12317.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12317:ℝ)) (by norm_num [ep12317]) ?_)
      (show bp12317^8 ≤ scalar12317.upperTail by norm_num [bp12317, scalar12317])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12317, bp12317, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12317:ℝ)) (by norm_num [em12317]) ?_)
      (show bm12317^8 ≤ scalar12317.lowerTail by norm_num [bm12317, scalar12317])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12317, bm12317, Finset.sum_range_succ, Nat.factorial]

theorem guards12317 :
    agent12317.root+dsL+scalar12317.worldRadius < √(1/100/aL) ∧
    2*(agent12317.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12317, agent12317, scalar12317, tp12317, tm12317, ep12317, em12317, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12317, agent12317, scalar12317, tp12317, tm12317, ep12317, em12317, dsL]

noncomputable def master12317 : MasterCertificate 12317 world12317 agent12317 :=
  master scalar12317 dsL tp12317 tm12317 ep12317 em12317
    (by norm_num [dsL]) (by norm_num [tp12317]) (by norm_num [tm12317])
    (by norm_num [ep12317]) (by norm_num [em12317])
    positive12317 negative12317 tails12317.1 tails12317.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12317.1 guards12317.2

theorem preserves12317 : master12317.toScalarCertificate = scalar12317 := rfl

noncomputable def tp12318 : ℝ := (144419279 / 625000000)
noncomputable def tm12318 : ℝ := (-((121536011 / 200000000)))
noncomputable def ep12318 : ℝ := (50880216258544903 / 100000000000000000000)
noncomputable def em12318 : ℝ := (24886124833249667 / 50000000000000000000)
noncomputable def bp12318 : ℝ := (22841861325697530113 / 50000000000000000000)
noncomputable def bm12318 : ℝ := (46469768981999260271 / 100000000000000000000)

theorem positive12318 :
    Eplus aL (agent12318.root+dsL) scalar12318.worldRadius world12318.frame
      agent12318.frame tp12318 ≤ -ep12318 := by
  apply positive_check (eT := (57849669651707591493 / 50000000000000000000)) (y := (37226491856813470393 / 100000000000000000000)) (u := (29020346636279978239 / 20000000000000000000))
  · norm_num [world12318, agent12318, scalar12318, tp12318, tm12318, ep12318, em12318, dsL]
  · norm_num [world12318, agent12318, scalar12318, tp12318, tm12318, ep12318, em12318, dsL]
  · norm_num [world12318, agent12318, scalar12318, tp12318, tm12318, ep12318, em12318, dsL]
  · norm_num [world12318, agent12318, scalar12318, tp12318, tm12318, ep12318, em12318, dsL]
  · norm_num [world12318, agent12318, scalar12318, tp12318, tm12318, ep12318, em12318, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12318, agent12318, tp12318, tm12318, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12318, agent12318, scalar12318, tp12318, tm12318, ep12318, em12318, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12318, agent12318, tp12318, tm12318, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12318, agent12318, scalar12318, tp12318, tm12318, ep12318, em12318, dsL]

theorem negative12318 :
    Eminus aL (agent12318.root+dsL) scalar12318.worldRadius world12318.frame
      agent12318.frame tm12318 ≤ -em12318 := by
  apply negative_check (lo := (68147468787548133257 / 100000000000000000000)) (hi := (34073734393774066629 / 50000000000000000000))
    (y := (-((35427791298081307381 / 50000000000000000000)))) (u := (24617736509501143169 / 50000000000000000000))
  · norm_num [world12318, agent12318, scalar12318, tp12318, tm12318, ep12318, em12318, dsL]
  · norm_num [world12318, agent12318, scalar12318, tp12318, tm12318, ep12318, em12318, dsL]
  · norm_num [world12318, agent12318, scalar12318, tp12318, tm12318, ep12318, em12318, dsL]
  · norm_num [world12318, agent12318, scalar12318, tp12318, tm12318, ep12318, em12318, dsL]
  · norm_num [world12318, agent12318, scalar12318, tp12318, tm12318, ep12318, em12318, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12318, agent12318, tp12318, tm12318, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12318, agent12318, tp12318, tm12318, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12318, agent12318, scalar12318, tp12318, tm12318, ep12318, em12318, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12318, agent12318, tp12318, tm12318, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12318, agent12318, scalar12318, tp12318, tm12318, ep12318, em12318, dsL]

theorem tails12318 :
    exp (-((12318:ℝ)*ep12318)) ≤ scalar12318.upperTail ∧
    exp (-((12318:ℝ)*em12318)) ≤ scalar12318.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12318:ℝ)) (by norm_num [ep12318]) ?_)
      (show bp12318^8 ≤ scalar12318.upperTail by norm_num [bp12318, scalar12318])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12318, bp12318, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12318:ℝ)) (by norm_num [em12318]) ?_)
      (show bm12318^8 ≤ scalar12318.lowerTail by norm_num [bm12318, scalar12318])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12318, bm12318, Finset.sum_range_succ, Nat.factorial]

theorem guards12318 :
    agent12318.root+dsL+scalar12318.worldRadius < √(1/100/aL) ∧
    2*(agent12318.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12318, agent12318, scalar12318, tp12318, tm12318, ep12318, em12318, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12318, agent12318, scalar12318, tp12318, tm12318, ep12318, em12318, dsL]

noncomputable def master12318 : MasterCertificate 12318 world12318 agent12318 :=
  master scalar12318 dsL tp12318 tm12318 ep12318 em12318
    (by norm_num [dsL]) (by norm_num [tp12318]) (by norm_num [tm12318])
    (by norm_num [ep12318]) (by norm_num [em12318])
    positive12318 negative12318 tails12318.1 tails12318.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12318.1 guards12318.2

theorem preserves12318 : master12318.toScalarCertificate = scalar12318 := rfl

noncomputable def tp12319 : ℝ := (1155404411 / 5000000000)
noncomputable def tm12319 : ℝ := (-((1519255967 / 2500000000)))
noncomputable def ep12319 : ℝ := (50883248331883111 / 100000000000000000000)
noncomputable def em12319 : ℝ := (24887450967993857 / 50000000000000000000)
noncomputable def bp12319 : ℝ := (45678684452747565141 / 100000000000000000000)
noncomputable def bm12319 : ℝ := (23232490098124701799 / 50000000000000000000)

theorem positive12319 :
    Eplus aL (agent12319.root+dsL) scalar12319.worldRadius world12319.frame
      agent12319.frame tp12319 ≤ -ep12319 := by
  apply positive_check (eT := (57849839074951859191 / 50000000000000000000)) (y := (37227310333434094187 / 100000000000000000000)) (u := (36275730202505581387 / 25000000000000000000))
  · norm_num [world12319, agent12319, scalar12319, tp12319, tm12319, ep12319, em12319, dsL]
  · norm_num [world12319, agent12319, scalar12319, tp12319, tm12319, ep12319, em12319, dsL]
  · norm_num [world12319, agent12319, scalar12319, tp12319, tm12319, ep12319, em12319, dsL]
  · norm_num [world12319, agent12319, scalar12319, tp12319, tm12319, ep12319, em12319, dsL]
  · norm_num [world12319, agent12319, scalar12319, tp12319, tm12319, ep12319, em12319, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12319, agent12319, tp12319, tm12319, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12319, agent12319, scalar12319, tp12319, tm12319, ep12319, em12319, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12319, agent12319, tp12319, tm12319, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12319, agent12319, scalar12319, tp12319, tm12319, ep12319, em12319, dsL]

theorem negative12319 :
    Eminus aL (agent12319.root+dsL) scalar12319.worldRadius world12319.frame
      agent12319.frame tm12319 ≤ -em12319 := by
  apply negative_check (lo := (68147118555793771371 / 100000000000000000000)) (hi := (17036779638948442843 / 25000000000000000000))
    (y := (-((35427813163468732549 / 50000000000000000000)))) (u := (12308862871988285437 / 25000000000000000000))
  · norm_num [world12319, agent12319, scalar12319, tp12319, tm12319, ep12319, em12319, dsL]
  · norm_num [world12319, agent12319, scalar12319, tp12319, tm12319, ep12319, em12319, dsL]
  · norm_num [world12319, agent12319, scalar12319, tp12319, tm12319, ep12319, em12319, dsL]
  · norm_num [world12319, agent12319, scalar12319, tp12319, tm12319, ep12319, em12319, dsL]
  · norm_num [world12319, agent12319, scalar12319, tp12319, tm12319, ep12319, em12319, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12319, agent12319, tp12319, tm12319, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12319, agent12319, tp12319, tm12319, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12319, agent12319, scalar12319, tp12319, tm12319, ep12319, em12319, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12319, agent12319, tp12319, tm12319, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12319, agent12319, scalar12319, tp12319, tm12319, ep12319, em12319, dsL]

theorem tails12319 :
    exp (-((12319:ℝ)*ep12319)) ≤ scalar12319.upperTail ∧
    exp (-((12319:ℝ)*em12319)) ≤ scalar12319.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12319:ℝ)) (by norm_num [ep12319]) ?_)
      (show bp12319^8 ≤ scalar12319.upperTail by norm_num [bp12319, scalar12319])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12319, bp12319, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12319:ℝ)) (by norm_num [em12319]) ?_)
      (show bm12319^8 ≤ scalar12319.lowerTail by norm_num [bm12319, scalar12319])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12319, bm12319, Finset.sum_range_succ, Nat.factorial]

theorem guards12319 :
    agent12319.root+dsL+scalar12319.worldRadius < √(1/100/aL) ∧
    2*(agent12319.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12319, agent12319, scalar12319, tp12319, tm12319, ep12319, em12319, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12319, agent12319, scalar12319, tp12319, tm12319, ep12319, em12319, dsL]

noncomputable def master12319 : MasterCertificate 12319 world12319 agent12319 :=
  master scalar12319 dsL tp12319 tm12319 ep12319 em12319
    (by norm_num [dsL]) (by norm_num [tp12319]) (by norm_num [tm12319])
    (by norm_num [ep12319]) (by norm_num [em12319])
    positive12319 negative12319 tails12319.1 tails12319.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12319.1 guards12319.2

theorem preserves12319 : master12319.toScalarCertificate = scalar12319 := rfl

noncomputable def tp12320 : ℝ := (2310909103 / 10000000000)
noncomputable def tm12320 : ℝ := (-((6077246989 / 10000000000)))
noncomputable def ep12320 : ℝ := (12721569748816557 / 25000000000000000000)
noncomputable def em12320 : ℝ := (24888776448579559 / 50000000000000000000)
noncomputable def bp12320 : ℝ := (45673647455245788283 / 100000000000000000000)
noncomputable def bm12320 : ℝ := (290376203325081979 / 625000000000000000)

theorem positive12320 :
    Eplus aL (agent12320.root+dsL) scalar12320.worldRadius world12320.frame
      agent12320.frame tp12320 ≤ -ep12320 := by
  apply positive_check (eT := (28925004116645622809 / 25000000000000000000)) (y := (18614064010076690359 / 50000000000000000000)) (u := (72552053651092986883 / 50000000000000000000))
  · norm_num [world12320, agent12320, scalar12320, tp12320, tm12320, ep12320, em12320, dsL]
  · norm_num [world12320, agent12320, scalar12320, tp12320, tm12320, ep12320, em12320, dsL]
  · norm_num [world12320, agent12320, scalar12320, tp12320, tm12320, ep12320, em12320, dsL]
  · norm_num [world12320, agent12320, scalar12320, tp12320, tm12320, ep12320, em12320, dsL]
  · norm_num [world12320, agent12320, scalar12320, tp12320, tm12320, ep12320, em12320, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12320, agent12320, tp12320, tm12320, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12320, agent12320, scalar12320, tp12320, tm12320, ep12320, em12320, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12320, agent12320, tp12320, tm12320, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12320, agent12320, scalar12320, tp12320, tm12320, ep12320, em12320, dsL]

theorem negative12320 :
    Eminus aL (agent12320.root+dsL) scalar12320.worldRadius world12320.frame
      agent12320.frame tm12320 ≤ -em12320 := by
  apply negative_check (lo := (34073384558118401299 / 50000000000000000000)) (hi := (68146769116236802599 / 100000000000000000000))
    (y := (-((70855669388905716117 / 100000000000000000000)))) (u := (9847086057240643741 / 20000000000000000000))
  · norm_num [world12320, agent12320, scalar12320, tp12320, tm12320, ep12320, em12320, dsL]
  · norm_num [world12320, agent12320, scalar12320, tp12320, tm12320, ep12320, em12320, dsL]
  · norm_num [world12320, agent12320, scalar12320, tp12320, tm12320, ep12320, em12320, dsL]
  · norm_num [world12320, agent12320, scalar12320, tp12320, tm12320, ep12320, em12320, dsL]
  · norm_num [world12320, agent12320, scalar12320, tp12320, tm12320, ep12320, em12320, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12320, agent12320, tp12320, tm12320, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12320, agent12320, tp12320, tm12320, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12320, agent12320, scalar12320, tp12320, tm12320, ep12320, em12320, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12320, agent12320, tp12320, tm12320, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12320, agent12320, scalar12320, tp12320, tm12320, ep12320, em12320, dsL]

theorem tails12320 :
    exp (-((12320:ℝ)*ep12320)) ≤ scalar12320.upperTail ∧
    exp (-((12320:ℝ)*em12320)) ≤ scalar12320.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12320:ℝ)) (by norm_num [ep12320]) ?_)
      (show bp12320^8 ≤ scalar12320.upperTail by norm_num [bp12320, scalar12320])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12320, bp12320, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12320:ℝ)) (by norm_num [em12320]) ?_)
      (show bm12320^8 ≤ scalar12320.lowerTail by norm_num [bm12320, scalar12320])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12320, bm12320, Finset.sum_range_succ, Nat.factorial]

theorem guards12320 :
    agent12320.root+dsL+scalar12320.worldRadius < √(1/100/aL) ∧
    2*(agent12320.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12320, agent12320, scalar12320, tp12320, tm12320, ep12320, em12320, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12320, agent12320, scalar12320, tp12320, tm12320, ep12320, em12320, dsL]

noncomputable def master12320 : MasterCertificate 12320 world12320 agent12320 :=
  master scalar12320 dsL tp12320 tm12320 ep12320 em12320
    (by norm_num [dsL]) (by norm_num [tp12320]) (by norm_num [tm12320])
    (by norm_num [ep12320]) (by norm_num [em12320])
    positive12320 negative12320 tails12320.1 tails12320.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12320.1 guards12320.2

theorem preserves12320 : master12320.toScalarCertificate = scalar12320 := rfl

noncomputable def tp12321 : ℝ := (1155504707 / 5000000000)
noncomputable def tm12321 : ℝ := (-((3038735023 / 5000000000)))
noncomputable def ep12321 : ℝ := (50889308402938353 / 100000000000000000000)
noncomputable def em12321 : ℝ := (49780202702648693 / 100000000000000000000)
noncomputable def bp12321 : ℝ := (9133722310073643313 / 20000000000000000000)
noncomputable def bm12321 : ℝ := (46455405880067262579 / 100000000000000000000)

theorem positive12321 :
    Eplus aL (agent12321.root+dsL) scalar12321.worldRadius world12321.frame
      agent12321.frame tp12321 ≤ -ep12321 := by
  apply positive_check (eT := (115700355034635894591 / 100000000000000000000)) (y := (37228946518538085437 / 100000000000000000000)) (u := (145105294981820945043 / 100000000000000000000))
  · norm_num [world12321, agent12321, scalar12321, tp12321, tm12321, ep12321, em12321, dsL]
  · norm_num [world12321, agent12321, scalar12321, tp12321, tm12321, ep12321, em12321, dsL]
  · norm_num [world12321, agent12321, scalar12321, tp12321, tm12321, ep12321, em12321, dsL]
  · norm_num [world12321, agent12321, scalar12321, tp12321, tm12321, ep12321, em12321, dsL]
  · norm_num [world12321, agent12321, scalar12321, tp12321, tm12321, ep12321, em12321, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12321, agent12321, tp12321, tm12321, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12321, agent12321, scalar12321, tp12321, tm12321, ep12321, em12321, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12321, agent12321, tp12321, tm12321, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12321, agent12321, scalar12321, tp12321, tm12321, ep12321, em12321, dsL]

theorem negative12321 :
    Eminus aL (agent12321.root+dsL) scalar12321.worldRadius world12321.frame
      agent12321.frame tm12321 ≤ -em12321 := by
  apply negative_check (lo := (1362928397939579561 / 2000000000000000000)) (hi := (68146419896978978051 / 100000000000000000000))
    (y := (-((8856964044988392529 / 12500000000000000000)))) (u := (4923540912925031493 / 10000000000000000000))
  · norm_num [world12321, agent12321, scalar12321, tp12321, tm12321, ep12321, em12321, dsL]
  · norm_num [world12321, agent12321, scalar12321, tp12321, tm12321, ep12321, em12321, dsL]
  · norm_num [world12321, agent12321, scalar12321, tp12321, tm12321, ep12321, em12321, dsL]
  · norm_num [world12321, agent12321, scalar12321, tp12321, tm12321, ep12321, em12321, dsL]
  · norm_num [world12321, agent12321, scalar12321, tp12321, tm12321, ep12321, em12321, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12321, agent12321, tp12321, tm12321, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12321, agent12321, tp12321, tm12321, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12321, agent12321, scalar12321, tp12321, tm12321, ep12321, em12321, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12321, agent12321, tp12321, tm12321, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12321, agent12321, scalar12321, tp12321, tm12321, ep12321, em12321, dsL]

theorem tails12321 :
    exp (-((12321:ℝ)*ep12321)) ≤ scalar12321.upperTail ∧
    exp (-((12321:ℝ)*em12321)) ≤ scalar12321.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12321:ℝ)) (by norm_num [ep12321]) ?_)
      (show bp12321^8 ≤ scalar12321.upperTail by norm_num [bp12321, scalar12321])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12321, bp12321, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12321:ℝ)) (by norm_num [em12321]) ?_)
      (show bm12321^8 ≤ scalar12321.lowerTail by norm_num [bm12321, scalar12321])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12321, bm12321, Finset.sum_range_succ, Nat.factorial]

theorem guards12321 :
    agent12321.root+dsL+scalar12321.worldRadius < √(1/100/aL) ∧
    2*(agent12321.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12321, agent12321, scalar12321, tp12321, tm12321, ep12321, em12321, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12321, agent12321, scalar12321, tp12321, tm12321, ep12321, em12321, dsL]

noncomputable def master12321 : MasterCertificate 12321 world12321 agent12321 :=
  master scalar12321 dsL tp12321 tm12321 ep12321 em12321
    (by norm_num [dsL]) (by norm_num [tp12321]) (by norm_num [tm12321])
    (by norm_num [ep12321]) (by norm_num [em12321])
    positive12321 negative12321 tails12321.1 tails12321.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12321.1 guards12321.2

theorem preserves12321 : master12321.toScalarCertificate = scalar12321 := rfl

noncomputable def tp12322 : ℝ := (1155554837 / 5000000000)
noncomputable def tm12322 : ℝ := (-((3038846449 / 5000000000)))
noncomputable def ep12322 : ℝ := (50892336279003899 / 100000000000000000000)
noncomputable def em12322 : ℝ := (4978285105632197 / 10000000000000000000)
noncomputable def bp12322 : ℝ := (45663576932137475861 / 100000000000000000000)
noncomputable def bm12322 : ℝ := (9290124090454600207 / 20000000000000000000)

theorem positive12322 :
    Eplus aL (agent12322.root+dsL) scalar12322.worldRadius world12322.frame
      agent12322.frame tp12322 ≤ -ep12322 := by
  apply positive_check (eT := (28925173315683253303 / 25000000000000000000)) (y := (4653720578128146303 / 12500000000000000000)) (u := (72553241051254122091 / 50000000000000000000))
  · norm_num [world12322, agent12322, scalar12322, tp12322, tm12322, ep12322, em12322, dsL]
  · norm_num [world12322, agent12322, scalar12322, tp12322, tm12322, ep12322, em12322, dsL]
  · norm_num [world12322, agent12322, scalar12322, tp12322, tm12322, ep12322, em12322, dsL]
  · norm_num [world12322, agent12322, scalar12322, tp12322, tm12322, ep12322, em12322, dsL]
  · norm_num [world12322, agent12322, scalar12322, tp12322, tm12322, ep12322, em12322, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12322, agent12322, tp12322, tm12322, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12322, agent12322, scalar12322, tp12322, tm12322, ep12322, em12322, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12322, agent12322, tp12322, tm12322, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12322, agent12322, scalar12322, tp12322, tm12322, ep12322, em12322, dsL]

theorem negative12322 :
    Eminus aL (agent12322.root+dsL) scalar12322.worldRadius world12322.frame
      agent12322.frame tm12322 ≤ -em12322 := by
  apply negative_check (lo := (8518258938028573669 / 12500000000000000000)) (hi := (68146071504228589353 / 100000000000000000000))
    (y := (-((70855754052453454587 / 100000000000000000000)))) (u := (769302946902481873 / 1562500000000000000))
  · norm_num [world12322, agent12322, scalar12322, tp12322, tm12322, ep12322, em12322, dsL]
  · norm_num [world12322, agent12322, scalar12322, tp12322, tm12322, ep12322, em12322, dsL]
  · norm_num [world12322, agent12322, scalar12322, tp12322, tm12322, ep12322, em12322, dsL]
  · norm_num [world12322, agent12322, scalar12322, tp12322, tm12322, ep12322, em12322, dsL]
  · norm_num [world12322, agent12322, scalar12322, tp12322, tm12322, ep12322, em12322, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12322, agent12322, tp12322, tm12322, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12322, agent12322, tp12322, tm12322, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12322, agent12322, scalar12322, tp12322, tm12322, ep12322, em12322, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12322, agent12322, tp12322, tm12322, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12322, agent12322, scalar12322, tp12322, tm12322, ep12322, em12322, dsL]

theorem tails12322 :
    exp (-((12322:ℝ)*ep12322)) ≤ scalar12322.upperTail ∧
    exp (-((12322:ℝ)*em12322)) ≤ scalar12322.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12322:ℝ)) (by norm_num [ep12322]) ?_)
      (show bp12322^8 ≤ scalar12322.upperTail by norm_num [bp12322, scalar12322])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12322, bp12322, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12322:ℝ)) (by norm_num [em12322]) ?_)
      (show bm12322^8 ≤ scalar12322.lowerTail by norm_num [bm12322, scalar12322])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12322, bm12322, Finset.sum_range_succ, Nat.factorial]

theorem guards12322 :
    agent12322.root+dsL+scalar12322.worldRadius < √(1/100/aL) ∧
    2*(agent12322.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12322, agent12322, scalar12322, tp12322, tm12322, ep12322, em12322, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12322, agent12322, scalar12322, tp12322, tm12322, ep12322, em12322, dsL]

noncomputable def master12322 : MasterCertificate 12322 world12322 agent12322 :=
  master scalar12322 dsL tp12322 tm12322 ep12322 em12322
    (by norm_num [dsL]) (by norm_num [tp12322]) (by norm_num [tm12322])
    (by norm_num [ep12322]) (by norm_num [em12322])
    positive12322 negative12322 tails12322.1 tails12322.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12322.1 guards12322.2

theorem preserves12322 : master12322.toScalarCertificate = scalar12322 := rfl

noncomputable def tp12323 : ℝ := (577802461 / 2500000000)
noncomputable def tm12323 : ℝ := (-((3038957879 / 5000000000)))
noncomputable def ep12323 : ℝ := (5089536275901949 / 10000000000000000000)
noncomputable def em12323 : ℝ := (24892749053698961 / 50000000000000000000)
noncomputable def bp12323 : ℝ := (22829271752586993017 / 50000000000000000000)
noncomputable def bm12323 : ℝ := (46445836141849257221 / 100000000000000000000)

theorem positive12323 :
    Eplus aL (agent12323.root+dsL) scalar12323.worldRadius world12323.frame
      agent12323.frame tp12323 ≤ -ep12323 := by
  apply positive_check (eT := (3615657214566230601 / 3125000000000000000)) (y := (18615290807675694799 / 50000000000000000000)) (u := (145107667613272486167 / 100000000000000000000))
  · norm_num [world12323, agent12323, scalar12323, tp12323, tm12323, ep12323, em12323, dsL]
  · norm_num [world12323, agent12323, scalar12323, tp12323, tm12323, ep12323, em12323, dsL]
  · norm_num [world12323, agent12323, scalar12323, tp12323, tm12323, ep12323, em12323, dsL]
  · norm_num [world12323, agent12323, scalar12323, tp12323, tm12323, ep12323, em12323, dsL]
  · norm_num [world12323, agent12323, scalar12323, tp12323, tm12323, ep12323, em12323, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12323, agent12323, tp12323, tm12323, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12323, agent12323, scalar12323, tp12323, tm12323, ep12323, em12323, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12323, agent12323, tp12323, tm12323, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12323, agent12323, scalar12323, tp12323, tm12323, ep12323, em12323, dsL]

theorem negative12323 :
    Eminus aL (agent12323.root+dsL) scalar12323.worldRadius world12323.frame
      agent12323.frame tm12323 ≤ -em12323 := by
  apply negative_check (lo := (68145723022071287289 / 100000000000000000000)) (hi := (6814572302207128729 / 10000000000000000000))
    (y := (-((17713949156891407381 / 25000000000000000000)))) (u := (49235367639741375209 / 100000000000000000000))
  · norm_num [world12323, agent12323, scalar12323, tp12323, tm12323, ep12323, em12323, dsL]
  · norm_num [world12323, agent12323, scalar12323, tp12323, tm12323, ep12323, em12323, dsL]
  · norm_num [world12323, agent12323, scalar12323, tp12323, tm12323, ep12323, em12323, dsL]
  · norm_num [world12323, agent12323, scalar12323, tp12323, tm12323, ep12323, em12323, dsL]
  · norm_num [world12323, agent12323, scalar12323, tp12323, tm12323, ep12323, em12323, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12323, agent12323, tp12323, tm12323, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12323, agent12323, tp12323, tm12323, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12323, agent12323, scalar12323, tp12323, tm12323, ep12323, em12323, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12323, agent12323, tp12323, tm12323, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12323, agent12323, scalar12323, tp12323, tm12323, ep12323, em12323, dsL]

theorem tails12323 :
    exp (-((12323:ℝ)*ep12323)) ≤ scalar12323.upperTail ∧
    exp (-((12323:ℝ)*em12323)) ≤ scalar12323.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12323:ℝ)) (by norm_num [ep12323]) ?_)
      (show bp12323^8 ≤ scalar12323.upperTail by norm_num [bp12323, scalar12323])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12323, bp12323, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12323:ℝ)) (by norm_num [em12323]) ?_)
      (show bm12323^8 ≤ scalar12323.lowerTail by norm_num [bm12323, scalar12323])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12323, bm12323, Finset.sum_range_succ, Nat.factorial]

theorem guards12323 :
    agent12323.root+dsL+scalar12323.worldRadius < √(1/100/aL) ∧
    2*(agent12323.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12323, agent12323, scalar12323, tp12323, tm12323, ep12323, em12323, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12323, agent12323, scalar12323, tp12323, tm12323, ep12323, em12323, dsL]

noncomputable def master12323 : MasterCertificate 12323 world12323 agent12323 :=
  master scalar12323 dsL tp12323 tm12323 ep12323 em12323
    (by norm_num [dsL]) (by norm_num [tp12323]) (by norm_num [tm12323])
    (by norm_num [ep12323]) (by norm_num [em12323])
    positive12323 negative12323 tails12323.1 tails12323.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12323.1 guards12323.2

theorem preserves12323 : master12323.toScalarCertificate = scalar12323 := rfl

noncomputable def tp12324 : ℝ := (2311309977 / 10000000000)
noncomputable def tm12324 : ℝ := (-((6078138349 / 10000000000)))
noncomputable def ep12324 : ℝ := (25449193751769437 / 50000000000000000000)
noncomputable def em12324 : ℝ := (3111758972834413 / 6250000000000000000)
noncomputable def bp12324 : ℝ := (913070230163502381 / 2000000000000000000)
noncomputable def bm12324 : ℝ := (46441053156628516519 / 100000000000000000000)

theorem positive12324 :
    Eplus aL (agent12324.root+dsL) scalar12324.worldRadius world12324.frame
      agent12324.frame tp12324 ≤ -ep12324 := by
  apply positive_check (eT := (28925342057938426043 / 25000000000000000000)) (y := (1489255936239749697 / 4000000000000000000)) (u := (72554426421981653959 / 50000000000000000000))
  · norm_num [world12324, agent12324, scalar12324, tp12324, tm12324, ep12324, em12324, dsL]
  · norm_num [world12324, agent12324, scalar12324, tp12324, tm12324, ep12324, em12324, dsL]
  · norm_num [world12324, agent12324, scalar12324, tp12324, tm12324, ep12324, em12324, dsL]
  · norm_num [world12324, agent12324, scalar12324, tp12324, tm12324, ep12324, em12324, dsL]
  · norm_num [world12324, agent12324, scalar12324, tp12324, tm12324, ep12324, em12324, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12324, agent12324, tp12324, tm12324, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12324, agent12324, scalar12324, tp12324, tm12324, ep12324, em12324, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12324, agent12324, tp12324, tm12324, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12324, agent12324, scalar12324, tp12324, tm12324, ep12324, em12324, dsL]

theorem negative12324 :
    Eminus aL (agent12324.root+dsL) scalar12324.worldRadius world12324.frame
      agent12324.frame tm12324 ≤ -em12324 := by
  apply negative_check (lo := (34072687820811186177 / 50000000000000000000)) (hi := (13629075128324474471 / 20000000000000000000))
    (y := (-((70855837432170865759 / 100000000000000000000)))) (u := (24617673774724036043 / 50000000000000000000))
  · norm_num [world12324, agent12324, scalar12324, tp12324, tm12324, ep12324, em12324, dsL]
  · norm_num [world12324, agent12324, scalar12324, tp12324, tm12324, ep12324, em12324, dsL]
  · norm_num [world12324, agent12324, scalar12324, tp12324, tm12324, ep12324, em12324, dsL]
  · norm_num [world12324, agent12324, scalar12324, tp12324, tm12324, ep12324, em12324, dsL]
  · norm_num [world12324, agent12324, scalar12324, tp12324, tm12324, ep12324, em12324, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12324, agent12324, tp12324, tm12324, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12324, agent12324, tp12324, tm12324, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12324, agent12324, scalar12324, tp12324, tm12324, ep12324, em12324, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12324, agent12324, tp12324, tm12324, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12324, agent12324, scalar12324, tp12324, tm12324, ep12324, em12324, dsL]

theorem tails12324 :
    exp (-((12324:ℝ)*ep12324)) ≤ scalar12324.upperTail ∧
    exp (-((12324:ℝ)*em12324)) ≤ scalar12324.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12324:ℝ)) (by norm_num [ep12324]) ?_)
      (show bp12324^8 ≤ scalar12324.upperTail by norm_num [bp12324, scalar12324])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12324, bp12324, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12324:ℝ)) (by norm_num [em12324]) ?_)
      (show bm12324^8 ≤ scalar12324.lowerTail by norm_num [bm12324, scalar12324])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12324, bm12324, Finset.sum_range_succ, Nat.factorial]

theorem guards12324 :
    agent12324.root+dsL+scalar12324.worldRadius < √(1/100/aL) ∧
    2*(agent12324.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12324, agent12324, scalar12324, tp12324, tm12324, ep12324, em12324, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12324, agent12324, scalar12324, tp12324, tm12324, ep12324, em12324, dsL]

noncomputable def master12324 : MasterCertificate 12324 world12324 agent12324 :=
  master scalar12324 dsL tp12324 tm12324 ep12324 em12324
    (by norm_num [dsL]) (by norm_num [tp12324]) (by norm_num [tm12324])
    (by norm_num [ep12324]) (by norm_num [em12324])
    positive12324 negative12324 tails12324.1 tails12324.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12324.1 guards12324.2

theorem preserves12324 : master12324.toScalarCertificate = scalar12324 := rfl

end BstLean.Part261
