import BstLean.Part261Checker
import BstLean.Part268Scalar17
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12775 : ℝ := (58082771 / 250000000)
noncomputable def tm12775 : ℝ := (-((3038988227 / 5000000000)))
noncomputable def ep12775 : ℝ := (6453495436960623 / 12500000000000000000)
noncomputable def em12775 : ℝ := (25143082801887271 / 50000000000000000000)
noncomputable def bp12775 : ℝ := (21924154261589833589 / 50000000000000000000)
noncomputable def bm12775 : ℝ := (11199494214737847257 / 25000000000000000000)

theorem positive12775 :
    Eplus aL (agent12775.root+dsL) scalar12775.worldRadius world12775.frame
      agent12775.frame tp12775 ≤ -ep12775 := by
  apply positive_check (eT := (1445212410842536001 / 1250000000000000000)) (y := (18957402623877566337 / 50000000000000000000)) (u := (146103933022420949801 / 100000000000000000000))
  · norm_num [world12775, agent12775, scalar12775, tp12775, tm12775, ep12775, em12775, dsL]
  · norm_num [world12775, agent12775, scalar12775, tp12775, tm12775, ep12775, em12775, dsL]
  · norm_num [world12775, agent12775, scalar12775, tp12775, tm12775, ep12775, em12775, dsL]
  · norm_num [world12775, agent12775, scalar12775, tp12775, tm12775, ep12775, em12775, dsL]
  · norm_num [world12775, agent12775, scalar12775, tp12775, tm12775, ep12775, em12775, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12775, agent12775, tp12775, tm12775, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12775, agent12775, scalar12775, tp12775, tm12775, ep12775, em12775, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12775, agent12775, tp12775, tm12775, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12775, agent12775, scalar12775, tp12775, tm12775, ep12775, em12775, dsL]

theorem negative12775 :
    Eminus aL (agent12775.root+dsL) scalar12775.worldRadius world12775.frame
      agent12775.frame tm12775 ≤ -em12775 := by
  apply negative_check (lo := (1368232842542408327 / 2000000000000000000)) (hi := (68411642127120416351 / 100000000000000000000))
    (y := (-((35839325268262177799 / 50000000000000000000)))) (u := (3051993422827619553 / 6250000000000000000))
  · norm_num [world12775, agent12775, scalar12775, tp12775, tm12775, ep12775, em12775, dsL]
  · norm_num [world12775, agent12775, scalar12775, tp12775, tm12775, ep12775, em12775, dsL]
  · norm_num [world12775, agent12775, scalar12775, tp12775, tm12775, ep12775, em12775, dsL]
  · norm_num [world12775, agent12775, scalar12775, tp12775, tm12775, ep12775, em12775, dsL]
  · norm_num [world12775, agent12775, scalar12775, tp12775, tm12775, ep12775, em12775, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12775, agent12775, tp12775, tm12775, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12775, agent12775, tp12775, tm12775, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12775, agent12775, scalar12775, tp12775, tm12775, ep12775, em12775, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12775, agent12775, tp12775, tm12775, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12775, agent12775, scalar12775, tp12775, tm12775, ep12775, em12775, dsL]

theorem tails12775 :
    exp (-((12775:ℝ)*ep12775)) ≤ scalar12775.upperTail ∧
    exp (-((12775:ℝ)*em12775)) ≤ scalar12775.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12775:ℝ)) (by norm_num [ep12775]) ?_)
      (show bp12775^8 ≤ scalar12775.upperTail by norm_num [bp12775, scalar12775])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12775, bp12775, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12775:ℝ)) (by norm_num [em12775]) ?_)
      (show bm12775^8 ≤ scalar12775.lowerTail by norm_num [bm12775, scalar12775])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12775, bm12775, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12775 :
    agent12775.root+dsL+scalar12775.worldRadius < √(1/100/aL) ∧
    2*(agent12775.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12775, agent12775, scalar12775, tp12775, tm12775, ep12775, em12775, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12775, agent12775, scalar12775, tp12775, tm12775, ep12775, em12775, dsL]

noncomputable def master12775 : MasterCertificate 12775 world12775 agent12775 :=
  master scalar12775 dsL tp12775 tm12775 ep12775 em12775
    (by norm_num [dsL]) (by norm_num [tp12775]) (by norm_num [tm12775])
    (by norm_num [ep12775]) (by norm_num [em12775])
    positive12775 negative12775 tails12775.1 tails12775.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12775.1 tailGuards12775.2

theorem preserves12775 : master12775.toScalarCertificate = scalar12775 := rfl

noncomputable def tp12776 : ℝ := (290424171 / 1250000000)
noncomputable def tm12776 : ℝ := (-((607815299 / 1000000000)))
noncomputable def ep12776 : ℝ := (12907622880368809 / 25000000000000000000)
noncomputable def em12776 : ℝ := (6286041119257827 / 12500000000000000000)
noncomputable def bp12776 : ℝ := (2740231796680155627 / 6250000000000000000)
noncomputable def bm12776 : ℝ := (22396806730657842021 / 50000000000000000000)

theorem positive12776 :
    Eplus aL (agent12776.root+dsL) scalar12776.worldRadius world12776.frame
      agent12776.frame tp12776 ≤ -ep12776 := by
  apply positive_check (eT := (115617221431405777769 / 100000000000000000000)) (y := (236972324007153449 / 625000000000000000)) (u := (36526263262451550887 / 25000000000000000000))
  · norm_num [world12776, agent12776, scalar12776, tp12776, tm12776, ep12776, em12776, dsL]
  · norm_num [world12776, agent12776, scalar12776, tp12776, tm12776, ep12776, em12776, dsL]
  · norm_num [world12776, agent12776, scalar12776, tp12776, tm12776, ep12776, em12776, dsL]
  · norm_num [world12776, agent12776, scalar12776, tp12776, tm12776, ep12776, em12776, dsL]
  · norm_num [world12776, agent12776, scalar12776, tp12776, tm12776, ep12776, em12776, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12776, agent12776, tp12776, tm12776, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12776, agent12776, scalar12776, tp12776, tm12776, ep12776, em12776, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12776, agent12776, tp12776, tm12776, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12776, agent12776, scalar12776, tp12776, tm12776, ep12776, em12776, dsL]

theorem negative12776 :
    Eminus aL (agent12776.root+dsL) scalar12776.worldRadius world12776.frame
      agent12776.frame tm12776 ≤ -em12776 := by
  apply negative_check (lo := (34205728258617873859 / 50000000000000000000)) (hi := (68411456517235747719 / 100000000000000000000))
    (y := (-((35839347482302016139 / 50000000000000000000)))) (u := (24415936535086809133 / 50000000000000000000))
  · norm_num [world12776, agent12776, scalar12776, tp12776, tm12776, ep12776, em12776, dsL]
  · norm_num [world12776, agent12776, scalar12776, tp12776, tm12776, ep12776, em12776, dsL]
  · norm_num [world12776, agent12776, scalar12776, tp12776, tm12776, ep12776, em12776, dsL]
  · norm_num [world12776, agent12776, scalar12776, tp12776, tm12776, ep12776, em12776, dsL]
  · norm_num [world12776, agent12776, scalar12776, tp12776, tm12776, ep12776, em12776, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12776, agent12776, tp12776, tm12776, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12776, agent12776, tp12776, tm12776, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12776, agent12776, scalar12776, tp12776, tm12776, ep12776, em12776, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12776, agent12776, tp12776, tm12776, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12776, agent12776, scalar12776, tp12776, tm12776, ep12776, em12776, dsL]

theorem tails12776 :
    exp (-((12776:ℝ)*ep12776)) ≤ scalar12776.upperTail ∧
    exp (-((12776:ℝ)*em12776)) ≤ scalar12776.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12776:ℝ)) (by norm_num [ep12776]) ?_)
      (show bp12776^8 ≤ scalar12776.upperTail by norm_num [bp12776, scalar12776])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12776, bp12776, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12776:ℝ)) (by norm_num [em12776]) ?_)
      (show bm12776^8 ≤ scalar12776.lowerTail by norm_num [bm12776, scalar12776])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12776, bm12776, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12776 :
    agent12776.root+dsL+scalar12776.worldRadius < √(1/100/aL) ∧
    2*(agent12776.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12776, agent12776, scalar12776, tp12776, tm12776, ep12776, em12776, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12776, agent12776, scalar12776, tp12776, tm12776, ep12776, em12776, dsL]

noncomputable def master12776 : MasterCertificate 12776 world12776 agent12776 :=
  master scalar12776 dsL tp12776 tm12776 ep12776 em12776
    (by norm_num [dsL]) (by norm_num [tp12776]) (by norm_num [tm12776])
    (by norm_num [ep12776]) (by norm_num [em12776])
    positive12776 negative12776 tails12776.1 tails12776.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12776.1 tailGuards12776.2

theorem preserves12776 : master12776.toScalarCertificate = scalar12776 := rfl

noncomputable def tp12777 : ℝ := (2323475939 / 10000000000)
noncomputable def tm12777 : ℝ := (-((6078329477 / 10000000000)))
noncomputable def ep12777 : ℝ := (2065320759440419 / 4000000000000000000)
noncomputable def em12777 : ℝ := (1571577867288313 / 3125000000000000000)
noncomputable def bp12777 : ℝ := (8767821913803296857 / 20000000000000000000)
noncomputable def bm12777 : ℝ := (44789250640686787993 / 100000000000000000000)

theorem positive12777 :
    Eplus aL (agent12777.root+dsL) scalar12777.worldRadius world12777.frame
      agent12777.frame tp12777 ≤ -ep12777 := by
  apply positive_check (eT := (57808725169387600999 / 50000000000000000000)) (y := (18958169798578693381 / 50000000000000000000)) (u := (18263271848055267017 / 12500000000000000000))
  · norm_num [world12777, agent12777, scalar12777, tp12777, tm12777, ep12777, em12777, dsL]
  · norm_num [world12777, agent12777, scalar12777, tp12777, tm12777, ep12777, em12777, dsL]
  · norm_num [world12777, agent12777, scalar12777, tp12777, tm12777, ep12777, em12777, dsL]
  · norm_num [world12777, agent12777, scalar12777, tp12777, tm12777, ep12777, em12777, dsL]
  · norm_num [world12777, agent12777, scalar12777, tp12777, tm12777, ep12777, em12777, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12777, agent12777, tp12777, tm12777, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12777, agent12777, scalar12777, tp12777, tm12777, ep12777, em12777, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12777, agent12777, tp12777, tm12777, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12777, agent12777, scalar12777, tp12777, tm12777, ep12777, em12777, dsL]

theorem negative12777 :
    Eminus aL (agent12777.root+dsL) scalar12777.worldRadius world12777.frame
      agent12777.frame tm12777 ≤ -em12777 := by
  apply negative_check (lo := (68411271059688218977 / 100000000000000000000)) (hi := (34205635529844109489 / 50000000000000000000))
    (y := (-((71678739873192782617 / 100000000000000000000)))) (u := (24415925570236743127 / 50000000000000000000))
  · norm_num [world12777, agent12777, scalar12777, tp12777, tm12777, ep12777, em12777, dsL]
  · norm_num [world12777, agent12777, scalar12777, tp12777, tm12777, ep12777, em12777, dsL]
  · norm_num [world12777, agent12777, scalar12777, tp12777, tm12777, ep12777, em12777, dsL]
  · norm_num [world12777, agent12777, scalar12777, tp12777, tm12777, ep12777, em12777, dsL]
  · norm_num [world12777, agent12777, scalar12777, tp12777, tm12777, ep12777, em12777, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12777, agent12777, tp12777, tm12777, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12777, agent12777, tp12777, tm12777, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12777, agent12777, scalar12777, tp12777, tm12777, ep12777, em12777, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12777, agent12777, tp12777, tm12777, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12777, agent12777, scalar12777, tp12777, tm12777, ep12777, em12777, dsL]

theorem tails12777 :
    exp (-((12777:ℝ)*ep12777)) ≤ scalar12777.upperTail ∧
    exp (-((12777:ℝ)*em12777)) ≤ scalar12777.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12777:ℝ)) (by norm_num [ep12777]) ?_)
      (show bp12777^8 ≤ scalar12777.upperTail by norm_num [bp12777, scalar12777])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12777, bp12777, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12777:ℝ)) (by norm_num [em12777]) ?_)
      (show bm12777^8 ≤ scalar12777.lowerTail by norm_num [bm12777, scalar12777])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12777, bm12777, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12777 :
    agent12777.root+dsL+scalar12777.worldRadius < √(1/100/aL) ∧
    2*(agent12777.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12777, agent12777, scalar12777, tp12777, tm12777, ep12777, em12777, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12777, agent12777, scalar12777, tp12777, tm12777, ep12777, em12777, dsL]

noncomputable def master12777 : MasterCertificate 12777 world12777 agent12777 :=
  master scalar12777 dsL tp12777 tm12777 ep12777 em12777
    (by norm_num [dsL]) (by norm_num [tp12777]) (by norm_num [tm12777])
    (by norm_num [ep12777]) (by norm_num [em12777])
    positive12777 negative12777 tails12777.1 tails12777.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12777.1 tailGuards12777.2

theorem preserves12777 : master12777.toScalarCertificate = scalar12777 := rfl

noncomputable def tp12778 : ℝ := (2323558421 / 10000000000)
noncomputable def tm12778 : ℝ := (-((3039252889 / 5000000000)))
noncomputable def ep12778 : ℝ := (10327108893696273 / 20000000000000000000)
noncomputable def em12778 : ℝ := (10058530549653573 / 20000000000000000000)
noncomputable def bp12778 : ℝ := (43834511984361832847 / 100000000000000000000)
noncomputable def bm12778 : ℝ := (5598111161671686251 / 12500000000000000000)

theorem positive12778 :
    Eplus aL (agent12778.root+dsL) scalar12778.worldRadius world12778.frame
      agent12778.frame tp12778 ≤ -ep12778 := by
  apply positive_check (eT := (115617678636334387089 / 100000000000000000000)) (y := (18958553072929982403 / 50000000000000000000)) (u := (146107294763721920521 / 100000000000000000000))
  · norm_num [world12778, agent12778, scalar12778, tp12778, tm12778, ep12778, em12778, dsL]
  · norm_num [world12778, agent12778, scalar12778, tp12778, tm12778, ep12778, em12778, dsL]
  · norm_num [world12778, agent12778, scalar12778, tp12778, tm12778, ep12778, em12778, dsL]
  · norm_num [world12778, agent12778, scalar12778, tp12778, tm12778, ep12778, em12778, dsL]
  · norm_num [world12778, agent12778, scalar12778, tp12778, tm12778, ep12778, em12778, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12778, agent12778, tp12778, tm12778, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12778, agent12778, scalar12778, tp12778, tm12778, ep12778, em12778, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12778, agent12778, tp12778, tm12778, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12778, agent12778, scalar12778, tp12778, tm12778, ep12778, em12778, dsL]

theorem negative12778 :
    Eminus aL (agent12778.root+dsL) scalar12778.worldRadius world12778.frame
      agent12778.frame tm12778 ≤ -em12778 := by
  apply negative_check (lo := (34205543169903269113 / 50000000000000000000)) (hi := (68411086339806538227 / 100000000000000000000))
    (y := (-((8959847923023107427 / 12500000000000000000)))) (u := (24415914946627614003 / 50000000000000000000))
  · norm_num [world12778, agent12778, scalar12778, tp12778, tm12778, ep12778, em12778, dsL]
  · norm_num [world12778, agent12778, scalar12778, tp12778, tm12778, ep12778, em12778, dsL]
  · norm_num [world12778, agent12778, scalar12778, tp12778, tm12778, ep12778, em12778, dsL]
  · norm_num [world12778, agent12778, scalar12778, tp12778, tm12778, ep12778, em12778, dsL]
  · norm_num [world12778, agent12778, scalar12778, tp12778, tm12778, ep12778, em12778, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12778, agent12778, tp12778, tm12778, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12778, agent12778, tp12778, tm12778, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12778, agent12778, scalar12778, tp12778, tm12778, ep12778, em12778, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12778, agent12778, tp12778, tm12778, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12778, agent12778, scalar12778, tp12778, tm12778, ep12778, em12778, dsL]

theorem tails12778 :
    exp (-((12778:ℝ)*ep12778)) ≤ scalar12778.upperTail ∧
    exp (-((12778:ℝ)*em12778)) ≤ scalar12778.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12778:ℝ)) (by norm_num [ep12778]) ?_)
      (show bp12778^8 ≤ scalar12778.upperTail by norm_num [bp12778, scalar12778])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12778, bp12778, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12778:ℝ)) (by norm_num [em12778]) ?_)
      (show bm12778^8 ≤ scalar12778.lowerTail by norm_num [bm12778, scalar12778])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12778, bm12778, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12778 :
    agent12778.root+dsL+scalar12778.worldRadius < √(1/100/aL) ∧
    2*(agent12778.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12778, agent12778, scalar12778, tp12778, tm12778, ep12778, em12778, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12778, agent12778, scalar12778, tp12778, tm12778, ep12778, em12778, dsL]

noncomputable def master12778 : MasterCertificate 12778 world12778 agent12778 :=
  master scalar12778 dsL tp12778 tm12778 ep12778 em12778
    (by norm_num [dsL]) (by norm_num [tp12778]) (by norm_num [tm12778])
    (by norm_num [ep12778]) (by norm_num [em12778])
    positive12778 negative12778 tails12778.1 tails12778.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12778.1 tailGuards12778.2

theorem preserves12778 : master12778.toScalarCertificate = scalar12778 := rfl

noncomputable def tp12779 : ℝ := (464728169 / 2000000000)
noncomputable def tm12779 : ℝ := (-((6078682121 / 10000000000)))
noncomputable def ep12779 : ℝ := (51638069059054893 / 100000000000000000000)
noncomputable def em12779 : ℝ := (12573703225778901 / 25000000000000000000)
noncomputable def bp12779 : ℝ := (8765983045917535287 / 20000000000000000000)
noncomputable def bm12779 : ℝ := (22390264364910648789 / 50000000000000000000)

theorem positive12779 :
    Eplus aL (agent12779.root+dsL) scalar12779.worldRadius world12779.frame
      agent12779.frame tp12779 ≤ -ep12779 := by
  apply positive_check (eT := (23123581309594594217 / 20000000000000000000)) (y := (37917871983462154799 / 100000000000000000000)) (u := (14610841371260942387 / 10000000000000000000))
  · norm_num [world12779, agent12779, scalar12779, tp12779, tm12779, ep12779, em12779, dsL]
  · norm_num [world12779, agent12779, scalar12779, tp12779, tm12779, ep12779, em12779, dsL]
  · norm_num [world12779, agent12779, scalar12779, tp12779, tm12779, ep12779, em12779, dsL]
  · norm_num [world12779, agent12779, scalar12779, tp12779, tm12779, ep12779, em12779, dsL]
  · norm_num [world12779, agent12779, scalar12779, tp12779, tm12779, ep12779, em12779, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12779, agent12779, tp12779, tm12779, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12779, agent12779, scalar12779, tp12779, tm12779, ep12779, em12779, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12779, agent12779, tp12779, tm12779, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12779, agent12779, scalar12779, tp12779, tm12779, ep12779, em12779, dsL]

theorem negative12779 :
    Eminus aL (agent12779.root+dsL) scalar12779.worldRadius world12779.frame
      agent12779.frame tm12779 ≤ -em12779 := by
  apply negative_check (lo := (68410901383386841601 / 100000000000000000000)) (hi := (34205450691693420801 / 50000000000000000000))
    (y := (-((71678827842279403603 / 100000000000000000000)))) (u := (9766361636711790453 / 20000000000000000000))
  · norm_num [world12779, agent12779, scalar12779, tp12779, tm12779, ep12779, em12779, dsL]
  · norm_num [world12779, agent12779, scalar12779, tp12779, tm12779, ep12779, em12779, dsL]
  · norm_num [world12779, agent12779, scalar12779, tp12779, tm12779, ep12779, em12779, dsL]
  · norm_num [world12779, agent12779, scalar12779, tp12779, tm12779, ep12779, em12779, dsL]
  · norm_num [world12779, agent12779, scalar12779, tp12779, tm12779, ep12779, em12779, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12779, agent12779, tp12779, tm12779, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12779, agent12779, tp12779, tm12779, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12779, agent12779, scalar12779, tp12779, tm12779, ep12779, em12779, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12779, agent12779, tp12779, tm12779, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12779, agent12779, scalar12779, tp12779, tm12779, ep12779, em12779, dsL]

theorem tails12779 :
    exp (-((12779:ℝ)*ep12779)) ≤ scalar12779.upperTail ∧
    exp (-((12779:ℝ)*em12779)) ≤ scalar12779.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12779:ℝ)) (by norm_num [ep12779]) ?_)
      (show bp12779^8 ≤ scalar12779.upperTail by norm_num [bp12779, scalar12779])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12779, bp12779, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12779:ℝ)) (by norm_num [em12779]) ?_)
      (show bm12779^8 ≤ scalar12779.lowerTail by norm_num [bm12779, scalar12779])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12779, bm12779, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12779 :
    agent12779.root+dsL+scalar12779.worldRadius < √(1/100/aL) ∧
    2*(agent12779.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12779, agent12779, scalar12779, tp12779, tm12779, ep12779, em12779, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12779, agent12779, scalar12779, tp12779, tm12779, ep12779, em12779, dsL]

noncomputable def master12779 : MasterCertificate 12779 world12779 agent12779 :=
  master scalar12779 dsL tp12779 tm12779 ep12779 em12779
    (by norm_num [dsL]) (by norm_num [tp12779]) (by norm_num [tm12779])
    (by norm_num [ep12779]) (by norm_num [em12779])
    positive12779 negative12779 tails12779.1 tails12779.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12779.1 tailGuards12779.2

theorem preserves12779 : master12779.toScalarCertificate = scalar12779 := rfl

noncomputable def tp12780 : ℝ := (2323796957 / 10000000000)
noncomputable def tm12780 : ℝ := (-((6079081233 / 10000000000)))
noncomputable def ep12780 : ℝ := (25820998725986451 / 50000000000000000000)
noncomputable def em12780 : ℝ := (50298503192572891 / 100000000000000000000)
noncomputable def bp12780 : ℝ := (43824335875965298239 / 100000000000000000000)
noncomputable def bm12780 : ℝ := (44775073858212802283 / 100000000000000000000)

theorem positive12780 :
    Eplus aL (agent12780.root+dsL) scalar12780.worldRadius world12780.frame
      agent12780.frame tp12780 ≤ -ep12780 := by
  apply positive_check (eT := (28904666642359264781 / 25000000000000000000)) (y := (37917915722124418643 / 100000000000000000000)) (u := (36527119404622253119 / 25000000000000000000))
  · norm_num [world12780, agent12780, scalar12780, tp12780, tm12780, ep12780, em12780, dsL]
  · norm_num [world12780, agent12780, scalar12780, tp12780, tm12780, ep12780, em12780, dsL]
  · norm_num [world12780, agent12780, scalar12780, tp12780, tm12780, ep12780, em12780, dsL]
  · norm_num [world12780, agent12780, scalar12780, tp12780, tm12780, ep12780, em12780, dsL]
  · norm_num [world12780, agent12780, scalar12780, tp12780, tm12780, ep12780, em12780, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12780, agent12780, tp12780, tm12780, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12780, agent12780, scalar12780, tp12780, tm12780, ep12780, em12780, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12780, agent12780, tp12780, tm12780, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12780, agent12780, scalar12780, tp12780, tm12780, ep12780, em12780, dsL]

theorem negative12780 :
    Eminus aL (agent12780.root+dsL) scalar12780.worldRadius world12780.frame
      agent12780.frame tm12780 ≤ -em12780 := by
  apply negative_check (lo := (17102441152950531897 / 25000000000000000000)) (hi := (68409764611802127589 / 100000000000000000000))
    (y := (-((14335394955200093161 / 20000000000000000000)))) (u := (48832713077713915713 / 100000000000000000000))
  · norm_num [world12780, agent12780, scalar12780, tp12780, tm12780, ep12780, em12780, dsL]
  · norm_num [world12780, agent12780, scalar12780, tp12780, tm12780, ep12780, em12780, dsL]
  · norm_num [world12780, agent12780, scalar12780, tp12780, tm12780, ep12780, em12780, dsL]
  · norm_num [world12780, agent12780, scalar12780, tp12780, tm12780, ep12780, em12780, dsL]
  · norm_num [world12780, agent12780, scalar12780, tp12780, tm12780, ep12780, em12780, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12780, agent12780, tp12780, tm12780, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12780, agent12780, tp12780, tm12780, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12780, agent12780, scalar12780, tp12780, tm12780, ep12780, em12780, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12780, agent12780, tp12780, tm12780, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12780, agent12780, scalar12780, tp12780, tm12780, ep12780, em12780, dsL]

theorem tails12780 :
    exp (-((12780:ℝ)*ep12780)) ≤ scalar12780.upperTail ∧
    exp (-((12780:ℝ)*em12780)) ≤ scalar12780.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12780:ℝ)) (by norm_num [ep12780]) ?_)
      (show bp12780^8 ≤ scalar12780.upperTail by norm_num [bp12780, scalar12780])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12780, bp12780, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12780:ℝ)) (by norm_num [em12780]) ?_)
      (show bm12780^8 ≤ scalar12780.lowerTail by norm_num [bm12780, scalar12780])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12780, bm12780, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12780 :
    agent12780.root+dsL+scalar12780.worldRadius < √(1/100/aL) ∧
    2*(agent12780.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12780, agent12780, scalar12780, tp12780, tm12780, ep12780, em12780, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12780, agent12780, scalar12780, tp12780, tm12780, ep12780, em12780, dsL]

noncomputable def master12780 : MasterCertificate 12780 world12780 agent12780 :=
  master scalar12780 dsL tp12780 tm12780 ep12780 em12780
    (by norm_num [dsL]) (by norm_num [tp12780]) (by norm_num [tm12780])
    (by norm_num [ep12780]) (by norm_num [em12780])
    positive12780 negative12780 tails12780.1 tails12780.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12780.1 tailGuards12780.2

theorem preserves12780 : master12780.toScalarCertificate = scalar12780 := rfl

noncomputable def tp12781 : ℝ := (464775857 / 2000000000)
noncomputable def tm12781 : ℝ := (-((1215851449 / 2000000000)))
noncomputable def ep12781 : ℝ := (6455564931457539 / 12500000000000000000)
noncomputable def em12781 : ℝ := (50300660935251459 / 100000000000000000000)
noncomputable def bp12781 : ℝ := (43819741372107652841 / 100000000000000000000)
noncomputable def bm12781 : ℝ := (4477071540651643297 / 10000000000000000000)

theorem positive12781 :
    Eplus aL (agent12781.root+dsL) scalar12781.worldRadius world12781.frame
      agent12781.frame tp12781 ≤ -ep12781 := by
  apply positive_check (eT := (28904723460763182349 / 25000000000000000000)) (y := (18959340355314854001 / 50000000000000000000)) (u := (73054797667911623153 / 50000000000000000000))
  · norm_num [world12781, agent12781, scalar12781, tp12781, tm12781, ep12781, em12781, dsL]
  · norm_num [world12781, agent12781, scalar12781, tp12781, tm12781, ep12781, em12781, dsL]
  · norm_num [world12781, agent12781, scalar12781, tp12781, tm12781, ep12781, em12781, dsL]
  · norm_num [world12781, agent12781, scalar12781, tp12781, tm12781, ep12781, em12781, dsL]
  · norm_num [world12781, agent12781, scalar12781, tp12781, tm12781, ep12781, em12781, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12781, agent12781, tp12781, tm12781, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12781, agent12781, scalar12781, tp12781, tm12781, ep12781, em12781, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12781, agent12781, tp12781, tm12781, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12781, agent12781, scalar12781, tp12781, tm12781, ep12781, em12781, dsL]

theorem negative12781 :
    Eminus aL (agent12781.root+dsL) scalar12781.worldRadius world12781.frame
      agent12781.frame tm12781 ≤ -em12781 := by
  apply negative_check (lo := (68409580978840666127 / 100000000000000000000)) (hi := (4275598811177541633 / 6250000000000000000))
    (y := (-((35838508783978521763 / 50000000000000000000)))) (u := (48832692181245010779 / 100000000000000000000))
  · norm_num [world12781, agent12781, scalar12781, tp12781, tm12781, ep12781, em12781, dsL]
  · norm_num [world12781, agent12781, scalar12781, tp12781, tm12781, ep12781, em12781, dsL]
  · norm_num [world12781, agent12781, scalar12781, tp12781, tm12781, ep12781, em12781, dsL]
  · norm_num [world12781, agent12781, scalar12781, tp12781, tm12781, ep12781, em12781, dsL]
  · norm_num [world12781, agent12781, scalar12781, tp12781, tm12781, ep12781, em12781, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12781, agent12781, tp12781, tm12781, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12781, agent12781, tp12781, tm12781, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12781, agent12781, scalar12781, tp12781, tm12781, ep12781, em12781, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12781, agent12781, tp12781, tm12781, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12781, agent12781, scalar12781, tp12781, tm12781, ep12781, em12781, dsL]

theorem tails12781 :
    exp (-((12781:ℝ)*ep12781)) ≤ scalar12781.upperTail ∧
    exp (-((12781:ℝ)*em12781)) ≤ scalar12781.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12781:ℝ)) (by norm_num [ep12781]) ?_)
      (show bp12781^8 ≤ scalar12781.upperTail by norm_num [bp12781, scalar12781])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12781, bp12781, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12781:ℝ)) (by norm_num [em12781]) ?_)
      (show bm12781^8 ≤ scalar12781.lowerTail by norm_num [bm12781, scalar12781])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12781, bm12781, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12781 :
    agent12781.root+dsL+scalar12781.worldRadius < √(1/100/aL) ∧
    2*(agent12781.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12781, agent12781, scalar12781, tp12781, tm12781, ep12781, em12781, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12781, agent12781, scalar12781, tp12781, tm12781, ep12781, em12781, dsL]

noncomputable def master12781 : MasterCertificate 12781 world12781 agent12781 :=
  master scalar12781 dsL tp12781 tm12781 ep12781 em12781
    (by norm_num [dsL]) (by norm_num [tp12781]) (by norm_num [tm12781])
    (by norm_num [ep12781]) (by norm_num [em12781])
    positive12781 negative12781 tails12781.1 tails12781.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12781.1 tailGuards12781.2

theorem preserves12781 : master12781.toScalarCertificate = scalar12781 := rfl

noncomputable def tp12782 : ℝ := (464792321 / 2000000000)
noncomputable def tm12782 : ℝ := (-((759929167 / 1250000000)))
noncomputable def ep12782 : ℝ := (51647039777847953 / 100000000000000000000)
noncomputable def em12782 : ℝ := (6287852142119811 / 12500000000000000000)
noncomputable def bp12782 : ℝ := (4381514824522360757 / 10000000000000000000)
noncomputable def bm12782 : ℝ := (22383179119888663939 / 50000000000000000000)

theorem positive12782 :
    Eplus aL (agent12782.root+dsL) scalar12782.worldRadius world12782.frame
      agent12782.frame tp12782 ≤ -ep12782 := by
  apply positive_check (eT := (23123824218360553571 / 20000000000000000000)) (y := (9479861478055185577 / 25000000000000000000)) (u := (36527678343262255919 / 25000000000000000000))
  · norm_num [world12782, agent12782, scalar12782, tp12782, tm12782, ep12782, em12782, dsL]
  · norm_num [world12782, agent12782, scalar12782, tp12782, tm12782, ep12782, em12782, dsL]
  · norm_num [world12782, agent12782, scalar12782, tp12782, tm12782, ep12782, em12782, dsL]
  · norm_num [world12782, agent12782, scalar12782, tp12782, tm12782, ep12782, em12782, dsL]
  · norm_num [world12782, agent12782, scalar12782, tp12782, tm12782, ep12782, em12782, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12782, agent12782, tp12782, tm12782, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12782, agent12782, scalar12782, tp12782, tm12782, ep12782, em12782, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12782, agent12782, tp12782, tm12782, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12782, agent12782, scalar12782, tp12782, tm12782, ep12782, em12782, dsL]

theorem negative12782 :
    Eminus aL (agent12782.root+dsL) scalar12782.worldRadius world12782.frame
      agent12782.frame tm12782 ≤ -em12782 := by
  apply negative_check (lo := (68409396951284620267 / 100000000000000000000)) (hi := (17102349237821155067 / 25000000000000000000))
    (y := (-((8959632691667729523 / 12500000000000000000)))) (u := (195330682847074833 / 400000000000000000))
  · norm_num [world12782, agent12782, scalar12782, tp12782, tm12782, ep12782, em12782, dsL]
  · norm_num [world12782, agent12782, scalar12782, tp12782, tm12782, ep12782, em12782, dsL]
  · norm_num [world12782, agent12782, scalar12782, tp12782, tm12782, ep12782, em12782, dsL]
  · norm_num [world12782, agent12782, scalar12782, tp12782, tm12782, ep12782, em12782, dsL]
  · norm_num [world12782, agent12782, scalar12782, tp12782, tm12782, ep12782, em12782, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12782, agent12782, tp12782, tm12782, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12782, agent12782, tp12782, tm12782, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12782, agent12782, scalar12782, tp12782, tm12782, ep12782, em12782, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12782, agent12782, tp12782, tm12782, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12782, agent12782, scalar12782, tp12782, tm12782, ep12782, em12782, dsL]

theorem tails12782 :
    exp (-((12782:ℝ)*ep12782)) ≤ scalar12782.upperTail ∧
    exp (-((12782:ℝ)*em12782)) ≤ scalar12782.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12782:ℝ)) (by norm_num [ep12782]) ?_)
      (show bp12782^8 ≤ scalar12782.upperTail by norm_num [bp12782, scalar12782])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12782, bp12782, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12782:ℝ)) (by norm_num [em12782]) ?_)
      (show bm12782^8 ≤ scalar12782.lowerTail by norm_num [bm12782, scalar12782])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12782, bm12782, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12782 :
    agent12782.root+dsL+scalar12782.worldRadius < √(1/100/aL) ∧
    2*(agent12782.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12782, agent12782, scalar12782, tp12782, tm12782, ep12782, em12782, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12782, agent12782, scalar12782, tp12782, tm12782, ep12782, em12782, dsL]

noncomputable def master12782 : MasterCertificate 12782 world12782 agent12782 :=
  master scalar12782 dsL tp12782 tm12782 ep12782 em12782
    (by norm_num [dsL]) (by norm_num [tp12782]) (by norm_num [tm12782])
    (by norm_num [ep12782]) (by norm_num [em12782])
    positive12782 negative12782 tails12782.1 tails12782.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12782.1 tailGuards12782.2

theorem preserves12782 : master12782.toScalarCertificate = scalar12782 := rfl

noncomputable def tp12783 : ℝ := (2324043867 / 10000000000)
noncomputable def tm12783 : ℝ := (-((94993893 / 156250000)))
noncomputable def ep12783 : ℝ := (403512179145197 / 781250000000000000)
noncomputable def em12783 : ℝ := (25152486132993843 / 50000000000000000000)
noncomputable def bp12783 : ℝ := (21905278072601266729 / 50000000000000000000)
noncomputable def bm12783 : ℝ := (11190500505754692981 / 25000000000000000000)

theorem positive12783 :
    Eplus aL (agent12783.root+dsL) scalar12783.worldRadius world12783.frame
      agent12783.frame tp12783 ≤ -ep12783 := by
  apply positive_check (eT := (28904836988664309161 / 25000000000000000000)) (y := (37920210503046450243 / 100000000000000000000)) (u := (146111830526429671113 / 100000000000000000000))
  · norm_num [world12783, agent12783, scalar12783, tp12783, tm12783, ep12783, em12783, dsL]
  · norm_num [world12783, agent12783, scalar12783, tp12783, tm12783, ep12783, em12783, dsL]
  · norm_num [world12783, agent12783, scalar12783, tp12783, tm12783, ep12783, em12783, dsL]
  · norm_num [world12783, agent12783, scalar12783, tp12783, tm12783, ep12783, em12783, dsL]
  · norm_num [world12783, agent12783, scalar12783, tp12783, tm12783, ep12783, em12783, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12783, agent12783, tp12783, tm12783, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12783, agent12783, scalar12783, tp12783, tm12783, ep12783, em12783, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12783, agent12783, tp12783, tm12783, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12783, agent12783, scalar12783, tp12783, tm12783, ep12783, em12783, dsL]

theorem negative12783 :
    Eminus aL (agent12783.root+dsL) scalar12783.worldRadius world12783.frame
      agent12783.frame tm12783 ≤ -em12783 := by
  apply negative_check (lo := (2137787938796890309 / 3125000000000000000)) (hi := (68409214041500489889 / 100000000000000000000))
    (y := (-((7167710378039189641 / 10000000000000000000)))) (u := (48832650081410224763 / 100000000000000000000))
  · norm_num [world12783, agent12783, scalar12783, tp12783, tm12783, ep12783, em12783, dsL]
  · norm_num [world12783, agent12783, scalar12783, tp12783, tm12783, ep12783, em12783, dsL]
  · norm_num [world12783, agent12783, scalar12783, tp12783, tm12783, ep12783, em12783, dsL]
  · norm_num [world12783, agent12783, scalar12783, tp12783, tm12783, ep12783, em12783, dsL]
  · norm_num [world12783, agent12783, scalar12783, tp12783, tm12783, ep12783, em12783, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12783, agent12783, tp12783, tm12783, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12783, agent12783, tp12783, tm12783, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12783, agent12783, scalar12783, tp12783, tm12783, ep12783, em12783, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12783, agent12783, tp12783, tm12783, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12783, agent12783, scalar12783, tp12783, tm12783, ep12783, em12783, dsL]

theorem tails12783 :
    exp (-((12783:ℝ)*ep12783)) ≤ scalar12783.upperTail ∧
    exp (-((12783:ℝ)*em12783)) ≤ scalar12783.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12783:ℝ)) (by norm_num [ep12783]) ?_)
      (show bp12783^8 ≤ scalar12783.upperTail by norm_num [bp12783, scalar12783])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12783, bp12783, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12783:ℝ)) (by norm_num [em12783]) ?_)
      (show bm12783^8 ≤ scalar12783.lowerTail by norm_num [bm12783, scalar12783])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12783, bm12783, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12783 :
    agent12783.root+dsL+scalar12783.worldRadius < √(1/100/aL) ∧
    2*(agent12783.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12783, agent12783, scalar12783, tp12783, tm12783, ep12783, em12783, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12783, agent12783, scalar12783, tp12783, tm12783, ep12783, em12783, dsL]

noncomputable def master12783 : MasterCertificate 12783 world12783 agent12783 :=
  master scalar12783 dsL tp12783 tm12783 ep12783 em12783
    (by norm_num [dsL]) (by norm_num [tp12783]) (by norm_num [tm12783])
    (by norm_num [ep12783]) (by norm_num [em12783])
    positive12783 negative12783 tails12783.1 tails12783.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12783.1 tailGuards12783.2

theorem preserves12783 : master12783.toScalarCertificate = scalar12783 := rfl

noncomputable def tp12784 : ℝ := (581031527 / 2500000000)
noncomputable def tm12784 : ℝ := (-((3039892461 / 5000000000)))
noncomputable def ep12784 : ℝ := (25826038595840561 / 50000000000000000000)
noncomputable def em12784 : ℝ := (25153563277617183 / 50000000000000000000)
noncomputable def bp12784 : ℝ := (21902982437371741367 / 50000000000000000000)
noncomputable def bm12784 : ℝ := (44757646589652938619 / 100000000000000000000)

theorem positive12784 :
    Eplus aL (agent12784.root+dsL) scalar12784.worldRadius world12784.frame
      agent12784.frame tp12784 ≤ -ep12784 := by
  apply positive_check (eT := (57809787349382462571 / 50000000000000000000)) (y := (18960487515342224801 / 50000000000000000000)) (u := (146112947596026579913 / 100000000000000000000))
  · norm_num [world12784, agent12784, scalar12784, tp12784, tm12784, ep12784, em12784, dsL]
  · norm_num [world12784, agent12784, scalar12784, tp12784, tm12784, ep12784, em12784, dsL]
  · norm_num [world12784, agent12784, scalar12784, tp12784, tm12784, ep12784, em12784, dsL]
  · norm_num [world12784, agent12784, scalar12784, tp12784, tm12784, ep12784, em12784, dsL]
  · norm_num [world12784, agent12784, scalar12784, tp12784, tm12784, ep12784, em12784, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12784, agent12784, tp12784, tm12784, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12784, agent12784, scalar12784, tp12784, tm12784, ep12784, em12784, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12784, agent12784, tp12784, tm12784, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12784, agent12784, scalar12784, tp12784, tm12784, ep12784, em12784, dsL]

theorem negative12784 :
    Eminus aL (agent12784.root+dsL) scalar12784.worldRadius world12784.frame
      agent12784.frame tm12784 ≤ -em12784 := by
  apply negative_check (lo := (13681806254231874883 / 20000000000000000000)) (hi := (4275564454447460901 / 6250000000000000000))
    (y := (-((14335429223993005013 / 20000000000000000000)))) (u := (976652588117580197 / 2000000000000000000))
  · norm_num [world12784, agent12784, scalar12784, tp12784, tm12784, ep12784, em12784, dsL]
  · norm_num [world12784, agent12784, scalar12784, tp12784, tm12784, ep12784, em12784, dsL]
  · norm_num [world12784, agent12784, scalar12784, tp12784, tm12784, ep12784, em12784, dsL]
  · norm_num [world12784, agent12784, scalar12784, tp12784, tm12784, ep12784, em12784, dsL]
  · norm_num [world12784, agent12784, scalar12784, tp12784, tm12784, ep12784, em12784, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12784, agent12784, tp12784, tm12784, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12784, agent12784, tp12784, tm12784, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12784, agent12784, scalar12784, tp12784, tm12784, ep12784, em12784, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12784, agent12784, tp12784, tm12784, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12784, agent12784, scalar12784, tp12784, tm12784, ep12784, em12784, dsL]

theorem tails12784 :
    exp (-((12784:ℝ)*ep12784)) ≤ scalar12784.upperTail ∧
    exp (-((12784:ℝ)*em12784)) ≤ scalar12784.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12784:ℝ)) (by norm_num [ep12784]) ?_)
      (show bp12784^8 ≤ scalar12784.upperTail by norm_num [bp12784, scalar12784])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12784, bp12784, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12784:ℝ)) (by norm_num [em12784]) ?_)
      (show bm12784^8 ≤ scalar12784.lowerTail by norm_num [bm12784, scalar12784])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12784, bm12784, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12784 :
    agent12784.root+dsL+scalar12784.worldRadius < √(1/100/aL) ∧
    2*(agent12784.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12784, agent12784, scalar12784, tp12784, tm12784, ep12784, em12784, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12784, agent12784, scalar12784, tp12784, tm12784, ep12784, em12784, dsL]

noncomputable def master12784 : MasterCertificate 12784 world12784 agent12784 :=
  master scalar12784 dsL tp12784 tm12784 ep12784 em12784
    (by norm_num [dsL]) (by norm_num [tp12784]) (by norm_num [tm12784])
    (by norm_num [ep12784]) (by norm_num [em12784])
    positive12784 negative12784 tails12784.1 tails12784.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12784.1 tailGuards12784.2

theorem preserves12784 : master12784.toScalarCertificate = scalar12784 := rfl

noncomputable def tp12785 : ℝ := (464841663 / 2000000000)
noncomputable def tm12785 : ℝ := (-((6079960647 / 10000000000)))
noncomputable def ep12785 : ℝ := (6456824244166401 / 12500000000000000000)
noncomputable def em12785 : ℝ := (6288659935836881 / 12500000000000000000)
noncomputable def bp12785 : ℝ := (21900687429648266937 / 50000000000000000000)
noncomputable def bm12785 : ℝ := (5594161538769710617 / 12500000000000000000)

theorem positive12785 :
    Eplus aL (agent12785.root+dsL) scalar12785.worldRadius world12785.frame
      agent12785.frame tp12785 ≤ -ep12785 := by
  apply positive_check (eT := (115619801230281662271 / 100000000000000000000)) (y := (37921739265186947111 / 100000000000000000000)) (u := (29222812849170326207 / 20000000000000000000))
  · norm_num [world12785, agent12785, scalar12785, tp12785, tm12785, ep12785, em12785, dsL]
  · norm_num [world12785, agent12785, scalar12785, tp12785, tm12785, ep12785, em12785, dsL]
  · norm_num [world12785, agent12785, scalar12785, tp12785, tm12785, ep12785, em12785, dsL]
  · norm_num [world12785, agent12785, scalar12785, tp12785, tm12785, ep12785, em12785, dsL]
  · norm_num [world12785, agent12785, scalar12785, tp12785, tm12785, ep12785, em12785, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12785, agent12785, tp12785, tm12785, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12785, agent12785, scalar12785, tp12785, tm12785, ep12785, em12785, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12785, agent12785, tp12785, tm12785, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12785, agent12785, scalar12785, tp12785, tm12785, ep12785, em12785, dsL]

theorem negative12785 :
    Eminus aL (agent12785.root+dsL) scalar12785.worldRadius world12785.frame
      agent12785.frame tm12785 ≤ -em12785 := by
  apply negative_check (lo := (13681769727193515189 / 20000000000000000000)) (hi := (34204424317983787973 / 50000000000000000000))
    (y := (-((71677188555025466663 / 100000000000000000000)))) (u := (12208152170931900743 / 25000000000000000000))
  · norm_num [world12785, agent12785, scalar12785, tp12785, tm12785, ep12785, em12785, dsL]
  · norm_num [world12785, agent12785, scalar12785, tp12785, tm12785, ep12785, em12785, dsL]
  · norm_num [world12785, agent12785, scalar12785, tp12785, tm12785, ep12785, em12785, dsL]
  · norm_num [world12785, agent12785, scalar12785, tp12785, tm12785, ep12785, em12785, dsL]
  · norm_num [world12785, agent12785, scalar12785, tp12785, tm12785, ep12785, em12785, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12785, agent12785, tp12785, tm12785, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12785, agent12785, tp12785, tm12785, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12785, agent12785, scalar12785, tp12785, tm12785, ep12785, em12785, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12785, agent12785, tp12785, tm12785, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12785, agent12785, scalar12785, tp12785, tm12785, ep12785, em12785, dsL]

theorem tails12785 :
    exp (-((12785:ℝ)*ep12785)) ≤ scalar12785.upperTail ∧
    exp (-((12785:ℝ)*em12785)) ≤ scalar12785.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12785:ℝ)) (by norm_num [ep12785]) ?_)
      (show bp12785^8 ≤ scalar12785.upperTail by norm_num [bp12785, scalar12785])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12785, bp12785, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12785:ℝ)) (by norm_num [em12785]) ?_)
      (show bm12785^8 ≤ scalar12785.lowerTail by norm_num [bm12785, scalar12785])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12785, bm12785, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12785 :
    agent12785.root+dsL+scalar12785.worldRadius < √(1/100/aL) ∧
    2*(agent12785.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12785, agent12785, scalar12785, tp12785, tm12785, ep12785, em12785, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12785, agent12785, scalar12785, tp12785, tm12785, ep12785, em12785, dsL]

noncomputable def master12785 : MasterCertificate 12785 world12785 agent12785 :=
  master scalar12785 dsL tp12785 tm12785 ep12785 em12785
    (by norm_num [dsL]) (by norm_num [tp12785]) (by norm_num [tm12785])
    (by norm_num [ep12785]) (by norm_num [em12785])
    positive12785 negative12785 tails12785.1 tails12785.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12785.1 tailGuards12785.2

theorem preserves12785 : master12785.toScalarCertificate = scalar12785 := rfl

noncomputable def tp12786 : ℝ := (2324290479 / 10000000000)
noncomputable def tm12786 : ℝ := (-((760017063 / 1250000000)))
noncomputable def ep12786 : ℝ := (51657109203009757 / 100000000000000000000)
noncomputable def em12786 : ℝ := (402491447901139 / 800000000000000000)
noncomputable def bp12786 : ℝ := (43796786107582051503 / 100000000000000000000)
noncomputable def bm12786 : ℝ := (22374469618260572273 / 50000000000000000000)

theorem positive12786 :
    Eplus aL (agent12786.root+dsL) scalar12786.worldRadius world12786.frame
      agent12786.frame tp12786 ≤ -ep12786 := by
  apply positive_check (eT := (115620027484276931347 / 100000000000000000000)) (y := (1185078226608390041 / 3125000000000000000)) (u := (18264397567690253609 / 12500000000000000000))
  · norm_num [world12786, agent12786, scalar12786, tp12786, tm12786, ep12786, em12786, dsL]
  · norm_num [world12786, agent12786, scalar12786, tp12786, tm12786, ep12786, em12786, dsL]
  · norm_num [world12786, agent12786, scalar12786, tp12786, tm12786, ep12786, em12786, dsL]
  · norm_num [world12786, agent12786, scalar12786, tp12786, tm12786, ep12786, em12786, dsL]
  · norm_num [world12786, agent12786, scalar12786, tp12786, tm12786, ep12786, em12786, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12786, agent12786, tp12786, tm12786, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12786, agent12786, scalar12786, tp12786, tm12786, ep12786, em12786, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12786, agent12786, tp12786, tm12786, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12786, agent12786, scalar12786, tp12786, tm12786, ep12786, em12786, dsL]

theorem negative12786 :
    Eminus aL (agent12786.root+dsL) scalar12786.worldRadius world12786.frame
      agent12786.frame tm12786 ≤ -em12786 := by
  apply negative_check (lo := (68408665379763914947 / 100000000000000000000)) (hi := (17102166344940978737 / 25000000000000000000))
    (y := (-((4479827060375887429 / 6250000000000000000)))) (u := (48832586996688078517 / 100000000000000000000))
  · norm_num [world12786, agent12786, scalar12786, tp12786, tm12786, ep12786, em12786, dsL]
  · norm_num [world12786, agent12786, scalar12786, tp12786, tm12786, ep12786, em12786, dsL]
  · norm_num [world12786, agent12786, scalar12786, tp12786, tm12786, ep12786, em12786, dsL]
  · norm_num [world12786, agent12786, scalar12786, tp12786, tm12786, ep12786, em12786, dsL]
  · norm_num [world12786, agent12786, scalar12786, tp12786, tm12786, ep12786, em12786, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12786, agent12786, tp12786, tm12786, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12786, agent12786, tp12786, tm12786, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12786, agent12786, scalar12786, tp12786, tm12786, ep12786, em12786, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12786, agent12786, tp12786, tm12786, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12786, agent12786, scalar12786, tp12786, tm12786, ep12786, em12786, dsL]

theorem tails12786 :
    exp (-((12786:ℝ)*ep12786)) ≤ scalar12786.upperTail ∧
    exp (-((12786:ℝ)*em12786)) ≤ scalar12786.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12786:ℝ)) (by norm_num [ep12786]) ?_)
      (show bp12786^8 ≤ scalar12786.upperTail by norm_num [bp12786, scalar12786])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12786, bp12786, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12786:ℝ)) (by norm_num [em12786]) ?_)
      (show bm12786^8 ≤ scalar12786.lowerTail by norm_num [bm12786, scalar12786])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12786, bm12786, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12786 :
    agent12786.root+dsL+scalar12786.worldRadius < √(1/100/aL) ∧
    2*(agent12786.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12786, agent12786, scalar12786, tp12786, tm12786, ep12786, em12786, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12786, agent12786, scalar12786, tp12786, tm12786, ep12786, em12786, dsL]

noncomputable def master12786 : MasterCertificate 12786 world12786 agent12786 :=
  master scalar12786 dsL tp12786 tm12786 ep12786 em12786
    (by norm_num [dsL]) (by norm_num [tp12786]) (by norm_num [tm12786])
    (by norm_num [ep12786]) (by norm_num [em12786])
    positive12786 negative12786 tails12786.1 tails12786.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12786.1 tailGuards12786.2

theorem preserves12786 : master12786.toScalarCertificate = scalar12786 := rfl

noncomputable def tp12787 : ℝ := (9297491 / 40000000)
noncomputable def tm12787 : ℝ := (-((608031231 / 1000000000)))
noncomputable def ep12787 : ℝ := (12914906516257667 / 25000000000000000000)
noncomputable def em12787 : ℝ := (10062716875574617 / 20000000000000000000)
noncomputable def bp12787 : ℝ := (21896098216323054983 / 50000000000000000000)
noncomputable def bm12787 : ℝ := (44744584994440793877 / 100000000000000000000)

theorem positive12787 :
    Eplus aL (agent12787.root+dsL) scalar12787.worldRadius world12787.frame
      agent12787.frame tp12787 ≤ -ep12787 := by
  apply positive_check (eT := (28905063635911890657 / 25000000000000000000)) (y := (37923265973549227393 / 100000000000000000000)) (u := (36529073749629360113 / 25000000000000000000))
  · norm_num [world12787, agent12787, scalar12787, tp12787, tm12787, ep12787, em12787, dsL]
  · norm_num [world12787, agent12787, scalar12787, tp12787, tm12787, ep12787, em12787, dsL]
  · norm_num [world12787, agent12787, scalar12787, tp12787, tm12787, ep12787, em12787, dsL]
  · norm_num [world12787, agent12787, scalar12787, tp12787, tm12787, ep12787, em12787, dsL]
  · norm_num [world12787, agent12787, scalar12787, tp12787, tm12787, ep12787, em12787, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12787, agent12787, tp12787, tm12787, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12787, agent12787, scalar12787, tp12787, tm12787, ep12787, em12787, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12787, agent12787, tp12787, tm12787, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12787, agent12787, scalar12787, tp12787, tm12787, ep12787, em12787, dsL]

theorem negative12787 :
    Eminus aL (agent12787.root+dsL) scalar12787.worldRadius world12787.frame
      agent12787.frame tm12787 ≤ -em12787 := by
  apply negative_check (lo := (8551060285552076649 / 12500000000000000000)) (hi := (68408482284416613193 / 100000000000000000000))
    (y := (-((17919317672045538659 / 25000000000000000000)))) (u := (48832568575981068823 / 100000000000000000000))
  · norm_num [world12787, agent12787, scalar12787, tp12787, tm12787, ep12787, em12787, dsL]
  · norm_num [world12787, agent12787, scalar12787, tp12787, tm12787, ep12787, em12787, dsL]
  · norm_num [world12787, agent12787, scalar12787, tp12787, tm12787, ep12787, em12787, dsL]
  · norm_num [world12787, agent12787, scalar12787, tp12787, tm12787, ep12787, em12787, dsL]
  · norm_num [world12787, agent12787, scalar12787, tp12787, tm12787, ep12787, em12787, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12787, agent12787, tp12787, tm12787, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12787, agent12787, tp12787, tm12787, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12787, agent12787, scalar12787, tp12787, tm12787, ep12787, em12787, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12787, agent12787, tp12787, tm12787, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12787, agent12787, scalar12787, tp12787, tm12787, ep12787, em12787, dsL]

theorem tails12787 :
    exp (-((12787:ℝ)*ep12787)) ≤ scalar12787.upperTail ∧
    exp (-((12787:ℝ)*em12787)) ≤ scalar12787.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12787:ℝ)) (by norm_num [ep12787]) ?_)
      (show bp12787^8 ≤ scalar12787.upperTail by norm_num [bp12787, scalar12787])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12787, bp12787, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12787:ℝ)) (by norm_num [em12787]) ?_)
      (show bm12787^8 ≤ scalar12787.lowerTail by norm_num [bm12787, scalar12787])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12787, bm12787, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12787 :
    agent12787.root+dsL+scalar12787.worldRadius < √(1/100/aL) ∧
    2*(agent12787.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12787, agent12787, scalar12787, tp12787, tm12787, ep12787, em12787, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12787, agent12787, scalar12787, tp12787, tm12787, ep12787, em12787, dsL]

noncomputable def master12787 : MasterCertificate 12787 world12787 agent12787 :=
  master scalar12787 dsL tp12787 tm12787 ep12787 em12787
    (by norm_num [dsL]) (by norm_num [tp12787]) (by norm_num [tm12787])
    (by norm_num [ep12787]) (by norm_num [em12787])
    positive12787 negative12787 tails12787.1 tails12787.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12787.1 tailGuards12787.2

theorem preserves12787 : master12787.toScalarCertificate = scalar12787 := rfl

noncomputable def tp12788 : ℝ := (1162227557 / 5000000000)
noncomputable def tm12788 : ℝ := (-((30402443 / 50000000)))
noncomputable def ep12788 : ℝ := (3228884026218329 / 6250000000000000000)
noncomputable def em12788 : ℝ := (2515786985237861 / 5000000000000000000)
noncomputable def bp12788 : ℝ := (10946901479634709943 / 25000000000000000000)
noncomputable def bm12788 : ℝ := (5592528693768174901 / 12500000000000000000)

theorem positive12788 :
    Eplus aL (agent12788.root+dsL) scalar12788.worldRadius world12788.frame
      agent12788.frame tp12788 ≤ -ep12788 := by
  apply positive_check (eT := (28905120576820066523 / 25000000000000000000)) (y := (37924026068133153001 / 100000000000000000000)) (u := (29223481124956571329 / 20000000000000000000))
  · norm_num [world12788, agent12788, scalar12788, tp12788, tm12788, ep12788, em12788, dsL]
  · norm_num [world12788, agent12788, scalar12788, tp12788, tm12788, ep12788, em12788, dsL]
  · norm_num [world12788, agent12788, scalar12788, tp12788, tm12788, ep12788, em12788, dsL]
  · norm_num [world12788, agent12788, scalar12788, tp12788, tm12788, ep12788, em12788, dsL]
  · norm_num [world12788, agent12788, scalar12788, tp12788, tm12788, ep12788, em12788, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12788, agent12788, tp12788, tm12788, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12788, agent12788, scalar12788, tp12788, tm12788, ep12788, em12788, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12788, agent12788, tp12788, tm12788, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12788, agent12788, scalar12788, tp12788, tm12788, ep12788, em12788, dsL]

theorem negative12788 :
    Eminus aL (agent12788.root+dsL) scalar12788.worldRadius world12788.frame
      agent12788.frame tm12788 ≤ -em12788 := by
  apply negative_check (lo := (6840829706463334283 / 10000000000000000000)) (hi := (68408297064633342831 / 100000000000000000000))
    (y := (-((17919326087785081967 / 25000000000000000000)))) (u := (6104069017187087627 / 12500000000000000000))
  · norm_num [world12788, agent12788, scalar12788, tp12788, tm12788, ep12788, em12788, dsL]
  · norm_num [world12788, agent12788, scalar12788, tp12788, tm12788, ep12788, em12788, dsL]
  · norm_num [world12788, agent12788, scalar12788, tp12788, tm12788, ep12788, em12788, dsL]
  · norm_num [world12788, agent12788, scalar12788, tp12788, tm12788, ep12788, em12788, dsL]
  · norm_num [world12788, agent12788, scalar12788, tp12788, tm12788, ep12788, em12788, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12788, agent12788, tp12788, tm12788, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12788, agent12788, tp12788, tm12788, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12788, agent12788, scalar12788, tp12788, tm12788, ep12788, em12788, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12788, agent12788, tp12788, tm12788, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12788, agent12788, scalar12788, tp12788, tm12788, ep12788, em12788, dsL]

theorem tails12788 :
    exp (-((12788:ℝ)*ep12788)) ≤ scalar12788.upperTail ∧
    exp (-((12788:ℝ)*em12788)) ≤ scalar12788.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12788:ℝ)) (by norm_num [ep12788]) ?_)
      (show bp12788^8 ≤ scalar12788.upperTail by norm_num [bp12788, scalar12788])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12788, bp12788, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12788:ℝ)) (by norm_num [em12788]) ?_)
      (show bm12788^8 ≤ scalar12788.lowerTail by norm_num [bm12788, scalar12788])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12788, bm12788, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12788 :
    agent12788.root+dsL+scalar12788.worldRadius < √(1/100/aL) ∧
    2*(agent12788.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12788, agent12788, scalar12788, tp12788, tm12788, ep12788, em12788, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12788, agent12788, scalar12788, tp12788, tm12788, ep12788, em12788, dsL]

noncomputable def master12788 : MasterCertificate 12788 world12788 agent12788 :=
  master scalar12788 dsL tp12788 tm12788 ep12788 em12788
    (by norm_num [dsL]) (by norm_num [tp12788]) (by norm_num [tm12788])
    (by norm_num [ep12788]) (by norm_num [em12788])
    positive12788 negative12788 tails12788.1 tails12788.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12788.1 tailGuards12788.2

theorem preserves12788 : master12788.toScalarCertificate = scalar12788 := rfl

noncomputable def tp12789 : ℝ := (464907491 / 2000000000)
noncomputable def tm12789 : ℝ := (-((608066479 / 1000000000)))
noncomputable def ep12789 : ℝ := (206658648892509 / 400000000000000000)
noncomputable def em12789 : ℝ := (25158947244960251 / 50000000000000000000)
noncomputable def bp12789 : ℝ := (43783015995518421729 / 100000000000000000000)
noncomputable def bm12789 : ℝ := (44735874676174967407 / 100000000000000000000)

theorem positive12789 :
    Eplus aL (agent12789.root+dsL) scalar12789.worldRadius world12789.frame
      agent12789.frame tp12789 ≤ -ep12789 := by
  apply positive_check (eT := (28905177484429568927 / 25000000000000000000)) (y := (3792478616626186831 / 10000000000000000000)) (u := (18264814533083713641 / 12500000000000000000))
  · norm_num [world12789, agent12789, scalar12789, tp12789, tm12789, ep12789, em12789, dsL]
  · norm_num [world12789, agent12789, scalar12789, tp12789, tm12789, ep12789, em12789, dsL]
  · norm_num [world12789, agent12789, scalar12789, tp12789, tm12789, ep12789, em12789, dsL]
  · norm_num [world12789, agent12789, scalar12789, tp12789, tm12789, ep12789, em12789, dsL]
  · norm_num [world12789, agent12789, scalar12789, tp12789, tm12789, ep12789, em12789, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12789, agent12789, tp12789, tm12789, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12789, agent12789, scalar12789, tp12789, tm12789, ep12789, em12789, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12789, agent12789, tp12789, tm12789, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12789, agent12789, scalar12789, tp12789, tm12789, ep12789, em12789, dsL]

theorem negative12789 :
    Eminus aL (agent12789.root+dsL) scalar12789.worldRadius world12789.frame
      agent12789.frame tm12789 ≤ -em12789 := by
  apply negative_check (lo := (3420405610751503091 / 5000000000000000000)) (hi := (68408112215030061821 / 100000000000000000000))
    (y := (-((2867093519869829871 / 4000000000000000000)))) (u := (48832535707491656839 / 100000000000000000000))
  · norm_num [world12789, agent12789, scalar12789, tp12789, tm12789, ep12789, em12789, dsL]
  · norm_num [world12789, agent12789, scalar12789, tp12789, tm12789, ep12789, em12789, dsL]
  · norm_num [world12789, agent12789, scalar12789, tp12789, tm12789, ep12789, em12789, dsL]
  · norm_num [world12789, agent12789, scalar12789, tp12789, tm12789, ep12789, em12789, dsL]
  · norm_num [world12789, agent12789, scalar12789, tp12789, tm12789, ep12789, em12789, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12789, agent12789, tp12789, tm12789, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12789, agent12789, tp12789, tm12789, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12789, agent12789, scalar12789, tp12789, tm12789, ep12789, em12789, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12789, agent12789, tp12789, tm12789, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12789, agent12789, scalar12789, tp12789, tm12789, ep12789, em12789, dsL]

theorem tails12789 :
    exp (-((12789:ℝ)*ep12789)) ≤ scalar12789.upperTail ∧
    exp (-((12789:ℝ)*em12789)) ≤ scalar12789.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12789:ℝ)) (by norm_num [ep12789]) ?_)
      (show bp12789^8 ≤ scalar12789.upperTail by norm_num [bp12789, scalar12789])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12789, bp12789, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12789:ℝ)) (by norm_num [em12789]) ?_)
      (show bm12789^8 ≤ scalar12789.lowerTail by norm_num [bm12789, scalar12789])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12789, bm12789, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12789 :
    agent12789.root+dsL+scalar12789.worldRadius < √(1/100/aL) ∧
    2*(agent12789.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12789, agent12789, scalar12789, tp12789, tm12789, ep12789, em12789, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12789, agent12789, scalar12789, tp12789, tm12789, ep12789, em12789, dsL]

noncomputable def master12789 : MasterCertificate 12789 world12789 agent12789 :=
  master scalar12789 dsL tp12789 tm12789 ep12789 em12789
    (by norm_num [dsL]) (by norm_num [tp12789]) (by norm_num [tm12789])
    (by norm_num [ep12789]) (by norm_num [em12789])
    positive12789 negative12789 tails12789.1 tails12789.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12789.1 tailGuards12789.2

theorem preserves12789 : master12789.toScalarCertificate = scalar12789 := rfl

noncomputable def tp12790 : ℝ := (290586669 / 1250000000)
noncomputable def tm12790 : ℝ := (-((760132937 / 1250000000)))
noncomputable def ep12790 : ℝ := (807321569223951 / 1562500000000000000)
noncomputable def em12790 : ℝ := (50321576014096243 / 100000000000000000000)
noncomputable def bp12790 : ℝ := (1751097845437774591 / 4000000000000000000)
noncomputable def bm12790 : ℝ := (22365214079206503487 / 50000000000000000000)

theorem positive12790 :
    Eplus aL (agent12790.root+dsL) scalar12790.worldRadius world12790.frame
      agent12790.frame tp12790 ≤ -ep12790 := by
  apply positive_check (eT := (57810734310756098783 / 50000000000000000000)) (y := (3792482385269617927 / 10000000000000000000)) (u := (36529642832884683433 / 25000000000000000000))
  · norm_num [world12790, agent12790, scalar12790, tp12790, tm12790, ep12790, em12790, dsL]
  · norm_num [world12790, agent12790, scalar12790, tp12790, tm12790, ep12790, em12790, dsL]
  · norm_num [world12790, agent12790, scalar12790, tp12790, tm12790, ep12790, em12790, dsL]
  · norm_num [world12790, agent12790, scalar12790, tp12790, tm12790, ep12790, em12790, dsL]
  · norm_num [world12790, agent12790, scalar12790, tp12790, tm12790, ep12790, em12790, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12790, agent12790, tp12790, tm12790, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12790, agent12790, scalar12790, tp12790, tm12790, ep12790, em12790, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12790, agent12790, tp12790, tm12790, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12790, agent12790, scalar12790, tp12790, tm12790, ep12790, em12790, dsL]

theorem negative12790 :
    Eminus aL (agent12790.root+dsL) scalar12790.worldRadius world12790.frame
      agent12790.frame tm12790 ≤ -em12790 := by
  apply negative_check (lo := (2137718027435794573 / 3125000000000000000)) (hi := (68406976877945426337 / 100000000000000000000))
    (y := (-((14335095003775233513 / 20000000000000000000)))) (u := (6104180681912401953 / 12500000000000000000))
  · norm_num [world12790, agent12790, scalar12790, tp12790, tm12790, ep12790, em12790, dsL]
  · norm_num [world12790, agent12790, scalar12790, tp12790, tm12790, ep12790, em12790, dsL]
  · norm_num [world12790, agent12790, scalar12790, tp12790, tm12790, ep12790, em12790, dsL]
  · norm_num [world12790, agent12790, scalar12790, tp12790, tm12790, ep12790, em12790, dsL]
  · norm_num [world12790, agent12790, scalar12790, tp12790, tm12790, ep12790, em12790, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12790, agent12790, tp12790, tm12790, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12790, agent12790, tp12790, tm12790, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12790, agent12790, scalar12790, tp12790, tm12790, ep12790, em12790, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12790, agent12790, tp12790, tm12790, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12790, agent12790, scalar12790, tp12790, tm12790, ep12790, em12790, dsL]

theorem tails12790 :
    exp (-((12790:ℝ)*ep12790)) ≤ scalar12790.upperTail ∧
    exp (-((12790:ℝ)*em12790)) ≤ scalar12790.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12790:ℝ)) (by norm_num [ep12790]) ?_)
      (show bp12790^8 ≤ scalar12790.upperTail by norm_num [bp12790, scalar12790])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12790, bp12790, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12790:ℝ)) (by norm_num [em12790]) ?_)
      (show bm12790^8 ≤ scalar12790.lowerTail by norm_num [bm12790, scalar12790])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12790, bm12790, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12790 :
    agent12790.root+dsL+scalar12790.worldRadius < √(1/100/aL) ∧
    2*(agent12790.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12790, agent12790, scalar12790, tp12790, tm12790, ep12790, em12790, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12790, agent12790, scalar12790, tp12790, tm12790, ep12790, em12790, dsL]

noncomputable def master12790 : MasterCertificate 12790 world12790 agent12790 :=
  master scalar12790 dsL tp12790 tm12790 ep12790 em12790
    (by norm_num [dsL]) (by norm_num [tp12790]) (by norm_num [tm12790])
    (by norm_num [ep12790]) (by norm_num [em12790])
    positive12790 negative12790 tails12790.1 tails12790.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12790.1 tailGuards12790.2

theorem preserves12790 : master12790.toScalarCertificate = scalar12790 := rfl

noncomputable def tp12791 : ℝ := (2324775617 / 10000000000)
noncomputable def tm12791 : ℝ := (-((1520309909 / 2500000000)))
noncomputable def ep12791 : ℝ := (25835547661223703 / 50000000000000000000)
noncomputable def em12791 : ℝ := (12580932026800591 / 25000000000000000000)
noncomputable def bp12791 : ℝ := (43772858687909776021 / 100000000000000000000)
noncomputable def bm12791 : ℝ := (22363037798187755301 / 50000000000000000000)

theorem positive12791 :
    Eplus aL (agent12791.root+dsL) scalar12791.worldRadius world12791.frame
      agent12791.frame tp12791 ≤ -ep12791 := by
  apply positive_check (eT := (11562169575836462069 / 10000000000000000000)) (y := (37925583346533386993 / 100000000000000000000)) (u := (36529920274324327169 / 25000000000000000000))
  · norm_num [world12791, agent12791, scalar12791, tp12791, tm12791, ep12791, em12791, dsL]
  · norm_num [world12791, agent12791, scalar12791, tp12791, tm12791, ep12791, em12791, dsL]
  · norm_num [world12791, agent12791, scalar12791, tp12791, tm12791, ep12791, em12791, dsL]
  · norm_num [world12791, agent12791, scalar12791, tp12791, tm12791, ep12791, em12791, dsL]
  · norm_num [world12791, agent12791, scalar12791, tp12791, tm12791, ep12791, em12791, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12791, agent12791, tp12791, tm12791, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12791, agent12791, scalar12791, tp12791, tm12791, ep12791, em12791, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12791, agent12791, tp12791, tm12791, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12791, agent12791, scalar12791, tp12791, tm12791, ep12791, em12791, dsL]

theorem negative12791 :
    Eminus aL (agent12791.root+dsL) scalar12791.worldRadius world12791.frame
      agent12791.frame tm12791 ≤ -em12791 := by
  apply negative_check (lo := (68406792151416100863 / 100000000000000000000)) (hi := (33401753980183643 / 48828125000000000))
    (y := (-((71675509301666179959 / 100000000000000000000)))) (u := (6104178589229315511 / 12500000000000000000))
  · norm_num [world12791, agent12791, scalar12791, tp12791, tm12791, ep12791, em12791, dsL]
  · norm_num [world12791, agent12791, scalar12791, tp12791, tm12791, ep12791, em12791, dsL]
  · norm_num [world12791, agent12791, scalar12791, tp12791, tm12791, ep12791, em12791, dsL]
  · norm_num [world12791, agent12791, scalar12791, tp12791, tm12791, ep12791, em12791, dsL]
  · norm_num [world12791, agent12791, scalar12791, tp12791, tm12791, ep12791, em12791, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12791, agent12791, tp12791, tm12791, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12791, agent12791, tp12791, tm12791, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12791, agent12791, scalar12791, tp12791, tm12791, ep12791, em12791, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12791, agent12791, tp12791, tm12791, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12791, agent12791, scalar12791, tp12791, tm12791, ep12791, em12791, dsL]

theorem tails12791 :
    exp (-((12791:ℝ)*ep12791)) ≤ scalar12791.upperTail ∧
    exp (-((12791:ℝ)*em12791)) ≤ scalar12791.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12791:ℝ)) (by norm_num [ep12791]) ?_)
      (show bp12791^8 ≤ scalar12791.upperTail by norm_num [bp12791, scalar12791])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12791, bp12791, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12791:ℝ)) (by norm_num [em12791]) ?_)
      (show bm12791^8 ≤ scalar12791.lowerTail by norm_num [bm12791, scalar12791])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12791, bm12791, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12791 :
    agent12791.root+dsL+scalar12791.worldRadius < √(1/100/aL) ∧
    2*(agent12791.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12791, agent12791, scalar12791, tp12791, tm12791, ep12791, em12791, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12791, agent12791, scalar12791, tp12791, tm12791, ep12791, em12791, dsL]

noncomputable def master12791 : MasterCertificate 12791 world12791 agent12791 :=
  master scalar12791 dsL tp12791 tm12791 ep12791 em12791
    (by norm_num [dsL]) (by norm_num [tp12791]) (by norm_num [tm12791])
    (by norm_num [ep12791]) (by norm_num [em12791])
    positive12791 negative12791 tails12791.1 tails12791.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12791.1 tailGuards12791.2

theorem preserves12791 : master12791.toScalarCertificate = scalar12791 := rfl

noncomputable def tp12792 : ℝ := (232485783 / 1000000000)
noncomputable def tm12792 : ℝ := (-((1946053 / 3200000)))
noncomputable def ep12792 : ℝ := (25836804440954031 / 50000000000000000000)
noncomputable def em12792 : ℝ := (50325878957610969 / 100000000000000000000)
noncomputable def bp12792 : ℝ := (43768272378077697591 / 100000000000000000000)
noncomputable def bm12792 : ℝ := (22360862052955407471 / 50000000000000000000)

theorem positive12792 :
    Eplus aL (agent12792.root+dsL) scalar12792.worldRadius world12792.frame
      agent12792.frame tp12792 ≤ -ep12792 := by
  apply positive_check (eT := (57810961276324726943 / 50000000000000000000)) (y := (7585268476658660529 / 20000000000000000000)) (u := (146120790203599565631 / 100000000000000000000))
  · norm_num [world12792, agent12792, scalar12792, tp12792, tm12792, ep12792, em12792, dsL]
  · norm_num [world12792, agent12792, scalar12792, tp12792, tm12792, ep12792, em12792, dsL]
  · norm_num [world12792, agent12792, scalar12792, tp12792, tm12792, ep12792, em12792, dsL]
  · norm_num [world12792, agent12792, scalar12792, tp12792, tm12792, ep12792, em12792, dsL]
  · norm_num [world12792, agent12792, scalar12792, tp12792, tm12792, ep12792, em12792, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12792, agent12792, tp12792, tm12792, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12792, agent12792, scalar12792, tp12792, tm12792, ep12792, em12792, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12792, agent12792, tp12792, tm12792, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12792, agent12792, scalar12792, tp12792, tm12792, ep12792, em12792, dsL]

theorem negative12792 :
    Eminus aL (agent12792.root+dsL) scalar12792.worldRadius world12792.frame
      agent12792.frame tm12792 ≤ -em12792 := by
  apply negative_check (lo := (13681321602584308487 / 20000000000000000000)) (hi := (17101652003230385609 / 25000000000000000000))
    (y := (-((71675542940742399973 / 100000000000000000000)))) (u := (48833412286722981159 / 100000000000000000000))
  · norm_num [world12792, agent12792, scalar12792, tp12792, tm12792, ep12792, em12792, dsL]
  · norm_num [world12792, agent12792, scalar12792, tp12792, tm12792, ep12792, em12792, dsL]
  · norm_num [world12792, agent12792, scalar12792, tp12792, tm12792, ep12792, em12792, dsL]
  · norm_num [world12792, agent12792, scalar12792, tp12792, tm12792, ep12792, em12792, dsL]
  · norm_num [world12792, agent12792, scalar12792, tp12792, tm12792, ep12792, em12792, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12792, agent12792, tp12792, tm12792, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12792, agent12792, tp12792, tm12792, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12792, agent12792, scalar12792, tp12792, tm12792, ep12792, em12792, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12792, agent12792, tp12792, tm12792, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12792, agent12792, scalar12792, tp12792, tm12792, ep12792, em12792, dsL]

theorem tails12792 :
    exp (-((12792:ℝ)*ep12792)) ≤ scalar12792.upperTail ∧
    exp (-((12792:ℝ)*em12792)) ≤ scalar12792.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12792:ℝ)) (by norm_num [ep12792]) ?_)
      (show bp12792^8 ≤ scalar12792.upperTail by norm_num [bp12792, scalar12792])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12792, bp12792, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12792:ℝ)) (by norm_num [em12792]) ?_)
      (show bm12792^8 ≤ scalar12792.lowerTail by norm_num [bm12792, scalar12792])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12792, bm12792, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12792 :
    agent12792.root+dsL+scalar12792.worldRadius < √(1/100/aL) ∧
    2*(agent12792.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12792, agent12792, scalar12792, tp12792, tm12792, ep12792, em12792, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12792, agent12792, scalar12792, tp12792, tm12792, ep12792, em12792, dsL]

noncomputable def master12792 : MasterCertificate 12792 world12792 agent12792 :=
  master scalar12792 dsL tp12792 tm12792 ep12792 em12792
    (by norm_num [dsL]) (by norm_num [tp12792]) (by norm_num [tm12792])
    (by norm_num [ep12792]) (by norm_num [em12792])
    positive12792 negative12792 tails12792.1 tails12792.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12792.1 tailGuards12792.2

theorem preserves12792 : master12792.toScalarCertificate = scalar12792 := rfl

noncomputable def tp12793 : ℝ := (2324940017 / 10000000000)
noncomputable def tm12793 : ℝ := (-((3040795651 / 5000000000)))
noncomputable def ep12793 : ℝ := (645951505805013 / 1250000000000000000)
noncomputable def em12793 : ℝ := (25164014004412381 / 50000000000000000000)
noncomputable def bp12793 : ℝ := (5470460957165478487 / 12500000000000000000)
noncomputable def bm12793 : ℝ := (44717374084940766049 / 100000000000000000000)

theorem positive12793 :
    Eplus aL (agent12793.root+dsL) scalar12793.worldRadius world12793.frame
      agent12793.frame tp12793 ≤ -ep12793 := by
  apply positive_check (eT := (115622149192058827051 / 100000000000000000000)) (y := (37927101314820472441 / 100000000000000000000)) (u := (146121899164552292207 / 100000000000000000000))
  · norm_num [world12793, agent12793, scalar12793, tp12793, tm12793, ep12793, em12793, dsL]
  · norm_num [world12793, agent12793, scalar12793, tp12793, tm12793, ep12793, em12793, dsL]
  · norm_num [world12793, agent12793, scalar12793, tp12793, tm12793, ep12793, em12793, dsL]
  · norm_num [world12793, agent12793, scalar12793, tp12793, tm12793, ep12793, em12793, dsL]
  · norm_num [world12793, agent12793, scalar12793, tp12793, tm12793, ep12793, em12793, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12793, agent12793, tp12793, tm12793, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12793, agent12793, scalar12793, tp12793, tm12793, ep12793, em12793, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12793, agent12793, tp12793, tm12793, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12793, agent12793, scalar12793, tp12793, tm12793, ep12793, em12793, dsL]

theorem negative12793 :
    Eminus aL (agent12793.root+dsL) scalar12793.worldRadius world12793.frame
      agent12793.frame tm12793 ≤ -em12793 := by
  apply negative_check (lo := (68406425150070963277 / 100000000000000000000)) (hi := (34203212575035481639 / 50000000000000000000))
    (y := (-((71675573957705913633 / 100000000000000000000)))) (u := (1953335885603346349 / 4000000000000000000))
  · norm_num [world12793, agent12793, scalar12793, tp12793, tm12793, ep12793, em12793, dsL]
  · norm_num [world12793, agent12793, scalar12793, tp12793, tm12793, ep12793, em12793, dsL]
  · norm_num [world12793, agent12793, scalar12793, tp12793, tm12793, ep12793, em12793, dsL]
  · norm_num [world12793, agent12793, scalar12793, tp12793, tm12793, ep12793, em12793, dsL]
  · norm_num [world12793, agent12793, scalar12793, tp12793, tm12793, ep12793, em12793, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12793, agent12793, tp12793, tm12793, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12793, agent12793, tp12793, tm12793, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12793, agent12793, scalar12793, tp12793, tm12793, ep12793, em12793, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12793, agent12793, tp12793, tm12793, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12793, agent12793, scalar12793, tp12793, tm12793, ep12793, em12793, dsL]

theorem tails12793 :
    exp (-((12793:ℝ)*ep12793)) ≤ scalar12793.upperTail ∧
    exp (-((12793:ℝ)*em12793)) ≤ scalar12793.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12793:ℝ)) (by norm_num [ep12793]) ?_)
      (show bp12793^8 ≤ scalar12793.upperTail by norm_num [bp12793, scalar12793])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12793, bp12793, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12793:ℝ)) (by norm_num [em12793]) ?_)
      (show bm12793^8 ≤ scalar12793.lowerTail by norm_num [bm12793, scalar12793])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12793, bm12793, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12793 :
    agent12793.root+dsL+scalar12793.worldRadius < √(1/100/aL) ∧
    2*(agent12793.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12793, agent12793, scalar12793, tp12793, tm12793, ep12793, em12793, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12793, agent12793, scalar12793, tp12793, tm12793, ep12793, em12793, dsL]

noncomputable def master12793 : MasterCertificate 12793 world12793 agent12793 :=
  master scalar12793 dsL tp12793 tm12793 ep12793 em12793
    (by norm_num [dsL]) (by norm_num [tp12793]) (by norm_num [tm12793])
    (by norm_num [ep12793]) (by norm_num [em12793])
    positive12793 negative12793 tails12793.1 tails12793.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12793.1 tailGuards12793.2

theorem preserves12793 : master12793.toScalarCertificate = scalar12793 := rfl

noncomputable def tp12794 : ℝ := (1162511047 / 5000000000)
noncomputable def tm12794 : ℝ := (-((1520441751 / 2500000000)))
noncomputable def ep12794 : ℝ := (10335726300212007 / 20000000000000000000)
noncomputable def em12794 : ℝ := (25165088261392409 / 50000000000000000000)
noncomputable def bp12794 : ℝ := (21879551762020754641 / 50000000000000000000)
noncomputable def bm12794 : ℝ := (2235651231552026353 / 5000000000000000000)

theorem positive12794 :
    Eplus aL (agent12794.root+dsL) scalar12794.worldRadius world12794.frame
      agent12794.frame tp12794 ≤ -ep12794 := by
  apply positive_check (eT := (57811187535132710687 / 50000000000000000000)) (y := (9481964681098905399 / 25000000000000000000)) (u := (73061502954999623511 / 50000000000000000000))
  · norm_num [world12794, agent12794, scalar12794, tp12794, tm12794, ep12794, em12794, dsL]
  · norm_num [world12794, agent12794, scalar12794, tp12794, tm12794, ep12794, em12794, dsL]
  · norm_num [world12794, agent12794, scalar12794, tp12794, tm12794, ep12794, em12794, dsL]
  · norm_num [world12794, agent12794, scalar12794, tp12794, tm12794, ep12794, em12794, dsL]
  · norm_num [world12794, agent12794, scalar12794, tp12794, tm12794, ep12794, em12794, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12794, agent12794, tp12794, tm12794, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12794, agent12794, scalar12794, tp12794, tm12794, ep12794, em12794, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12794, agent12794, tp12794, tm12794, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12794, agent12794, scalar12794, tp12794, tm12794, ep12794, em12794, dsL]

theorem negative12794 :
    Eminus aL (agent12794.root+dsL) scalar12794.worldRadius world12794.frame
      agent12794.frame tm12794 ≤ -em12794 := by
  apply negative_check (lo := (68406242123443502941 / 100000000000000000000)) (hi := (34203121061721751471 / 50000000000000000000))
    (y := (-((573404849336989719 / 800000000000000000)))) (u := (24416690705566640219 / 50000000000000000000))
  · norm_num [world12794, agent12794, scalar12794, tp12794, tm12794, ep12794, em12794, dsL]
  · norm_num [world12794, agent12794, scalar12794, tp12794, tm12794, ep12794, em12794, dsL]
  · norm_num [world12794, agent12794, scalar12794, tp12794, tm12794, ep12794, em12794, dsL]
  · norm_num [world12794, agent12794, scalar12794, tp12794, tm12794, ep12794, em12794, dsL]
  · norm_num [world12794, agent12794, scalar12794, tp12794, tm12794, ep12794, em12794, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12794, agent12794, tp12794, tm12794, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12794, agent12794, tp12794, tm12794, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12794, agent12794, scalar12794, tp12794, tm12794, ep12794, em12794, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12794, agent12794, tp12794, tm12794, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12794, agent12794, scalar12794, tp12794, tm12794, ep12794, em12794, dsL]

theorem tails12794 :
    exp (-((12794:ℝ)*ep12794)) ≤ scalar12794.upperTail ∧
    exp (-((12794:ℝ)*em12794)) ≤ scalar12794.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12794:ℝ)) (by norm_num [ep12794]) ?_)
      (show bp12794^8 ≤ scalar12794.upperTail by norm_num [bp12794, scalar12794])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12794, bp12794, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12794:ℝ)) (by norm_num [em12794]) ?_)
      (show bm12794^8 ≤ scalar12794.lowerTail by norm_num [bm12794, scalar12794])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12794, bm12794, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12794 :
    agent12794.root+dsL+scalar12794.worldRadius < √(1/100/aL) ∧
    2*(agent12794.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12794, agent12794, scalar12794, tp12794, tm12794, ep12794, em12794, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12794, agent12794, scalar12794, tp12794, tm12794, ep12794, em12794, dsL]

noncomputable def master12794 : MasterCertificate 12794 world12794 agent12794 :=
  master scalar12794 dsL tp12794 tm12794 ep12794 em12794
    (by norm_num [dsL]) (by norm_num [tp12794]) (by norm_num [tm12794])
    (by norm_num [ep12794]) (by norm_num [em12794])
    positive12794 negative12794 tails12794.1 tails12794.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12794.1 tailGuards12794.2

theorem preserves12794 : master12794.toScalarCertificate = scalar12794 := rfl

noncomputable def tp12795 : ℝ := (1162552109 / 5000000000)
noncomputable def tm12795 : ℝ := (-((1216388547 / 2000000000)))
noncomputable def ep12795 : ℝ := (51681140727033019 / 100000000000000000000)
noncomputable def em12795 : ℝ := (50332323351974493 / 100000000000000000000)
noncomputable def bp12795 : ℝ := (1367328776980572203 / 3125000000000000000)
noncomputable def bm12795 : ℝ := (22354338282379781509 / 50000000000000000000)

theorem positive12795 :
    Eplus aL (agent12795.root+dsL) scalar12795.worldRadius world12795.frame
      agent12795.frame tp12795 ≤ -ep12795 := by
  apply positive_check (eT := (115622601320584397711 / 100000000000000000000)) (y := (7585723492121631701 / 20000000000000000000)) (u := (146124114602365953551 / 100000000000000000000))
  · norm_num [world12795, agent12795, scalar12795, tp12795, tm12795, ep12795, em12795, dsL]
  · norm_num [world12795, agent12795, scalar12795, tp12795, tm12795, ep12795, em12795, dsL]
  · norm_num [world12795, agent12795, scalar12795, tp12795, tm12795, ep12795, em12795, dsL]
  · norm_num [world12795, agent12795, scalar12795, tp12795, tm12795, ep12795, em12795, dsL]
  · norm_num [world12795, agent12795, scalar12795, tp12795, tm12795, ep12795, em12795, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12795, agent12795, tp12795, tm12795, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12795, agent12795, scalar12795, tp12795, tm12795, ep12795, em12795, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12795, agent12795, tp12795, tm12795, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12795, agent12795, scalar12795, tp12795, tm12795, ep12795, em12795, dsL]

theorem negative12795 :
    Eminus aL (agent12795.root+dsL) scalar12795.worldRadius world12795.frame
      agent12795.frame tm12795 ≤ -em12795 := by
  apply negative_check (lo := (17101514729009977281 / 25000000000000000000)) (hi := (547248471328319273 / 800000000000000000))
    (y := (-((71675639348080306733 / 100000000000000000000)))) (u := (12208341301938220073 / 25000000000000000000))
  · norm_num [world12795, agent12795, scalar12795, tp12795, tm12795, ep12795, em12795, dsL]
  · norm_num [world12795, agent12795, scalar12795, tp12795, tm12795, ep12795, em12795, dsL]
  · norm_num [world12795, agent12795, scalar12795, tp12795, tm12795, ep12795, em12795, dsL]
  · norm_num [world12795, agent12795, scalar12795, tp12795, tm12795, ep12795, em12795, dsL]
  · norm_num [world12795, agent12795, scalar12795, tp12795, tm12795, ep12795, em12795, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12795, agent12795, tp12795, tm12795, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12795, agent12795, tp12795, tm12795, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12795, agent12795, scalar12795, tp12795, tm12795, ep12795, em12795, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12795, agent12795, tp12795, tm12795, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12795, agent12795, scalar12795, tp12795, tm12795, ep12795, em12795, dsL]

theorem tails12795 :
    exp (-((12795:ℝ)*ep12795)) ≤ scalar12795.upperTail ∧
    exp (-((12795:ℝ)*em12795)) ≤ scalar12795.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12795:ℝ)) (by norm_num [ep12795]) ?_)
      (show bp12795^8 ≤ scalar12795.upperTail by norm_num [bp12795, scalar12795])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12795, bp12795, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12795:ℝ)) (by norm_num [em12795]) ?_)
      (show bm12795^8 ≤ scalar12795.lowerTail by norm_num [bm12795, scalar12795])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12795, bm12795, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12795 :
    agent12795.root+dsL+scalar12795.worldRadius < √(1/100/aL) ∧
    2*(agent12795.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12795, agent12795, scalar12795, tp12795, tm12795, ep12795, em12795, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12795, agent12795, scalar12795, tp12795, tm12795, ep12795, em12795, dsL]

noncomputable def master12795 : MasterCertificate 12795 world12795 agent12795 :=
  master scalar12795 dsL tp12795 tm12795 ep12795 em12795
    (by norm_num [dsL]) (by norm_num [tp12795]) (by norm_num [tm12795])
    (by norm_num [ep12795]) (by norm_num [em12795])
    positive12795 negative12795 tails12795.1 tails12795.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12795.1 tailGuards12795.2

theorem preserves12795 : master12795.toScalarCertificate = scalar12795 := rfl

noncomputable def tp12796 : ℝ := (1162593147 / 5000000000)
noncomputable def tm12796 : ℝ := (-((608211829 / 1000000000)))
noncomputable def ep12796 : ℝ := (3230228028679221 / 6250000000000000000)
noncomputable def em12796 : ℝ := (314590430177313 / 625000000000000000)
noncomputable def bp12796 : ℝ := (8749987890751093913 / 20000000000000000000)
noncomputable def bm12796 : ℝ := (22352164824339764423 / 50000000000000000000)

theorem positive12796 :
    Eplus aL (agent12796.root+dsL) scalar12796.worldRadius world12796.frame
      agent12796.frame tp12796 ≤ -ep12796 := by
  apply positive_check (eT := (115622827257251554257 / 100000000000000000000)) (y := (37929375656482639213 / 100000000000000000000)) (u := (73062611256787276691 / 50000000000000000000))
  · norm_num [world12796, agent12796, scalar12796, tp12796, tm12796, ep12796, em12796, dsL]
  · norm_num [world12796, agent12796, scalar12796, tp12796, tm12796, ep12796, em12796, dsL]
  · norm_num [world12796, agent12796, scalar12796, tp12796, tm12796, ep12796, em12796, dsL]
  · norm_num [world12796, agent12796, scalar12796, tp12796, tm12796, ep12796, em12796, dsL]
  · norm_num [world12796, agent12796, scalar12796, tp12796, tm12796, ep12796, em12796, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12796, agent12796, tp12796, tm12796, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12796, agent12796, scalar12796, tp12796, tm12796, ep12796, em12796, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12796, agent12796, tp12796, tm12796, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12796, agent12796, scalar12796, tp12796, tm12796, ep12796, em12796, dsL]

theorem negative12796 :
    Eminus aL (agent12796.root+dsL) scalar12796.worldRadius world12796.frame
      agent12796.frame tm12796 ≤ -em12796 := by
  apply negative_check (lo := (68405876403341680339 / 100000000000000000000)) (hi := (3420293820167084017 / 5000000000000000000))
    (y := (-((71675671351920033873 / 100000000000000000000)))) (u := (48833349579203446701 / 100000000000000000000))
  · norm_num [world12796, agent12796, scalar12796, tp12796, tm12796, ep12796, em12796, dsL]
  · norm_num [world12796, agent12796, scalar12796, tp12796, tm12796, ep12796, em12796, dsL]
  · norm_num [world12796, agent12796, scalar12796, tp12796, tm12796, ep12796, em12796, dsL]
  · norm_num [world12796, agent12796, scalar12796, tp12796, tm12796, ep12796, em12796, dsL]
  · norm_num [world12796, agent12796, scalar12796, tp12796, tm12796, ep12796, em12796, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12796, agent12796, tp12796, tm12796, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12796, agent12796, tp12796, tm12796, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12796, agent12796, scalar12796, tp12796, tm12796, ep12796, em12796, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12796, agent12796, tp12796, tm12796, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12796, agent12796, scalar12796, tp12796, tm12796, ep12796, em12796, dsL]

theorem tails12796 :
    exp (-((12796:ℝ)*ep12796)) ≤ scalar12796.upperTail ∧
    exp (-((12796:ℝ)*em12796)) ≤ scalar12796.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12796:ℝ)) (by norm_num [ep12796]) ?_)
      (show bp12796^8 ≤ scalar12796.upperTail by norm_num [bp12796, scalar12796])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12796, bp12796, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12796:ℝ)) (by norm_num [em12796]) ?_)
      (show bm12796^8 ≤ scalar12796.lowerTail by norm_num [bm12796, scalar12796])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12796, bm12796, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12796 :
    agent12796.root+dsL+scalar12796.worldRadius < √(1/100/aL) ∧
    2*(agent12796.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12796, agent12796, scalar12796, tp12796, tm12796, ep12796, em12796, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12796, agent12796, scalar12796, tp12796, tm12796, ep12796, em12796, dsL]

noncomputable def master12796 : MasterCertificate 12796 world12796 agent12796 :=
  master scalar12796 dsL tp12796 tm12796 ep12796 em12796
    (by norm_num [dsL]) (by norm_num [tp12796]) (by norm_num [tm12796])
    (by norm_num [ep12796]) (by norm_num [em12796])
    positive12796 negative12796 tails12796.1 tails12796.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12796.1 tailGuards12796.2

theorem preserves12796 : master12796.toScalarCertificate = scalar12796 := rfl

noncomputable def tp12797 : ℝ := (1162634181 / 5000000000)
noncomputable def tm12797 : ℝ := (-((243291749 / 400000000)))
noncomputable def ep12797 : ℝ := (25843077817822117 / 50000000000000000000)
noncomputable def em12797 : ℝ := (50336613759763489 / 100000000000000000000)
noncomputable def bp12797 : ℝ := (21872679318996469069 / 50000000000000000000)
noncomputable def bm12797 : ℝ := (11174995826294187521 / 25000000000000000000)

theorem positive12797 :
    Eplus aL (agent12797.root+dsL) scalar12797.worldRadius world12797.frame
      agent12797.frame tp12797 ≤ -ep12797 := by
  apply positive_check (eT := (115623053169025162059 / 100000000000000000000)) (y := (9482533529395021579 / 25000000000000000000)) (u := (36531582705185977727 / 25000000000000000000))
  · norm_num [world12797, agent12797, scalar12797, tp12797, tm12797, ep12797, em12797, dsL]
  · norm_num [world12797, agent12797, scalar12797, tp12797, tm12797, ep12797, em12797, dsL]
  · norm_num [world12797, agent12797, scalar12797, tp12797, tm12797, ep12797, em12797, dsL]
  · norm_num [world12797, agent12797, scalar12797, tp12797, tm12797, ep12797, em12797, dsL]
  · norm_num [world12797, agent12797, scalar12797, tp12797, tm12797, ep12797, em12797, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12797, agent12797, tp12797, tm12797, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12797, agent12797, scalar12797, tp12797, tm12797, ep12797, em12797, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12797, agent12797, tp12797, tm12797, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12797, agent12797, scalar12797, tp12797, tm12797, ep12797, em12797, dsL]

theorem negative12797 :
    Eminus aL (agent12797.root+dsL) scalar12797.worldRadius world12797.frame
      agent12797.frame tm12797 ≤ -em12797 := by
  apply negative_check (lo := (68405694346136618803 / 100000000000000000000)) (hi := (17101423586534154701 / 25000000000000000000))
    (y := (-((17918925785598840913 / 25000000000000000000)))) (u := (48833334054851963653 / 100000000000000000000))
  · norm_num [world12797, agent12797, scalar12797, tp12797, tm12797, ep12797, em12797, dsL]
  · norm_num [world12797, agent12797, scalar12797, tp12797, tm12797, ep12797, em12797, dsL]
  · norm_num [world12797, agent12797, scalar12797, tp12797, tm12797, ep12797, em12797, dsL]
  · norm_num [world12797, agent12797, scalar12797, tp12797, tm12797, ep12797, em12797, dsL]
  · norm_num [world12797, agent12797, scalar12797, tp12797, tm12797, ep12797, em12797, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12797, agent12797, tp12797, tm12797, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12797, agent12797, tp12797, tm12797, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12797, agent12797, scalar12797, tp12797, tm12797, ep12797, em12797, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12797, agent12797, tp12797, tm12797, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12797, agent12797, scalar12797, tp12797, tm12797, ep12797, em12797, dsL]

theorem tails12797 :
    exp (-((12797:ℝ)*ep12797)) ≤ scalar12797.upperTail ∧
    exp (-((12797:ℝ)*em12797)) ≤ scalar12797.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12797:ℝ)) (by norm_num [ep12797]) ?_)
      (show bp12797^8 ≤ scalar12797.upperTail by norm_num [bp12797, scalar12797])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12797, bp12797, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12797:ℝ)) (by norm_num [em12797]) ?_)
      (show bm12797^8 ≤ scalar12797.lowerTail by norm_num [bm12797, scalar12797])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12797, bm12797, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12797 :
    agent12797.root+dsL+scalar12797.worldRadius < √(1/100/aL) ∧
    2*(agent12797.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12797, agent12797, scalar12797, tp12797, tm12797, ep12797, em12797, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12797, agent12797, scalar12797, tp12797, tm12797, ep12797, em12797, dsL]

noncomputable def master12797 : MasterCertificate 12797 world12797 agent12797 :=
  master scalar12797 dsL tp12797 tm12797 ep12797 em12797
    (by norm_num [dsL]) (by norm_num [tp12797]) (by norm_num [tm12797])
    (by norm_num [ep12797]) (by norm_num [em12797])
    positive12797 negative12797 tails12797.1 tails12797.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12797.1 tailGuards12797.2

theorem preserves12797 : master12797.toScalarCertificate = scalar12797 := rfl

noncomputable def tp12798 : ℝ := (465070061 / 2000000000)
noncomputable def tm12798 : ℝ := (-((6082469211 / 10000000000)))
noncomputable def ep12798 : ℝ := (12922165371159131 / 25000000000000000000)
noncomputable def em12798 : ℝ := (50338757452851513 / 100000000000000000000)
noncomputable def bp12798 : ℝ := (21870389478402889733 / 50000000000000000000)
noncomputable def bm12798 : ℝ := (8939127605996468821 / 20000000000000000000)

theorem positive12798 :
    Eplus aL (agent12798.root+dsL) scalar12798.worldRadius world12798.frame
      agent12798.frame tp12798 ≤ -ep12798 := by
  apply positive_check (eT := (5781163910568302783 / 5000000000000000000)) (y := (1517235633658487857 / 4000000000000000000)) (u := (146127436597771116849 / 100000000000000000000))
  · norm_num [world12798, agent12798, scalar12798, tp12798, tm12798, ep12798, em12798, dsL]
  · norm_num [world12798, agent12798, scalar12798, tp12798, tm12798, ep12798, em12798, dsL]
  · norm_num [world12798, agent12798, scalar12798, tp12798, tm12798, ep12798, em12798, dsL]
  · norm_num [world12798, agent12798, scalar12798, tp12798, tm12798, ep12798, em12798, dsL]
  · norm_num [world12798, agent12798, scalar12798, tp12798, tm12798, ep12798, em12798, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12798, agent12798, tp12798, tm12798, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12798, agent12798, scalar12798, tp12798, tm12798, ep12798, em12798, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12798, agent12798, tp12798, tm12798, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12798, agent12798, scalar12798, tp12798, tm12798, ep12798, em12798, dsL]

theorem negative12798 :
    Eminus aL (agent12798.root+dsL) scalar12798.worldRadius world12798.frame
      agent12798.frame tm12798 ≤ -em12798 := by
  apply negative_check (lo := (34202756007089432629 / 50000000000000000000)) (hi := (68405512014178865259 / 100000000000000000000))
    (y := (-((3583786812231344671 / 5000000000000000000)))) (u := (9766663577986267317 / 20000000000000000000))
  · norm_num [world12798, agent12798, scalar12798, tp12798, tm12798, ep12798, em12798, dsL]
  · norm_num [world12798, agent12798, scalar12798, tp12798, tm12798, ep12798, em12798, dsL]
  · norm_num [world12798, agent12798, scalar12798, tp12798, tm12798, ep12798, em12798, dsL]
  · norm_num [world12798, agent12798, scalar12798, tp12798, tm12798, ep12798, em12798, dsL]
  · norm_num [world12798, agent12798, scalar12798, tp12798, tm12798, ep12798, em12798, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12798, agent12798, tp12798, tm12798, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12798, agent12798, tp12798, tm12798, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12798, agent12798, scalar12798, tp12798, tm12798, ep12798, em12798, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12798, agent12798, tp12798, tm12798, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12798, agent12798, scalar12798, tp12798, tm12798, ep12798, em12798, dsL]

theorem tails12798 :
    exp (-((12798:ℝ)*ep12798)) ≤ scalar12798.upperTail ∧
    exp (-((12798:ℝ)*em12798)) ≤ scalar12798.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12798:ℝ)) (by norm_num [ep12798]) ?_)
      (show bp12798^8 ≤ scalar12798.upperTail by norm_num [bp12798, scalar12798])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12798, bp12798, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12798:ℝ)) (by norm_num [em12798]) ?_)
      (show bm12798^8 ≤ scalar12798.lowerTail by norm_num [bm12798, scalar12798])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12798, bm12798, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12798 :
    agent12798.root+dsL+scalar12798.worldRadius < √(1/100/aL) ∧
    2*(agent12798.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12798, agent12798, scalar12798, tp12798, tm12798, ep12798, em12798, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12798, agent12798, scalar12798, tp12798, tm12798, ep12798, em12798, dsL]

noncomputable def master12798 : MasterCertificate 12798 world12798 agent12798 :=
  master scalar12798 dsL tp12798 tm12798 ep12798 em12798
    (by norm_num [dsL]) (by norm_num [tp12798]) (by norm_num [tm12798])
    (by norm_num [ep12798]) (by norm_num [em12798])
    positive12798 negative12798 tails12798.1 tails12798.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12798.1 tailGuards12798.2

theorem preserves12798 : master12798.toScalarCertificate = scalar12798 := rfl

noncomputable def tp12799 : ℝ := (2325432199 / 10000000000)
noncomputable def tm12799 : ℝ := (-((6082644317 / 10000000000)))
noncomputable def ep12799 : ℝ := (12922791341519457 / 25000000000000000000)
noncomputable def em12799 : ℝ := (3146306209687983 / 6250000000000000000)
noncomputable def bp12799 : ℝ := (2733512553613513883 / 6250000000000000000)
noncomputable def bm12799 : ℝ := (2793205888637813069 / 6250000000000000000)

theorem positive12799 :
    Eplus aL (agent12799.root+dsL) scalar12799.worldRadius world12799.frame
      agent12799.frame tp12799 ≤ -ep12799 := by
  apply positive_check (eT := (11562350293287506101 / 10000000000000000000)) (y := (3793164705621063019 / 10000000000000000000)) (u := (146128541639176415169 / 100000000000000000000))
  · norm_num [world12799, agent12799, scalar12799, tp12799, tm12799, ep12799, em12799, dsL]
  · norm_num [world12799, agent12799, scalar12799, tp12799, tm12799, ep12799, em12799, dsL]
  · norm_num [world12799, agent12799, scalar12799, tp12799, tm12799, ep12799, em12799, dsL]
  · norm_num [world12799, agent12799, scalar12799, tp12799, tm12799, ep12799, em12799, dsL]
  · norm_num [world12799, agent12799, scalar12799, tp12799, tm12799, ep12799, em12799, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12799, agent12799, tp12799, tm12799, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12799, agent12799, scalar12799, tp12799, tm12799, ep12799, em12799, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12799, agent12799, tp12799, tm12799, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12799, agent12799, scalar12799, tp12799, tm12799, ep12799, em12799, dsL]

theorem negative12799 :
    Eminus aL (agent12799.root+dsL) scalar12799.worldRadius world12799.frame
      agent12799.frame tm12799 ≤ -em12799 := by
  apply negative_check (lo := (1368106624960524837 / 2000000000000000000)) (hi := (68405331248026241851 / 100000000000000000000))
    (y := (-((1791894151617800667 / 2500000000000000000)))) (u := (48833303327796539633 / 100000000000000000000))
  · norm_num [world12799, agent12799, scalar12799, tp12799, tm12799, ep12799, em12799, dsL]
  · norm_num [world12799, agent12799, scalar12799, tp12799, tm12799, ep12799, em12799, dsL]
  · norm_num [world12799, agent12799, scalar12799, tp12799, tm12799, ep12799, em12799, dsL]
  · norm_num [world12799, agent12799, scalar12799, tp12799, tm12799, ep12799, em12799, dsL]
  · norm_num [world12799, agent12799, scalar12799, tp12799, tm12799, ep12799, em12799, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12799, agent12799, tp12799, tm12799, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12799, agent12799, tp12799, tm12799, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12799, agent12799, scalar12799, tp12799, tm12799, ep12799, em12799, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12799, agent12799, tp12799, tm12799, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12799, agent12799, scalar12799, tp12799, tm12799, ep12799, em12799, dsL]

theorem tails12799 :
    exp (-((12799:ℝ)*ep12799)) ≤ scalar12799.upperTail ∧
    exp (-((12799:ℝ)*em12799)) ≤ scalar12799.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12799:ℝ)) (by norm_num [ep12799]) ?_)
      (show bp12799^8 ≤ scalar12799.upperTail by norm_num [bp12799, scalar12799])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12799, bp12799, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12799:ℝ)) (by norm_num [em12799]) ?_)
      (show bm12799^8 ≤ scalar12799.lowerTail by norm_num [bm12799, scalar12799])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12799, bm12799, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12799 :
    agent12799.root+dsL+scalar12799.worldRadius < √(1/100/aL) ∧
    2*(agent12799.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12799, agent12799, scalar12799, tp12799, tm12799, ep12799, em12799, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12799, agent12799, scalar12799, tp12799, tm12799, ep12799, em12799, dsL]

noncomputable def master12799 : MasterCertificate 12799 world12799 agent12799 :=
  master scalar12799 dsL tp12799 tm12799 ep12799 em12799
    (by norm_num [dsL]) (by norm_num [tp12799]) (by norm_num [tm12799])
    (by norm_num [ep12799]) (by norm_num [em12799])
    positive12799 negative12799 tails12799.1 tails12799.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12799.1 tailGuards12799.2

theorem preserves12799 : master12799.toScalarCertificate = scalar12799 := rfl

end BstLean.Part268
