import BstLean.Part261Checker
import BstLean.Part281Scalar6
namespace BstLean.Part281
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12009 : ℝ := (2358676479 / 10000000000)
noncomputable def tm12009 : ℝ := (-((1526747957 / 2500000000)))
noncomputable def ep12009 : ℝ := (54177036595800903 / 100000000000000000000)
noncomputable def em12009 : ℝ := (1633582163090469 / 3125000000000000000)
noncomputable def bp12009 : ℝ := (22170397759998953489 / 50000000000000000000)
noncomputable def bm12009 : ℝ := (5703164045000902243 / 12500000000000000000)

theorem positive12009 :
    Eplus aL (agent12009.root+dsL) scalar12009.worldRadius world12009.frame
      agent12009.frame tp12009 ≤ -ep12009 := by
  apply positive_check (eT := (116178111344827065031 / 100000000000000000000)) (y := (7907042404555759757 / 20000000000000000000)) (u := (74245348232727380457 / 50000000000000000000))
  · norm_num [world12009, agent12009, scalar12009, tp12009, tm12009, ep12009, em12009, dsL]
  · norm_num [world12009, agent12009, scalar12009, tp12009, tm12009, ep12009, em12009, dsL]
  · norm_num [world12009, agent12009, scalar12009, tp12009, tm12009, ep12009, em12009, dsL]
  · norm_num [world12009, agent12009, scalar12009, tp12009, tm12009, ep12009, em12009, dsL]
  · norm_num [world12009, agent12009, scalar12009, tp12009, tm12009, ep12009, em12009, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12009, agent12009, tp12009, tm12009, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12009, agent12009, scalar12009, tp12009, tm12009, ep12009, em12009, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12009, agent12009, tp12009, tm12009, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12009, agent12009, scalar12009, tp12009, tm12009, ep12009, em12009, dsL]

theorem negative12009 :
    Eminus aL (agent12009.root+dsL) scalar12009.worldRadius world12009.frame
      agent12009.frame tm12009 ≤ -em12009 := by
  apply negative_check (lo := (16955972996085161401 / 25000000000000000000)) (hi := (13564778396868129121 / 20000000000000000000))
    (y := (-((36678386771872105341 / 50000000000000000000)))) (u := (12004818242765220677 / 25000000000000000000))
  · norm_num [world12009, agent12009, scalar12009, tp12009, tm12009, ep12009, em12009, dsL]
  · norm_num [world12009, agent12009, scalar12009, tp12009, tm12009, ep12009, em12009, dsL]
  · norm_num [world12009, agent12009, scalar12009, tp12009, tm12009, ep12009, em12009, dsL]
  · norm_num [world12009, agent12009, scalar12009, tp12009, tm12009, ep12009, em12009, dsL]
  · norm_num [world12009, agent12009, scalar12009, tp12009, tm12009, ep12009, em12009, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12009, agent12009, tp12009, tm12009, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12009, agent12009, tp12009, tm12009, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12009, agent12009, scalar12009, tp12009, tm12009, ep12009, em12009, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12009, agent12009, tp12009, tm12009, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12009, agent12009, scalar12009, tp12009, tm12009, ep12009, em12009, dsL]

theorem tails12009 :
    exp (-((12009:ℝ)*ep12009)) ≤ scalar12009.upperTail ∧
    exp (-((12009:ℝ)*em12009)) ≤ scalar12009.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12009:ℝ)) (by norm_num [ep12009]) ?_)
      (show bp12009^8 ≤ scalar12009.upperTail by norm_num [bp12009, scalar12009])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12009, bp12009, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12009:ℝ)) (by norm_num [em12009]) ?_)
      (show bm12009^8 ≤ scalar12009.lowerTail by norm_num [bm12009, scalar12009])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12009, bm12009, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12009 :
    agent12009.root+dsL+scalar12009.worldRadius < √(1/100/aL) ∧
    2*(agent12009.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12009, agent12009, scalar12009, tp12009, tm12009, ep12009, em12009, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12009, agent12009, scalar12009, tp12009, tm12009, ep12009, em12009, dsL]

noncomputable def master12009 : MasterCertificate 12009 world12009 agent12009 :=
  master scalar12009 dsL tp12009 tm12009 ep12009 em12009
    (by norm_num [dsL]) (by norm_num [tp12009]) (by norm_num [tm12009])
    (by norm_num [ep12009]) (by norm_num [em12009])
    positive12009 negative12009 tails12009.1 tails12009.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12009.1 tailGuards12009.2

theorem preserves12009 : master12009.toScalarCertificate = scalar12009 := rfl

noncomputable def tp12010 : ℝ := (2358781483 / 10000000000)
noncomputable def tm12010 : ℝ := (-((763403553 / 1250000000)))
noncomputable def ep12010 : ℝ := (54180140139049177 / 100000000000000000000)
noncomputable def em12010 : ℝ := (52277338035099829 / 100000000000000000000)
noncomputable def bp12010 : ℝ := (11083931767438461411 / 25000000000000000000)
noncomputable def bm12010 : ℝ := (11137811500206037 / 24414062500000000)

theorem positive12010 :
    Eplus aL (agent12010.root+dsL) scalar12010.worldRadius world12010.frame
      agent12010.frame tp12010 ≤ -ep12010 := by
  apply positive_check (eT := (453822115178788103 / 390625000000000000)) (y := (39535888561388377759 / 100000000000000000000)) (u := (74245850532873116513 / 50000000000000000000))
  · norm_num [world12010, agent12010, scalar12010, tp12010, tm12010, ep12010, em12010, dsL]
  · norm_num [world12010, agent12010, scalar12010, tp12010, tm12010, ep12010, em12010, dsL]
  · norm_num [world12010, agent12010, scalar12010, tp12010, tm12010, ep12010, em12010, dsL]
  · norm_num [world12010, agent12010, scalar12010, tp12010, tm12010, ep12010, em12010, dsL]
  · norm_num [world12010, agent12010, scalar12010, tp12010, tm12010, ep12010, em12010, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12010, agent12010, tp12010, tm12010, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12010, agent12010, scalar12010, tp12010, tm12010, ep12010, em12010, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12010, agent12010, tp12010, tm12010, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12010, agent12010, scalar12010, tp12010, tm12010, ep12010, em12010, dsL]

theorem negative12010 :
    Eminus aL (agent12010.root+dsL) scalar12010.worldRadius world12010.frame
      agent12010.frame tm12010 ≤ -em12010 := by
  apply negative_check (lo := (16955878710562195221 / 25000000000000000000)) (hi := (13564702968449756177 / 20000000000000000000))
    (y := (-((18339102636210529111 / 25000000000000000000)))) (u := (48019447280810932343 / 100000000000000000000))
  · norm_num [world12010, agent12010, scalar12010, tp12010, tm12010, ep12010, em12010, dsL]
  · norm_num [world12010, agent12010, scalar12010, tp12010, tm12010, ep12010, em12010, dsL]
  · norm_num [world12010, agent12010, scalar12010, tp12010, tm12010, ep12010, em12010, dsL]
  · norm_num [world12010, agent12010, scalar12010, tp12010, tm12010, ep12010, em12010, dsL]
  · norm_num [world12010, agent12010, scalar12010, tp12010, tm12010, ep12010, em12010, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12010, agent12010, tp12010, tm12010, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12010, agent12010, tp12010, tm12010, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12010, agent12010, scalar12010, tp12010, tm12010, ep12010, em12010, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12010, agent12010, tp12010, tm12010, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12010, agent12010, scalar12010, tp12010, tm12010, ep12010, em12010, dsL]

theorem tails12010 :
    exp (-((12010:ℝ)*ep12010)) ≤ scalar12010.upperTail ∧
    exp (-((12010:ℝ)*em12010)) ≤ scalar12010.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12010:ℝ)) (by norm_num [ep12010]) ?_)
      (show bp12010^8 ≤ scalar12010.upperTail by norm_num [bp12010, scalar12010])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12010, bp12010, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12010:ℝ)) (by norm_num [em12010]) ?_)
      (show bm12010^8 ≤ scalar12010.lowerTail by norm_num [bm12010, scalar12010])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12010, bm12010, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12010 :
    agent12010.root+dsL+scalar12010.worldRadius < √(1/100/aL) ∧
    2*(agent12010.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12010, agent12010, scalar12010, tp12010, tm12010, ep12010, em12010, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12010, agent12010, scalar12010, tp12010, tm12010, ep12010, em12010, dsL]

noncomputable def master12010 : MasterCertificate 12010 world12010 agent12010 :=
  master scalar12010 dsL tp12010 tm12010 ep12010 em12010
    (by norm_num [dsL]) (by norm_num [tp12010]) (by norm_num [tm12010])
    (by norm_num [ep12010]) (by norm_num [em12010])
    positive12010 negative12010 tails12010.1 tails12010.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12010.1 tailGuards12010.2

theorem preserves12010 : master12010.toScalarCertificate = scalar12010 := rfl

noncomputable def tp12011 : ℝ := (1179443253 / 5000000000)
noncomputable def tm12011 : ℝ := (-((6107465249 / 10000000000)))
noncomputable def ep12011 : ℝ := (54183243678884409 / 100000000000000000000)
noncomputable def em12011 : ℝ := (52280046896573591 / 100000000000000000000)
noncomputable def bp12011 : ℝ := (44330658857183955063 / 100000000000000000000)
noncomputable def bm12011 : ℝ := (9123127924489838627 / 20000000000000000000)

theorem positive12011 :
    Eplus aL (agent12011.root+dsL) scalar12011.worldRadius world12011.frame
      agent12011.frame tp12011 ≤ -ep12011 := by
  apply positive_check (eT := (116178811803310116823 / 100000000000000000000)) (y := (9884141290722936121 / 25000000000000000000)) (u := (74246352883113462067 / 50000000000000000000))
  · norm_num [world12011, agent12011, scalar12011, tp12011, tm12011, ep12011, em12011, dsL]
  · norm_num [world12011, agent12011, scalar12011, tp12011, tm12011, ep12011, em12011, dsL]
  · norm_num [world12011, agent12011, scalar12011, tp12011, tm12011, ep12011, em12011, dsL]
  · norm_num [world12011, agent12011, scalar12011, tp12011, tm12011, ep12011, em12011, dsL]
  · norm_num [world12011, agent12011, scalar12011, tp12011, tm12011, ep12011, em12011, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12011, agent12011, tp12011, tm12011, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12011, agent12011, scalar12011, tp12011, tm12011, ep12011, em12011, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12011, agent12011, tp12011, tm12011, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12011, agent12011, scalar12011, tp12011, tm12011, ep12011, em12011, dsL]

theorem negative12011 :
    Eminus aL (agent12011.root+dsL) scalar12011.worldRadius world12011.frame
      agent12011.frame tm12011 ≤ -em12011 := by
  apply negative_check (lo := (16955784163556635547 / 25000000000000000000)) (hi := (67823136654226542189 / 100000000000000000000))
    (y := (-((36678024737929445657 / 50000000000000000000)))) (u := (6002452583056749573 / 12500000000000000000))
  · norm_num [world12011, agent12011, scalar12011, tp12011, tm12011, ep12011, em12011, dsL]
  · norm_num [world12011, agent12011, scalar12011, tp12011, tm12011, ep12011, em12011, dsL]
  · norm_num [world12011, agent12011, scalar12011, tp12011, tm12011, ep12011, em12011, dsL]
  · norm_num [world12011, agent12011, scalar12011, tp12011, tm12011, ep12011, em12011, dsL]
  · norm_num [world12011, agent12011, scalar12011, tp12011, tm12011, ep12011, em12011, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12011, agent12011, tp12011, tm12011, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12011, agent12011, tp12011, tm12011, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12011, agent12011, scalar12011, tp12011, tm12011, ep12011, em12011, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12011, agent12011, tp12011, tm12011, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12011, agent12011, scalar12011, tp12011, tm12011, ep12011, em12011, dsL]

theorem tails12011 :
    exp (-((12011:ℝ)*ep12011)) ≤ scalar12011.upperTail ∧
    exp (-((12011:ℝ)*em12011)) ≤ scalar12011.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12011:ℝ)) (by norm_num [ep12011]) ?_)
      (show bp12011^8 ≤ scalar12011.upperTail by norm_num [bp12011, scalar12011])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12011, bp12011, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12011:ℝ)) (by norm_num [em12011]) ?_)
      (show bm12011^8 ≤ scalar12011.lowerTail by norm_num [bm12011, scalar12011])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12011, bm12011, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12011 :
    agent12011.root+dsL+scalar12011.worldRadius < √(1/100/aL) ∧
    2*(agent12011.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12011, agent12011, scalar12011, tp12011, tm12011, ep12011, em12011, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12011, agent12011, scalar12011, tp12011, tm12011, ep12011, em12011, dsL]

noncomputable def master12011 : MasterCertificate 12011 world12011 agent12011 :=
  master scalar12011 dsL tp12011 tm12011 ep12011 em12011
    (by norm_num [dsL]) (by norm_num [tp12011]) (by norm_num [tm12011])
    (by norm_num [ep12011]) (by norm_num [em12011])
    positive12011 negative12011 tails12011.1 tails12011.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12011.1 tailGuards12011.2

theorem preserves12011 : master12011.toScalarCertificate = scalar12011 := rfl

noncomputable def tp12012 : ℝ := (235899143 / 1000000000)
noncomputable def tm12012 : ℝ := (-((6107701591 / 10000000000)))
noncomputable def ep12012 : ℝ := (54186344606858969 / 100000000000000000000)
noncomputable def em12012 : ℝ := (52282753354026793 / 100000000000000000000)
noncomputable def bp12012 : ℝ := (44325592618388842189 / 100000000000000000000)
noncomputable def bm12012 : ℝ := (9122161038051140817 / 20000000000000000000)

theorem positive12012 :
    Eplus aL (agent12012.root+dsL) scalar12012.worldRadius world12012.frame
      agent12012.frame tp12012 ≤ -ep12012 := by
  apply positive_check (eT := (116179161425891392783 / 100000000000000000000)) (y := (1976862037854918633 / 5000000000000000000)) (u := (148493708977733161779 / 100000000000000000000))
  · norm_num [world12012, agent12012, scalar12012, tp12012, tm12012, ep12012, em12012, dsL]
  · norm_num [world12012, agent12012, scalar12012, tp12012, tm12012, ep12012, em12012, dsL]
  · norm_num [world12012, agent12012, scalar12012, tp12012, tm12012, ep12012, em12012, dsL]
  · norm_num [world12012, agent12012, scalar12012, tp12012, tm12012, ep12012, em12012, dsL]
  · norm_num [world12012, agent12012, scalar12012, tp12012, tm12012, ep12012, em12012, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12012, agent12012, tp12012, tm12012, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12012, agent12012, scalar12012, tp12012, tm12012, ep12012, em12012, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12012, agent12012, tp12012, tm12012, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12012, agent12012, scalar12012, tp12012, tm12012, ep12012, em12012, dsL]

theorem negative12012 :
    Eminus aL (agent12012.root+dsL) scalar12012.worldRadius world12012.frame
      agent12012.frame tm12012 ≤ -em12012 := by
  apply negative_check (lo := (67822760490262148297 / 100000000000000000000)) (hi := (33911380245131074149 / 50000000000000000000))
    (y := (-((36677842425259319229 / 50000000000000000000)))) (u := (48019795756478447231 / 100000000000000000000))
  · norm_num [world12012, agent12012, scalar12012, tp12012, tm12012, ep12012, em12012, dsL]
  · norm_num [world12012, agent12012, scalar12012, tp12012, tm12012, ep12012, em12012, dsL]
  · norm_num [world12012, agent12012, scalar12012, tp12012, tm12012, ep12012, em12012, dsL]
  · norm_num [world12012, agent12012, scalar12012, tp12012, tm12012, ep12012, em12012, dsL]
  · norm_num [world12012, agent12012, scalar12012, tp12012, tm12012, ep12012, em12012, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12012, agent12012, tp12012, tm12012, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12012, agent12012, tp12012, tm12012, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12012, agent12012, scalar12012, tp12012, tm12012, ep12012, em12012, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12012, agent12012, tp12012, tm12012, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12012, agent12012, scalar12012, tp12012, tm12012, ep12012, em12012, dsL]

theorem tails12012 :
    exp (-((12012:ℝ)*ep12012)) ≤ scalar12012.upperTail ∧
    exp (-((12012:ℝ)*em12012)) ≤ scalar12012.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12012:ℝ)) (by norm_num [ep12012]) ?_)
      (show bp12012^8 ≤ scalar12012.upperTail by norm_num [bp12012, scalar12012])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12012, bp12012, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12012:ℝ)) (by norm_num [em12012]) ?_)
      (show bm12012^8 ≤ scalar12012.lowerTail by norm_num [bm12012, scalar12012])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12012, bm12012, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12012 :
    agent12012.root+dsL+scalar12012.worldRadius < √(1/100/aL) ∧
    2*(agent12012.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12012, agent12012, scalar12012, tp12012, tm12012, ep12012, em12012, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12012, agent12012, scalar12012, tp12012, tm12012, ep12012, em12012, dsL]

noncomputable def master12012 : MasterCertificate 12012 world12012 agent12012 :=
  master scalar12012 dsL tp12012 tm12012 ep12012 em12012
    (by norm_num [dsL]) (by norm_num [tp12012]) (by norm_num [tm12012])
    (by norm_num [ep12012]) (by norm_num [em12012])
    positive12012 negative12012 tails12012.1 tails12012.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12012.1 tailGuards12012.2

theorem preserves12012 : master12012.toScalarCertificate = scalar12012 := rfl

noncomputable def tp12013 : ℝ := (2359096331 / 10000000000)
noncomputable def tm12013 : ℝ := (-((610793789 / 1000000000)))
noncomputable def ep12013 : ℝ := (54189443925648113 / 100000000000000000000)
noncomputable def em12013 : ℝ := (1307136457986977 / 2500000000000000000)
noncomputable def bp12013 : ℝ := (44320527685949715941 / 100000000000000000000)
noncomputable def bm12013 : ℝ := (2850373248975997629 / 6250000000000000000)

theorem positive12013 :
    Eplus aL (agent12013.root+dsL) scalar12013.worldRadius world12013.frame
      agent12013.frame tp12013 ≤ -ep12013 := by
  apply positive_check (eT := (58089755457419102053 / 50000000000000000000)) (y := (39537916504928993413 / 100000000000000000000)) (u := (18561839053017570869 / 12500000000000000000))
  · norm_num [world12013, agent12013, scalar12013, tp12013, tm12013, ep12013, em12013, dsL]
  · norm_num [world12013, agent12013, scalar12013, tp12013, tm12013, ep12013, em12013, dsL]
  · norm_num [world12013, agent12013, scalar12013, tp12013, tm12013, ep12013, em12013, dsL]
  · norm_num [world12013, agent12013, scalar12013, tp12013, tm12013, ep12013, em12013, dsL]
  · norm_num [world12013, agent12013, scalar12013, tp12013, tm12013, ep12013, em12013, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12013, agent12013, tp12013, tm12013, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12013, agent12013, scalar12013, tp12013, tm12013, ep12013, em12013, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12013, agent12013, tp12013, tm12013, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12013, agent12013, scalar12013, tp12013, tm12013, ep12013, em12013, dsL]

theorem negative12013 :
    Eminus aL (agent12013.root+dsL) scalar12013.worldRadius world12013.frame
      agent12013.frame tm12013 ≤ -em12013 := by
  apply negative_check (lo := (8477798056646230079 / 12500000000000000000)) (hi := (67822384453169840633 / 100000000000000000000))
    (y := (-((36677660414792818937 / 50000000000000000000)))) (u := (24009985279452571729 / 50000000000000000000))
  · norm_num [world12013, agent12013, scalar12013, tp12013, tm12013, ep12013, em12013, dsL]
  · norm_num [world12013, agent12013, scalar12013, tp12013, tm12013, ep12013, em12013, dsL]
  · norm_num [world12013, agent12013, scalar12013, tp12013, tm12013, ep12013, em12013, dsL]
  · norm_num [world12013, agent12013, scalar12013, tp12013, tm12013, ep12013, em12013, dsL]
  · norm_num [world12013, agent12013, scalar12013, tp12013, tm12013, ep12013, em12013, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12013, agent12013, tp12013, tm12013, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12013, agent12013, tp12013, tm12013, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12013, agent12013, scalar12013, tp12013, tm12013, ep12013, em12013, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12013, agent12013, tp12013, tm12013, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12013, agent12013, scalar12013, tp12013, tm12013, ep12013, em12013, dsL]

theorem tails12013 :
    exp (-((12013:ℝ)*ep12013)) ≤ scalar12013.upperTail ∧
    exp (-((12013:ℝ)*em12013)) ≤ scalar12013.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12013:ℝ)) (by norm_num [ep12013]) ?_)
      (show bp12013^8 ≤ scalar12013.upperTail by norm_num [bp12013, scalar12013])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12013, bp12013, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12013:ℝ)) (by norm_num [em12013]) ?_)
      (show bm12013^8 ≤ scalar12013.lowerTail by norm_num [bm12013, scalar12013])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12013, bm12013, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12013 :
    agent12013.root+dsL+scalar12013.worldRadius < √(1/100/aL) ∧
    2*(agent12013.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12013, agent12013, scalar12013, tp12013, tm12013, ep12013, em12013, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12013, agent12013, scalar12013, tp12013, tm12013, ep12013, em12013, dsL]

noncomputable def master12013 : MasterCertificate 12013 world12013 agent12013 :=
  master scalar12013 dsL tp12013 tm12013 ep12013 em12013
    (by norm_num [dsL]) (by norm_num [tp12013]) (by norm_num [tm12013])
    (by norm_num [ep12013]) (by norm_num [em12013])
    positive12013 negative12013 tails12013.1 tails12013.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12013.1 tailGuards12013.2

theorem preserves12013 : master12013.toScalarCertificate = scalar12013 := rfl

noncomputable def tp12014 : ℝ := (1179600577 / 5000000000)
noncomputable def tm12014 : ℝ := (-((1527043589 / 2500000000)))
noncomputable def ep12014 : ℝ := (54192542670724301 / 100000000000000000000)
noncomputable def em12014 : ℝ := (52288162681471567 / 100000000000000000000)
noncomputable def bp12014 : ℝ := (8863092674140764239 / 20000000000000000000)
noncomputable def bm12014 : ℝ := (9120227878803539111 / 20000000000000000000)

theorem positive12014 :
    Eplus aL (agent12014.root+dsL) scalar12014.worldRadius world12014.frame
      agent12014.frame tp12014 ≤ -ep12014 := by
  apply positive_check (eT := (29044964966001819451 / 25000000000000000000)) (y := (308895247116839023 / 781250000000000000)) (u := (74247857476988069273 / 50000000000000000000))
  · norm_num [world12014, agent12014, scalar12014, tp12014, tm12014, ep12014, em12014, dsL]
  · norm_num [world12014, agent12014, scalar12014, tp12014, tm12014, ep12014, em12014, dsL]
  · norm_num [world12014, agent12014, scalar12014, tp12014, tm12014, ep12014, em12014, dsL]
  · norm_num [world12014, agent12014, scalar12014, tp12014, tm12014, ep12014, em12014, dsL]
  · norm_num [world12014, agent12014, scalar12014, tp12014, tm12014, ep12014, em12014, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12014, agent12014, tp12014, tm12014, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12014, agent12014, scalar12014, tp12014, tm12014, ep12014, em12014, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12014, agent12014, tp12014, tm12014, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12014, agent12014, scalar12014, tp12014, tm12014, ep12014, em12014, dsL]

theorem negative12014 :
    Eminus aL (agent12014.root+dsL) scalar12014.worldRadius world12014.frame
      agent12014.frame tm12014 ≤ -em12014 := by
  apply negative_check (lo := (16955501909376757737 / 25000000000000000000)) (hi := (67822007637507030949 / 100000000000000000000))
    (y := (-((36677480165846806691 / 50000000000000000000)))) (u := (12005035917549697547 / 25000000000000000000))
  · norm_num [world12014, agent12014, scalar12014, tp12014, tm12014, ep12014, em12014, dsL]
  · norm_num [world12014, agent12014, scalar12014, tp12014, tm12014, ep12014, em12014, dsL]
  · norm_num [world12014, agent12014, scalar12014, tp12014, tm12014, ep12014, em12014, dsL]
  · norm_num [world12014, agent12014, scalar12014, tp12014, tm12014, ep12014, em12014, dsL]
  · norm_num [world12014, agent12014, scalar12014, tp12014, tm12014, ep12014, em12014, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12014, agent12014, tp12014, tm12014, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12014, agent12014, tp12014, tm12014, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12014, agent12014, scalar12014, tp12014, tm12014, ep12014, em12014, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12014, agent12014, tp12014, tm12014, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12014, agent12014, scalar12014, tp12014, tm12014, ep12014, em12014, dsL]

theorem tails12014 :
    exp (-((12014:ℝ)*ep12014)) ≤ scalar12014.upperTail ∧
    exp (-((12014:ℝ)*em12014)) ≤ scalar12014.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12014:ℝ)) (by norm_num [ep12014]) ?_)
      (show bp12014^8 ≤ scalar12014.upperTail by norm_num [bp12014, scalar12014])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12014, bp12014, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12014:ℝ)) (by norm_num [em12014]) ?_)
      (show bm12014^8 ≤ scalar12014.lowerTail by norm_num [bm12014, scalar12014])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12014, bm12014, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12014 :
    agent12014.root+dsL+scalar12014.worldRadius < √(1/100/aL) ∧
    2*(agent12014.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12014, agent12014, scalar12014, tp12014, tm12014, ep12014, em12014, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12014, agent12014, scalar12014, tp12014, tm12014, ep12014, em12014, dsL]

noncomputable def master12014 : MasterCertificate 12014 world12014 agent12014 :=
  master scalar12014 dsL tp12014 tm12014 ep12014 em12014
    (by norm_num [dsL]) (by norm_num [tp12014]) (by norm_num [tm12014])
    (by norm_num [ep12014]) (by norm_num [em12014])
    positive12014 negative12014 tails12014.1 tails12014.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12014.1 tailGuards12014.2

theorem preserves12014 : master12014.toScalarCertificate = scalar12014 := rfl

noncomputable def tp12015 : ℝ := (2359305923 / 10000000000)
noncomputable def tm12015 : ℝ := (-((6108410297 / 10000000000)))
noncomputable def ep12015 : ℝ := (433565106549993 / 800000000000000000)
noncomputable def em12015 : ℝ := (26145432096983577 / 50000000000000000000)
noncomputable def bp12015 : ℝ := (44310401351915651273 / 100000000000000000000)
noncomputable def bm12015 : ℝ := (45596308959561678039 / 100000000000000000000)

theorem positive12015 :
    Eplus aL (agent12015.root+dsL) scalar12015.worldRadius world12015.frame
      agent12015.frame tp12015 ≤ -ep12015 := by
  apply positive_check (eT := (116180208450634306647 / 100000000000000000000)) (y := (19769633306148658093 / 50000000000000000000)) (u := (148496717275728369037 / 100000000000000000000))
  · norm_num [world12015, agent12015, scalar12015, tp12015, tm12015, ep12015, em12015, dsL]
  · norm_num [world12015, agent12015, scalar12015, tp12015, tm12015, ep12015, em12015, dsL]
  · norm_num [world12015, agent12015, scalar12015, tp12015, tm12015, ep12015, em12015, dsL]
  · norm_num [world12015, agent12015, scalar12015, tp12015, tm12015, ep12015, em12015, dsL]
  · norm_num [world12015, agent12015, scalar12015, tp12015, tm12015, ep12015, em12015, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12015, agent12015, tp12015, tm12015, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12015, agent12015, scalar12015, tp12015, tm12015, ep12015, em12015, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12015, agent12015, tp12015, tm12015, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12015, agent12015, scalar12015, tp12015, tm12015, ep12015, em12015, dsL]

theorem negative12015 :
    Eminus aL (agent12015.root+dsL) scalar12015.worldRadius world12015.frame
      agent12015.frame tm12015 ≤ -em12015 := by
  apply negative_check (lo := (2712865321069547457 / 4000000000000000000)) (hi := (33910816513369343213 / 50000000000000000000))
    (y := (-((73354595733347401217 / 100000000000000000000)))) (u := (48020318751167631403 / 100000000000000000000))
  · norm_num [world12015, agent12015, scalar12015, tp12015, tm12015, ep12015, em12015, dsL]
  · norm_num [world12015, agent12015, scalar12015, tp12015, tm12015, ep12015, em12015, dsL]
  · norm_num [world12015, agent12015, scalar12015, tp12015, tm12015, ep12015, em12015, dsL]
  · norm_num [world12015, agent12015, scalar12015, tp12015, tm12015, ep12015, em12015, dsL]
  · norm_num [world12015, agent12015, scalar12015, tp12015, tm12015, ep12015, em12015, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12015, agent12015, tp12015, tm12015, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12015, agent12015, tp12015, tm12015, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12015, agent12015, scalar12015, tp12015, tm12015, ep12015, em12015, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12015, agent12015, tp12015, tm12015, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12015, agent12015, scalar12015, tp12015, tm12015, ep12015, em12015, dsL]

theorem tails12015 :
    exp (-((12015:ℝ)*ep12015)) ≤ scalar12015.upperTail ∧
    exp (-((12015:ℝ)*em12015)) ≤ scalar12015.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12015:ℝ)) (by norm_num [ep12015]) ?_)
      (show bp12015^8 ≤ scalar12015.upperTail by norm_num [bp12015, scalar12015])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12015, bp12015, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12015:ℝ)) (by norm_num [em12015]) ?_)
      (show bm12015^8 ≤ scalar12015.lowerTail by norm_num [bm12015, scalar12015])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12015, bm12015, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12015 :
    agent12015.root+dsL+scalar12015.worldRadius < √(1/100/aL) ∧
    2*(agent12015.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12015, agent12015, scalar12015, tp12015, tm12015, ep12015, em12015, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12015, agent12015, scalar12015, tp12015, tm12015, ep12015, em12015, dsL]

noncomputable def master12015 : MasterCertificate 12015 world12015 agent12015 :=
  master scalar12015 dsL tp12015 tm12015 ep12015 em12015
    (by norm_num [dsL]) (by norm_num [tp12015]) (by norm_num [tm12015])
    (by norm_num [ep12015]) (by norm_num [em12015])
    positive12015 negative12015 tails12015.1 tails12015.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12015.1 tailGuards12015.2

theorem preserves12015 : master12015.toScalarCertificate = scalar12015 := rfl

noncomputable def tp12016 : ℝ := (235941059 / 1000000000)
noncomputable def tm12016 : ℝ := (-((3054323157 / 5000000000)))
noncomputable def ep12016 : ℝ := (54198733068331073 / 100000000000000000000)
noncomputable def em12016 : ℝ := (52293564822012943 / 100000000000000000000)
noncomputable def bp12016 : ℝ := (21633466878098297 / 48828125000000000)
noncomputable def bm12016 : ℝ := (5698934916815726107 / 12500000000000000000)

theorem positive12016 :
    Eplus aL (agent12016.root+dsL) scalar12016.worldRadius world12016.frame
      agent12016.frame tp12016 ≤ -ep12016 := by
  apply positive_check (eT := (116180556320275583013 / 100000000000000000000)) (y := (39539940429747989813 / 100000000000000000000)) (u := (37124429468973538963 / 25000000000000000000))
  · norm_num [world12016, agent12016, scalar12016, tp12016, tm12016, ep12016, em12016, dsL]
  · norm_num [world12016, agent12016, scalar12016, tp12016, tm12016, ep12016, em12016, dsL]
  · norm_num [world12016, agent12016, scalar12016, tp12016, tm12016, ep12016, em12016, dsL]
  · norm_num [world12016, agent12016, scalar12016, tp12016, tm12016, ep12016, em12016, dsL]
  · norm_num [world12016, agent12016, scalar12016, tp12016, tm12016, ep12016, em12016, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12016, agent12016, tp12016, tm12016, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12016, agent12016, scalar12016, tp12016, tm12016, ep12016, em12016, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12016, agent12016, tp12016, tm12016, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12016, agent12016, scalar12016, tp12016, tm12016, ep12016, em12016, dsL]

theorem negative12016 :
    Eminus aL (agent12016.root+dsL) scalar12016.worldRadius world12016.frame
      agent12016.frame tm12016 ≤ -em12016 := by
  apply negative_check (lo := (67821258029714452049 / 100000000000000000000)) (hi := (1356425160594289041 / 2000000000000000000))
    (y := (-((458463958350728231 / 625000000000000000)))) (u := (300128079848677359 / 625000000000000000))
  · norm_num [world12016, agent12016, scalar12016, tp12016, tm12016, ep12016, em12016, dsL]
  · norm_num [world12016, agent12016, scalar12016, tp12016, tm12016, ep12016, em12016, dsL]
  · norm_num [world12016, agent12016, scalar12016, tp12016, tm12016, ep12016, em12016, dsL]
  · norm_num [world12016, agent12016, scalar12016, tp12016, tm12016, ep12016, em12016, dsL]
  · norm_num [world12016, agent12016, scalar12016, tp12016, tm12016, ep12016, em12016, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12016, agent12016, tp12016, tm12016, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12016, agent12016, tp12016, tm12016, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12016, agent12016, scalar12016, tp12016, tm12016, ep12016, em12016, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12016, agent12016, tp12016, tm12016, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12016, agent12016, scalar12016, tp12016, tm12016, ep12016, em12016, dsL]

theorem tails12016 :
    exp (-((12016:ℝ)*ep12016)) ≤ scalar12016.upperTail ∧
    exp (-((12016:ℝ)*em12016)) ≤ scalar12016.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12016:ℝ)) (by norm_num [ep12016]) ?_)
      (show bp12016^8 ≤ scalar12016.upperTail by norm_num [bp12016, scalar12016])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12016, bp12016, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12016:ℝ)) (by norm_num [em12016]) ?_)
      (show bm12016^8 ≤ scalar12016.lowerTail by norm_num [bm12016, scalar12016])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12016, bm12016, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12016 :
    agent12016.root+dsL+scalar12016.worldRadius < √(1/100/aL) ∧
    2*(agent12016.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12016, agent12016, scalar12016, tp12016, tm12016, ep12016, em12016, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12016, agent12016, scalar12016, tp12016, tm12016, ep12016, em12016, dsL]

noncomputable def master12016 : MasterCertificate 12016 world12016 agent12016 :=
  master scalar12016 dsL tp12016 tm12016 ep12016 em12016
    (by norm_num [dsL]) (by norm_num [tp12016]) (by norm_num [tm12016])
    (by norm_num [ep12016]) (by norm_num [em12016])
    positive12016 negative12016 tails12016.1 tails12016.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12016.1 tailGuards12016.2

theorem preserves12016 : master12016.toScalarCertificate = scalar12016 := rfl

noncomputable def tp12017 : ℝ := (2359515247 / 10000000000)
noncomputable def tm12017 : ℝ := (-((6108882073 / 10000000000)))
noncomputable def ep12017 : ℝ := (54201825358127043 / 100000000000000000000)
noncomputable def em12017 : ℝ := (52296263203982253 / 100000000000000000000)
noncomputable def bp12017 : ℝ := (1384383776655547103 / 3125000000000000000)
noncomputable def bm12017 : ℝ := (11396662862827876507 / 25000000000000000000)

theorem positive12017 :
    Eplus aL (agent12017.root+dsL) scalar12017.worldRadius world12017.frame
      agent12017.frame tp12017 ≤ -ep12017 := by
  apply positive_check (eT := (2904522603809157999 / 2500000000000000000)) (y := (19770307342113020689 / 50000000000000000000)) (u := (74249359565891120493 / 50000000000000000000))
  · norm_num [world12017, agent12017, scalar12017, tp12017, tm12017, ep12017, em12017, dsL]
  · norm_num [world12017, agent12017, scalar12017, tp12017, tm12017, ep12017, em12017, dsL]
  · norm_num [world12017, agent12017, scalar12017, tp12017, tm12017, ep12017, em12017, dsL]
  · norm_num [world12017, agent12017, scalar12017, tp12017, tm12017, ep12017, em12017, dsL]
  · norm_num [world12017, agent12017, scalar12017, tp12017, tm12017, ep12017, em12017, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12017, agent12017, tp12017, tm12017, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12017, agent12017, scalar12017, tp12017, tm12017, ep12017, em12017, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12017, agent12017, tp12017, tm12017, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12017, agent12017, scalar12017, tp12017, tm12017, ep12017, em12017, dsL]

theorem negative12017 :
    Eminus aL (agent12017.root+dsL) scalar12017.worldRadius world12017.frame
      agent12017.frame tm12017 ≤ -em12017 := by
  apply negative_check (lo := (67820884086337820153 / 100000000000000000000)) (hi := (33910442043168910077 / 50000000000000000000))
    (y := (-((73353869293844133669 / 100000000000000000000)))) (u := (9604133518199937703 / 20000000000000000000))
  · norm_num [world12017, agent12017, scalar12017, tp12017, tm12017, ep12017, em12017, dsL]
  · norm_num [world12017, agent12017, scalar12017, tp12017, tm12017, ep12017, em12017, dsL]
  · norm_num [world12017, agent12017, scalar12017, tp12017, tm12017, ep12017, em12017, dsL]
  · norm_num [world12017, agent12017, scalar12017, tp12017, tm12017, ep12017, em12017, dsL]
  · norm_num [world12017, agent12017, scalar12017, tp12017, tm12017, ep12017, em12017, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12017, agent12017, tp12017, tm12017, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12017, agent12017, tp12017, tm12017, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12017, agent12017, scalar12017, tp12017, tm12017, ep12017, em12017, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12017, agent12017, tp12017, tm12017, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12017, agent12017, scalar12017, tp12017, tm12017, ep12017, em12017, dsL]

theorem tails12017 :
    exp (-((12017:ℝ)*ep12017)) ≤ scalar12017.upperTail ∧
    exp (-((12017:ℝ)*em12017)) ≤ scalar12017.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12017:ℝ)) (by norm_num [ep12017]) ?_)
      (show bp12017^8 ≤ scalar12017.upperTail by norm_num [bp12017, scalar12017])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12017, bp12017, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12017:ℝ)) (by norm_num [em12017]) ?_)
      (show bm12017^8 ≤ scalar12017.lowerTail by norm_num [bm12017, scalar12017])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12017, bm12017, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12017 :
    agent12017.root+dsL+scalar12017.worldRadius < √(1/100/aL) ∧
    2*(agent12017.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12017, agent12017, scalar12017, tp12017, tm12017, ep12017, em12017, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12017, agent12017, scalar12017, tp12017, tm12017, ep12017, em12017, dsL]

noncomputable def master12017 : MasterCertificate 12017 world12017 agent12017 :=
  master scalar12017 dsL tp12017 tm12017 ep12017 em12017
    (by norm_num [dsL]) (by norm_num [tp12017]) (by norm_num [tm12017])
    (by norm_num [ep12017]) (by norm_num [em12017])
    positive12017 negative12017 tails12017.1 tails12017.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12017.1 tailGuards12017.2

theorem preserves12017 : master12017.toScalarCertificate = scalar12017 := rfl

noncomputable def tp12018 : ℝ := (1179809933 / 5000000000)
noncomputable def tm12018 : ℝ := (-((3054558889 / 5000000000)))
noncomputable def ep12018 : ℝ := (27102458111891423 / 50000000000000000000)
noncomputable def em12018 : ℝ := (1307474005714353 / 2500000000000000000)
noncomputable def bp12018 : ℝ := (1771808908902674463 / 4000000000000000000)
noncomputable def bm12018 : ℝ := (364654597610547009 / 800000000000000000)

theorem positive12018 :
    Eplus aL (agent12018.root+dsL) scalar12018.worldRadius world12018.frame
      agent12018.frame tp12018 ≤ -ep12018 := by
  apply positive_check (eT := (116181251740095685447 / 100000000000000000000)) (y := (19770644543792009631 / 50000000000000000000)) (u := (148499720615507636013 / 100000000000000000000))
  · norm_num [world12018, agent12018, scalar12018, tp12018, tm12018, ep12018, em12018, dsL]
  · norm_num [world12018, agent12018, scalar12018, tp12018, tm12018, ep12018, em12018, dsL]
  · norm_num [world12018, agent12018, scalar12018, tp12018, tm12018, ep12018, em12018, dsL]
  · norm_num [world12018, agent12018, scalar12018, tp12018, tm12018, ep12018, em12018, dsL]
  · norm_num [world12018, agent12018, scalar12018, tp12018, tm12018, ep12018, em12018, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12018, agent12018, tp12018, tm12018, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12018, agent12018, scalar12018, tp12018, tm12018, ep12018, em12018, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12018, agent12018, tp12018, tm12018, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12018, agent12018, scalar12018, tp12018, tm12018, ep12018, em12018, dsL]

theorem negative12018 :
    Eminus aL (agent12018.root+dsL) scalar12018.worldRadius world12018.frame
      agent12018.frame tm12018 ≤ -em12018 := by
  apply negative_check (lo := (132461934213243013 / 195312500000000000)) (hi := (67820510317180422657 / 100000000000000000000))
    (y := (-((14670701293219127231 / 20000000000000000000)))) (u := (6002605227952850547 / 12500000000000000000))
  · norm_num [world12018, agent12018, scalar12018, tp12018, tm12018, ep12018, em12018, dsL]
  · norm_num [world12018, agent12018, scalar12018, tp12018, tm12018, ep12018, em12018, dsL]
  · norm_num [world12018, agent12018, scalar12018, tp12018, tm12018, ep12018, em12018, dsL]
  · norm_num [world12018, agent12018, scalar12018, tp12018, tm12018, ep12018, em12018, dsL]
  · norm_num [world12018, agent12018, scalar12018, tp12018, tm12018, ep12018, em12018, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12018, agent12018, tp12018, tm12018, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12018, agent12018, tp12018, tm12018, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12018, agent12018, scalar12018, tp12018, tm12018, ep12018, em12018, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12018, agent12018, tp12018, tm12018, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12018, agent12018, scalar12018, tp12018, tm12018, ep12018, em12018, dsL]

theorem tails12018 :
    exp (-((12018:ℝ)*ep12018)) ≤ scalar12018.upperTail ∧
    exp (-((12018:ℝ)*em12018)) ≤ scalar12018.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12018:ℝ)) (by norm_num [ep12018]) ?_)
      (show bp12018^8 ≤ scalar12018.upperTail by norm_num [bp12018, scalar12018])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12018, bp12018, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12018:ℝ)) (by norm_num [em12018]) ?_)
      (show bm12018^8 ≤ scalar12018.lowerTail by norm_num [bm12018, scalar12018])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12018, bm12018, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12018 :
    agent12018.root+dsL+scalar12018.worldRadius < √(1/100/aL) ∧
    2*(agent12018.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12018, agent12018, scalar12018, tp12018, tm12018, ep12018, em12018, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12018, agent12018, scalar12018, tp12018, tm12018, ep12018, em12018, dsL]

noncomputable def master12018 : MasterCertificate 12018 world12018 agent12018 :=
  master scalar12018 dsL tp12018 tm12018 ep12018 em12018
    (by norm_num [dsL]) (by norm_num [tp12018]) (by norm_num [tm12018])
    (by norm_num [ep12018]) (by norm_num [em12018])
    positive12018 negative12018 tails12018.1 tails12018.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12018.1 tailGuards12018.2

theorem preserves12018 : master12018.toScalarCertificate = scalar12018 := rfl

noncomputable def tp12019 : ℝ := (47194489 / 200000000)
noncomputable def tm12019 : ℝ := (-((3054676587 / 5000000000)))
noncomputable def ep12019 : ℝ := (27104002690251831 / 50000000000000000000)
noncomputable def em12019 : ℝ := (52301655641556721 / 100000000000000000000)
noncomputable def bp12019 : ℝ := (4429016596458034547 / 10000000000000000000)
noncomputable def bm12019 : ℝ := (45576999258608757827 / 100000000000000000000)

theorem positive12019 :
    Eplus aL (agent12019.root+dsL) scalar12019.worldRadius world12019.frame
      agent12019.frame tp12019 ≤ -ep12019 := by
  apply positive_check (eT := (11618159910570008177 / 10000000000000000000)) (y := (158167853913620877 / 400000000000000000)) (u := (29700144417473977597 / 20000000000000000000))
  · norm_num [world12019, agent12019, scalar12019, tp12019, tm12019, ep12019, em12019, dsL]
  · norm_num [world12019, agent12019, scalar12019, tp12019, tm12019, ep12019, em12019, dsL]
  · norm_num [world12019, agent12019, scalar12019, tp12019, tm12019, ep12019, em12019, dsL]
  · norm_num [world12019, agent12019, scalar12019, tp12019, tm12019, ep12019, em12019, dsL]
  · norm_num [world12019, agent12019, scalar12019, tp12019, tm12019, ep12019, em12019, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12019, agent12019, tp12019, tm12019, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12019, agent12019, scalar12019, tp12019, tm12019, ep12019, em12019, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12019, agent12019, tp12019, tm12019, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12019, agent12019, scalar12019, tp12019, tm12019, ep12019, em12019, dsL]

theorem negative12019 :
    Eminus aL (agent12019.root+dsL) scalar12019.worldRadius world12019.frame
      agent12019.frame tm12019 ≤ -em12019 := by
  apply negative_check (lo := (33910068910671732179 / 50000000000000000000)) (hi := (67820137821343464359 / 100000000000000000000))
    (y := (-((73353141498530678137 / 100000000000000000000)))) (u := (48021017084439702767 / 100000000000000000000))
  · norm_num [world12019, agent12019, scalar12019, tp12019, tm12019, ep12019, em12019, dsL]
  · norm_num [world12019, agent12019, scalar12019, tp12019, tm12019, ep12019, em12019, dsL]
  · norm_num [world12019, agent12019, scalar12019, tp12019, tm12019, ep12019, em12019, dsL]
  · norm_num [world12019, agent12019, scalar12019, tp12019, tm12019, ep12019, em12019, dsL]
  · norm_num [world12019, agent12019, scalar12019, tp12019, tm12019, ep12019, em12019, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12019, agent12019, tp12019, tm12019, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12019, agent12019, tp12019, tm12019, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12019, agent12019, scalar12019, tp12019, tm12019, ep12019, em12019, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12019, agent12019, tp12019, tm12019, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12019, agent12019, scalar12019, tp12019, tm12019, ep12019, em12019, dsL]

theorem tails12019 :
    exp (-((12019:ℝ)*ep12019)) ≤ scalar12019.upperTail ∧
    exp (-((12019:ℝ)*em12019)) ≤ scalar12019.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12019:ℝ)) (by norm_num [ep12019]) ?_)
      (show bp12019^8 ≤ scalar12019.upperTail by norm_num [bp12019, scalar12019])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12019, bp12019, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12019:ℝ)) (by norm_num [em12019]) ?_)
      (show bm12019^8 ≤ scalar12019.lowerTail by norm_num [bm12019, scalar12019])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12019, bm12019, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12019 :
    agent12019.root+dsL+scalar12019.worldRadius < √(1/100/aL) ∧
    2*(agent12019.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12019, agent12019, scalar12019, tp12019, tm12019, ep12019, em12019, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12019, agent12019, scalar12019, tp12019, tm12019, ep12019, em12019, dsL]

noncomputable def master12019 : MasterCertificate 12019 world12019 agent12019 :=
  master scalar12019 dsL tp12019 tm12019 ep12019 em12019
    (by norm_num [dsL]) (by norm_num [tp12019]) (by norm_num [tm12019])
    (by norm_num [ep12019]) (by norm_num [em12019])
    positive12019 negative12019 tails12019.1 tails12019.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12019.1 tailGuards12019.2

theorem preserves12019 : master12019.toScalarCertificate = scalar12019 := rfl

noncomputable def tp12020 : ℝ := (2359828923 / 10000000000)
noncomputable def tm12020 : ℝ := (-((3054794367 / 5000000000)))
noncomputable def ep12020 : ℝ := (10842218547676681 / 20000000000000000000)
noncomputable def em12020 : ℝ := (26152174690413377 / 50000000000000000000)
noncomputable def bp12020 : ℝ := (88570221277571269 / 200000000000000000)
noncomputable def bm12020 : ℝ := (1822887006626983083 / 4000000000000000000)

theorem positive12020 :
    Eplus aL (agent12020.root+dsL) scalar12020.worldRadius world12020.frame
      agent12020.frame tp12020 ≤ -ep12020 := by
  apply positive_check (eT := (116181945687912930463 / 100000000000000000000)) (y := (1977131834935164039 / 5000000000000000000)) (u := (148501721827738971871 / 100000000000000000000))
  · norm_num [world12020, agent12020, scalar12020, tp12020, tm12020, ep12020, em12020, dsL]
  · norm_num [world12020, agent12020, scalar12020, tp12020, tm12020, ep12020, em12020, dsL]
  · norm_num [world12020, agent12020, scalar12020, tp12020, tm12020, ep12020, em12020, dsL]
  · norm_num [world12020, agent12020, scalar12020, tp12020, tm12020, ep12020, em12020, dsL]
  · norm_num [world12020, agent12020, scalar12020, tp12020, tm12020, ep12020, em12020, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12020, agent12020, tp12020, tm12020, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12020, agent12020, scalar12020, tp12020, tm12020, ep12020, em12020, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12020, agent12020, tp12020, tm12020, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12020, agent12020, scalar12020, tp12020, tm12020, ep12020, em12020, dsL]

theorem negative12020 :
    Eminus aL (agent12020.root+dsL) scalar12020.worldRadius world12020.frame
      agent12020.frame tm12020 ≤ -em12020 := by
  apply negative_check (lo := (67819764559941734841 / 100000000000000000000)) (hi := (33909882279970867421 / 50000000000000000000))
    (y := (-((36676389940932720151 / 50000000000000000000)))) (u := (24010595368377137237 / 50000000000000000000))
  · norm_num [world12020, agent12020, scalar12020, tp12020, tm12020, ep12020, em12020, dsL]
  · norm_num [world12020, agent12020, scalar12020, tp12020, tm12020, ep12020, em12020, dsL]
  · norm_num [world12020, agent12020, scalar12020, tp12020, tm12020, ep12020, em12020, dsL]
  · norm_num [world12020, agent12020, scalar12020, tp12020, tm12020, ep12020, em12020, dsL]
  · norm_num [world12020, agent12020, scalar12020, tp12020, tm12020, ep12020, em12020, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12020, agent12020, tp12020, tm12020, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12020, agent12020, tp12020, tm12020, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12020, agent12020, scalar12020, tp12020, tm12020, ep12020, em12020, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12020, agent12020, tp12020, tm12020, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12020, agent12020, scalar12020, tp12020, tm12020, ep12020, em12020, dsL]

theorem tails12020 :
    exp (-((12020:ℝ)*ep12020)) ≤ scalar12020.upperTail ∧
    exp (-((12020:ℝ)*em12020)) ≤ scalar12020.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12020:ℝ)) (by norm_num [ep12020]) ?_)
      (show bp12020^8 ≤ scalar12020.upperTail by norm_num [bp12020, scalar12020])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12020, bp12020, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12020:ℝ)) (by norm_num [em12020]) ?_)
      (show bm12020^8 ≤ scalar12020.lowerTail by norm_num [bm12020, scalar12020])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12020, bm12020, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12020 :
    agent12020.root+dsL+scalar12020.worldRadius < √(1/100/aL) ∧
    2*(agent12020.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12020, agent12020, scalar12020, tp12020, tm12020, ep12020, em12020, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12020, agent12020, scalar12020, tp12020, tm12020, ep12020, em12020, dsL]

noncomputable def master12020 : MasterCertificate 12020 world12020 agent12020 :=
  master scalar12020 dsL tp12020 tm12020 ep12020 em12020
    (by norm_num [dsL]) (by norm_num [tp12020]) (by norm_num [tm12020])
    (by norm_num [ep12020]) (by norm_num [em12020])
    positive12020 negative12020 tails12020.1 tails12020.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12020.1 tailGuards12020.2

theorem preserves12020 : master12020.toScalarCertificate = scalar12020 := rfl

noncomputable def tp12021 : ℝ := (18879467 / 80000000)
noncomputable def tm12021 : ℝ := (-((3054912003 / 5000000000)))
noncomputable def ep12021 : ℝ := (13553544718461773 / 25000000000000000000)
noncomputable def em12021 : ℝ := (6538380244444251 / 12500000000000000000)
noncomputable def bp12021 : ℝ := (44280056361590789081 / 100000000000000000000)
noncomputable def bm12021 : ℝ := (45567352073849536097 / 100000000000000000000)

theorem positive12021 :
    Eplus aL (agent12021.root+dsL) scalar12021.worldRadius world12021.frame
      agent12021.frame tp12021 ≤ -ep12021 := by
  apply positive_check (eT := (116182292151347118327 / 100000000000000000000)) (y := (19771655053308509347 / 50000000000000000000)) (u := (74251360926726459649 / 50000000000000000000))
  · norm_num [world12021, agent12021, scalar12021, tp12021, tm12021, ep12021, em12021, dsL]
  · norm_num [world12021, agent12021, scalar12021, tp12021, tm12021, ep12021, em12021, dsL]
  · norm_num [world12021, agent12021, scalar12021, tp12021, tm12021, ep12021, em12021, dsL]
  · norm_num [world12021, agent12021, scalar12021, tp12021, tm12021, ep12021, em12021, dsL]
  · norm_num [world12021, agent12021, scalar12021, tp12021, tm12021, ep12021, em12021, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12021, agent12021, tp12021, tm12021, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12021, agent12021, scalar12021, tp12021, tm12021, ep12021, em12021, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12021, agent12021, tp12021, tm12021, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12021, agent12021, scalar12021, tp12021, tm12021, ep12021, em12021, dsL]

theorem negative12021 :
    Eminus aL (agent12021.root+dsL) scalar12021.worldRadius world12021.frame
      agent12021.frame tm12021 ≤ -em12021 := by
  apply negative_check (lo := (67819392481367387837 / 100000000000000000000)) (hi := (33909696240683693919 / 50000000000000000000))
    (y := (-((14670483291911290031 / 20000000000000000000)))) (u := (48021365256791576731 / 100000000000000000000))
  · norm_num [world12021, agent12021, scalar12021, tp12021, tm12021, ep12021, em12021, dsL]
  · norm_num [world12021, agent12021, scalar12021, tp12021, tm12021, ep12021, em12021, dsL]
  · norm_num [world12021, agent12021, scalar12021, tp12021, tm12021, ep12021, em12021, dsL]
  · norm_num [world12021, agent12021, scalar12021, tp12021, tm12021, ep12021, em12021, dsL]
  · norm_num [world12021, agent12021, scalar12021, tp12021, tm12021, ep12021, em12021, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12021, agent12021, tp12021, tm12021, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12021, agent12021, tp12021, tm12021, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12021, agent12021, scalar12021, tp12021, tm12021, ep12021, em12021, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12021, agent12021, tp12021, tm12021, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12021, agent12021, scalar12021, tp12021, tm12021, ep12021, em12021, dsL]

theorem tails12021 :
    exp (-((12021:ℝ)*ep12021)) ≤ scalar12021.upperTail ∧
    exp (-((12021:ℝ)*em12021)) ≤ scalar12021.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12021:ℝ)) (by norm_num [ep12021]) ?_)
      (show bp12021^8 ≤ scalar12021.upperTail by norm_num [bp12021, scalar12021])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12021, bp12021, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12021:ℝ)) (by norm_num [em12021]) ?_)
      (show bm12021^8 ≤ scalar12021.lowerTail by norm_num [bm12021, scalar12021])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12021, bm12021, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12021 :
    agent12021.root+dsL+scalar12021.worldRadius < √(1/100/aL) ∧
    2*(agent12021.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12021, agent12021, scalar12021, tp12021, tm12021, ep12021, em12021, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12021, agent12021, scalar12021, tp12021, tm12021, ep12021, em12021, dsL]

noncomputable def master12021 : MasterCertificate 12021 world12021 agent12021 :=
  master scalar12021 dsL tp12021 tm12021 ep12021 em12021
    (by norm_num [dsL]) (by norm_num [tp12021]) (by norm_num [tm12021])
    (by norm_num [ep12021]) (by norm_num [em12021])
    positive12021 negative12021 tails12021.1 tails12021.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12021.1 tailGuards12021.2

theorem preserves12021 : master12021.toScalarCertificate = scalar12021 := rfl

noncomputable def tp12022 : ℝ := (147502361 / 625000000)
noncomputable def tm12022 : ℝ := (-((3055029571 / 5000000000)))
noncomputable def ep12022 : ℝ := (27108631440376831 / 50000000000000000000)
noncomputable def em12022 : ℝ := (52309732571355949 / 100000000000000000000)
noncomputable def bp12022 : ℝ := (22137501867932852177 / 50000000000000000000)
noncomputable def bm12022 : ℝ := (45562530527029337771 / 100000000000000000000)

theorem positive12022 :
    Eplus aL (agent12022.root+dsL) scalar12022.worldRadius world12022.frame
      agent12022.frame tp12022 ≤ -ep12022 := by
  apply positive_check (eT := (3630707446079883739 / 3125000000000000000)) (y := (19771991658850560679 / 50000000000000000000)) (u := (18562965199200225983 / 12500000000000000000))
  · norm_num [world12022, agent12022, scalar12022, tp12022, tm12022, ep12022, em12022, dsL]
  · norm_num [world12022, agent12022, scalar12022, tp12022, tm12022, ep12022, em12022, dsL]
  · norm_num [world12022, agent12022, scalar12022, tp12022, tm12022, ep12022, em12022, dsL]
  · norm_num [world12022, agent12022, scalar12022, tp12022, tm12022, ep12022, em12022, dsL]
  · norm_num [world12022, agent12022, scalar12022, tp12022, tm12022, ep12022, em12022, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12022, agent12022, tp12022, tm12022, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12022, agent12022, scalar12022, tp12022, tm12022, ep12022, em12022, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12022, agent12022, tp12022, tm12022, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12022, agent12022, scalar12022, tp12022, tm12022, ep12022, em12022, dsL]

theorem negative12022 :
    Eminus aL (agent12022.root+dsL) scalar12022.worldRadius world12022.frame
      agent12022.frame tm12022 ≤ -em12022 := by
  apply negative_check (lo := (2712760837210156313 / 4000000000000000000)) (hi := (33909510465126953913 / 50000000000000000000))
    (y := (-((36676026506436545503 / 50000000000000000000)))) (u := (24010769894584036099 / 50000000000000000000))
  · norm_num [world12022, agent12022, scalar12022, tp12022, tm12022, ep12022, em12022, dsL]
  · norm_num [world12022, agent12022, scalar12022, tp12022, tm12022, ep12022, em12022, dsL]
  · norm_num [world12022, agent12022, scalar12022, tp12022, tm12022, ep12022, em12022, dsL]
  · norm_num [world12022, agent12022, scalar12022, tp12022, tm12022, ep12022, em12022, dsL]
  · norm_num [world12022, agent12022, scalar12022, tp12022, tm12022, ep12022, em12022, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12022, agent12022, tp12022, tm12022, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12022, agent12022, tp12022, tm12022, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12022, agent12022, scalar12022, tp12022, tm12022, ep12022, em12022, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12022, agent12022, tp12022, tm12022, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12022, agent12022, scalar12022, tp12022, tm12022, ep12022, em12022, dsL]

theorem tails12022 :
    exp (-((12022:ℝ)*ep12022)) ≤ scalar12022.upperTail ∧
    exp (-((12022:ℝ)*em12022)) ≤ scalar12022.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12022:ℝ)) (by norm_num [ep12022]) ?_)
      (show bp12022^8 ≤ scalar12022.upperTail by norm_num [bp12022, scalar12022])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12022, bp12022, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12022:ℝ)) (by norm_num [em12022]) ?_)
      (show bm12022^8 ≤ scalar12022.lowerTail by norm_num [bm12022, scalar12022])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12022, bm12022, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12022 :
    agent12022.root+dsL+scalar12022.worldRadius < √(1/100/aL) ∧
    2*(agent12022.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12022, agent12022, scalar12022, tp12022, tm12022, ep12022, em12022, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12022, agent12022, scalar12022, tp12022, tm12022, ep12022, em12022, dsL]

noncomputable def master12022 : MasterCertificate 12022 world12022 agent12022 :=
  master scalar12022 dsL tp12022 tm12022 ep12022 em12022
    (by norm_num [dsL]) (by norm_num [tp12022]) (by norm_num [tm12022])
    (by norm_num [ep12022]) (by norm_num [em12022])
    positive12022 negative12022 tails12022.1 tails12022.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12022.1 tailGuards12022.2

theorem preserves12022 : master12022.toScalarCertificate = scalar12022 := rfl

noncomputable def tp12023 : ℝ := (1180071061 / 5000000000)
noncomputable def tm12023 : ℝ := (-((6110294161 / 10000000000)))
noncomputable def ep12023 : ℝ := (27110172516715757 / 50000000000000000000)
noncomputable def em12023 : ℝ := (52312421424125239 / 100000000000000000000)
noncomputable def bp12023 : ℝ := (4426995257901331493 / 10000000000000000000)
noncomputable def bm12023 : ℝ := (5694713798880415777 / 12500000000000000000)

theorem positive12023 :
    Eplus aL (agent12023.root+dsL) scalar12023.worldRadius world12023.frame
      agent12023.frame tp12023 ≤ -ep12023 := by
  apply positive_check (eT := (7261436501745586317 / 6250000000000000000)) (y := (7908931262718959719 / 20000000000000000000)) (u := (148504721020913139291 / 100000000000000000000))
  · norm_num [world12023, agent12023, scalar12023, tp12023, tm12023, ep12023, em12023, dsL]
  · norm_num [world12023, agent12023, scalar12023, tp12023, tm12023, ep12023, em12023, dsL]
  · norm_num [world12023, agent12023, scalar12023, tp12023, tm12023, ep12023, em12023, dsL]
  · norm_num [world12023, agent12023, scalar12023, tp12023, tm12023, ep12023, em12023, dsL]
  · norm_num [world12023, agent12023, scalar12023, tp12023, tm12023, ep12023, em12023, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12023, agent12023, tp12023, tm12023, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12023, agent12023, scalar12023, tp12023, tm12023, ep12023, em12023, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12023, agent12023, tp12023, tm12023, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12023, agent12023, scalar12023, tp12023, tm12023, ep12023, em12023, dsL]

theorem negative12023 :
    Eminus aL (agent12023.root+dsL) scalar12023.worldRadius world12023.frame
      agent12023.frame tm12023 ≤ -em12023 := by
  apply negative_check (lo := (67818649824810171593 / 100000000000000000000)) (hi := (33909324912405085797 / 50000000000000000000))
    (y := (-((73351689606492831743 / 100000000000000000000)))) (u := (6002714287853082683 / 12500000000000000000))
  · norm_num [world12023, agent12023, scalar12023, tp12023, tm12023, ep12023, em12023, dsL]
  · norm_num [world12023, agent12023, scalar12023, tp12023, tm12023, ep12023, em12023, dsL]
  · norm_num [world12023, agent12023, scalar12023, tp12023, tm12023, ep12023, em12023, dsL]
  · norm_num [world12023, agent12023, scalar12023, tp12023, tm12023, ep12023, em12023, dsL]
  · norm_num [world12023, agent12023, scalar12023, tp12023, tm12023, ep12023, em12023, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12023, agent12023, tp12023, tm12023, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12023, agent12023, tp12023, tm12023, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12023, agent12023, scalar12023, tp12023, tm12023, ep12023, em12023, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12023, agent12023, tp12023, tm12023, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12023, agent12023, scalar12023, tp12023, tm12023, ep12023, em12023, dsL]

theorem tails12023 :
    exp (-((12023:ℝ)*ep12023)) ≤ scalar12023.upperTail ∧
    exp (-((12023:ℝ)*em12023)) ≤ scalar12023.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12023:ℝ)) (by norm_num [ep12023]) ?_)
      (show bp12023^8 ≤ scalar12023.upperTail by norm_num [bp12023, scalar12023])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12023, bp12023, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12023:ℝ)) (by norm_num [em12023]) ?_)
      (show bm12023^8 ≤ scalar12023.lowerTail by norm_num [bm12023, scalar12023])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12023, bm12023, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12023 :
    agent12023.root+dsL+scalar12023.worldRadius < √(1/100/aL) ∧
    2*(agent12023.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12023, agent12023, scalar12023, tp12023, tm12023, ep12023, em12023, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12023, agent12023, scalar12023, tp12023, tm12023, ep12023, em12023, dsL]

noncomputable def master12023 : MasterCertificate 12023 world12023 agent12023 :=
  master scalar12023 dsL tp12023 tm12023 ep12023 em12023
    (by norm_num [dsL]) (by norm_num [tp12023]) (by norm_num [tm12023])
    (by norm_num [ep12023]) (by norm_num [em12023])
    positive12023 negative12023 tails12023.1 tails12023.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12023.1 tailGuards12023.2

theorem preserves12023 : master12023.toScalarCertificate = scalar12023 := rfl

noncomputable def tp12024 : ℝ := (590061597 / 2500000000)
noncomputable def tm12024 : ℝ := (-((6110528873 / 10000000000)))
noncomputable def ep12024 : ℝ := (6777928132836051 / 12500000000000000000)
noncomputable def em12024 : ℝ := (52315108322478743 / 100000000000000000000)
noncomputable def bp12024 : ℝ := (44264903070064213673 / 100000000000000000000)
noncomputable def bm12024 : ℝ := (22776445898442604769 / 50000000000000000000)

theorem positive12024 :
    Eplus aL (agent12024.root+dsL) scalar12024.worldRadius world12024.frame
      agent12024.frame tp12024 ≤ -ep12024 := by
  apply positive_check (eT := (116183329226964250627 / 100000000000000000000)) (y := (2471583036790170199 / 6250000000000000000)) (u := (37126429846113355909 / 25000000000000000000))
  · norm_num [world12024, agent12024, scalar12024, tp12024, tm12024, ep12024, em12024, dsL]
  · norm_num [world12024, agent12024, scalar12024, tp12024, tm12024, ep12024, em12024, dsL]
  · norm_num [world12024, agent12024, scalar12024, tp12024, tm12024, ep12024, em12024, dsL]
  · norm_num [world12024, agent12024, scalar12024, tp12024, tm12024, ep12024, em12024, dsL]
  · norm_num [world12024, agent12024, scalar12024, tp12024, tm12024, ep12024, em12024, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12024, agent12024, tp12024, tm12024, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12024, agent12024, scalar12024, tp12024, tm12024, ep12024, em12024, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12024, agent12024, tp12024, tm12024, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12024, agent12024, scalar12024, tp12024, tm12024, ep12024, em12024, dsL]

theorem negative12024 :
    Eminus aL (agent12024.root+dsL) scalar12024.worldRadius world12024.frame
      agent12024.frame tm12024 ≤ -em12024 := by
  apply negative_check (lo := (67818279983798406239 / 100000000000000000000)) (hi := (423864249898740039 / 625000000000000000))
    (y := (-((36675662247196717339 / 50000000000000000000)))) (u := (48021889636234000519 / 100000000000000000000))
  · norm_num [world12024, agent12024, scalar12024, tp12024, tm12024, ep12024, em12024, dsL]
  · norm_num [world12024, agent12024, scalar12024, tp12024, tm12024, ep12024, em12024, dsL]
  · norm_num [world12024, agent12024, scalar12024, tp12024, tm12024, ep12024, em12024, dsL]
  · norm_num [world12024, agent12024, scalar12024, tp12024, tm12024, ep12024, em12024, dsL]
  · norm_num [world12024, agent12024, scalar12024, tp12024, tm12024, ep12024, em12024, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12024, agent12024, tp12024, tm12024, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12024, agent12024, tp12024, tm12024, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12024, agent12024, scalar12024, tp12024, tm12024, ep12024, em12024, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12024, agent12024, tp12024, tm12024, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12024, agent12024, scalar12024, tp12024, tm12024, ep12024, em12024, dsL]

theorem tails12024 :
    exp (-((12024:ℝ)*ep12024)) ≤ scalar12024.upperTail ∧
    exp (-((12024:ℝ)*em12024)) ≤ scalar12024.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12024:ℝ)) (by norm_num [ep12024]) ?_)
      (show bp12024^8 ≤ scalar12024.upperTail by norm_num [bp12024, scalar12024])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12024, bp12024, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12024:ℝ)) (by norm_num [em12024]) ?_)
      (show bm12024^8 ≤ scalar12024.lowerTail by norm_num [bm12024, scalar12024])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12024, bm12024, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12024 :
    agent12024.root+dsL+scalar12024.worldRadius < √(1/100/aL) ∧
    2*(agent12024.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12024, agent12024, scalar12024, tp12024, tm12024, ep12024, em12024, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12024, agent12024, scalar12024, tp12024, tm12024, ep12024, em12024, dsL]

noncomputable def master12024 : MasterCertificate 12024 world12024 agent12024 :=
  master scalar12024 dsL tp12024 tm12024 ep12024 em12024
    (by norm_num [dsL]) (by norm_num [tp12024]) (by norm_num [tm12024])
    (by norm_num [ep12024]) (by norm_num [em12024])
    positive12024 negative12024 tails12024.1 tails12024.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12024.1 tailGuards12024.2

theorem preserves12024 : master12024.toScalarCertificate = scalar12024 := rfl

noncomputable def tp12025 : ℝ := (2360350581 / 10000000000)
noncomputable def tm12025 : ℝ := (-((381922723 / 625000000)))
noncomputable def ep12025 : ℝ := (54226504196050587 / 100000000000000000000)
noncomputable def em12025 : ℝ := (52317794339374083 / 100000000000000000000)
noncomputable def bp12025 : ℝ := (44259854392288576013 / 100000000000000000000)
noncomputable def bm12025 : ℝ := (45548074009912910397 / 100000000000000000000)

theorem positive12025 :
    Eplus aL (agent12025.root+dsL) scalar12025.worldRadius world12025.frame
      agent12025.frame tp12025 ≤ -ep12025 := by
  apply positive_check (eT := (116183673923311466469 / 100000000000000000000)) (y := (9886500054883065369 / 25000000000000000000)) (u := (148506716798087005961 / 100000000000000000000))
  · norm_num [world12025, agent12025, scalar12025, tp12025, tm12025, ep12025, em12025, dsL]
  · norm_num [world12025, agent12025, scalar12025, tp12025, tm12025, ep12025, em12025, dsL]
  · norm_num [world12025, agent12025, scalar12025, tp12025, tm12025, ep12025, em12025, dsL]
  · norm_num [world12025, agent12025, scalar12025, tp12025, tm12025, ep12025, em12025, dsL]
  · norm_num [world12025, agent12025, scalar12025, tp12025, tm12025, ep12025, em12025, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12025, agent12025, tp12025, tm12025, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12025, agent12025, scalar12025, tp12025, tm12025, ep12025, em12025, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12025, agent12025, tp12025, tm12025, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12025, agent12025, scalar12025, tp12025, tm12025, ep12025, em12025, dsL]

theorem negative12025 :
    Eminus aL (agent12025.root+dsL) scalar12025.worldRadius world12025.frame
      agent12025.frame tm12025 ≤ -em12025 := by
  apply negative_check (lo := (67817910157347084759 / 100000000000000000000)) (hi := (1695447753933677119 / 2500000000000000000))
    (y := (-((73350960661839059359 / 100000000000000000000)))) (u := (48022064355819566499 / 100000000000000000000))
  · norm_num [world12025, agent12025, scalar12025, tp12025, tm12025, ep12025, em12025, dsL]
  · norm_num [world12025, agent12025, scalar12025, tp12025, tm12025, ep12025, em12025, dsL]
  · norm_num [world12025, agent12025, scalar12025, tp12025, tm12025, ep12025, em12025, dsL]
  · norm_num [world12025, agent12025, scalar12025, tp12025, tm12025, ep12025, em12025, dsL]
  · norm_num [world12025, agent12025, scalar12025, tp12025, tm12025, ep12025, em12025, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12025, agent12025, tp12025, tm12025, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12025, agent12025, tp12025, tm12025, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12025, agent12025, scalar12025, tp12025, tm12025, ep12025, em12025, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12025, agent12025, tp12025, tm12025, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12025, agent12025, scalar12025, tp12025, tm12025, ep12025, em12025, dsL]

theorem tails12025 :
    exp (-((12025:ℝ)*ep12025)) ≤ scalar12025.upperTail ∧
    exp (-((12025:ℝ)*em12025)) ≤ scalar12025.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12025:ℝ)) (by norm_num [ep12025]) ?_)
      (show bp12025^8 ≤ scalar12025.upperTail by norm_num [bp12025, scalar12025])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12025, bp12025, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12025:ℝ)) (by norm_num [em12025]) ?_)
      (show bm12025^8 ≤ scalar12025.lowerTail by norm_num [bm12025, scalar12025])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12025, bm12025, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12025 :
    agent12025.root+dsL+scalar12025.worldRadius < √(1/100/aL) ∧
    2*(agent12025.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12025, agent12025, scalar12025, tp12025, tm12025, ep12025, em12025, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12025, agent12025, scalar12025, tp12025, tm12025, ep12025, em12025, dsL]

noncomputable def master12025 : MasterCertificate 12025 world12025 agent12025 :=
  master scalar12025 dsL tp12025 tm12025 ep12025 em12025
    (by norm_num [dsL]) (by norm_num [tp12025]) (by norm_num [tm12025])
    (by norm_num [ep12025]) (by norm_num [em12025])
    positive12025 negative12025 tails12025.1 tails12025.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12025.1 tailGuards12025.2

theorem preserves12025 : master12025.toScalarCertificate = scalar12025 := rfl

noncomputable def tp12026 : ℝ := (2360454753 / 10000000000)
noncomputable def tm12026 : ℝ := (-((1527749531 / 2500000000)))
noncomputable def ep12026 : ℝ := (27114790605632961 / 50000000000000000000)
noncomputable def em12026 : ℝ := (26160239203251637 / 50000000000000000000)
noncomputable def bp12026 : ℝ := (44254807358797981329 / 100000000000000000000)
noncomputable def bm12026 : ℝ := (45543257761523308113 / 100000000000000000000)

theorem positive12026 :
    Eplus aL (agent12026.root+dsL) scalar12026.worldRadius world12026.frame
      agent12026.frame tp12026 ≤ -ep12026 := by
  apply positive_check (eT := (116184018500980152551 / 100000000000000000000)) (y := (39546672193279780477 / 100000000000000000000)) (u := (3712692868189752497 / 2500000000000000000))
  · norm_num [world12026, agent12026, scalar12026, tp12026, tm12026, ep12026, em12026, dsL]
  · norm_num [world12026, agent12026, scalar12026, tp12026, tm12026, ep12026, em12026, dsL]
  · norm_num [world12026, agent12026, scalar12026, tp12026, tm12026, ep12026, em12026, dsL]
  · norm_num [world12026, agent12026, scalar12026, tp12026, tm12026, ep12026, em12026, dsL]
  · norm_num [world12026, agent12026, scalar12026, tp12026, tm12026, ep12026, em12026, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12026, agent12026, tp12026, tm12026, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12026, agent12026, scalar12026, tp12026, tm12026, ep12026, em12026, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12026, agent12026, tp12026, tm12026, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12026, agent12026, scalar12026, tp12026, tm12026, ep12026, em12026, dsL]

theorem negative12026 :
    Eminus aL (agent12026.root+dsL) scalar12026.worldRadius world12026.frame
      agent12026.frame tm12026 ≤ -em12026 := by
  apply negative_check (lo := (3390877043559321601 / 5000000000000000000)) (hi := (67817540871186432021 / 100000000000000000000))
    (y := (-((916882459655414627 / 1250000000000000000)))) (u := (48022239103342190287 / 100000000000000000000))
  · norm_num [world12026, agent12026, scalar12026, tp12026, tm12026, ep12026, em12026, dsL]
  · norm_num [world12026, agent12026, scalar12026, tp12026, tm12026, ep12026, em12026, dsL]
  · norm_num [world12026, agent12026, scalar12026, tp12026, tm12026, ep12026, em12026, dsL]
  · norm_num [world12026, agent12026, scalar12026, tp12026, tm12026, ep12026, em12026, dsL]
  · norm_num [world12026, agent12026, scalar12026, tp12026, tm12026, ep12026, em12026, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12026, agent12026, tp12026, tm12026, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12026, agent12026, tp12026, tm12026, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12026, agent12026, scalar12026, tp12026, tm12026, ep12026, em12026, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12026, agent12026, tp12026, tm12026, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12026, agent12026, scalar12026, tp12026, tm12026, ep12026, em12026, dsL]

theorem tails12026 :
    exp (-((12026:ℝ)*ep12026)) ≤ scalar12026.upperTail ∧
    exp (-((12026:ℝ)*em12026)) ≤ scalar12026.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12026:ℝ)) (by norm_num [ep12026]) ?_)
      (show bp12026^8 ≤ scalar12026.upperTail by norm_num [bp12026, scalar12026])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12026, bp12026, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12026:ℝ)) (by norm_num [em12026]) ?_)
      (show bm12026^8 ≤ scalar12026.lowerTail by norm_num [bm12026, scalar12026])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12026, bm12026, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12026 :
    agent12026.root+dsL+scalar12026.worldRadius < √(1/100/aL) ∧
    2*(agent12026.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12026, agent12026, scalar12026, tp12026, tm12026, ep12026, em12026, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12026, agent12026, scalar12026, tp12026, tm12026, ep12026, em12026, dsL]

noncomputable def master12026 : MasterCertificate 12026 world12026 agent12026 :=
  master scalar12026 dsL tp12026 tm12026 ep12026 em12026
    (by norm_num [dsL]) (by norm_num [tp12026]) (by norm_num [tm12026])
    (by norm_num [ep12026]) (by norm_num [em12026])
    positive12026 negative12026 tails12026.1 tails12026.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12026.1 tailGuards12026.2

theorem preserves12026 : master12026.toScalarCertificate = scalar12026 := rfl

noncomputable def tp12027 : ℝ := (590139713 / 2500000000)
noncomputable def tm12027 : ℝ := (-((1527808159 / 2500000000)))
noncomputable def ep12027 : ℝ := (54232656377906961 / 100000000000000000000)
noncomputable def em12027 : ℝ := (26161580357862773 / 50000000000000000000)
noncomputable def bp12027 : ℝ := (22124880895091157051 / 50000000000000000000)
noncomputable def bm12027 : ℝ := (45538442920319608191 / 100000000000000000000)

theorem positive12027 :
    Eplus aL (agent12027.root+dsL) scalar12027.worldRadius world12027.frame
      agent12027.frame tp12027 ≤ -ep12027 := by
  apply positive_check (eT := (14523045322004234019 / 12500000000000000000)) (y := (39547343625482755061 / 100000000000000000000)) (u := (148508711859558211373 / 100000000000000000000))
  · norm_num [world12027, agent12027, scalar12027, tp12027, tm12027, ep12027, em12027, dsL]
  · norm_num [world12027, agent12027, scalar12027, tp12027, tm12027, ep12027, em12027, dsL]
  · norm_num [world12027, agent12027, scalar12027, tp12027, tm12027, ep12027, em12027, dsL]
  · norm_num [world12027, agent12027, scalar12027, tp12027, tm12027, ep12027, em12027, dsL]
  · norm_num [world12027, agent12027, scalar12027, tp12027, tm12027, ep12027, em12027, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12027, agent12027, tp12027, tm12027, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12027, agent12027, scalar12027, tp12027, tm12027, ep12027, em12027, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12027, agent12027, tp12027, tm12027, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12027, agent12027, scalar12027, tp12027, tm12027, ep12027, em12027, dsL]

theorem negative12027 :
    Eminus aL (agent12027.root+dsL) scalar12027.worldRadius world12027.frame
      agent12027.frame tm12027 ≤ -em12027 := by
  apply negative_check (lo := (67817171715878255123 / 100000000000000000000)) (hi := (16954292928969563781 / 25000000000000000000))
    (y := (-((4584389602323193223 / 6250000000000000000)))) (u := (9604482697868528511 / 20000000000000000000))
  · norm_num [world12027, agent12027, scalar12027, tp12027, tm12027, ep12027, em12027, dsL]
  · norm_num [world12027, agent12027, scalar12027, tp12027, tm12027, ep12027, em12027, dsL]
  · norm_num [world12027, agent12027, scalar12027, tp12027, tm12027, ep12027, em12027, dsL]
  · norm_num [world12027, agent12027, scalar12027, tp12027, tm12027, ep12027, em12027, dsL]
  · norm_num [world12027, agent12027, scalar12027, tp12027, tm12027, ep12027, em12027, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12027, agent12027, tp12027, tm12027, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12027, agent12027, tp12027, tm12027, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12027, agent12027, scalar12027, tp12027, tm12027, ep12027, em12027, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12027, agent12027, tp12027, tm12027, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12027, agent12027, scalar12027, tp12027, tm12027, ep12027, em12027, dsL]

theorem tails12027 :
    exp (-((12027:ℝ)*ep12027)) ≤ scalar12027.upperTail ∧
    exp (-((12027:ℝ)*em12027)) ≤ scalar12027.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12027:ℝ)) (by norm_num [ep12027]) ?_)
      (show bp12027^8 ≤ scalar12027.upperTail by norm_num [bp12027, scalar12027])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12027, bp12027, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12027:ℝ)) (by norm_num [em12027]) ?_)
      (show bm12027^8 ≤ scalar12027.lowerTail by norm_num [bm12027, scalar12027])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12027, bm12027, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12027 :
    agent12027.root+dsL+scalar12027.worldRadius < √(1/100/aL) ∧
    2*(agent12027.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12027, agent12027, scalar12027, tp12027, tm12027, ep12027, em12027, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12027, agent12027, scalar12027, tp12027, tm12027, ep12027, em12027, dsL]

noncomputable def master12027 : MasterCertificate 12027 world12027 agent12027 :=
  master scalar12027 dsL tp12027 tm12027 ep12027 em12027
    (by norm_num [dsL]) (by norm_num [tp12027]) (by norm_num [tm12027])
    (by norm_num [ep12027]) (by norm_num [em12027])
    positive12027 negative12027 tails12027.1 tails12027.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12027.1 tailGuards12027.2

theorem preserves12027 : master12027.toScalarCertificate = scalar12027 := rfl

noncomputable def tp12028 : ℝ := (1180331459 / 5000000000)
noncomputable def tm12028 : ℝ := (-((6111466901 / 10000000000)))
noncomputable def ep12028 : ℝ := (27117865027287981 / 50000000000000000000)
noncomputable def em12028 : ℝ := (52325841670971683 / 100000000000000000000)
noncomputable def bp12028 : ℝ := (44244717447829314413 / 100000000000000000000)
noncomputable def bm12028 : ℝ := (1138340730243327181 / 2500000000000000000)

theorem positive12028 :
    Eplus aL (agent12028.root+dsL) scalar12028.worldRadius world12028.frame
      agent12028.frame tp12028 ≤ -ep12028 := by
  apply positive_check (eT := (116184706443785941253 / 100000000000000000000)) (y := (7909602994326156441 / 20000000000000000000)) (u := (37127427217605364629 / 25000000000000000000))
  · norm_num [world12028, agent12028, scalar12028, tp12028, tm12028, ep12028, em12028, dsL]
  · norm_num [world12028, agent12028, scalar12028, tp12028, tm12028, ep12028, em12028, dsL]
  · norm_num [world12028, agent12028, scalar12028, tp12028, tm12028, ep12028, em12028, dsL]
  · norm_num [world12028, agent12028, scalar12028, tp12028, tm12028, ep12028, em12028, dsL]
  · norm_num [world12028, agent12028, scalar12028, tp12028, tm12028, ep12028, em12028, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12028, agent12028, tp12028, tm12028, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12028, agent12028, scalar12028, tp12028, tm12028, ep12028, em12028, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12028, agent12028, tp12028, tm12028, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12028, agent12028, scalar12028, tp12028, tm12028, ep12028, em12028, dsL]

theorem negative12028 :
    Eminus aL (agent12028.root+dsL) scalar12028.worldRadius world12028.frame
      agent12028.frame tm12028 ≤ -em12028 := by
  apply negative_check (lo := (6781680356630462163 / 10000000000000000000)) (hi := (67816803566304621631 / 100000000000000000000))
    (y := (-((9168733651922230293 / 12500000000000000000)))) (u := (93794118151956873 / 195312500000000000))
  · norm_num [world12028, agent12028, scalar12028, tp12028, tm12028, ep12028, em12028, dsL]
  · norm_num [world12028, agent12028, scalar12028, tp12028, tm12028, ep12028, em12028, dsL]
  · norm_num [world12028, agent12028, scalar12028, tp12028, tm12028, ep12028, em12028, dsL]
  · norm_num [world12028, agent12028, scalar12028, tp12028, tm12028, ep12028, em12028, dsL]
  · norm_num [world12028, agent12028, scalar12028, tp12028, tm12028, ep12028, em12028, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12028, agent12028, tp12028, tm12028, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12028, agent12028, tp12028, tm12028, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12028, agent12028, scalar12028, tp12028, tm12028, ep12028, em12028, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12028, agent12028, tp12028, tm12028, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12028, agent12028, scalar12028, tp12028, tm12028, ep12028, em12028, dsL]

theorem tails12028 :
    exp (-((12028:ℝ)*ep12028)) ≤ scalar12028.upperTail ∧
    exp (-((12028:ℝ)*em12028)) ≤ scalar12028.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12028:ℝ)) (by norm_num [ep12028]) ?_)
      (show bp12028^8 ≤ scalar12028.upperTail by norm_num [bp12028, scalar12028])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12028, bp12028, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12028:ℝ)) (by norm_num [em12028]) ?_)
      (show bm12028^8 ≤ scalar12028.lowerTail by norm_num [bm12028, scalar12028])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12028, bm12028, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12028 :
    agent12028.root+dsL+scalar12028.worldRadius < √(1/100/aL) ∧
    2*(agent12028.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12028, agent12028, scalar12028, tp12028, tm12028, ep12028, em12028, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12028, agent12028, scalar12028, tp12028, tm12028, ep12028, em12028, dsL]

noncomputable def master12028 : MasterCertificate 12028 world12028 agent12028 :=
  master scalar12028 dsL tp12028 tm12028 ep12028 em12028
    (by norm_num [dsL]) (by norm_num [tp12028]) (by norm_num [tm12028])
    (by norm_num [ep12028]) (by norm_num [em12028])
    positive12028 negative12028 tails12028.1 tails12028.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12028.1 tailGuards12028.2

theorem preserves12028 : master12028.toScalarCertificate = scalar12028 := rfl

noncomputable def tp12029 : ℝ := (472153389 / 2000000000)
noncomputable def tm12029 : ℝ := (-((6111701113 / 10000000000)))
noncomputable def ep12029 : ℝ := (2711940086363397 / 5000000000000000000)
noncomputable def em12029 : ℝ := (52328520708175891 / 100000000000000000000)
noncomputable def bp12029 : ℝ := (22119837336806722041 / 50000000000000000000)
noncomputable def bm12029 : ℝ := (22764408507946824543 / 50000000000000000000)

theorem positive12029 :
    Eplus aL (agent12029.root+dsL) scalar12029.worldRadius world12029.frame
      agent12029.frame tp12029 ≤ -ep12029 := by
  apply positive_check (eT := (5809252502999588537 / 5000000000000000000)) (y := (39548686548663261749 / 100000000000000000000)) (u := (148510706230866252593 / 100000000000000000000))
  · norm_num [world12029, agent12029, scalar12029, tp12029, tm12029, ep12029, em12029, dsL]
  · norm_num [world12029, agent12029, scalar12029, tp12029, tm12029, ep12029, em12029, dsL]
  · norm_num [world12029, agent12029, scalar12029, tp12029, tm12029, ep12029, em12029, dsL]
  · norm_num [world12029, agent12029, scalar12029, tp12029, tm12029, ep12029, em12029, dsL]
  · norm_num [world12029, agent12029, scalar12029, tp12029, tm12029, ep12029, em12029, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12029, agent12029, tp12029, tm12029, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12029, agent12029, scalar12029, tp12029, tm12029, ep12029, em12029, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12029, agent12029, tp12029, tm12029, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12029, agent12029, scalar12029, tp12029, tm12029, ep12029, em12029, dsL]

theorem negative12029 :
    Eminus aL (agent12029.root+dsL) scalar12029.worldRadius world12029.frame
      agent12029.frame tm12029 ≤ -em12029 := by
  apply negative_check (lo := (13563287117259969753 / 20000000000000000000)) (hi := (33908217793149924383 / 50000000000000000000))
    (y := (-((36674752877069875939 / 50000000000000000000)))) (u := (12005690759403455249 / 25000000000000000000))
  · norm_num [world12029, agent12029, scalar12029, tp12029, tm12029, ep12029, em12029, dsL]
  · norm_num [world12029, agent12029, scalar12029, tp12029, tm12029, ep12029, em12029, dsL]
  · norm_num [world12029, agent12029, scalar12029, tp12029, tm12029, ep12029, em12029, dsL]
  · norm_num [world12029, agent12029, scalar12029, tp12029, tm12029, ep12029, em12029, dsL]
  · norm_num [world12029, agent12029, scalar12029, tp12029, tm12029, ep12029, em12029, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12029, agent12029, tp12029, tm12029, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12029, agent12029, tp12029, tm12029, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12029, agent12029, scalar12029, tp12029, tm12029, ep12029, em12029, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12029, agent12029, tp12029, tm12029, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12029, agent12029, scalar12029, tp12029, tm12029, ep12029, em12029, dsL]

theorem tails12029 :
    exp (-((12029:ℝ)*ep12029)) ≤ scalar12029.upperTail ∧
    exp (-((12029:ℝ)*em12029)) ≤ scalar12029.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12029:ℝ)) (by norm_num [ep12029]) ?_)
      (show bp12029^8 ≤ scalar12029.upperTail by norm_num [bp12029, scalar12029])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12029, bp12029, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12029:ℝ)) (by norm_num [em12029]) ?_)
      (show bm12029^8 ≤ scalar12029.lowerTail by norm_num [bm12029, scalar12029])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12029, bm12029, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12029 :
    agent12029.root+dsL+scalar12029.worldRadius < √(1/100/aL) ∧
    2*(agent12029.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12029, agent12029, scalar12029, tp12029, tm12029, ep12029, em12029, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12029, agent12029, scalar12029, tp12029, tm12029, ep12029, em12029, dsL]

noncomputable def master12029 : MasterCertificate 12029 world12029 agent12029 :=
  master scalar12029 dsL tp12029 tm12029 ep12029 em12029
    (by norm_num [dsL]) (by norm_num [tp12029]) (by norm_num [tm12029])
    (by norm_num [ep12029]) (by norm_num [em12029])
    positive12029 negative12029 tails12029.1 tails12029.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12029.1 tailGuards12029.2

theorem preserves12029 : master12029.toScalarCertificate = scalar12029 := rfl

noncomputable def tp12030 : ℝ := (472174169 / 2000000000)
noncomputable def tm12030 : ℝ := (-((3055967543 / 5000000000)))
noncomputable def ep12030 : ℝ := (54241871920018469 / 100000000000000000000)
noncomputable def em12030 : ℝ := (26165599200038323 / 50000000000000000000)
noncomputable def bp12030 : ℝ := (22117316559442457449 / 50000000000000000000)
noncomputable def bm12030 : ℝ := (22762002973338692737 / 50000000000000000000)

theorem positive12030 :
    Eplus aL (agent12030.root+dsL) scalar12030.worldRadius world12030.frame
      agent12030.frame tp12030 ≤ -ep12030 := by
  apply positive_check (eT := (116185392774940749577 / 100000000000000000000)) (y := (494366954287548967 / 1250000000000000000)) (u := (148511700950503138813 / 100000000000000000000))
  · norm_num [world12030, agent12030, scalar12030, tp12030, tm12030, ep12030, em12030, dsL]
  · norm_num [world12030, agent12030, scalar12030, tp12030, tm12030, ep12030, em12030, dsL]
  · norm_num [world12030, agent12030, scalar12030, tp12030, tm12030, ep12030, em12030, dsL]
  · norm_num [world12030, agent12030, scalar12030, tp12030, tm12030, ep12030, em12030, dsL]
  · norm_num [world12030, agent12030, scalar12030, tp12030, tm12030, ep12030, em12030, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12030, agent12030, tp12030, tm12030, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12030, agent12030, scalar12030, tp12030, tm12030, ep12030, em12030, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12030, agent12030, tp12030, tm12030, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12030, agent12030, scalar12030, tp12030, tm12030, ep12030, em12030, dsL]

theorem negative12030 :
    Eminus aL (agent12030.root+dsL) scalar12030.worldRadius world12030.frame
      agent12030.frame tm12030 ≤ -em12030 := by
  apply negative_check (lo := (67816068577433415663 / 100000000000000000000)) (hi := (4238504286089588479 / 6250000000000000000))
    (y := (-((9168642635437804729 / 12500000000000000000)))) (u := (24011469081424580519 / 50000000000000000000))
  · norm_num [world12030, agent12030, scalar12030, tp12030, tm12030, ep12030, em12030, dsL]
  · norm_num [world12030, agent12030, scalar12030, tp12030, tm12030, ep12030, em12030, dsL]
  · norm_num [world12030, agent12030, scalar12030, tp12030, tm12030, ep12030, em12030, dsL]
  · norm_num [world12030, agent12030, scalar12030, tp12030, tm12030, ep12030, em12030, dsL]
  · norm_num [world12030, agent12030, scalar12030, tp12030, tm12030, ep12030, em12030, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12030, agent12030, tp12030, tm12030, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12030, agent12030, tp12030, tm12030, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12030, agent12030, scalar12030, tp12030, tm12030, ep12030, em12030, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12030, agent12030, tp12030, tm12030, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12030, agent12030, scalar12030, tp12030, tm12030, ep12030, em12030, dsL]

theorem tails12030 :
    exp (-((12030:ℝ)*ep12030)) ≤ scalar12030.upperTail ∧
    exp (-((12030:ℝ)*em12030)) ≤ scalar12030.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12030:ℝ)) (by norm_num [ep12030]) ?_)
      (show bp12030^8 ≤ scalar12030.upperTail by norm_num [bp12030, scalar12030])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12030, bp12030, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12030:ℝ)) (by norm_num [em12030]) ?_)
      (show bm12030^8 ≤ scalar12030.lowerTail by norm_num [bm12030, scalar12030])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12030, bm12030, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12030 :
    agent12030.root+dsL+scalar12030.worldRadius < √(1/100/aL) ∧
    2*(agent12030.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12030, agent12030, scalar12030, tp12030, tm12030, ep12030, em12030, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12030, agent12030, scalar12030, tp12030, tm12030, ep12030, em12030, dsL]

noncomputable def master12030 : MasterCertificate 12030 world12030 agent12030 :=
  master scalar12030 dsL tp12030 tm12030 ep12030 em12030
    (by norm_num [dsL]) (by norm_num [tp12030]) (by norm_num [tm12030])
    (by norm_num [ep12030]) (by norm_num [em12030])
    positive12030 negative12030 tails12030.1 tails12030.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12030.1 tailGuards12030.2

theorem preserves12030 : master12030.toScalarCertificate = scalar12030 := rfl

noncomputable def tp12031 : ℝ := (2360974751 / 10000000000)
noncomputable def tm12031 : ℝ := (-((611216911 / 1000000000)))
noncomputable def ep12031 : ℝ := (27122470370906423 / 50000000000000000000)
noncomputable def em12031 : ℝ := (52333874773822997 / 100000000000000000000)
noncomputable def bp12031 : ℝ := (44229592711110842141 / 100000000000000000000)
noncomputable def bm12031 : ℝ := (4551919598347996133 / 10000000000000000000)

theorem positive12031 :
    Eplus aL (agent12031.root+dsL) scalar12031.worldRadius world12031.frame
      agent12031.frame tp12031 ≤ -ep12031 := by
  apply positive_check (eT := (3630804236580968919 / 3125000000000000000)) (y := (39550026967703150937 / 100000000000000000000)) (u := (7425634845499526811 / 5000000000000000000))
  · norm_num [world12031, agent12031, scalar12031, tp12031, tm12031, ep12031, em12031, dsL]
  · norm_num [world12031, agent12031, scalar12031, tp12031, tm12031, ep12031, em12031, dsL]
  · norm_num [world12031, agent12031, scalar12031, tp12031, tm12031, ep12031, em12031, dsL]
  · norm_num [world12031, agent12031, scalar12031, tp12031, tm12031, ep12031, em12031, dsL]
  · norm_num [world12031, agent12031, scalar12031, tp12031, tm12031, ep12031, em12031, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12031, agent12031, tp12031, tm12031, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12031, agent12031, scalar12031, tp12031, tm12031, ep12031, em12031, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12031, agent12031, tp12031, tm12031, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12031, agent12031, scalar12031, tp12031, tm12031, ep12031, em12031, dsL]

theorem negative12031 :
    Eminus aL (agent12031.root+dsL) scalar12031.worldRadius world12031.frame
      agent12031.frame tm12031 ≤ -em12031 := by
  apply negative_check (lo := (67815701289959278683 / 100000000000000000000)) (hi := (16953925322489819671 / 25000000000000000000))
    (y := (-((14669755645186844801 / 20000000000000000000)))) (u := (48023112418030912449 / 100000000000000000000))
  · norm_num [world12031, agent12031, scalar12031, tp12031, tm12031, ep12031, em12031, dsL]
  · norm_num [world12031, agent12031, scalar12031, tp12031, tm12031, ep12031, em12031, dsL]
  · norm_num [world12031, agent12031, scalar12031, tp12031, tm12031, ep12031, em12031, dsL]
  · norm_num [world12031, agent12031, scalar12031, tp12031, tm12031, ep12031, em12031, dsL]
  · norm_num [world12031, agent12031, scalar12031, tp12031, tm12031, ep12031, em12031, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12031, agent12031, tp12031, tm12031, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12031, agent12031, tp12031, tm12031, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12031, agent12031, scalar12031, tp12031, tm12031, ep12031, em12031, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12031, agent12031, tp12031, tm12031, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12031, agent12031, scalar12031, tp12031, tm12031, ep12031, em12031, dsL]

theorem tails12031 :
    exp (-((12031:ℝ)*ep12031)) ≤ scalar12031.upperTail ∧
    exp (-((12031:ℝ)*em12031)) ≤ scalar12031.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12031:ℝ)) (by norm_num [ep12031]) ?_)
      (show bp12031^8 ≤ scalar12031.upperTail by norm_num [bp12031, scalar12031])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12031, bp12031, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12031:ℝ)) (by norm_num [em12031]) ?_)
      (show bm12031^8 ≤ scalar12031.lowerTail by norm_num [bm12031, scalar12031])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12031, bm12031, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12031 :
    agent12031.root+dsL+scalar12031.worldRadius < √(1/100/aL) ∧
    2*(agent12031.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12031, agent12031, scalar12031, tp12031, tm12031, ep12031, em12031, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12031, agent12031, scalar12031, tp12031, tm12031, ep12031, em12031, dsL]

noncomputable def master12031 : MasterCertificate 12031 world12031 agent12031 :=
  master scalar12031 dsL tp12031 tm12031 ep12031 em12031
    (by norm_num [dsL]) (by norm_num [tp12031]) (by norm_num [tm12031])
    (by norm_num [ep12031]) (by norm_num [em12031])
    positive12031 negative12031 tails12031.1 tails12031.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12031.1 tailGuards12031.2

theorem preserves12031 : master12031.toScalarCertificate = scalar12031 := rfl

noncomputable def tp12032 : ℝ := (236107861 / 1000000000)
noncomputable def tm12032 : ℝ := (-((1528100699 / 2500000000)))
noncomputable def ep12032 : ℝ := (13562001862897769 / 25000000000000000000)
noncomputable def em12032 : ℝ := (26168274601767857 / 50000000000000000000)
noncomputable def bp12032 : ℝ := (44224553943164072591 / 100000000000000000000)
noncomputable def bm12032 : ℝ := (2844649222170019339 / 6250000000000000000)

theorem positive12032 :
    Eplus aL (agent12032.root+dsL) scalar12032.worldRadius world12032.frame
      agent12032.frame tp12032 ≤ -ep12032 := by
  apply positive_check (eT := (58093039027825933893 / 50000000000000000000)) (y := (39550697463667154251 / 100000000000000000000)) (u := (74256846342483830983 / 50000000000000000000))
  · norm_num [world12032, agent12032, scalar12032, tp12032, tm12032, ep12032, em12032, dsL]
  · norm_num [world12032, agent12032, scalar12032, tp12032, tm12032, ep12032, em12032, dsL]
  · norm_num [world12032, agent12032, scalar12032, tp12032, tm12032, ep12032, em12032, dsL]
  · norm_num [world12032, agent12032, scalar12032, tp12032, tm12032, ep12032, em12032, dsL]
  · norm_num [world12032, agent12032, scalar12032, tp12032, tm12032, ep12032, em12032, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12032, agent12032, tp12032, tm12032, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12032, agent12032, scalar12032, tp12032, tm12032, ep12032, em12032, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12032, agent12032, tp12032, tm12032, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12032, agent12032, scalar12032, tp12032, tm12032, ep12032, em12032, dsL]

theorem negative12032 :
    Eminus aL (agent12032.root+dsL) scalar12032.worldRadius world12032.frame
      agent12032.frame tm12032 ≤ -em12032 := by
  apply negative_check (lo := (33907667700060752957 / 50000000000000000000)) (hi := (13563067080024301183 / 20000000000000000000))
    (y := (-((36674206676241222037 / 50000000000000000000)))) (u := (1200582191048462921 / 2500000000000000000))
  · norm_num [world12032, agent12032, scalar12032, tp12032, tm12032, ep12032, em12032, dsL]
  · norm_num [world12032, agent12032, scalar12032, tp12032, tm12032, ep12032, em12032, dsL]
  · norm_num [world12032, agent12032, scalar12032, tp12032, tm12032, ep12032, em12032, dsL]
  · norm_num [world12032, agent12032, scalar12032, tp12032, tm12032, ep12032, em12032, dsL]
  · norm_num [world12032, agent12032, scalar12032, tp12032, tm12032, ep12032, em12032, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12032, agent12032, tp12032, tm12032, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12032, agent12032, tp12032, tm12032, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12032, agent12032, scalar12032, tp12032, tm12032, ep12032, em12032, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12032, agent12032, tp12032, tm12032, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12032, agent12032, scalar12032, tp12032, tm12032, ep12032, em12032, dsL]

theorem tails12032 :
    exp (-((12032:ℝ)*ep12032)) ≤ scalar12032.upperTail ∧
    exp (-((12032:ℝ)*em12032)) ≤ scalar12032.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12032:ℝ)) (by norm_num [ep12032]) ?_)
      (show bp12032^8 ≤ scalar12032.upperTail by norm_num [bp12032, scalar12032])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12032, bp12032, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12032:ℝ)) (by norm_num [em12032]) ?_)
      (show bm12032^8 ≤ scalar12032.lowerTail by norm_num [bm12032, scalar12032])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12032, bm12032, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12032 :
    agent12032.root+dsL+scalar12032.worldRadius < √(1/100/aL) ∧
    2*(agent12032.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12032, agent12032, scalar12032, tp12032, tm12032, ep12032, em12032, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12032, agent12032, scalar12032, tp12032, tm12032, ep12032, em12032, dsL]

noncomputable def master12032 : MasterCertificate 12032 world12032 agent12032 :=
  master scalar12032 dsL tp12032 tm12032 ep12032 em12032
    (by norm_num [dsL]) (by norm_num [tp12032]) (by norm_num [tm12032])
    (by norm_num [ep12032]) (by norm_num [em12032])
    positive12032 negative12032 tails12032.1 tails12032.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12032.1 tailGuards12032.2

theorem preserves12032 : master12032.toScalarCertificate = scalar12032 := rfl

noncomputable def tp12033 : ℝ := (47223647 / 200000000)
noncomputable def tm12033 : ℝ := (-((382039777 / 625000000)))
noncomputable def ep12033 : ℝ := (54251072790965511 / 100000000000000000000)
noncomputable def em12033 : ℝ := (52339222315743553 / 100000000000000000000)
noncomputable def bp12033 : ℝ := (4421951632170639549 / 10000000000000000000)
noncomputable def bm12033 : ℝ := (22754790115739605297 / 50000000000000000000)

theorem positive12033 :
    Eplus aL (agent12033.root+dsL) scalar12033.worldRadius world12033.frame
      agent12033.frame tp12033 ≤ -ep12033 := by
  apply positive_check (eT := (116186419698602423117 / 100000000000000000000)) (y := (39551366534204033327 / 100000000000000000000)) (u := (29702937269930560667 / 20000000000000000000))
  · norm_num [world12033, agent12033, scalar12033, tp12033, tm12033, ep12033, em12033, dsL]
  · norm_num [world12033, agent12033, scalar12033, tp12033, tm12033, ep12033, em12033, dsL]
  · norm_num [world12033, agent12033, scalar12033, tp12033, tm12033, ep12033, em12033, dsL]
  · norm_num [world12033, agent12033, scalar12033, tp12033, tm12033, ep12033, em12033, dsL]
  · norm_num [world12033, agent12033, scalar12033, tp12033, tm12033, ep12033, em12033, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12033, agent12033, tp12033, tm12033, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12033, agent12033, scalar12033, tp12033, tm12033, ep12033, em12033, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12033, agent12033, tp12033, tm12033, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12033, agent12033, scalar12033, tp12033, tm12033, ep12033, em12033, dsL]

theorem negative12033 :
    Eminus aL (agent12033.root+dsL) scalar12033.worldRadius world12033.frame
      agent12033.frame tm12033 ≤ -em12033 := by
  apply negative_check (lo := (67814969666869567373 / 100000000000000000000)) (hi := (33907484833434783687 / 50000000000000000000))
    (y := (-((73348049298537284173 / 100000000000000000000)))) (u := (48023462472930012173 / 100000000000000000000))
  · norm_num [world12033, agent12033, scalar12033, tp12033, tm12033, ep12033, em12033, dsL]
  · norm_num [world12033, agent12033, scalar12033, tp12033, tm12033, ep12033, em12033, dsL]
  · norm_num [world12033, agent12033, scalar12033, tp12033, tm12033, ep12033, em12033, dsL]
  · norm_num [world12033, agent12033, scalar12033, tp12033, tm12033, ep12033, em12033, dsL]
  · norm_num [world12033, agent12033, scalar12033, tp12033, tm12033, ep12033, em12033, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12033, agent12033, tp12033, tm12033, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12033, agent12033, tp12033, tm12033, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12033, agent12033, scalar12033, tp12033, tm12033, ep12033, em12033, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12033, agent12033, tp12033, tm12033, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12033, agent12033, scalar12033, tp12033, tm12033, ep12033, em12033, dsL]

theorem tails12033 :
    exp (-((12033:ℝ)*ep12033)) ≤ scalar12033.upperTail ∧
    exp (-((12033:ℝ)*em12033)) ≤ scalar12033.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12033:ℝ)) (by norm_num [ep12033]) ?_)
      (show bp12033^8 ≤ scalar12033.upperTail by norm_num [bp12033, scalar12033])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12033, bp12033, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12033:ℝ)) (by norm_num [em12033]) ?_)
      (show bm12033^8 ≤ scalar12033.lowerTail by norm_num [bm12033, scalar12033])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12033, bm12033, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12033 :
    agent12033.root+dsL+scalar12033.worldRadius < √(1/100/aL) ∧
    2*(agent12033.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12033, agent12033, scalar12033, tp12033, tm12033, ep12033, em12033, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12033, agent12033, scalar12033, tp12033, tm12033, ep12033, em12033, dsL]

noncomputable def master12033 : MasterCertificate 12033 world12033 agent12033 :=
  master scalar12033 dsL tp12033 tm12033 ep12033 em12033
    (by norm_num [dsL]) (by norm_num [tp12033]) (by norm_num [tm12033])
    (by norm_num [ep12033]) (by norm_num [em12033])
    positive12033 negative12033 tails12033.1 tails12033.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12033.1 tailGuards12033.2

theorem preserves12033 : master12033.toScalarCertificate = scalar12033 := rfl

end BstLean.Part281
