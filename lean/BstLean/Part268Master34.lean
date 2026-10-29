import BstLean.Part261Checker
import BstLean.Part268Scalar34
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp13200 : ℝ := (2358731003 / 10000000000)
noncomputable def tm13200 : ℝ := (-((769510711 / 1250000000)))
noncomputable def ep13200 : ℝ := (526625661071031 / 1000000000000000000)
noncomputable def em13200 : ℝ := (51180168252719847 / 100000000000000000000)
noncomputable def bp13200 : ℝ := (20969954280146869849 / 50000000000000000000)
noncomputable def bm13200 : ℝ := (42978389079783409181 / 100000000000000000000)

theorem positive13200 :
    Eplus aL (agent13200.root+dsL) scalar13200.worldRadius world13200.frame
      agent13200.frame tp13200 ≤ -ep13200 := by
  apply positive_check (eT := (115719467688479466001 / 100000000000000000000)) (y := (19088902229491790091 / 50000000000000000000)) (u := (18311086368402627423 / 12500000000000000000))
  · norm_num [world13200, agent13200, scalar13200, tp13200, tm13200, ep13200, em13200, dsL]
  · norm_num [world13200, agent13200, scalar13200, tp13200, tm13200, ep13200, em13200, dsL]
  · norm_num [world13200, agent13200, scalar13200, tp13200, tm13200, ep13200, em13200, dsL]
  · norm_num [world13200, agent13200, scalar13200, tp13200, tm13200, ep13200, em13200, dsL]
  · norm_num [world13200, agent13200, scalar13200, tp13200, tm13200, ep13200, em13200, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13200, agent13200, tp13200, tm13200, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13200, agent13200, scalar13200, tp13200, tm13200, ep13200, em13200, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13200, agent13200, tp13200, tm13200, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13200, agent13200, scalar13200, tp13200, tm13200, ep13200, em13200, dsL]

theorem negative13200 :
    Eminus aL (agent13200.root+dsL) scalar13200.worldRadius world13200.frame
      agent13200.frame tm13200 ≤ -em13200 := by
  apply negative_check (lo := (8539347247153012009 / 12500000000000000000)) (hi := (68314777977224096073 / 100000000000000000000))
    (y := (-((4473740749032727243 / 6250000000000000000)))) (u := (48880163810817187127 / 100000000000000000000))
  · norm_num [world13200, agent13200, scalar13200, tp13200, tm13200, ep13200, em13200, dsL]
  · norm_num [world13200, agent13200, scalar13200, tp13200, tm13200, ep13200, em13200, dsL]
  · norm_num [world13200, agent13200, scalar13200, tp13200, tm13200, ep13200, em13200, dsL]
  · norm_num [world13200, agent13200, scalar13200, tp13200, tm13200, ep13200, em13200, dsL]
  · norm_num [world13200, agent13200, scalar13200, tp13200, tm13200, ep13200, em13200, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13200, agent13200, tp13200, tm13200, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13200, agent13200, tp13200, tm13200, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13200, agent13200, scalar13200, tp13200, tm13200, ep13200, em13200, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13200, agent13200, tp13200, tm13200, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13200, agent13200, scalar13200, tp13200, tm13200, ep13200, em13200, dsL]

theorem tails13200 :
    exp (-((13200:ℝ)*ep13200)) ≤ scalar13200.upperTail ∧
    exp (-((13200:ℝ)*em13200)) ≤ scalar13200.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13200:ℝ)) (by norm_num [ep13200]) ?_)
      (show bp13200^8 ≤ scalar13200.upperTail by norm_num [bp13200, scalar13200])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13200, bp13200, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13200:ℝ)) (by norm_num [em13200]) ?_)
      (show bm13200^8 ≤ scalar13200.lowerTail by norm_num [bm13200, scalar13200])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13200, bm13200, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13200 :
    agent13200.root+dsL+scalar13200.worldRadius < √(1/100/aL) ∧
    2*(agent13200.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13200, agent13200, scalar13200, tp13200, tm13200, ep13200, em13200, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13200, agent13200, scalar13200, tp13200, tm13200, ep13200, em13200, dsL]

noncomputable def master13200 : MasterCertificate 13200 world13200 agent13200 :=
  master scalar13200 dsL tp13200 tm13200 ep13200 em13200
    (by norm_num [dsL]) (by norm_num [tp13200]) (by norm_num [tm13200])
    (by norm_num [ep13200]) (by norm_num [em13200])
    positive13200 negative13200 tails13200.1 tails13200.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13200.1 tailGuards13200.2

theorem preserves13200 : master13200.toScalarCertificate = scalar13200 := rfl

noncomputable def tp13201 : ℝ := (2358800877 / 10000000000)
noncomputable def tm13201 : ℝ := (-((1231246681 / 2000000000)))
noncomputable def ep13201 : ℝ := (52664642816167979 / 100000000000000000000)
noncomputable def em13201 : ℝ := (12795480347945017 / 25000000000000000000)
noncomputable def bp13201 : ℝ := (41935710732204371121 / 100000000000000000000)
noncomputable def bm13201 : ℝ := (8594879278512423429 / 20000000000000000000)

theorem positive13201 :
    Eplus aL (agent13201.root+dsL) scalar13201.worldRadius world13201.frame
      agent13201.frame tp13201 ≤ -ep13201 := by
  apply positive_check (eT := (115719618818424631853 / 100000000000000000000)) (y := (3817842506414063211 / 10000000000000000000)) (u := (73244800033206276537 / 50000000000000000000))
  · norm_num [world13201, agent13201, scalar13201, tp13201, tm13201, ep13201, em13201, dsL]
  · norm_num [world13201, agent13201, scalar13201, tp13201, tm13201, ep13201, em13201, dsL]
  · norm_num [world13201, agent13201, scalar13201, tp13201, tm13201, ep13201, em13201, dsL]
  · norm_num [world13201, agent13201, scalar13201, tp13201, tm13201, ep13201, em13201, dsL]
  · norm_num [world13201, agent13201, scalar13201, tp13201, tm13201, ep13201, em13201, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13201, agent13201, tp13201, tm13201, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13201, agent13201, scalar13201, tp13201, tm13201, ep13201, em13201, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13201, agent13201, tp13201, tm13201, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13201, agent13201, scalar13201, tp13201, tm13201, ep13201, em13201, dsL]

theorem negative13201 :
    Eminus aL (agent13201.root+dsL) scalar13201.worldRadius world13201.frame
      agent13201.frame tm13201 ≤ -em13201 := by
  apply negative_check (lo := (34157345814513908689 / 50000000000000000000)) (hi := (68314691629027817379 / 100000000000000000000))
    (y := (-((71579728598175139911 / 100000000000000000000)))) (u := (48880224122303660209 / 100000000000000000000))
  · norm_num [world13201, agent13201, scalar13201, tp13201, tm13201, ep13201, em13201, dsL]
  · norm_num [world13201, agent13201, scalar13201, tp13201, tm13201, ep13201, em13201, dsL]
  · norm_num [world13201, agent13201, scalar13201, tp13201, tm13201, ep13201, em13201, dsL]
  · norm_num [world13201, agent13201, scalar13201, tp13201, tm13201, ep13201, em13201, dsL]
  · norm_num [world13201, agent13201, scalar13201, tp13201, tm13201, ep13201, em13201, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13201, agent13201, tp13201, tm13201, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13201, agent13201, tp13201, tm13201, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13201, agent13201, scalar13201, tp13201, tm13201, ep13201, em13201, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13201, agent13201, tp13201, tm13201, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13201, agent13201, scalar13201, tp13201, tm13201, ep13201, em13201, dsL]

theorem tails13201 :
    exp (-((13201:ℝ)*ep13201)) ≤ scalar13201.upperTail ∧
    exp (-((13201:ℝ)*em13201)) ≤ scalar13201.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13201:ℝ)) (by norm_num [ep13201]) ?_)
      (show bp13201^8 ≤ scalar13201.upperTail by norm_num [bp13201, scalar13201])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13201, bp13201, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13201:ℝ)) (by norm_num [em13201]) ?_)
      (show bm13201^8 ≤ scalar13201.lowerTail by norm_num [bm13201, scalar13201])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13201, bm13201, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13201 :
    agent13201.root+dsL+scalar13201.worldRadius < √(1/100/aL) ∧
    2*(agent13201.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13201, agent13201, scalar13201, tp13201, tm13201, ep13201, em13201, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13201, agent13201, scalar13201, tp13201, tm13201, ep13201, em13201, dsL]

noncomputable def master13201 : MasterCertificate 13201 world13201 agent13201 :=
  master scalar13201 dsL tp13201 tm13201 ep13201 em13201
    (by norm_num [dsL]) (by norm_num [tp13201]) (by norm_num [tm13201])
    (by norm_num [ep13201]) (by norm_num [em13201])
    positive13201 negative13201 tails13201.1 tails13201.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13201.1 tailGuards13201.2

theorem preserves13201 : master13201.toScalarCertificate = scalar13201 := rfl

noncomputable def tp13202 : ℝ := (2358870773 / 10000000000)
noncomputable def tm13202 : ℝ := (-((6156380909 / 10000000000)))
noncomputable def ep13202 : ℝ := (52666718698963241 / 100000000000000000000)
noncomputable def em13202 : ℝ := (51183673731916879 / 100000000000000000000)
noncomputable def bp13202 : ℝ := (2620719604896297167 / 6250000000000000000)
noncomputable def bm13202 : ℝ := (42970404454460103133 / 100000000000000000000)

theorem positive13202 :
    Eplus aL (agent13202.root+dsL) scalar13202.worldRadius world13202.frame
      agent13202.frame tp13202 ≤ -ep13202 := by
  apply positive_check (eT := (115719770138944445029 / 100000000000000000000)) (y := (4772380807170616993 / 12500000000000000000)) (u := (146490510345689879493 / 100000000000000000000))
  · norm_num [world13202, agent13202, scalar13202, tp13202, tm13202, ep13202, em13202, dsL]
  · norm_num [world13202, agent13202, scalar13202, tp13202, tm13202, ep13202, em13202, dsL]
  · norm_num [world13202, agent13202, scalar13202, tp13202, tm13202, ep13202, em13202, dsL]
  · norm_num [world13202, agent13202, scalar13202, tp13202, tm13202, ep13202, em13202, dsL]
  · norm_num [world13202, agent13202, scalar13202, tp13202, tm13202, ep13202, em13202, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13202, agent13202, tp13202, tm13202, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13202, agent13202, scalar13202, tp13202, tm13202, ep13202, em13202, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13202, agent13202, tp13202, tm13202, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13202, agent13202, scalar13202, tp13202, tm13202, ep13202, em13202, dsL]

theorem negative13202 :
    Eminus aL (agent13202.root+dsL) scalar13202.worldRadius world13202.frame
      agent13202.frame tm13202 ≤ -em13202 := by
  apply negative_check (lo := (34157303062484372229 / 50000000000000000000)) (hi := (68314606124968744459 / 100000000000000000000))
    (y := (-((35789801951078336871 / 50000000000000000000)))) (u := (9776057014806992049 / 20000000000000000000))
  · norm_num [world13202, agent13202, scalar13202, tp13202, tm13202, ep13202, em13202, dsL]
  · norm_num [world13202, agent13202, scalar13202, tp13202, tm13202, ep13202, em13202, dsL]
  · norm_num [world13202, agent13202, scalar13202, tp13202, tm13202, ep13202, em13202, dsL]
  · norm_num [world13202, agent13202, scalar13202, tp13202, tm13202, ep13202, em13202, dsL]
  · norm_num [world13202, agent13202, scalar13202, tp13202, tm13202, ep13202, em13202, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13202, agent13202, tp13202, tm13202, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13202, agent13202, tp13202, tm13202, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13202, agent13202, scalar13202, tp13202, tm13202, ep13202, em13202, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13202, agent13202, tp13202, tm13202, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13202, agent13202, scalar13202, tp13202, tm13202, ep13202, em13202, dsL]

theorem tails13202 :
    exp (-((13202:ℝ)*ep13202)) ≤ scalar13202.upperTail ∧
    exp (-((13202:ℝ)*em13202)) ≤ scalar13202.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13202:ℝ)) (by norm_num [ep13202]) ?_)
      (show bp13202^8 ≤ scalar13202.upperTail by norm_num [bp13202, scalar13202])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13202, bp13202, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13202:ℝ)) (by norm_num [em13202]) ?_)
      (show bm13202^8 ≤ scalar13202.lowerTail by norm_num [bm13202, scalar13202])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13202, bm13202, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13202 :
    agent13202.root+dsL+scalar13202.worldRadius < √(1/100/aL) ∧
    2*(agent13202.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13202, agent13202, scalar13202, tp13202, tm13202, ep13202, em13202, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13202, agent13202, scalar13202, tp13202, tm13202, ep13202, em13202, dsL]

noncomputable def master13202 : MasterCertificate 13202 world13202 agent13202 :=
  master scalar13202 dsL tp13202 tm13202 ep13202 em13202
    (by norm_num [dsL]) (by norm_num [tp13202]) (by norm_num [tm13202])
    (by norm_num [ep13202]) (by norm_num [em13202])
    positive13202 negative13202 tails13202.1 tails13202.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13202.1 tailGuards13202.2

theorem preserves13202 : master13202.toScalarCertificate = scalar13202 := rfl

noncomputable def tp13203 : ℝ := (2358940561 / 10000000000)
noncomputable def tm13203 : ℝ := (-((6156528367 / 10000000000)))
noncomputable def ep13203 : ℝ := (52668793316431931 / 100000000000000000000)
noncomputable def em13203 : ℝ := (2559271246365679 / 5000000000000000000)
noncomputable def bp13203 : ℝ := (4192731770249339959 / 10000000000000000000)
noncomputable def bm13203 : ℝ := (268540084441795401 / 625000000000000000)

theorem positive13203 :
    Eplus aL (agent13203.root+dsL) scalar13203.worldRadius world13203.frame
      agent13203.frame tp13203 ≤ -ep13203 := by
  apply positive_check (eT := (115719920718909967027 / 100000000000000000000)) (y := (19089833111435734317 / 50000000000000000000)) (u := (73245709123078384919 / 50000000000000000000))
  · norm_num [world13203, agent13203, scalar13203, tp13203, tm13203, ep13203, em13203, dsL]
  · norm_num [world13203, agent13203, scalar13203, tp13203, tm13203, ep13203, em13203, dsL]
  · norm_num [world13203, agent13203, scalar13203, tp13203, tm13203, ep13203, em13203, dsL]
  · norm_num [world13203, agent13203, scalar13203, tp13203, tm13203, ep13203, em13203, dsL]
  · norm_num [world13203, agent13203, scalar13203, tp13203, tm13203, ep13203, em13203, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13203, agent13203, tp13203, tm13203, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13203, agent13203, scalar13203, tp13203, tm13203, ep13203, em13203, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13203, agent13203, tp13203, tm13203, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13203, agent13203, scalar13203, tp13203, tm13203, ep13203, em13203, dsL]

theorem negative13203 :
    Eminus aL (agent13203.root+dsL) scalar13203.worldRadius world13203.frame
      agent13203.frame tm13203 ≤ -em13203 := by
  apply negative_check (lo := (3415726037945637479 / 5000000000000000000)) (hi := (68314520758912749581 / 100000000000000000000))
    (y := (-((894743489994923783 / 1250000000000000000)))) (u := (48880346029041143607 / 100000000000000000000))
  · norm_num [world13203, agent13203, scalar13203, tp13203, tm13203, ep13203, em13203, dsL]
  · norm_num [world13203, agent13203, scalar13203, tp13203, tm13203, ep13203, em13203, dsL]
  · norm_num [world13203, agent13203, scalar13203, tp13203, tm13203, ep13203, em13203, dsL]
  · norm_num [world13203, agent13203, scalar13203, tp13203, tm13203, ep13203, em13203, dsL]
  · norm_num [world13203, agent13203, scalar13203, tp13203, tm13203, ep13203, em13203, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13203, agent13203, tp13203, tm13203, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13203, agent13203, tp13203, tm13203, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13203, agent13203, scalar13203, tp13203, tm13203, ep13203, em13203, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13203, agent13203, tp13203, tm13203, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13203, agent13203, scalar13203, tp13203, tm13203, ep13203, em13203, dsL]

theorem tails13203 :
    exp (-((13203:ℝ)*ep13203)) ≤ scalar13203.upperTail ∧
    exp (-((13203:ℝ)*em13203)) ≤ scalar13203.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13203:ℝ)) (by norm_num [ep13203]) ?_)
      (show bp13203^8 ≤ scalar13203.upperTail by norm_num [bp13203, scalar13203])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13203, bp13203, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13203:ℝ)) (by norm_num [em13203]) ?_)
      (show bm13203^8 ≤ scalar13203.lowerTail by norm_num [bm13203, scalar13203])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13203, bm13203, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13203 :
    agent13203.root+dsL+scalar13203.worldRadius < √(1/100/aL) ∧
    2*(agent13203.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13203, agent13203, scalar13203, tp13203, tm13203, ep13203, em13203, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13203, agent13203, scalar13203, tp13203, tm13203, ep13203, em13203, dsL]

noncomputable def master13203 : MasterCertificate 13203 world13203 agent13203 :=
  master scalar13203 dsL tp13203 tm13203 ep13203 em13203
    (by norm_num [dsL]) (by norm_num [tp13203]) (by norm_num [tm13203])
    (by norm_num [ep13203]) (by norm_num [em13203])
    positive13203 negative13203 tails13203.1 tails13203.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13203.1 tailGuards13203.2

theorem preserves13203 : master13203.toScalarCertificate = scalar13203 := rfl

noncomputable def tp13204 : ℝ := (589752601 / 2500000000)
noncomputable def tm13204 : ℝ := (-((6156675677 / 10000000000)))
noncomputable def ep13204 : ℝ := (52670866818130441 / 100000000000000000000)
noncomputable def em13204 : ℝ := (51187175077484291 / 100000000000000000000)
noncomputable def bp13204 : ℝ := (41923122701137447569 / 100000000000000000000)
noncomputable def bm13204 : ℝ := (42962423490654908317 / 100000000000000000000)

theorem positive13204 :
    Eplus aL (agent13204.root+dsL) scalar13204.worldRadius world13204.frame
      agent13204.frame tp13204 ≤ -ep13204 := by
  apply positive_check (eT := (23144014345160252777 / 20000000000000000000)) (y := (7636057469874603943 / 20000000000000000000)) (u := (36623082036500951593 / 25000000000000000000))
  · norm_num [world13204, agent13204, scalar13204, tp13204, tm13204, ep13204, em13204, dsL]
  · norm_num [world13204, agent13204, scalar13204, tp13204, tm13204, ep13204, em13204, dsL]
  · norm_num [world13204, agent13204, scalar13204, tp13204, tm13204, ep13204, em13204, dsL]
  · norm_num [world13204, agent13204, scalar13204, tp13204, tm13204, ep13204, em13204, dsL]
  · norm_num [world13204, agent13204, scalar13204, tp13204, tm13204, ep13204, em13204, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13204, agent13204, tp13204, tm13204, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13204, agent13204, scalar13204, tp13204, tm13204, ep13204, em13204, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13204, agent13204, tp13204, tm13204, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13204, agent13204, scalar13204, tp13204, tm13204, ep13204, em13204, dsL]

theorem negative13204 :
    Eminus aL (agent13204.root+dsL) scalar13204.worldRadius world13204.frame
      agent13204.frame tm13204 ≤ -em13204 := by
  apply negative_check (lo := (6831443596210939711 / 10000000000000000000)) (hi := (68314435962109397111 / 100000000000000000000))
    (y := (-((71579353804893385109 / 100000000000000000000)))) (u := (48880407322443087987 / 100000000000000000000))
  · norm_num [world13204, agent13204, scalar13204, tp13204, tm13204, ep13204, em13204, dsL]
  · norm_num [world13204, agent13204, scalar13204, tp13204, tm13204, ep13204, em13204, dsL]
  · norm_num [world13204, agent13204, scalar13204, tp13204, tm13204, ep13204, em13204, dsL]
  · norm_num [world13204, agent13204, scalar13204, tp13204, tm13204, ep13204, em13204, dsL]
  · norm_num [world13204, agent13204, scalar13204, tp13204, tm13204, ep13204, em13204, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13204, agent13204, tp13204, tm13204, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13204, agent13204, tp13204, tm13204, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13204, agent13204, scalar13204, tp13204, tm13204, ep13204, em13204, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13204, agent13204, tp13204, tm13204, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13204, agent13204, scalar13204, tp13204, tm13204, ep13204, em13204, dsL]

theorem tails13204 :
    exp (-((13204:ℝ)*ep13204)) ≤ scalar13204.upperTail ∧
    exp (-((13204:ℝ)*em13204)) ≤ scalar13204.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13204:ℝ)) (by norm_num [ep13204]) ?_)
      (show bp13204^8 ≤ scalar13204.upperTail by norm_num [bp13204, scalar13204])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13204, bp13204, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13204:ℝ)) (by norm_num [em13204]) ?_)
      (show bm13204^8 ≤ scalar13204.lowerTail by norm_num [bm13204, scalar13204])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13204, bm13204, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13204 :
    agent13204.root+dsL+scalar13204.worldRadius < √(1/100/aL) ∧
    2*(agent13204.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13204, agent13204, scalar13204, tp13204, tm13204, ep13204, em13204, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13204, agent13204, scalar13204, tp13204, tm13204, ep13204, em13204, dsL]

noncomputable def master13204 : MasterCertificate 13204 world13204 agent13204 :=
  master scalar13204 dsL tp13204 tm13204 ep13204 em13204
    (by norm_num [dsL]) (by norm_num [tp13204]) (by norm_num [tm13204])
    (by norm_num [ep13204]) (by norm_num [em13204])
    positive13204 negative13204 tails13204.1 tails13204.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13204.1 tailGuards13204.2

theorem preserves13204 : master13204.toScalarCertificate = scalar13204 := rfl

noncomputable def tp13205 : ℝ := (2359080147 / 10000000000)
noncomputable def tm13205 : ℝ := (-((1231364607 / 2000000000)))
noncomputable def ep13205 : ℝ := (13168234909588359 / 25000000000000000000)
noncomputable def em13205 : ℝ := (51188924579788591 / 100000000000000000000)
noncomputable def bp13205 : ℝ := (41918928373740765341 / 100000000000000000000)
noncomputable def bm13205 : ℝ := (42958434112582121983 / 100000000000000000000)

theorem positive13205 :
    Eplus aL (agent13205.root+dsL) scalar13205.worldRadius world13205.frame
      agent13205.frame tp13205 ≤ -ep13205 := by
  apply positive_check (eT := (115720222049434171599 / 100000000000000000000)) (y := (7636181397816465057 / 20000000000000000000)) (u := (146493235873452402189 / 100000000000000000000))
  · norm_num [world13205, agent13205, scalar13205, tp13205, tm13205, ep13205, em13205, dsL]
  · norm_num [world13205, agent13205, scalar13205, tp13205, tm13205, ep13205, em13205, dsL]
  · norm_num [world13205, agent13205, scalar13205, tp13205, tm13205, ep13205, em13205, dsL]
  · norm_num [world13205, agent13205, scalar13205, tp13205, tm13205, ep13205, em13205, dsL]
  · norm_num [world13205, agent13205, scalar13205, tp13205, tm13205, ep13205, em13205, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13205, agent13205, tp13205, tm13205, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13205, agent13205, scalar13205, tp13205, tm13205, ep13205, em13205, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13205, agent13205, tp13205, tm13205, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13205, agent13205, scalar13205, tp13205, tm13205, ep13205, em13205, dsL]

theorem negative13205 :
    Eminus aL (agent13205.root+dsL) scalar13205.worldRadius world13205.frame
      agent13205.frame tm13205 ≤ -em13205 := by
  apply negative_check (lo := (68314350905902939143 / 100000000000000000000)) (hi := (8539293863237867393 / 12500000000000000000))
    (y := (-((35789614653749661823 / 50000000000000000000)))) (u := (48880468177314292413 / 100000000000000000000))
  · norm_num [world13205, agent13205, scalar13205, tp13205, tm13205, ep13205, em13205, dsL]
  · norm_num [world13205, agent13205, scalar13205, tp13205, tm13205, ep13205, em13205, dsL]
  · norm_num [world13205, agent13205, scalar13205, tp13205, tm13205, ep13205, em13205, dsL]
  · norm_num [world13205, agent13205, scalar13205, tp13205, tm13205, ep13205, em13205, dsL]
  · norm_num [world13205, agent13205, scalar13205, tp13205, tm13205, ep13205, em13205, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13205, agent13205, tp13205, tm13205, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13205, agent13205, tp13205, tm13205, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13205, agent13205, scalar13205, tp13205, tm13205, ep13205, em13205, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13205, agent13205, tp13205, tm13205, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13205, agent13205, scalar13205, tp13205, tm13205, ep13205, em13205, dsL]

theorem tails13205 :
    exp (-((13205:ℝ)*ep13205)) ≤ scalar13205.upperTail ∧
    exp (-((13205:ℝ)*em13205)) ≤ scalar13205.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13205:ℝ)) (by norm_num [ep13205]) ?_)
      (show bp13205^8 ≤ scalar13205.upperTail by norm_num [bp13205, scalar13205])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13205, bp13205, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13205:ℝ)) (by norm_num [em13205]) ?_)
      (show bm13205^8 ≤ scalar13205.lowerTail by norm_num [bm13205, scalar13205])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13205, bm13205, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13205 :
    agent13205.root+dsL+scalar13205.worldRadius < √(1/100/aL) ∧
    2*(agent13205.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13205, agent13205, scalar13205, tp13205, tm13205, ep13205, em13205, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13205, agent13205, scalar13205, tp13205, tm13205, ep13205, em13205, dsL]

noncomputable def master13205 : MasterCertificate 13205 world13205 agent13205 :=
  master scalar13205 dsL tp13205 tm13205 ep13205 em13205
    (by norm_num [dsL]) (by norm_num [tp13205]) (by norm_num [tm13205])
    (by norm_num [ep13205]) (by norm_num [em13205])
    positive13205 negative13205 tails13205.1 tails13205.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13205.1 tailGuards13205.2

theorem preserves13205 : master13205.toScalarCertificate = scalar13205 := rfl

noncomputable def tp13206 : ℝ := (1179574929 / 5000000000)
noncomputable def tm13206 : ℝ := (-((3078485101 / 5000000000)))
noncomputable def ep13206 : ℝ := (26337505358791047 / 50000000000000000000)
noncomputable def em13206 : ℝ := (51190672496010739 / 100000000000000000000)
noncomputable def bp13206 : ℝ := (20957367726690586917 / 50000000000000000000)
noncomputable def bm13206 : ℝ := (21477223020862178709 / 50000000000000000000)

theorem positive13206 :
    Eplus aL (agent13206.root+dsL) scalar13206.worldRadius world13206.frame
      agent13206.frame tp13206 ≤ -ep13206 := by
  apply positive_check (eT := (115720372176889719777 / 100000000000000000000)) (y := (38181526372370395523 / 100000000000000000000)) (u := (146494143230883562913 / 100000000000000000000))
  · norm_num [world13206, agent13206, scalar13206, tp13206, tm13206, ep13206, em13206, dsL]
  · norm_num [world13206, agent13206, scalar13206, tp13206, tm13206, ep13206, em13206, dsL]
  · norm_num [world13206, agent13206, scalar13206, tp13206, tm13206, ep13206, em13206, dsL]
  · norm_num [world13206, agent13206, scalar13206, tp13206, tm13206, ep13206, em13206, dsL]
  · norm_num [world13206, agent13206, scalar13206, tp13206, tm13206, ep13206, em13206, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13206, agent13206, tp13206, tm13206, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13206, agent13206, scalar13206, tp13206, tm13206, ep13206, em13206, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13206, agent13206, tp13206, tm13206, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13206, agent13206, scalar13206, tp13206, tm13206, ep13206, em13206, dsL]

theorem negative13206 :
    Eminus aL (agent13206.root+dsL) scalar13206.worldRadius world13206.frame
      agent13206.frame tm13206 ≤ -em13206 := by
  apply negative_check (lo := (34157133300367474877 / 50000000000000000000)) (hi := (13662853320146989951 / 20000000000000000000))
    (y := (-((71579103290492533451 / 100000000000000000000)))) (u := (24440264887528003153 / 50000000000000000000))
  · norm_num [world13206, agent13206, scalar13206, tp13206, tm13206, ep13206, em13206, dsL]
  · norm_num [world13206, agent13206, scalar13206, tp13206, tm13206, ep13206, em13206, dsL]
  · norm_num [world13206, agent13206, scalar13206, tp13206, tm13206, ep13206, em13206, dsL]
  · norm_num [world13206, agent13206, scalar13206, tp13206, tm13206, ep13206, em13206, dsL]
  · norm_num [world13206, agent13206, scalar13206, tp13206, tm13206, ep13206, em13206, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13206, agent13206, tp13206, tm13206, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13206, agent13206, tp13206, tm13206, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13206, agent13206, scalar13206, tp13206, tm13206, ep13206, em13206, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13206, agent13206, tp13206, tm13206, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13206, agent13206, scalar13206, tp13206, tm13206, ep13206, em13206, dsL]

theorem tails13206 :
    exp (-((13206:ℝ)*ep13206)) ≤ scalar13206.upperTail ∧
    exp (-((13206:ℝ)*em13206)) ≤ scalar13206.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13206:ℝ)) (by norm_num [ep13206]) ?_)
      (show bp13206^8 ≤ scalar13206.upperTail by norm_num [bp13206, scalar13206])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13206, bp13206, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13206:ℝ)) (by norm_num [em13206]) ?_)
      (show bm13206^8 ≤ scalar13206.lowerTail by norm_num [bm13206, scalar13206])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13206, bm13206, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13206 :
    agent13206.root+dsL+scalar13206.worldRadius < √(1/100/aL) ∧
    2*(agent13206.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13206, agent13206, scalar13206, tp13206, tm13206, ep13206, em13206, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13206, agent13206, scalar13206, tp13206, tm13206, ep13206, em13206, dsL]

noncomputable def master13206 : MasterCertificate 13206 world13206 agent13206 :=
  master scalar13206 dsL tp13206 tm13206 ep13206 em13206
    (by norm_num [dsL]) (by norm_num [tp13206]) (by norm_num [tm13206])
    (by norm_num [ep13206]) (by norm_num [em13206])
    positive13206 negative13206 tails13206.1 tails13206.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13206.1 tailGuards13206.2

theorem preserves13206 : master13206.toScalarCertificate = scalar13206 := rfl

noncomputable def tp13207 : ℝ := (1179609793 / 5000000000)
noncomputable def tm13207 : ℝ := (-((6157117383 / 10000000000)))
noncomputable def ep13207 : ℝ := (52677081451074139 / 100000000000000000000)
noncomputable def em13207 : ℝ := (51192420058990901 / 100000000000000000000)
noncomputable def bp13207 : ℝ := (10477635743657049287 / 25000000000000000000)
noncomputable def bm13207 : ℝ := (335550456280360313 / 781250000000000000)

theorem positive13207 :
    Eplus aL (agent13207.root+dsL) scalar13207.worldRadius world13207.frame
      agent13207.frame tp13207 ≤ -ep13207 := by
  apply positive_check (eT := (28930130614777747461 / 25000000000000000000)) (y := (763642928136202971 / 2000000000000000000)) (u := (4577970360869992237 / 3125000000000000000))
  · norm_num [world13207, agent13207, scalar13207, tp13207, tm13207, ep13207, em13207, dsL]
  · norm_num [world13207, agent13207, scalar13207, tp13207, tm13207, ep13207, em13207, dsL]
  · norm_num [world13207, agent13207, scalar13207, tp13207, tm13207, ep13207, em13207, dsL]
  · norm_num [world13207, agent13207, scalar13207, tp13207, tm13207, ep13207, em13207, dsL]
  · norm_num [world13207, agent13207, scalar13207, tp13207, tm13207, ep13207, em13207, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13207, agent13207, tp13207, tm13207, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13207, agent13207, scalar13207, tp13207, tm13207, ep13207, em13207, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13207, agent13207, tp13207, tm13207, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13207, agent13207, scalar13207, tp13207, tm13207, ep13207, em13207, dsL]

theorem negative13207 :
    Eminus aL (agent13207.root+dsL) scalar13207.worldRadius world13207.frame
      agent13207.frame tm13207 ≤ -em13207 := by
  apply negative_check (lo := (68314182179839378193 / 100000000000000000000)) (hi := (34157091089919689097 / 50000000000000000000))
    (y := (-((2863159130356124939 / 4000000000000000000)))) (u := (12220147722799375827 / 25000000000000000000))
  · norm_num [world13207, agent13207, scalar13207, tp13207, tm13207, ep13207, em13207, dsL]
  · norm_num [world13207, agent13207, scalar13207, tp13207, tm13207, ep13207, em13207, dsL]
  · norm_num [world13207, agent13207, scalar13207, tp13207, tm13207, ep13207, em13207, dsL]
  · norm_num [world13207, agent13207, scalar13207, tp13207, tm13207, ep13207, em13207, dsL]
  · norm_num [world13207, agent13207, scalar13207, tp13207, tm13207, ep13207, em13207, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13207, agent13207, tp13207, tm13207, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13207, agent13207, tp13207, tm13207, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13207, agent13207, scalar13207, tp13207, tm13207, ep13207, em13207, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13207, agent13207, tp13207, tm13207, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13207, agent13207, scalar13207, tp13207, tm13207, ep13207, em13207, dsL]

theorem tails13207 :
    exp (-((13207:ℝ)*ep13207)) ≤ scalar13207.upperTail ∧
    exp (-((13207:ℝ)*em13207)) ≤ scalar13207.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13207:ℝ)) (by norm_num [ep13207]) ?_)
      (show bp13207^8 ≤ scalar13207.upperTail by norm_num [bp13207, scalar13207])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13207, bp13207, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13207:ℝ)) (by norm_num [em13207]) ?_)
      (show bm13207^8 ≤ scalar13207.lowerTail by norm_num [bm13207, scalar13207])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13207, bm13207, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13207 :
    agent13207.root+dsL+scalar13207.worldRadius < √(1/100/aL) ∧
    2*(agent13207.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13207, agent13207, scalar13207, tp13207, tm13207, ep13207, em13207, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13207, agent13207, scalar13207, tp13207, tm13207, ep13207, em13207, dsL]

noncomputable def master13207 : MasterCertificate 13207 world13207 agent13207 :=
  master scalar13207 dsL tp13207 tm13207 ep13207 em13207
    (by norm_num [dsL]) (by norm_num [tp13207]) (by norm_num [tm13207])
    (by norm_num [ep13207]) (by norm_num [em13207])
    positive13207 negative13207 tails13207.1 tails13207.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13207.1 tailGuards13207.2

theorem preserves13207 : master13207.toScalarCertificate = scalar13207 := rfl

noncomputable def tp13208 : ℝ := (235928927 / 1000000000)
noncomputable def tm13208 : ℝ := (-((3078632217 / 5000000000)))
noncomputable def ep13208 : ℝ := (52679150924048699 / 100000000000000000000)
noncomputable def em13208 : ℝ := (5119416648145367 / 10000000000000000000)
noncomputable def bp13208 : ℝ := (41906351570400524719 / 100000000000000000000)
noncomputable def bm13208 : ℝ := (42946471757287113047 / 100000000000000000000)

theorem positive13208 :
    Eplus aL (agent13208.root+dsL) scalar13208.worldRadius world13208.frame
      agent13208.frame tp13208 ≤ -ep13208 := by
  apply positive_check (eT := (115720672459183939891 / 100000000000000000000)) (y := (38182765926445290161 / 100000000000000000000)) (u := (9155997444766242541 / 6250000000000000000))
  · norm_num [world13208, agent13208, scalar13208, tp13208, tm13208, ep13208, em13208, dsL]
  · norm_num [world13208, agent13208, scalar13208, tp13208, tm13208, ep13208, em13208, dsL]
  · norm_num [world13208, agent13208, scalar13208, tp13208, tm13208, ep13208, em13208, dsL]
  · norm_num [world13208, agent13208, scalar13208, tp13208, tm13208, ep13208, em13208, dsL]
  · norm_num [world13208, agent13208, scalar13208, tp13208, tm13208, ep13208, em13208, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13208, agent13208, tp13208, tm13208, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13208, agent13208, scalar13208, tp13208, tm13208, ep13208, em13208, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13208, agent13208, tp13208, tm13208, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13208, agent13208, scalar13208, tp13208, tm13208, ep13208, em13208, dsL]

theorem negative13208 :
    Eminus aL (agent13208.root+dsL) scalar13208.worldRadius world13208.frame
      agent13208.frame tm13208 ≤ -em13208 := by
  apply negative_check (lo := (1707852456302356081 / 2500000000000000000)) (hi := (68314098252094243241 / 100000000000000000000))
    (y := (-((71578852417711414549 / 100000000000000000000)))) (u := (24440326201577149419 / 50000000000000000000))
  · norm_num [world13208, agent13208, scalar13208, tp13208, tm13208, ep13208, em13208, dsL]
  · norm_num [world13208, agent13208, scalar13208, tp13208, tm13208, ep13208, em13208, dsL]
  · norm_num [world13208, agent13208, scalar13208, tp13208, tm13208, ep13208, em13208, dsL]
  · norm_num [world13208, agent13208, scalar13208, tp13208, tm13208, ep13208, em13208, dsL]
  · norm_num [world13208, agent13208, scalar13208, tp13208, tm13208, ep13208, em13208, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13208, agent13208, tp13208, tm13208, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13208, agent13208, tp13208, tm13208, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13208, agent13208, scalar13208, tp13208, tm13208, ep13208, em13208, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13208, agent13208, tp13208, tm13208, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13208, agent13208, scalar13208, tp13208, tm13208, ep13208, em13208, dsL]

theorem tails13208 :
    exp (-((13208:ℝ)*ep13208)) ≤ scalar13208.upperTail ∧
    exp (-((13208:ℝ)*em13208)) ≤ scalar13208.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13208:ℝ)) (by norm_num [ep13208]) ?_)
      (show bp13208^8 ≤ scalar13208.upperTail by norm_num [bp13208, scalar13208])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13208, bp13208, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13208:ℝ)) (by norm_num [em13208]) ?_)
      (show bm13208^8 ≤ scalar13208.lowerTail by norm_num [bm13208, scalar13208])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13208, bm13208, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13208 :
    agent13208.root+dsL+scalar13208.worldRadius < √(1/100/aL) ∧
    2*(agent13208.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13208, agent13208, scalar13208, tp13208, tm13208, ep13208, em13208, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13208, agent13208, scalar13208, tp13208, tm13208, ep13208, em13208, dsL]

noncomputable def master13208 : MasterCertificate 13208 world13208 agent13208 :=
  master scalar13208 dsL tp13208 tm13208 ep13208 em13208
    (by norm_num [dsL]) (by norm_num [tp13208]) (by norm_num [tm13208])
    (by norm_num [ep13208]) (by norm_num [em13208])
    positive13208 negative13208 tails13208.1 tails13208.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13208.1 tailGuards13208.2

theorem preserves13208 : master13208.toScalarCertificate = scalar13208 := rfl

noncomputable def tp13209 : ℝ := (589839721 / 2500000000)
noncomputable def tm13209 : ℝ := (-((3078705703 / 5000000000)))
noncomputable def ep13209 : ℝ := (52681218320393563 / 100000000000000000000)
noncomputable def em13209 : ℝ := (25597955483925893 / 50000000000000000000)
noncomputable def bp13209 : ℝ := (41902161805290709759 / 100000000000000000000)
noncomputable def bm13209 : ℝ := (10735621666493463409 / 25000000000000000000)

theorem positive13209 :
    Eplus aL (agent13209.root+dsL) scalar13209.worldRadius world13209.frame
      agent13209.frame tp13209 ≤ -ep13209 := by
  apply positive_check (eT := (57860410995466947747 / 50000000000000000000)) (y := (19091692365599338979 / 50000000000000000000)) (u := (73248432821511612787 / 50000000000000000000))
  · norm_num [world13209, agent13209, scalar13209, tp13209, tm13209, ep13209, em13209, dsL]
  · norm_num [world13209, agent13209, scalar13209, tp13209, tm13209, ep13209, em13209, dsL]
  · norm_num [world13209, agent13209, scalar13209, tp13209, tm13209, ep13209, em13209, dsL]
  · norm_num [world13209, agent13209, scalar13209, tp13209, tm13209, ep13209, em13209, dsL]
  · norm_num [world13209, agent13209, scalar13209, tp13209, tm13209, ep13209, em13209, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13209, agent13209, tp13209, tm13209, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13209, agent13209, scalar13209, tp13209, tm13209, ep13209, em13209, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13209, agent13209, tp13209, tm13209, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13209, agent13209, scalar13209, tp13209, tm13209, ep13209, em13209, dsL]

theorem negative13209 :
    Eminus aL (agent13209.root+dsL) scalar13209.worldRadius world13209.frame
      agent13209.frame tm13209 ≤ -em13209 := by
  apply negative_check (lo := (34157007300923671117 / 50000000000000000000)) (hi := (13662802920369468447 / 20000000000000000000))
    (y := (-((2863149051492503051 / 4000000000000000000)))) (u := (24440357028277505759 / 50000000000000000000))
  · norm_num [world13209, agent13209, scalar13209, tp13209, tm13209, ep13209, em13209, dsL]
  · norm_num [world13209, agent13209, scalar13209, tp13209, tm13209, ep13209, em13209, dsL]
  · norm_num [world13209, agent13209, scalar13209, tp13209, tm13209, ep13209, em13209, dsL]
  · norm_num [world13209, agent13209, scalar13209, tp13209, tm13209, ep13209, em13209, dsL]
  · norm_num [world13209, agent13209, scalar13209, tp13209, tm13209, ep13209, em13209, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13209, agent13209, tp13209, tm13209, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13209, agent13209, tp13209, tm13209, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13209, agent13209, scalar13209, tp13209, tm13209, ep13209, em13209, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13209, agent13209, tp13209, tm13209, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13209, agent13209, scalar13209, tp13209, tm13209, ep13209, em13209, dsL]

theorem tails13209 :
    exp (-((13209:ℝ)*ep13209)) ≤ scalar13209.upperTail ∧
    exp (-((13209:ℝ)*em13209)) ≤ scalar13209.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13209:ℝ)) (by norm_num [ep13209]) ?_)
      (show bp13209^8 ≤ scalar13209.upperTail by norm_num [bp13209, scalar13209])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13209, bp13209, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13209:ℝ)) (by norm_num [em13209]) ?_)
      (show bm13209^8 ≤ scalar13209.lowerTail by norm_num [bm13209, scalar13209])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13209, bm13209, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13209 :
    agent13209.root+dsL+scalar13209.worldRadius < √(1/100/aL) ∧
    2*(agent13209.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13209, agent13209, scalar13209, tp13209, tm13209, ep13209, em13209, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13209, agent13209, scalar13209, tp13209, tm13209, ep13209, em13209, dsL]

noncomputable def master13209 : MasterCertificate 13209 world13209 agent13209 :=
  master scalar13209 dsL tp13209 tm13209 ep13209 em13209
    (by norm_num [dsL]) (by norm_num [tp13209]) (by norm_num [tm13209])
    (by norm_num [ep13209]) (by norm_num [em13209])
    positive13209 negative13209 tails13209.1 tails13209.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13209.1 tailGuards13209.2

theorem preserves13209 : master13209.toScalarCertificate = scalar13209 := rfl

noncomputable def tp13210 : ℝ := (1179749273 / 5000000000)
noncomputable def tm13210 : ℝ := (-((6157770467 / 10000000000)))
noncomputable def ep13210 : ℝ := (13171150171674641 / 25000000000000000000)
noncomputable def em13210 : ℝ := (12799773180964289 / 25000000000000000000)
noncomputable def bp13210 : ℝ := (20948531251615044519 / 50000000000000000000)
noncomputable def bm13210 : ℝ := (21468741356743788891 / 50000000000000000000)

theorem positive13210 :
    Eplus aL (agent13210.root+dsL) scalar13210.worldRadius world13210.frame
      agent13210.frame tp13210 ≤ -ep13210 := by
  apply positive_check (eT := (115721473192683510177 / 100000000000000000000)) (y := (19091648053760887719 / 50000000000000000000)) (u := (36624183953042969057 / 25000000000000000000))
  · norm_num [world13210, agent13210, scalar13210, tp13210, tm13210, ep13210, em13210, dsL]
  · norm_num [world13210, agent13210, scalar13210, tp13210, tm13210, ep13210, em13210, dsL]
  · norm_num [world13210, agent13210, scalar13210, tp13210, tm13210, ep13210, em13210, dsL]
  · norm_num [world13210, agent13210, scalar13210, tp13210, tm13210, ep13210, em13210, dsL]
  · norm_num [world13210, agent13210, scalar13210, tp13210, tm13210, ep13210, em13210, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13210, agent13210, tp13210, tm13210, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13210, agent13210, scalar13210, tp13210, tm13210, ep13210, em13210, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13210, agent13210, tp13210, tm13210, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13210, agent13210, scalar13210, tp13210, tm13210, ep13210, em13210, dsL]

theorem negative13210 :
    Eminus aL (agent13210.root+dsL) scalar13210.worldRadius world13210.frame
      agent13210.frame tm13210 ≤ -em13210 := by
  apply negative_check (lo := (1366260685627604803 / 2000000000000000000)) (hi := (68313034281380240151 / 100000000000000000000))
    (y := (-((71576754326291072957 / 100000000000000000000)))) (u := (12220419493671813241 / 25000000000000000000))
  · norm_num [world13210, agent13210, scalar13210, tp13210, tm13210, ep13210, em13210, dsL]
  · norm_num [world13210, agent13210, scalar13210, tp13210, tm13210, ep13210, em13210, dsL]
  · norm_num [world13210, agent13210, scalar13210, tp13210, tm13210, ep13210, em13210, dsL]
  · norm_num [world13210, agent13210, scalar13210, tp13210, tm13210, ep13210, em13210, dsL]
  · norm_num [world13210, agent13210, scalar13210, tp13210, tm13210, ep13210, em13210, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13210, agent13210, tp13210, tm13210, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13210, agent13210, tp13210, tm13210, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13210, agent13210, scalar13210, tp13210, tm13210, ep13210, em13210, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13210, agent13210, tp13210, tm13210, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13210, agent13210, scalar13210, tp13210, tm13210, ep13210, em13210, dsL]

theorem tails13210 :
    exp (-((13210:ℝ)*ep13210)) ≤ scalar13210.upperTail ∧
    exp (-((13210:ℝ)*em13210)) ≤ scalar13210.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13210:ℝ)) (by norm_num [ep13210]) ?_)
      (show bp13210^8 ≤ scalar13210.upperTail by norm_num [bp13210, scalar13210])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13210, bp13210, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13210:ℝ)) (by norm_num [em13210]) ?_)
      (show bm13210^8 ≤ scalar13210.lowerTail by norm_num [bm13210, scalar13210])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13210, bm13210, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13210 :
    agent13210.root+dsL+scalar13210.worldRadius < √(1/100/aL) ∧
    2*(agent13210.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13210, agent13210, scalar13210, tp13210, tm13210, ep13210, em13210, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13210, agent13210, scalar13210, tp13210, tm13210, ep13210, em13210, dsL]

noncomputable def master13210 : MasterCertificate 13210 world13210 agent13210 :=
  master scalar13210 dsL tp13210 tm13210 ep13210 em13210
    (by norm_num [dsL]) (by norm_num [tp13210]) (by norm_num [tm13210])
    (by norm_num [ep13210]) (by norm_num [em13210])
    positive13210 negative13210 tails13210.1 tails13210.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13210.1 tailGuards13210.2

theorem preserves13210 : master13210.toScalarCertificate = scalar13210 := rfl

noncomputable def tp13211 : ℝ := (589892009 / 2500000000)
noncomputable def tm13211 : ℝ := (-((3078958621 / 5000000000)))
noncomputable def ep13211 : ℝ := (52686666699547921 / 100000000000000000000)
noncomputable def em13211 : ℝ := (12800208985300597 / 25000000000000000000)
noncomputable def bp13211 : ℝ := (41892874122042301173 / 100000000000000000000)
noncomputable def bm13211 : ℝ := (1717339956176702293 / 4000000000000000000)

theorem positive13211 :
    Eplus aL (agent13211.root+dsL) scalar13211.worldRadius world13211.frame
      agent13211.frame tp13211 ≤ -ep13211 := by
  apply positive_check (eT := (57860810946358445927 / 50000000000000000000)) (y := (38183913146166594351 / 100000000000000000000)) (u := (146497639756434075441 / 100000000000000000000))
  · norm_num [world13211, agent13211, scalar13211, tp13211, tm13211, ep13211, em13211, dsL]
  · norm_num [world13211, agent13211, scalar13211, tp13211, tm13211, ep13211, em13211, dsL]
  · norm_num [world13211, agent13211, scalar13211, tp13211, tm13211, ep13211, em13211, dsL]
  · norm_num [world13211, agent13211, scalar13211, tp13211, tm13211, ep13211, em13211, dsL]
  · norm_num [world13211, agent13211, scalar13211, tp13211, tm13211, ep13211, em13211, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13211, agent13211, tp13211, tm13211, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13211, agent13211, scalar13211, tp13211, tm13211, ep13211, em13211, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13211, agent13211, tp13211, tm13211, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13211, agent13211, scalar13211, tp13211, tm13211, ep13211, em13211, dsL]

theorem negative13211 :
    Eminus aL (agent13211.root+dsL) scalar13211.worldRadius world13211.frame
      agent13211.frame tm13211 ≤ -em13211 := by
  apply negative_check (lo := (8539118921321419369 / 12500000000000000000)) (hi := (68312951370571354953 / 100000000000000000000))
    (y := (-((71576627235829745629 / 100000000000000000000)))) (u := (48881740098676772357 / 100000000000000000000))
  · norm_num [world13211, agent13211, scalar13211, tp13211, tm13211, ep13211, em13211, dsL]
  · norm_num [world13211, agent13211, scalar13211, tp13211, tm13211, ep13211, em13211, dsL]
  · norm_num [world13211, agent13211, scalar13211, tp13211, tm13211, ep13211, em13211, dsL]
  · norm_num [world13211, agent13211, scalar13211, tp13211, tm13211, ep13211, em13211, dsL]
  · norm_num [world13211, agent13211, scalar13211, tp13211, tm13211, ep13211, em13211, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13211, agent13211, tp13211, tm13211, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13211, agent13211, tp13211, tm13211, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13211, agent13211, scalar13211, tp13211, tm13211, ep13211, em13211, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13211, agent13211, tp13211, tm13211, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13211, agent13211, scalar13211, tp13211, tm13211, ep13211, em13211, dsL]

theorem tails13211 :
    exp (-((13211:ℝ)*ep13211)) ≤ scalar13211.upperTail ∧
    exp (-((13211:ℝ)*em13211)) ≤ scalar13211.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13211:ℝ)) (by norm_num [ep13211]) ?_)
      (show bp13211^8 ≤ scalar13211.upperTail by norm_num [bp13211, scalar13211])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13211, bp13211, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13211:ℝ)) (by norm_num [em13211]) ?_)
      (show bm13211^8 ≤ scalar13211.lowerTail by norm_num [bm13211, scalar13211])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13211, bm13211, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13211 :
    agent13211.root+dsL+scalar13211.worldRadius < √(1/100/aL) ∧
    2*(agent13211.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13211, agent13211, scalar13211, tp13211, tm13211, ep13211, em13211, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13211, agent13211, scalar13211, tp13211, tm13211, ep13211, em13211, dsL]

noncomputable def master13211 : MasterCertificate 13211 world13211 agent13211 :=
  master scalar13211 dsL tp13211 tm13211 ep13211 em13211
    (by norm_num [dsL]) (by norm_num [tp13211]) (by norm_num [tm13211])
    (by norm_num [ep13211]) (by norm_num [em13211])
    positive13211 negative13211 tails13211.1 tails13211.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13211.1 tailGuards13211.2

theorem preserves13211 : master13211.toScalarCertificate = scalar13211 := rfl

noncomputable def tp13212 : ℝ := (1179818809 / 5000000000)
noncomputable def tm13212 : ℝ := (-((30790321 / 50000000)))
noncomputable def ep13212 : ℝ := (13172183091710571 / 25000000000000000000)
noncomputable def em13212 : ℝ := (800040293837337 / 1562500000000000000)
noncomputable def bp13212 : ℝ := (2618042886390988641 / 6250000000000000000)
noncomputable def bm13212 : ℝ := (21464757764061814007 / 50000000000000000000)

theorem positive13212 :
    Eplus aL (agent13212.root+dsL) scalar13212.worldRadius world13212.frame
      agent13212.frame tp13212 ≤ -ep13212 := by
  apply positive_check (eT := (115721771284590378963 / 100000000000000000000)) (y := (19092266069977870637 / 50000000000000000000)) (u := (73249273285265986589 / 50000000000000000000))
  · norm_num [world13212, agent13212, scalar13212, tp13212, tm13212, ep13212, em13212, dsL]
  · norm_num [world13212, agent13212, scalar13212, tp13212, tm13212, ep13212, em13212, dsL]
  · norm_num [world13212, agent13212, scalar13212, tp13212, tm13212, ep13212, em13212, dsL]
  · norm_num [world13212, agent13212, scalar13212, tp13212, tm13212, ep13212, em13212, dsL]
  · norm_num [world13212, agent13212, scalar13212, tp13212, tm13212, ep13212, em13212, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13212, agent13212, tp13212, tm13212, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13212, agent13212, scalar13212, tp13212, tm13212, ep13212, em13212, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13212, agent13212, tp13212, tm13212, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13212, agent13212, scalar13212, tp13212, tm13212, ep13212, em13212, dsL]

theorem negative13212 :
    Eminus aL (agent13212.root+dsL) scalar13212.worldRadius world13212.frame
      agent13212.frame tm13212 ≤ -em13212 := by
  apply negative_check (lo := (68312867629647731149 / 100000000000000000000)) (hi := (1366257352592954623 / 2000000000000000000))
    (y := (-((17894125685907523549 / 25000000000000000000)))) (u := (1955272038106725133 / 4000000000000000000))
  · norm_num [world13212, agent13212, scalar13212, tp13212, tm13212, ep13212, em13212, dsL]
  · norm_num [world13212, agent13212, scalar13212, tp13212, tm13212, ep13212, em13212, dsL]
  · norm_num [world13212, agent13212, scalar13212, tp13212, tm13212, ep13212, em13212, dsL]
  · norm_num [world13212, agent13212, scalar13212, tp13212, tm13212, ep13212, em13212, dsL]
  · norm_num [world13212, agent13212, scalar13212, tp13212, tm13212, ep13212, em13212, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13212, agent13212, tp13212, tm13212, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13212, agent13212, tp13212, tm13212, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13212, agent13212, scalar13212, tp13212, tm13212, ep13212, em13212, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13212, agent13212, tp13212, tm13212, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13212, agent13212, scalar13212, tp13212, tm13212, ep13212, em13212, dsL]

theorem tails13212 :
    exp (-((13212:ℝ)*ep13212)) ≤ scalar13212.upperTail ∧
    exp (-((13212:ℝ)*em13212)) ≤ scalar13212.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13212:ℝ)) (by norm_num [ep13212]) ?_)
      (show bp13212^8 ≤ scalar13212.upperTail by norm_num [bp13212, scalar13212])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13212, bp13212, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13212:ℝ)) (by norm_num [em13212]) ?_)
      (show bm13212^8 ≤ scalar13212.lowerTail by norm_num [bm13212, scalar13212])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13212, bm13212, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13212 :
    agent13212.root+dsL+scalar13212.worldRadius < √(1/100/aL) ∧
    2*(agent13212.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13212, agent13212, scalar13212, tp13212, tm13212, ep13212, em13212, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13212, agent13212, scalar13212, tp13212, tm13212, ep13212, em13212, dsL]

noncomputable def master13212 : MasterCertificate 13212 world13212 agent13212 :=
  master scalar13212 dsL tp13212 tm13212 ep13212 em13212
    (by norm_num [dsL]) (by norm_num [tp13212]) (by norm_num [tm13212])
    (by norm_num [ep13212]) (by norm_num [em13212])
    positive13212 negative13212 tails13212.1 tails13212.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13212.1 tailGuards13212.2

theorem preserves13212 : master13212.toScalarCertificate = scalar13212 := rfl

noncomputable def tp13213 : ℝ := (1179853561 / 5000000000)
noncomputable def tm13213 : ℝ := (-((6158210771 / 10000000000)))
noncomputable def ep13213 : ℝ := (26345397908634633 / 50000000000000000000)
noncomputable def em13213 : ℝ := (3200269977651689 / 6250000000000000000)
noncomputable def bp13213 : ℝ := (41884499978403120121 / 100000000000000000000)
noncomputable def bm13213 : ℝ := (21462766885922022233 / 50000000000000000000)

theorem positive13213 :
    Eplus aL (agent13213.root+dsL) scalar13213.worldRadius world13213.frame
      agent13213.frame tp13213 ≤ -ep13213 := by
  apply positive_check (eT := (57860960075442423963 / 50000000000000000000)) (y := (38185150126174750737 / 100000000000000000000)) (u := (9156215744634892173 / 6250000000000000000))
  · norm_num [world13213, agent13213, scalar13213, tp13213, tm13213, ep13213, em13213, dsL]
  · norm_num [world13213, agent13213, scalar13213, tp13213, tm13213, ep13213, em13213, dsL]
  · norm_num [world13213, agent13213, scalar13213, tp13213, tm13213, ep13213, em13213, dsL]
  · norm_num [world13213, agent13213, scalar13213, tp13213, tm13213, ep13213, em13213, dsL]
  · norm_num [world13213, agent13213, scalar13213, tp13213, tm13213, ep13213, em13213, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13213, agent13213, tp13213, tm13213, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13213, agent13213, scalar13213, tp13213, tm13213, ep13213, em13213, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13213, agent13213, tp13213, tm13213, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13213, agent13213, scalar13213, tp13213, tm13213, ep13213, em13213, dsL]

theorem negative13213 :
    Eminus aL (agent13213.root+dsL) scalar13213.worldRadius world13213.frame
      agent13213.frame tm13213 ≤ -em13213 := by
  apply negative_check (lo := (68312785468217695857 / 100000000000000000000)) (hi := (34156392734108847929 / 50000000000000000000))
    (y := (-((14315274946367510031 / 20000000000000000000)))) (u := (12220465881794451753 / 25000000000000000000))
  · norm_num [world13213, agent13213, scalar13213, tp13213, tm13213, ep13213, em13213, dsL]
  · norm_num [world13213, agent13213, scalar13213, tp13213, tm13213, ep13213, em13213, dsL]
  · norm_num [world13213, agent13213, scalar13213, tp13213, tm13213, ep13213, em13213, dsL]
  · norm_num [world13213, agent13213, scalar13213, tp13213, tm13213, ep13213, em13213, dsL]
  · norm_num [world13213, agent13213, scalar13213, tp13213, tm13213, ep13213, em13213, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13213, agent13213, tp13213, tm13213, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13213, agent13213, tp13213, tm13213, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13213, agent13213, scalar13213, tp13213, tm13213, ep13213, em13213, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13213, agent13213, tp13213, tm13213, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13213, agent13213, scalar13213, tp13213, tm13213, ep13213, em13213, dsL]

theorem tails13213 :
    exp (-((13213:ℝ)*ep13213)) ≤ scalar13213.upperTail ∧
    exp (-((13213:ℝ)*em13213)) ≤ scalar13213.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13213:ℝ)) (by norm_num [ep13213]) ?_)
      (show bp13213^8 ≤ scalar13213.upperTail by norm_num [bp13213, scalar13213])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13213, bp13213, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13213:ℝ)) (by norm_num [em13213]) ?_)
      (show bm13213^8 ≤ scalar13213.lowerTail by norm_num [bm13213, scalar13213])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13213, bm13213, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13213 :
    agent13213.root+dsL+scalar13213.worldRadius < √(1/100/aL) ∧
    2*(agent13213.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13213, agent13213, scalar13213, tp13213, tm13213, ep13213, em13213, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13213, agent13213, scalar13213, tp13213, tm13213, ep13213, em13213, dsL]

noncomputable def master13213 : MasterCertificate 13213 world13213 agent13213 :=
  master scalar13213 dsL tp13213 tm13213 ep13213 em13213
    (by norm_num [dsL]) (by norm_num [tp13213]) (by norm_num [tm13213])
    (by norm_num [ep13213]) (by norm_num [em13213])
    positive13213 negative13213 tails13213.1 tails13213.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13213.1 tailGuards13213.2

theorem preserves13213 : master13213.toScalarCertificate = scalar13213 := rfl

noncomputable def tp13214 : ℝ := (2359776577 / 10000000000)
noncomputable def tm13214 : ℝ := (-((615835741 / 1000000000)))
noncomputable def ep13214 : ℝ := (26346429388630549 / 50000000000000000000)
noncomputable def em13214 : ℝ := (10241212006171449 / 20000000000000000000)
noncomputable def bp13214 : ℝ := (41880314316122102373 / 100000000000000000000)
noncomputable def bm13214 : ℝ := (42921552515979194017 / 100000000000000000000)

theorem positive13214 :
    Eplus aL (agent13214.root+dsL) scalar13214.worldRadius world13214.frame
      agent13214.frame tp13214 ≤ -ep13214 := by
  apply positive_check (eT := (57861034349663944119 / 50000000000000000000)) (y := (38185767461690155401 / 100000000000000000000)) (u := (29300071262019277967 / 20000000000000000000))
  · norm_num [world13214, agent13214, scalar13214, tp13214, tm13214, ep13214, em13214, dsL]
  · norm_num [world13214, agent13214, scalar13214, tp13214, tm13214, ep13214, em13214, dsL]
  · norm_num [world13214, agent13214, scalar13214, tp13214, tm13214, ep13214, em13214, dsL]
  · norm_num [world13214, agent13214, scalar13214, tp13214, tm13214, ep13214, em13214, dsL]
  · norm_num [world13214, agent13214, scalar13214, tp13214, tm13214, ep13214, em13214, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13214, agent13214, tp13214, tm13214, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13214, agent13214, scalar13214, tp13214, tm13214, ep13214, em13214, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13214, agent13214, tp13214, tm13214, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13214, agent13214, scalar13214, tp13214, tm13214, ep13214, em13214, dsL]

theorem negative13214 :
    Eminus aL (agent13214.root+dsL) scalar13214.worldRadius world13214.frame
      agent13214.frame tm13214 ≤ -em13214 := by
  apply negative_check (lo := (4269543935173659019 / 6250000000000000000)) (hi := (13662540592555708861 / 20000000000000000000))
    (y := (-((7157624793106178221 / 10000000000000000000)))) (u := (12220481377449816629 / 25000000000000000000))
  · norm_num [world13214, agent13214, scalar13214, tp13214, tm13214, ep13214, em13214, dsL]
  · norm_num [world13214, agent13214, scalar13214, tp13214, tm13214, ep13214, em13214, dsL]
  · norm_num [world13214, agent13214, scalar13214, tp13214, tm13214, ep13214, em13214, dsL]
  · norm_num [world13214, agent13214, scalar13214, tp13214, tm13214, ep13214, em13214, dsL]
  · norm_num [world13214, agent13214, scalar13214, tp13214, tm13214, ep13214, em13214, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13214, agent13214, tp13214, tm13214, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13214, agent13214, tp13214, tm13214, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13214, agent13214, scalar13214, tp13214, tm13214, ep13214, em13214, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13214, agent13214, tp13214, tm13214, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13214, agent13214, scalar13214, tp13214, tm13214, ep13214, em13214, dsL]

theorem tails13214 :
    exp (-((13214:ℝ)*ep13214)) ≤ scalar13214.upperTail ∧
    exp (-((13214:ℝ)*em13214)) ≤ scalar13214.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13214:ℝ)) (by norm_num [ep13214]) ?_)
      (show bp13214^8 ≤ scalar13214.upperTail by norm_num [bp13214, scalar13214])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13214, bp13214, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13214:ℝ)) (by norm_num [em13214]) ?_)
      (show bm13214^8 ≤ scalar13214.lowerTail by norm_num [bm13214, scalar13214])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13214, bm13214, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13214 :
    agent13214.root+dsL+scalar13214.worldRadius < √(1/100/aL) ∧
    2*(agent13214.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13214, agent13214, scalar13214, tp13214, tm13214, ep13214, em13214, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13214, agent13214, scalar13214, tp13214, tm13214, ep13214, em13214, dsL]

noncomputable def master13214 : MasterCertificate 13214 world13214 agent13214 :=
  master scalar13214 dsL tp13214 tm13214 ep13214 em13214
    (by norm_num [dsL]) (by norm_num [tp13214]) (by norm_num [tm13214])
    (by norm_num [ep13214]) (by norm_num [em13214])
    positive13214 negative13214 tails13214.1 tails13214.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13214.1 tailGuards13214.2

theorem preserves13214 : master13214.toScalarCertificate = scalar13214 := rfl

noncomputable def tp13215 : ℝ := (1179923013 / 5000000000)
noncomputable def tm13215 : ℝ := (-((6158503833 / 10000000000)))
noncomputable def ep13215 : ℝ := (52694920916038457 / 100000000000000000000)
noncomputable def em13215 : ℝ := (51207799624967547 / 100000000000000000000)
noncomputable def bp13215 : ℝ := (41876129424224753817 / 100000000000000000000)
noncomputable def bm13215 : ℝ := (42917572005763454539 / 100000000000000000000)

theorem positive13215 :
    Eplus aL (agent13215.root+dsL) scalar13215.worldRadius world13215.frame
      agent13215.frame tp13215 ≤ -ep13215 := by
  apply positive_check (eT := (7232638577360683601 / 6250000000000000000)) (y := (19093192548521053569 / 50000000000000000000)) (u := (146501261150882001657 / 100000000000000000000))
  · norm_num [world13215, agent13215, scalar13215, tp13215, tm13215, ep13215, em13215, dsL]
  · norm_num [world13215, agent13215, scalar13215, tp13215, tm13215, ep13215, em13215, dsL]
  · norm_num [world13215, agent13215, scalar13215, tp13215, tm13215, ep13215, em13215, dsL]
  · norm_num [world13215, agent13215, scalar13215, tp13215, tm13215, ep13215, em13215, dsL]
  · norm_num [world13215, agent13215, scalar13215, tp13215, tm13215, ep13215, em13215, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13215, agent13215, tp13215, tm13215, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13215, agent13215, scalar13215, tp13215, tm13215, ep13215, em13215, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13215, agent13215, tp13215, tm13215, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13215, agent13215, scalar13215, tp13215, tm13215, ep13215, em13215, dsL]

theorem negative13215 :
    Eminus aL (agent13215.root+dsL) scalar13215.worldRadius world13215.frame
      agent13215.frame tm13215 ≤ -em13215 := by
  apply negative_check (lo := (34156310656975291633 / 50000000000000000000)) (hi := (68312621313950583267 / 100000000000000000000))
    (y := (-((71576119790510596619 / 100000000000000000000)))) (u := (48881988147408176983 / 100000000000000000000))
  · norm_num [world13215, agent13215, scalar13215, tp13215, tm13215, ep13215, em13215, dsL]
  · norm_num [world13215, agent13215, scalar13215, tp13215, tm13215, ep13215, em13215, dsL]
  · norm_num [world13215, agent13215, scalar13215, tp13215, tm13215, ep13215, em13215, dsL]
  · norm_num [world13215, agent13215, scalar13215, tp13215, tm13215, ep13215, em13215, dsL]
  · norm_num [world13215, agent13215, scalar13215, tp13215, tm13215, ep13215, em13215, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13215, agent13215, tp13215, tm13215, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13215, agent13215, tp13215, tm13215, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13215, agent13215, scalar13215, tp13215, tm13215, ep13215, em13215, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13215, agent13215, tp13215, tm13215, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13215, agent13215, scalar13215, tp13215, tm13215, ep13215, em13215, dsL]

theorem tails13215 :
    exp (-((13215:ℝ)*ep13215)) ≤ scalar13215.upperTail ∧
    exp (-((13215:ℝ)*em13215)) ≤ scalar13215.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13215:ℝ)) (by norm_num [ep13215]) ?_)
      (show bp13215^8 ≤ scalar13215.upperTail by norm_num [bp13215, scalar13215])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13215, bp13215, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13215:ℝ)) (by norm_num [em13215]) ?_)
      (show bm13215^8 ≤ scalar13215.lowerTail by norm_num [bm13215, scalar13215])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13215, bm13215, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13215 :
    agent13215.root+dsL+scalar13215.worldRadius < √(1/100/aL) ∧
    2*(agent13215.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13215, agent13215, scalar13215, tp13215, tm13215, ep13215, em13215, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13215, agent13215, scalar13215, tp13215, tm13215, ep13215, em13215, dsL]

noncomputable def master13215 : MasterCertificate 13215 world13215 agent13215 :=
  master scalar13215 dsL tp13215 tm13215 ep13215 em13215
    (by norm_num [dsL]) (by norm_num [tp13215]) (by norm_num [tm13215])
    (by norm_num [ep13215]) (by norm_num [em13215])
    positive13215 negative13215 tails13215.1 tails13215.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13215.1 tailGuards13215.2

theorem preserves13215 : master13215.toScalarCertificate = scalar13215 := rfl

noncomputable def tp13216 : ℝ := (589978861 / 2500000000)
noncomputable def tm13216 : ℝ := (-((1539662583 / 2500000000)))
noncomputable def ep13216 : ℝ := (26348490827169279 / 50000000000000000000)
noncomputable def em13216 : ℝ := (25604768965944433 / 50000000000000000000)
noncomputable def bp13216 : ℝ := (20935972851691477079 / 50000000000000000000)
noncomputable def bm13216 : ℝ := (42913592590596606061 / 100000000000000000000)

theorem positive13216 :
    Eplus aL (agent13216.root+dsL) scalar13216.worldRadius world13216.frame
      agent13216.frame tp13216 ≤ -ep13216 := by
  apply positive_check (eT := (115722365587235734189 / 100000000000000000000)) (y := (19093501297711373921 / 50000000000000000000)) (u := (146502165796590309987 / 100000000000000000000))
  · norm_num [world13216, agent13216, scalar13216, tp13216, tm13216, ep13216, em13216, dsL]
  · norm_num [world13216, agent13216, scalar13216, tp13216, tm13216, ep13216, em13216, dsL]
  · norm_num [world13216, agent13216, scalar13216, tp13216, tm13216, ep13216, em13216, dsL]
  · norm_num [world13216, agent13216, scalar13216, tp13216, tm13216, ep13216, em13216, dsL]
  · norm_num [world13216, agent13216, scalar13216, tp13216, tm13216, ep13216, em13216, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13216, agent13216, tp13216, tm13216, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13216, agent13216, scalar13216, tp13216, tm13216, ep13216, em13216, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13216, agent13216, tp13216, tm13216, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13216, agent13216, scalar13216, tp13216, tm13216, ep13216, em13216, dsL]

theorem negative13216 :
    Eminus aL (agent13216.root+dsL) scalar13216.worldRadius world13216.frame
      agent13216.frame tm13216 ≤ -em13216 := by
  apply negative_check (lo := (34156269643677961063 / 50000000000000000000)) (hi := (68312539287355922127 / 100000000000000000000))
    (y := (-((7157599309174005439 / 10000000000000000000)))) (u := (48882050080325410461 / 100000000000000000000))
  · norm_num [world13216, agent13216, scalar13216, tp13216, tm13216, ep13216, em13216, dsL]
  · norm_num [world13216, agent13216, scalar13216, tp13216, tm13216, ep13216, em13216, dsL]
  · norm_num [world13216, agent13216, scalar13216, tp13216, tm13216, ep13216, em13216, dsL]
  · norm_num [world13216, agent13216, scalar13216, tp13216, tm13216, ep13216, em13216, dsL]
  · norm_num [world13216, agent13216, scalar13216, tp13216, tm13216, ep13216, em13216, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13216, agent13216, tp13216, tm13216, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13216, agent13216, tp13216, tm13216, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13216, agent13216, scalar13216, tp13216, tm13216, ep13216, em13216, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13216, agent13216, tp13216, tm13216, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13216, agent13216, scalar13216, tp13216, tm13216, ep13216, em13216, dsL]

theorem tails13216 :
    exp (-((13216:ℝ)*ep13216)) ≤ scalar13216.upperTail ∧
    exp (-((13216:ℝ)*em13216)) ≤ scalar13216.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13216:ℝ)) (by norm_num [ep13216]) ?_)
      (show bp13216^8 ≤ scalar13216.upperTail by norm_num [bp13216, scalar13216])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13216, bp13216, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13216:ℝ)) (by norm_num [em13216]) ?_)
      (show bm13216^8 ≤ scalar13216.lowerTail by norm_num [bm13216, scalar13216])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13216, bm13216, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13216 :
    agent13216.root+dsL+scalar13216.worldRadius < √(1/100/aL) ∧
    2*(agent13216.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13216, agent13216, scalar13216, tp13216, tm13216, ep13216, em13216, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13216, agent13216, scalar13216, tp13216, tm13216, ep13216, em13216, dsL]

noncomputable def master13216 : MasterCertificate 13216 world13216 agent13216 :=
  master scalar13216 dsL tp13216 tm13216 ep13216 em13216
    (by norm_num [dsL]) (by norm_num [tp13216]) (by norm_num [tm13216])
    (by norm_num [ep13216]) (by norm_num [em13216])
    positive13216 negative13216 tails13216.1 tails13216.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13216.1 tailGuards13216.2

theorem preserves13216 : master13216.toScalarCertificate = scalar13216 := rfl

noncomputable def tp13217 : ℝ := (294998099 / 1250000000)
noncomputable def tm13217 : ℝ := (-((3079398343 / 5000000000)))
noncomputable def ep13217 : ℝ := (2107961655019817 / 4000000000000000000)
noncomputable def em13217 : ℝ := (51211275296675211 / 100000000000000000000)
noncomputable def bp13217 : ℝ := (261673518052462607 / 625000000000000000)
noncomputable def bm13217 : ℝ := (42909614025833767983 / 100000000000000000000)

theorem positive13217 :
    Eplus aL (agent13217.root+dsL) scalar13217.worldRadius world13217.frame
      agent13217.frame tp13217 ≤ -ep13217 := by
  apply positive_check (eT := (23144502693697056587 / 20000000000000000000)) (y := (3818761902517779803 / 10000000000000000000)) (u := (146503068882315514831 / 100000000000000000000))
  · norm_num [world13217, agent13217, scalar13217, tp13217, tm13217, ep13217, em13217, dsL]
  · norm_num [world13217, agent13217, scalar13217, tp13217, tm13217, ep13217, em13217, dsL]
  · norm_num [world13217, agent13217, scalar13217, tp13217, tm13217, ep13217, em13217, dsL]
  · norm_num [world13217, agent13217, scalar13217, tp13217, tm13217, ep13217, em13217, dsL]
  · norm_num [world13217, agent13217, scalar13217, tp13217, tm13217, ep13217, em13217, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13217, agent13217, tp13217, tm13217, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13217, agent13217, scalar13217, tp13217, tm13217, ep13217, em13217, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13217, agent13217, tp13217, tm13217, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13217, agent13217, scalar13217, tp13217, tm13217, ep13217, em13217, dsL]

theorem negative13217 :
    Eminus aL (agent13217.root+dsL) scalar13217.worldRadius world13217.frame
      agent13217.frame tm13217 ≤ -em13217 := by
  apply negative_check (lo := (13662491563429243271 / 20000000000000000000)) (hi := (17078114454286554089 / 25000000000000000000))
    (y := (-((71575865031988888737 / 100000000000000000000)))) (u := (48882112678597189583 / 100000000000000000000))
  · norm_num [world13217, agent13217, scalar13217, tp13217, tm13217, ep13217, em13217, dsL]
  · norm_num [world13217, agent13217, scalar13217, tp13217, tm13217, ep13217, em13217, dsL]
  · norm_num [world13217, agent13217, scalar13217, tp13217, tm13217, ep13217, em13217, dsL]
  · norm_num [world13217, agent13217, scalar13217, tp13217, tm13217, ep13217, em13217, dsL]
  · norm_num [world13217, agent13217, scalar13217, tp13217, tm13217, ep13217, em13217, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13217, agent13217, tp13217, tm13217, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13217, agent13217, tp13217, tm13217, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13217, agent13217, scalar13217, tp13217, tm13217, ep13217, em13217, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13217, agent13217, tp13217, tm13217, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13217, agent13217, scalar13217, tp13217, tm13217, ep13217, em13217, dsL]

theorem tails13217 :
    exp (-((13217:ℝ)*ep13217)) ≤ scalar13217.upperTail ∧
    exp (-((13217:ℝ)*em13217)) ≤ scalar13217.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13217:ℝ)) (by norm_num [ep13217]) ?_)
      (show bp13217^8 ≤ scalar13217.upperTail by norm_num [bp13217, scalar13217])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13217, bp13217, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13217:ℝ)) (by norm_num [em13217]) ?_)
      (show bm13217^8 ≤ scalar13217.lowerTail by norm_num [bm13217, scalar13217])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13217, bm13217, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13217 :
    agent13217.root+dsL+scalar13217.worldRadius < √(1/100/aL) ∧
    2*(agent13217.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13217, agent13217, scalar13217, tp13217, tm13217, ep13217, em13217, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13217, agent13217, scalar13217, tp13217, tm13217, ep13217, em13217, dsL]

noncomputable def master13217 : MasterCertificate 13217 world13217 agent13217 :=
  master scalar13217 dsL tp13217 tm13217 ep13217 em13217
    (by norm_num [dsL]) (by norm_num [tp13217]) (by norm_num [tm13217])
    (by norm_num [ep13217]) (by norm_num [em13217])
    positive13217 negative13217 tails13217.1 tails13217.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13217.1 tailGuards13217.2

theorem preserves13217 : master13217.toScalarCertificate = scalar13217 := rfl

noncomputable def tp13218 : ℝ := (2360054173 / 10000000000)
noncomputable def tm13218 : ℝ := (-((6158942997 / 10000000000)))
noncomputable def ep13218 : ℝ := (52701100181535413 / 100000000000000000000)
noncomputable def em13218 : ℝ := (6401626478002449 / 12500000000000000000)
noncomputable def bp13218 : ℝ := (41863580908658941981 / 100000000000000000000)
noncomputable def bm13218 : ℝ := (1716225449489626479 / 4000000000000000000)

theorem positive13218 :
    Eplus aL (agent13218.root+dsL) scalar13218.worldRadius world13218.frame
      agent13218.frame tp13218 ≤ -ep13218 := by
  apply positive_check (eT := (115722661619003489049 / 100000000000000000000)) (y := (38188236381419859761 / 100000000000000000000)) (u := (5860158933237916159 / 4000000000000000000))
  · norm_num [world13218, agent13218, scalar13218, tp13218, tm13218, ep13218, em13218, dsL]
  · norm_num [world13218, agent13218, scalar13218, tp13218, tm13218, ep13218, em13218, dsL]
  · norm_num [world13218, agent13218, scalar13218, tp13218, tm13218, ep13218, em13218, dsL]
  · norm_num [world13218, agent13218, scalar13218, tp13218, tm13218, ep13218, em13218, dsL]
  · norm_num [world13218, agent13218, scalar13218, tp13218, tm13218, ep13218, em13218, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13218, agent13218, tp13218, tm13218, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13218, agent13218, scalar13218, tp13218, tm13218, ep13218, em13218, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13218, agent13218, tp13218, tm13218, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13218, agent13218, scalar13218, tp13218, tm13218, ep13218, em13218, dsL]

theorem negative13218 :
    Eminus aL (agent13218.root+dsL) scalar13218.worldRadius world13218.frame
      agent13218.frame tm13218 ≤ -em13218 := by
  apply negative_check (lo := (68312376472229411753 / 100000000000000000000)) (hi := (34156188236114705877 / 50000000000000000000))
    (y := (-((71575737405208065951 / 100000000000000000000)))) (u := (12220543766325952627 / 25000000000000000000))
  · norm_num [world13218, agent13218, scalar13218, tp13218, tm13218, ep13218, em13218, dsL]
  · norm_num [world13218, agent13218, scalar13218, tp13218, tm13218, ep13218, em13218, dsL]
  · norm_num [world13218, agent13218, scalar13218, tp13218, tm13218, ep13218, em13218, dsL]
  · norm_num [world13218, agent13218, scalar13218, tp13218, tm13218, ep13218, em13218, dsL]
  · norm_num [world13218, agent13218, scalar13218, tp13218, tm13218, ep13218, em13218, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13218, agent13218, tp13218, tm13218, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13218, agent13218, tp13218, tm13218, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13218, agent13218, scalar13218, tp13218, tm13218, ep13218, em13218, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13218, agent13218, tp13218, tm13218, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13218, agent13218, scalar13218, tp13218, tm13218, ep13218, em13218, dsL]

theorem tails13218 :
    exp (-((13218:ℝ)*ep13218)) ≤ scalar13218.upperTail ∧
    exp (-((13218:ℝ)*em13218)) ≤ scalar13218.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13218:ℝ)) (by norm_num [ep13218]) ?_)
      (show bp13218^8 ≤ scalar13218.upperTail by norm_num [bp13218, scalar13218])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13218, bp13218, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13218:ℝ)) (by norm_num [em13218]) ?_)
      (show bm13218^8 ≤ scalar13218.lowerTail by norm_num [bm13218, scalar13218])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13218, bm13218, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13218 :
    agent13218.root+dsL+scalar13218.worldRadius < √(1/100/aL) ∧
    2*(agent13218.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13218, agent13218, scalar13218, tp13218, tm13218, ep13218, em13218, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13218, agent13218, scalar13218, tp13218, tm13218, ep13218, em13218, dsL]

noncomputable def master13218 : MasterCertificate 13218 world13218 agent13218 :=
  master scalar13218 dsL tp13218 tm13218 ep13218 em13218
    (by norm_num [dsL]) (by norm_num [tp13218]) (by norm_num [tm13218])
    (by norm_num [ep13218]) (by norm_num [em13218])
    positive13218 negative13218 tails13218.1 tails13218.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13218.1 tailGuards13218.2

theorem preserves13218 : master13218.toScalarCertificate = scalar13218 := rfl

noncomputable def tp13219 : ℝ := (29501543 / 125000000)
noncomputable def tm13219 : ℝ := (-((769886147 / 1250000000)))
noncomputable def ep13219 : ℝ := (26351578840509187 / 50000000000000000000)
noncomputable def em13219 : ℝ := (51214747107447353 / 100000000000000000000)
noncomputable def bp13219 : ℝ := (8371880006980726261 / 20000000000000000000)
noncomputable def bm13219 : ℝ := (10725414878238230311 / 25000000000000000000)

theorem positive13219 :
    Eplus aL (agent13219.root+dsL) scalar13219.worldRadius world13219.frame
      agent13219.frame tp13219 ≤ -ep13219 := by
  apply positive_check (eT := (115722808986274036991 / 100000000000000000000)) (y := (38188852208352069601 / 100000000000000000000)) (u := (73252437772325234053 / 50000000000000000000))
  · norm_num [world13219, agent13219, scalar13219, tp13219, tm13219, ep13219, em13219, dsL]
  · norm_num [world13219, agent13219, scalar13219, tp13219, tm13219, ep13219, em13219, dsL]
  · norm_num [world13219, agent13219, scalar13219, tp13219, tm13219, ep13219, em13219, dsL]
  · norm_num [world13219, agent13219, scalar13219, tp13219, tm13219, ep13219, em13219, dsL]
  · norm_num [world13219, agent13219, scalar13219, tp13219, tm13219, ep13219, em13219, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13219, agent13219, tp13219, tm13219, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13219, agent13219, scalar13219, tp13219, tm13219, ep13219, em13219, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13219, agent13219, tp13219, tm13219, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13219, agent13219, scalar13219, tp13219, tm13219, ep13219, em13219, dsL]

theorem negative13219 :
    Eminus aL (agent13219.root+dsL) scalar13219.worldRadius world13219.frame
      agent13219.frame tm13219 ≤ -em13219 := by
  apply negative_check (lo := (8539036953590012337 / 12500000000000000000)) (hi := (68312295628720098697 / 100000000000000000000))
    (y := (-((71575609112362529183 / 100000000000000000000)))) (u := (24441118888838694893 / 50000000000000000000))
  · norm_num [world13219, agent13219, scalar13219, tp13219, tm13219, ep13219, em13219, dsL]
  · norm_num [world13219, agent13219, scalar13219, tp13219, tm13219, ep13219, em13219, dsL]
  · norm_num [world13219, agent13219, scalar13219, tp13219, tm13219, ep13219, em13219, dsL]
  · norm_num [world13219, agent13219, scalar13219, tp13219, tm13219, ep13219, em13219, dsL]
  · norm_num [world13219, agent13219, scalar13219, tp13219, tm13219, ep13219, em13219, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13219, agent13219, tp13219, tm13219, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13219, agent13219, tp13219, tm13219, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13219, agent13219, scalar13219, tp13219, tm13219, ep13219, em13219, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13219, agent13219, tp13219, tm13219, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13219, agent13219, scalar13219, tp13219, tm13219, ep13219, em13219, dsL]

theorem tails13219 :
    exp (-((13219:ℝ)*ep13219)) ≤ scalar13219.upperTail ∧
    exp (-((13219:ℝ)*em13219)) ≤ scalar13219.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13219:ℝ)) (by norm_num [ep13219]) ?_)
      (show bp13219^8 ≤ scalar13219.upperTail by norm_num [bp13219, scalar13219])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13219, bp13219, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13219:ℝ)) (by norm_num [em13219]) ?_)
      (show bm13219^8 ≤ scalar13219.lowerTail by norm_num [bm13219, scalar13219])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13219, bm13219, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13219 :
    agent13219.root+dsL+scalar13219.worldRadius < √(1/100/aL) ∧
    2*(agent13219.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13219, agent13219, scalar13219, tp13219, tm13219, ep13219, em13219, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13219, agent13219, scalar13219, tp13219, tm13219, ep13219, em13219, dsL]

noncomputable def master13219 : MasterCertificate 13219 world13219 agent13219 :=
  master scalar13219 dsL tp13219 tm13219 ep13219 em13219
    (by norm_num [dsL]) (by norm_num [tp13219]) (by norm_num [tm13219])
    (by norm_num [ep13219]) (by norm_num [em13219])
    positive13219 negative13219 tails13219.1 tails13219.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13219.1 tailGuards13219.2

theorem preserves13219 : master13219.toScalarCertificate = scalar13219 := rfl

noncomputable def tp13220 : ℝ := (1180131847 / 5000000000)
noncomputable def tm13220 : ℝ := (-((1539862597 / 2500000000)))
noncomputable def ep13220 : ℝ := (52706545787059631 / 100000000000000000000)
noncomputable def em13220 : ℝ := (51217937122307453 / 100000000000000000000)
noncomputable def bp13220 : ℝ := (41854299049507775637 / 100000000000000000000)
noncomputable def bm13220 : ℝ := (42896651747401496881 / 100000000000000000000)

theorem positive13220 :
    Eplus aL (agent13220.root+dsL) scalar13220.worldRadius world13220.frame
      agent13220.frame tp13220 ≤ -ep13220 := by
  apply positive_check (eT := (14465433081483884029 / 12500000000000000000)) (y := (4773593859269856657 / 12500000000000000000)) (u := (73252363542596016217 / 50000000000000000000))
  · norm_num [world13220, agent13220, scalar13220, tp13220, tm13220, ep13220, em13220, dsL]
  · norm_num [world13220, agent13220, scalar13220, tp13220, tm13220, ep13220, em13220, dsL]
  · norm_num [world13220, agent13220, scalar13220, tp13220, tm13220, ep13220, em13220, dsL]
  · norm_num [world13220, agent13220, scalar13220, tp13220, tm13220, ep13220, em13220, dsL]
  · norm_num [world13220, agent13220, scalar13220, tp13220, tm13220, ep13220, em13220, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13220, agent13220, tp13220, tm13220, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13220, agent13220, scalar13220, tp13220, tm13220, ep13220, em13220, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13220, agent13220, tp13220, tm13220, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13220, agent13220, scalar13220, tp13220, tm13220, ep13220, em13220, dsL]

theorem negative13220 :
    Eminus aL (agent13220.root+dsL) scalar13220.worldRadius world13220.frame
      agent13220.frame tm13220 ≤ -em13220 := by
  apply negative_check (lo := (34155652939820185201 / 50000000000000000000)) (hi := (68311305879640370403 / 100000000000000000000))
    (y := (-((35786805126231117747 / 50000000000000000000)))) (u := (9776642974978412733 / 20000000000000000000))
  · norm_num [world13220, agent13220, scalar13220, tp13220, tm13220, ep13220, em13220, dsL]
  · norm_num [world13220, agent13220, scalar13220, tp13220, tm13220, ep13220, em13220, dsL]
  · norm_num [world13220, agent13220, scalar13220, tp13220, tm13220, ep13220, em13220, dsL]
  · norm_num [world13220, agent13220, scalar13220, tp13220, tm13220, ep13220, em13220, dsL]
  · norm_num [world13220, agent13220, scalar13220, tp13220, tm13220, ep13220, em13220, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13220, agent13220, tp13220, tm13220, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13220, agent13220, tp13220, tm13220, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13220, agent13220, scalar13220, tp13220, tm13220, ep13220, em13220, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13220, agent13220, tp13220, tm13220, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13220, agent13220, scalar13220, tp13220, tm13220, ep13220, em13220, dsL]

theorem tails13220 :
    exp (-((13220:ℝ)*ep13220)) ≤ scalar13220.upperTail ∧
    exp (-((13220:ℝ)*em13220)) ≤ scalar13220.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13220:ℝ)) (by norm_num [ep13220]) ?_)
      (show bp13220^8 ≤ scalar13220.upperTail by norm_num [bp13220, scalar13220])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13220, bp13220, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13220:ℝ)) (by norm_num [em13220]) ?_)
      (show bm13220^8 ≤ scalar13220.lowerTail by norm_num [bm13220, scalar13220])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13220, bm13220, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13220 :
    agent13220.root+dsL+scalar13220.worldRadius < √(1/100/aL) ∧
    2*(agent13220.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13220, agent13220, scalar13220, tp13220, tm13220, ep13220, em13220, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13220, agent13220, scalar13220, tp13220, tm13220, ep13220, em13220, dsL]

noncomputable def master13220 : MasterCertificate 13220 world13220 agent13220 :=
  master scalar13220 dsL tp13220 tm13220 ep13220 em13220
    (by norm_num [dsL]) (by norm_num [tp13220]) (by norm_num [tm13220])
    (by norm_num [ep13220]) (by norm_num [em13220])
    positive13220 negative13220 tails13220.1 tails13220.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13220.1 tailGuards13220.2

theorem preserves13220 : master13220.toScalarCertificate = scalar13220 := rfl

noncomputable def tp13221 : ℝ := (2360332987 / 10000000000)
noncomputable def tm13221 : ℝ := (-((6159596393 / 10000000000)))
noncomputable def ep13221 : ℝ := (6588575239206169 / 12500000000000000000)
noncomputable def em13221 : ℝ := (10243934229249471 / 20000000000000000000)
noncomputable def bp13221 : ℝ := (8370023910421976657 / 20000000000000000000)
noncomputable def bm13221 : ℝ := (42892676298487392399 / 100000000000000000000)

theorem positive13221 :
    Eplus aL (agent13221.root+dsL) scalar13221.worldRadius world13221.frame
      agent13221.frame tp13221 ≤ -ep13221 := by
  apply positive_check (eT := (23144722452293326979 / 20000000000000000000)) (y := (38189367541537782301 / 100000000000000000000)) (u := (146505630534838192601 / 100000000000000000000))
  · norm_num [world13221, agent13221, scalar13221, tp13221, tm13221, ep13221, em13221, dsL]
  · norm_num [world13221, agent13221, scalar13221, tp13221, tm13221, ep13221, em13221, dsL]
  · norm_num [world13221, agent13221, scalar13221, tp13221, tm13221, ep13221, em13221, dsL]
  · norm_num [world13221, agent13221, scalar13221, tp13221, tm13221, ep13221, em13221, dsL]
  · norm_num [world13221, agent13221, scalar13221, tp13221, tm13221, ep13221, em13221, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13221, agent13221, tp13221, tm13221, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13221, agent13221, scalar13221, tp13221, tm13221, ep13221, em13221, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13221, agent13221, tp13221, tm13221, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13221, agent13221, scalar13221, tp13221, tm13221, ep13221, em13221, dsL]

theorem negative13221 :
    Eminus aL (agent13221.root+dsL) scalar13221.worldRadius world13221.frame
      agent13221.frame tm13221 ≤ -em13221 := by
  apply negative_check (lo := (68311225678384009689 / 100000000000000000000)) (hi := (6831122567838400969 / 10000000000000000000))
    (y := (-((71573481215766036847 / 100000000000000000000)))) (u := (48883277952218230351 / 100000000000000000000))
  · norm_num [world13221, agent13221, scalar13221, tp13221, tm13221, ep13221, em13221, dsL]
  · norm_num [world13221, agent13221, scalar13221, tp13221, tm13221, ep13221, em13221, dsL]
  · norm_num [world13221, agent13221, scalar13221, tp13221, tm13221, ep13221, em13221, dsL]
  · norm_num [world13221, agent13221, scalar13221, tp13221, tm13221, ep13221, em13221, dsL]
  · norm_num [world13221, agent13221, scalar13221, tp13221, tm13221, ep13221, em13221, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13221, agent13221, tp13221, tm13221, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13221, agent13221, tp13221, tm13221, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13221, agent13221, scalar13221, tp13221, tm13221, ep13221, em13221, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13221, agent13221, tp13221, tm13221, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13221, agent13221, scalar13221, tp13221, tm13221, ep13221, em13221, dsL]

theorem tails13221 :
    exp (-((13221:ℝ)*ep13221)) ≤ scalar13221.upperTail ∧
    exp (-((13221:ℝ)*em13221)) ≤ scalar13221.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13221:ℝ)) (by norm_num [ep13221]) ?_)
      (show bp13221^8 ≤ scalar13221.upperTail by norm_num [bp13221, scalar13221])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13221, bp13221, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13221:ℝ)) (by norm_num [em13221]) ?_)
      (show bm13221^8 ≤ scalar13221.lowerTail by norm_num [bm13221, scalar13221])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13221, bm13221, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13221 :
    agent13221.root+dsL+scalar13221.worldRadius < √(1/100/aL) ∧
    2*(agent13221.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13221, agent13221, scalar13221, tp13221, tm13221, ep13221, em13221, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13221, agent13221, scalar13221, tp13221, tm13221, ep13221, em13221, dsL]

noncomputable def master13221 : MasterCertificate 13221 world13221 agent13221 :=
  master scalar13221 dsL tp13221 tm13221 ep13221 em13221
    (by norm_num [dsL]) (by norm_num [tp13221]) (by norm_num [tm13221])
    (by norm_num [ep13221]) (by norm_num [em13221])
    positive13221 negative13221 tails13221.1 tails13221.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13221.1 tailGuards13221.2

theorem preserves13221 : master13221.toScalarCertificate = scalar13221 := rfl

noncomputable def tp13222 : ℝ := (2360402163 / 10000000000)
noncomputable def tm13222 : ℝ := (-((6159742271 / 10000000000)))
noncomputable def ep13222 : ℝ := (52710656159076099 / 100000000000000000000)
noncomputable def em13222 : ℝ := (1280535085935061 / 2500000000000000000)
noncomputable def bp13222 : ℝ := (10461485389499197349 / 25000000000000000000)
noncomputable def bm13222 : ℝ := (42888702260345505121 / 100000000000000000000)

theorem positive13222 :
    Eplus aL (agent13222.root+dsL) scalar13222.worldRadius world13222.frame
      agent13222.frame tp13222 ≤ -ep13222 := by
  apply positive_check (eT := (115723759066365127593 / 100000000000000000000)) (y := (9547495656355391001 / 25000000000000000000)) (u := (146506531670131811297 / 100000000000000000000))
  · norm_num [world13222, agent13222, scalar13222, tp13222, tm13222, ep13222, em13222, dsL]
  · norm_num [world13222, agent13222, scalar13222, tp13222, tm13222, ep13222, em13222, dsL]
  · norm_num [world13222, agent13222, scalar13222, tp13222, tm13222, ep13222, em13222, dsL]
  · norm_num [world13222, agent13222, scalar13222, tp13222, tm13222, ep13222, em13222, dsL]
  · norm_num [world13222, agent13222, scalar13222, tp13222, tm13222, ep13222, em13222, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13222, agent13222, tp13222, tm13222, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13222, agent13222, scalar13222, tp13222, tm13222, ep13222, em13222, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13222, agent13222, tp13222, tm13222, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13222, agent13222, scalar13222, tp13222, tm13222, ep13222, em13222, dsL]

theorem negative13222 :
    Eminus aL (agent13222.root+dsL) scalar13222.worldRadius world13222.frame
      agent13222.frame tm13222 ≤ -em13222 := by
  apply negative_check (lo := (34155572978684084007 / 50000000000000000000)) (hi := (13662229191473633603 / 20000000000000000000))
    (y := (-((8946668944266681833 / 12500000000000000000)))) (u := (1955333653404622981 / 4000000000000000000))
  · norm_num [world13222, agent13222, scalar13222, tp13222, tm13222, ep13222, em13222, dsL]
  · norm_num [world13222, agent13222, scalar13222, tp13222, tm13222, ep13222, em13222, dsL]
  · norm_num [world13222, agent13222, scalar13222, tp13222, tm13222, ep13222, em13222, dsL]
  · norm_num [world13222, agent13222, scalar13222, tp13222, tm13222, ep13222, em13222, dsL]
  · norm_num [world13222, agent13222, scalar13222, tp13222, tm13222, ep13222, em13222, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13222, agent13222, tp13222, tm13222, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13222, agent13222, tp13222, tm13222, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13222, agent13222, scalar13222, tp13222, tm13222, ep13222, em13222, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13222, agent13222, tp13222, tm13222, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13222, agent13222, scalar13222, tp13222, tm13222, ep13222, em13222, dsL]

theorem tails13222 :
    exp (-((13222:ℝ)*ep13222)) ≤ scalar13222.upperTail ∧
    exp (-((13222:ℝ)*em13222)) ≤ scalar13222.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13222:ℝ)) (by norm_num [ep13222]) ?_)
      (show bp13222^8 ≤ scalar13222.upperTail by norm_num [bp13222, scalar13222])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13222, bp13222, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13222:ℝ)) (by norm_num [em13222]) ?_)
      (show bm13222^8 ≤ scalar13222.lowerTail by norm_num [bm13222, scalar13222])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13222, bm13222, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13222 :
    agent13222.root+dsL+scalar13222.worldRadius < √(1/100/aL) ∧
    2*(agent13222.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13222, agent13222, scalar13222, tp13222, tm13222, ep13222, em13222, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13222, agent13222, scalar13222, tp13222, tm13222, ep13222, em13222, dsL]

noncomputable def master13222 : MasterCertificate 13222 world13222 agent13222 :=
  master scalar13222 dsL tp13222 tm13222 ep13222 em13222
    (by norm_num [dsL]) (by norm_num [tp13222]) (by norm_num [tm13222])
    (by norm_num [ep13222]) (by norm_num [em13222])
    positive13222 negative13222 tails13222.1 tails13222.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13222.1 tailGuards13222.2

theorem preserves13222 : master13222.toScalarCertificate = scalar13222 := rfl

noncomputable def tp13223 : ℝ := (2360471333 / 10000000000)
noncomputable def tm13223 : ℝ := (-((1231977631 / 2000000000)))
noncomputable def ep13223 : ℝ := (26356354626054907 / 50000000000000000000)
noncomputable def em13223 : ℝ := (5122313464366213 / 10000000000000000000)
noncomputable def bp13223 : ℝ := (5230220570385654937 / 12500000000000000000)
noncomputable def bm13223 : ℝ := (2144236458684327143 / 5000000000000000000)

theorem positive13223 :
    Eplus aL (agent13223.root+dsL) scalar13223.worldRadius world13223.frame
      agent13223.frame tp13223 ≤ -ep13223 := by
  apply positive_check (eT := (28930976465333272209 / 25000000000000000000)) (y := (7638119581131505923 / 20000000000000000000)) (u := (29301486619727745839 / 20000000000000000000))
  · norm_num [world13223, agent13223, scalar13223, tp13223, tm13223, ep13223, em13223, dsL]
  · norm_num [world13223, agent13223, scalar13223, tp13223, tm13223, ep13223, em13223, dsL]
  · norm_num [world13223, agent13223, scalar13223, tp13223, tm13223, ep13223, em13223, dsL]
  · norm_num [world13223, agent13223, scalar13223, tp13223, tm13223, ep13223, em13223, dsL]
  · norm_num [world13223, agent13223, scalar13223, tp13223, tm13223, ep13223, em13223, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13223, agent13223, tp13223, tm13223, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13223, agent13223, scalar13223, tp13223, tm13223, ep13223, em13223, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13223, agent13223, tp13223, tm13223, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13223, agent13223, scalar13223, tp13223, tm13223, ep13223, em13223, dsL]

theorem negative13223 :
    Eminus aL (agent13223.root+dsL) scalar13223.worldRadius world13223.frame
      agent13223.frame tm13223 ≤ -em13223 := by
  apply negative_check (lo := (17077766538615158193 / 25000000000000000000)) (hi := (68311066154460632773 / 100000000000000000000))
    (y := (-((17893305564489417731 / 25000000000000000000)))) (u := (1955336181577895061 / 4000000000000000000))
  · norm_num [world13223, agent13223, scalar13223, tp13223, tm13223, ep13223, em13223, dsL]
  · norm_num [world13223, agent13223, scalar13223, tp13223, tm13223, ep13223, em13223, dsL]
  · norm_num [world13223, agent13223, scalar13223, tp13223, tm13223, ep13223, em13223, dsL]
  · norm_num [world13223, agent13223, scalar13223, tp13223, tm13223, ep13223, em13223, dsL]
  · norm_num [world13223, agent13223, scalar13223, tp13223, tm13223, ep13223, em13223, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13223, agent13223, tp13223, tm13223, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13223, agent13223, tp13223, tm13223, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13223, agent13223, scalar13223, tp13223, tm13223, ep13223, em13223, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13223, agent13223, tp13223, tm13223, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13223, agent13223, scalar13223, tp13223, tm13223, ep13223, em13223, dsL]

theorem tails13223 :
    exp (-((13223:ℝ)*ep13223)) ≤ scalar13223.upperTail ∧
    exp (-((13223:ℝ)*em13223)) ≤ scalar13223.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13223:ℝ)) (by norm_num [ep13223]) ?_)
      (show bp13223^8 ≤ scalar13223.upperTail by norm_num [bp13223, scalar13223])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13223, bp13223, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13223:ℝ)) (by norm_num [em13223]) ?_)
      (show bm13223^8 ≤ scalar13223.lowerTail by norm_num [bm13223, scalar13223])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13223, bm13223, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13223 :
    agent13223.root+dsL+scalar13223.worldRadius < √(1/100/aL) ∧
    2*(agent13223.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13223, agent13223, scalar13223, tp13223, tm13223, ep13223, em13223, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13223, agent13223, scalar13223, tp13223, tm13223, ep13223, em13223, dsL]

noncomputable def master13223 : MasterCertificate 13223 world13223 agent13223 :=
  master scalar13223 dsL tp13223 tm13223 ep13223 em13223
    (by norm_num [dsL]) (by norm_num [tp13223]) (by norm_num [tm13223])
    (by norm_num [ep13223]) (by norm_num [em13223])
    positive13223 negative13223 tails13223.1 tails13223.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13223.1 tailGuards13223.2

theorem preserves13223 : master13223.toScalarCertificate = scalar13223 := rfl

noncomputable def tp13224 : ℝ := (73766891 / 312500000)
noncomputable def tm13224 : ℝ := (-((3080016977 / 5000000000)))
noncomputable def ep13224 : ℝ := (10542952410172119 / 20000000000000000000)
noncomputable def em13224 : ℝ := (25612432802720471 / 50000000000000000000)
noncomputable def bp13224 : ℝ := (41837587973892302271 / 100000000000000000000)
noncomputable def bm13224 : ℝ := (335005909709273777 / 781250000000000000)

theorem positive13224 :
    Eplus aL (agent13224.root+dsL) scalar13224.worldRadius world13224.frame
      agent13224.frame tp13224 ≤ -ep13224 := by
  apply positive_check (eT := (23144810550748417511 / 20000000000000000000)) (y := (1193475421641172621 / 3125000000000000000)) (u := (29301666996384346787 / 20000000000000000000))
  · norm_num [world13224, agent13224, scalar13224, tp13224, tm13224, ep13224, em13224, dsL]
  · norm_num [world13224, agent13224, scalar13224, tp13224, tm13224, ep13224, em13224, dsL]
  · norm_num [world13224, agent13224, scalar13224, tp13224, tm13224, ep13224, em13224, dsL]
  · norm_num [world13224, agent13224, scalar13224, tp13224, tm13224, ep13224, em13224, dsL]
  · norm_num [world13224, agent13224, scalar13224, tp13224, tm13224, ep13224, em13224, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13224, agent13224, tp13224, tm13224, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13224, agent13224, scalar13224, tp13224, tm13224, ep13224, em13224, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13224, agent13224, tp13224, tm13224, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13224, agent13224, scalar13224, tp13224, tm13224, ep13224, em13224, dsL]

theorem negative13224 :
    Eminus aL (agent13224.root+dsL) scalar13224.worldRadius world13224.frame
      agent13224.frame tm13224 ≤ -em13224 := by
  apply negative_check (lo := (17077746663570012667 / 25000000000000000000)) (hi := (68310986654280050669 / 100000000000000000000))
    (y := (-((8946636604344607629 / 12500000000000000000)))) (u := (24441733902977568543 / 50000000000000000000))
  · norm_num [world13224, agent13224, scalar13224, tp13224, tm13224, ep13224, em13224, dsL]
  · norm_num [world13224, agent13224, scalar13224, tp13224, tm13224, ep13224, em13224, dsL]
  · norm_num [world13224, agent13224, scalar13224, tp13224, tm13224, ep13224, em13224, dsL]
  · norm_num [world13224, agent13224, scalar13224, tp13224, tm13224, ep13224, em13224, dsL]
  · norm_num [world13224, agent13224, scalar13224, tp13224, tm13224, ep13224, em13224, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13224, agent13224, tp13224, tm13224, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13224, agent13224, tp13224, tm13224, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13224, agent13224, scalar13224, tp13224, tm13224, ep13224, em13224, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13224, agent13224, tp13224, tm13224, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13224, agent13224, scalar13224, tp13224, tm13224, ep13224, em13224, dsL]

theorem tails13224 :
    exp (-((13224:ℝ)*ep13224)) ≤ scalar13224.upperTail ∧
    exp (-((13224:ℝ)*em13224)) ≤ scalar13224.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13224:ℝ)) (by norm_num [ep13224]) ?_)
      (show bp13224^8 ≤ scalar13224.upperTail by norm_num [bp13224, scalar13224])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13224, bp13224, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13224:ℝ)) (by norm_num [em13224]) ?_)
      (show bm13224^8 ≤ scalar13224.lowerTail by norm_num [bm13224, scalar13224])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13224, bm13224, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13224 :
    agent13224.root+dsL+scalar13224.worldRadius < √(1/100/aL) ∧
    2*(agent13224.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13224, agent13224, scalar13224, tp13224, tm13224, ep13224, em13224, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13224, agent13224, scalar13224, tp13224, tm13224, ep13224, em13224, dsL]

noncomputable def master13224 : MasterCertificate 13224 world13224 agent13224 :=
  master scalar13224 dsL tp13224 tm13224 ep13224 em13224
    (by norm_num [dsL]) (by norm_num [tp13224]) (by norm_num [tm13224])
    (by norm_num [ep13224]) (by norm_num [em13224])
    positive13224 negative13224 tails13224.1 tails13224.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13224.1 tailGuards13224.2

theorem preserves13224 : master13224.toScalarCertificate = scalar13224 := rfl

end BstLean.Part268
