import BstLean.Part261Checker
import BstLean.Part268Scalar32
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp13150 : ℝ := (235485083 / 1000000000)
noncomputable def tm13150 : ℝ := (-((6147562899 / 10000000000)))
noncomputable def ep13150 : ℝ := (13137722478684467 / 25000000000000000000)
noncomputable def em13150 : ℝ := (51084171329568223 / 100000000000000000000)
noncomputable def bp13150 : ℝ := (42155490334633729487 / 100000000000000000000)
noncomputable def bm13150 : ℝ := (21592087738895962333 / 50000000000000000000)

theorem positive13150 :
    Eplus aL (agent13150.root+dsL) scalar13150.worldRadius world13150.frame
      agent13150.frame tp13150 ≤ -ep13150 := by
  apply positive_check (eT := (57854591290786095693 / 50000000000000000000)) (y := (38149896371827770549 / 100000000000000000000)) (u := (146447814459866232223 / 100000000000000000000))
  · norm_num [world13150, agent13150, scalar13150, tp13150, tm13150, ep13150, em13150, dsL]
  · norm_num [world13150, agent13150, scalar13150, tp13150, tm13150, ep13150, em13150, dsL]
  · norm_num [world13150, agent13150, scalar13150, tp13150, tm13150, ep13150, em13150, dsL]
  · norm_num [world13150, agent13150, scalar13150, tp13150, tm13150, ep13150, em13150, dsL]
  · norm_num [world13150, agent13150, scalar13150, tp13150, tm13150, ep13150, em13150, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13150, agent13150, tp13150, tm13150, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13150, agent13150, scalar13150, tp13150, tm13150, ep13150, em13150, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13150, agent13150, tp13150, tm13150, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13150, agent13150, scalar13150, tp13150, tm13150, ep13150, em13150, dsL]

theorem negative13150 :
    Eminus aL (agent13150.root+dsL) scalar13150.worldRadius world13150.frame
      agent13150.frame tm13150 ≤ -em13150 := by
  apply negative_check (lo := (8540479507286675559 / 12500000000000000000)) (hi := (68323836058293404473 / 100000000000000000000))
    (y := (-((715948297420326059 / 1000000000000000000)))) (u := (48872843206656470761 / 100000000000000000000))
  · norm_num [world13150, agent13150, scalar13150, tp13150, tm13150, ep13150, em13150, dsL]
  · norm_num [world13150, agent13150, scalar13150, tp13150, tm13150, ep13150, em13150, dsL]
  · norm_num [world13150, agent13150, scalar13150, tp13150, tm13150, ep13150, em13150, dsL]
  · norm_num [world13150, agent13150, scalar13150, tp13150, tm13150, ep13150, em13150, dsL]
  · norm_num [world13150, agent13150, scalar13150, tp13150, tm13150, ep13150, em13150, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13150, agent13150, tp13150, tm13150, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13150, agent13150, tp13150, tm13150, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13150, agent13150, scalar13150, tp13150, tm13150, ep13150, em13150, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13150, agent13150, tp13150, tm13150, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13150, agent13150, scalar13150, tp13150, tm13150, ep13150, em13150, dsL]

theorem tails13150 :
    exp (-((13150:ℝ)*ep13150)) ≤ scalar13150.upperTail ∧
    exp (-((13150:ℝ)*em13150)) ≤ scalar13150.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13150:ℝ)) (by norm_num [ep13150]) ?_)
      (show bp13150^8 ≤ scalar13150.upperTail by norm_num [bp13150, scalar13150])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13150, bp13150, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13150:ℝ)) (by norm_num [em13150]) ?_)
      (show bm13150^8 ≤ scalar13150.lowerTail by norm_num [bm13150, scalar13150])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13150, bm13150, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13150 :
    agent13150.root+dsL+scalar13150.worldRadius < √(1/100/aL) ∧
    2*(agent13150.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13150, agent13150, scalar13150, tp13150, tm13150, ep13150, em13150, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13150, agent13150, scalar13150, tp13150, tm13150, ep13150, em13150, dsL]

noncomputable def master13150 : MasterCertificate 13150 world13150 agent13150 :=
  master scalar13150 dsL tp13150 tm13150 ep13150 em13150
    (by norm_num [dsL]) (by norm_num [tp13150]) (by norm_num [tm13150])
    (by norm_num [ep13150]) (by norm_num [em13150])
    positive13150 negative13150 tails13150.1 tails13150.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13150.1 tailGuards13150.2

theorem preserves13150 : master13150.toScalarCertificate = scalar13150 := rfl

noncomputable def tp13151 : ℝ := (1177461051 / 5000000000)
noncomputable def tm13151 : ℝ := (-((1536928393 / 2500000000)))
noncomputable def ep13151 : ℝ := (26276507583130993 / 50000000000000000000)
noncomputable def em13151 : ℝ := (25542984306457603 / 50000000000000000000)
noncomputable def bp13151 : ℝ := (8430249729600222791 / 20000000000000000000)
noncomputable def bm13151 : ℝ := (2698758890684536861 / 6250000000000000000)

theorem positive13151 :
    Eplus aL (agent13151.root+dsL) scalar13151.worldRadius world13151.frame
      agent13151.frame tp13151 ≤ -ep13151 := by
  apply positive_check (eT := (2892733553211086757 / 2500000000000000000)) (y := (9537633332044621557 / 25000000000000000000)) (u := (73224373635745858473 / 50000000000000000000))
  · norm_num [world13151, agent13151, scalar13151, tp13151, tm13151, ep13151, em13151, dsL]
  · norm_num [world13151, agent13151, scalar13151, tp13151, tm13151, ep13151, em13151, dsL]
  · norm_num [world13151, agent13151, scalar13151, tp13151, tm13151, ep13151, em13151, dsL]
  · norm_num [world13151, agent13151, scalar13151, tp13151, tm13151, ep13151, em13151, dsL]
  · norm_num [world13151, agent13151, scalar13151, tp13151, tm13151, ep13151, em13151, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13151, agent13151, tp13151, tm13151, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13151, agent13151, scalar13151, tp13151, tm13151, ep13151, em13151, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13151, agent13151, tp13151, tm13151, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13151, agent13151, scalar13151, tp13151, tm13151, ep13151, em13151, dsL]

theorem negative13151 :
    Eminus aL (agent13151.root+dsL) scalar13151.worldRadius world13151.frame
      agent13151.frame tm13151 ≤ -em13151 := by
  apply negative_check (lo := (13664747986470417453 / 20000000000000000000)) (hi := (34161869966176043633 / 50000000000000000000))
    (y := (-((35797361626948077507 / 50000000000000000000)))) (u := (48872895250464142329 / 100000000000000000000))
  · norm_num [world13151, agent13151, scalar13151, tp13151, tm13151, ep13151, em13151, dsL]
  · norm_num [world13151, agent13151, scalar13151, tp13151, tm13151, ep13151, em13151, dsL]
  · norm_num [world13151, agent13151, scalar13151, tp13151, tm13151, ep13151, em13151, dsL]
  · norm_num [world13151, agent13151, scalar13151, tp13151, tm13151, ep13151, em13151, dsL]
  · norm_num [world13151, agent13151, scalar13151, tp13151, tm13151, ep13151, em13151, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13151, agent13151, tp13151, tm13151, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13151, agent13151, tp13151, tm13151, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13151, agent13151, scalar13151, tp13151, tm13151, ep13151, em13151, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13151, agent13151, tp13151, tm13151, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13151, agent13151, scalar13151, tp13151, tm13151, ep13151, em13151, dsL]

theorem tails13151 :
    exp (-((13151:ℝ)*ep13151)) ≤ scalar13151.upperTail ∧
    exp (-((13151:ℝ)*em13151)) ≤ scalar13151.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13151:ℝ)) (by norm_num [ep13151]) ?_)
      (show bp13151^8 ≤ scalar13151.upperTail by norm_num [bp13151, scalar13151])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13151, bp13151, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13151:ℝ)) (by norm_num [em13151]) ?_)
      (show bm13151^8 ≤ scalar13151.lowerTail by norm_num [bm13151, scalar13151])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13151, bm13151, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13151 :
    agent13151.root+dsL+scalar13151.worldRadius < √(1/100/aL) ∧
    2*(agent13151.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13151, agent13151, scalar13151, tp13151, tm13151, ep13151, em13151, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13151, agent13151, scalar13151, tp13151, tm13151, ep13151, em13151, dsL]

noncomputable def master13151 : MasterCertificate 13151 world13151 agent13151 :=
  master scalar13151 dsL tp13151 tm13151 ep13151 em13151
    (by norm_num [dsL]) (by norm_num [tp13151]) (by norm_num [tm13151])
    (by norm_num [ep13151]) (by norm_num [em13151])
    positive13151 negative13151 tails13151.1 tails13151.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13151.1 tailGuards13151.2

theorem preserves13151 : master13151.toScalarCertificate = scalar13151 := rfl

noncomputable def tp13152 : ℝ := (294374157 / 1250000000)
noncomputable def tm13152 : ℝ := (-((76848303 / 125000000)))
noncomputable def ep13152 : ℝ := (2627756988088527 / 5000000000000000000)
noncomputable def em13152 : ℝ := (51087765277448621 / 100000000000000000000)
noncomputable def bp13152 : ℝ := (21073503809392867533 / 50000000000000000000)
noncomputable def bm13152 : ℝ := (43176109646044328403 / 100000000000000000000)

theorem positive13152 :
    Eplus aL (agent13152.root+dsL) scalar13152.worldRadius world13152.frame
      agent13152.frame tp13152 ≤ -ep13152 := by
  apply positive_check (eT := (57854750431178442743 / 50000000000000000000)) (y := (19075584294962416581 / 50000000000000000000)) (u := (73224838803658083853 / 50000000000000000000))
  · norm_num [world13152, agent13152, scalar13152, tp13152, tm13152, ep13152, em13152, dsL]
  · norm_num [world13152, agent13152, scalar13152, tp13152, tm13152, ep13152, em13152, dsL]
  · norm_num [world13152, agent13152, scalar13152, tp13152, tm13152, ep13152, em13152, dsL]
  · norm_num [world13152, agent13152, scalar13152, tp13152, tm13152, ep13152, em13152, dsL]
  · norm_num [world13152, agent13152, scalar13152, tp13152, tm13152, ep13152, em13152, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13152, agent13152, tp13152, tm13152, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13152, agent13152, scalar13152, tp13152, tm13152, ep13152, em13152, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13152, agent13152, tp13152, tm13152, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13152, agent13152, scalar13152, tp13152, tm13152, ep13152, em13152, dsL]

theorem negative13152 :
    Eminus aL (agent13152.root+dsL) scalar13152.worldRadius world13152.frame
      agent13152.frame tm13152 ≤ -em13152 := by
  apply negative_check (lo := (68323643770930096371 / 100000000000000000000)) (hi := (17080910942732524093 / 25000000000000000000))
    (y := (-((3579730878850286637 / 5000000000000000000)))) (u := (6109118362230924003 / 12500000000000000000))
  · norm_num [world13152, agent13152, scalar13152, tp13152, tm13152, ep13152, em13152, dsL]
  · norm_num [world13152, agent13152, scalar13152, tp13152, tm13152, ep13152, em13152, dsL]
  · norm_num [world13152, agent13152, scalar13152, tp13152, tm13152, ep13152, em13152, dsL]
  · norm_num [world13152, agent13152, scalar13152, tp13152, tm13152, ep13152, em13152, dsL]
  · norm_num [world13152, agent13152, scalar13152, tp13152, tm13152, ep13152, em13152, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13152, agent13152, tp13152, tm13152, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13152, agent13152, tp13152, tm13152, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13152, agent13152, scalar13152, tp13152, tm13152, ep13152, em13152, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13152, agent13152, tp13152, tm13152, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13152, agent13152, scalar13152, tp13152, tm13152, ep13152, em13152, dsL]

theorem tails13152 :
    exp (-((13152:ℝ)*ep13152)) ≤ scalar13152.upperTail ∧
    exp (-((13152:ℝ)*em13152)) ≤ scalar13152.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13152:ℝ)) (by norm_num [ep13152]) ?_)
      (show bp13152^8 ≤ scalar13152.upperTail by norm_num [bp13152, scalar13152])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13152, bp13152, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13152:ℝ)) (by norm_num [em13152]) ?_)
      (show bm13152^8 ≤ scalar13152.lowerTail by norm_num [bm13152, scalar13152])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13152, bm13152, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13152 :
    agent13152.root+dsL+scalar13152.worldRadius < √(1/100/aL) ∧
    2*(agent13152.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13152, agent13152, scalar13152, tp13152, tm13152, ep13152, em13152, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13152, agent13152, scalar13152, tp13152, tm13152, ep13152, em13152, dsL]

noncomputable def master13152 : MasterCertificate 13152 world13152 agent13152 :=
  master scalar13152 dsL tp13152 tm13152 ep13152 em13152
    (by norm_num [dsL]) (by norm_num [tp13152]) (by norm_num [tm13152])
    (by norm_num [ep13152]) (by norm_num [em13152])
    positive13152 negative13152 tails13152.1 tails13152.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13152.1 tailGuards13152.2

theorem preserves13152 : master13152.toScalarCertificate = scalar13152 := rfl

noncomputable def tp13153 : ℝ := (294383063 / 1250000000)
noncomputable def tm13153 : ℝ := (-((3074007351 / 5000000000)))
noncomputable def ep13153 : ℝ := (52557263361477593 / 100000000000000000000)
noncomputable def em13153 : ℝ := (51089561025333539 / 100000000000000000000)
noncomputable def bp13153 : ℝ := (8428553496481902889 / 20000000000000000000)
noncomputable def bm13153 : ℝ := (863441557489350713 / 2000000000000000000)

theorem positive13153 :
    Eplus aL (agent13153.root+dsL) scalar13153.worldRadius world13153.frame
      agent13153.frame tp13153 ≤ -ep13153 := by
  apply positive_check (eT := (23141932060637019397 / 20000000000000000000)) (y := (19075902872558862793 / 50000000000000000000)) (u := (146450610722014708157 / 100000000000000000000))
  · norm_num [world13153, agent13153, scalar13153, tp13153, tm13153, ep13153, em13153, dsL]
  · norm_num [world13153, agent13153, scalar13153, tp13153, tm13153, ep13153, em13153, dsL]
  · norm_num [world13153, agent13153, scalar13153, tp13153, tm13153, ep13153, em13153, dsL]
  · norm_num [world13153, agent13153, scalar13153, tp13153, tm13153, ep13153, em13153, dsL]
  · norm_num [world13153, agent13153, scalar13153, tp13153, tm13153, ep13153, em13153, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13153, agent13153, tp13153, tm13153, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13153, agent13153, scalar13153, tp13153, tm13153, ep13153, em13153, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13153, agent13153, tp13153, tm13153, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13153, agent13153, scalar13153, tp13153, tm13153, ep13153, em13153, dsL]

theorem negative13153 :
    Eminus aL (agent13153.root+dsL) scalar13153.worldRadius world13153.frame
      agent13153.frame tm13153 ≤ -em13153 := by
  apply negative_check (lo := (4270221776557919729 / 6250000000000000000)) (hi := (13664709684985343133 / 20000000000000000000))
    (y := (-((35797255187189276867 / 50000000000000000000)))) (u := (12218249822739632427 / 25000000000000000000))
  · norm_num [world13153, agent13153, scalar13153, tp13153, tm13153, ep13153, em13153, dsL]
  · norm_num [world13153, agent13153, scalar13153, tp13153, tm13153, ep13153, em13153, dsL]
  · norm_num [world13153, agent13153, scalar13153, tp13153, tm13153, ep13153, em13153, dsL]
  · norm_num [world13153, agent13153, scalar13153, tp13153, tm13153, ep13153, em13153, dsL]
  · norm_num [world13153, agent13153, scalar13153, tp13153, tm13153, ep13153, em13153, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13153, agent13153, tp13153, tm13153, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13153, agent13153, tp13153, tm13153, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13153, agent13153, scalar13153, tp13153, tm13153, ep13153, em13153, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13153, agent13153, tp13153, tm13153, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13153, agent13153, scalar13153, tp13153, tm13153, ep13153, em13153, dsL]

theorem tails13153 :
    exp (-((13153:ℝ)*ep13153)) ≤ scalar13153.upperTail ∧
    exp (-((13153:ℝ)*em13153)) ≤ scalar13153.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13153:ℝ)) (by norm_num [ep13153]) ?_)
      (show bp13153^8 ≤ scalar13153.upperTail by norm_num [bp13153, scalar13153])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13153, bp13153, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13153:ℝ)) (by norm_num [em13153]) ?_)
      (show bm13153^8 ≤ scalar13153.lowerTail by norm_num [bm13153, scalar13153])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13153, bm13153, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13153 :
    agent13153.root+dsL+scalar13153.worldRadius < √(1/100/aL) ∧
    2*(agent13153.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13153, agent13153, scalar13153, tp13153, tm13153, ep13153, em13153, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13153, agent13153, scalar13153, tp13153, tm13153, ep13153, em13153, dsL]

noncomputable def master13153 : MasterCertificate 13153 world13153 agent13153 :=
  master scalar13153 dsL tp13153 tm13153 ep13153 em13153
    (by norm_num [dsL]) (by norm_num [tp13153]) (by norm_num [tm13153])
    (by norm_num [ep13153]) (by norm_num [em13153])
    positive13153 negative13153 tails13153.1 tails13153.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13153.1 tailGuards13153.2

theorem preserves13153 : master13153.toScalarCertificate = scalar13153 := rfl

noncomputable def tp13154 : ℝ := (588783901 / 2500000000)
noncomputable def tm13154 : ℝ := (-((76852067 / 125000000)))
noncomputable def ep13154 : ℝ := (5255938582091701 / 10000000000000000000)
noncomputable def em13154 : ℝ := (51091355705905587 / 100000000000000000000)
noncomputable def bp13154 : ℝ := (10534632084735348963 / 25000000000000000000)
noncomputable def bm13154 : ℝ := (2158402352157381919 / 5000000000000000000)

theorem positive13154 :
    Eplus aL (agent13154.root+dsL) scalar13154.worldRadius world13154.frame
      agent13154.frame tp13154 ≤ -ep13154 := by
  apply positive_check (eT := (115709818716009541907 / 100000000000000000000)) (y := (1907622036631566471 / 5000000000000000000)) (u := (29290308133611781403 / 20000000000000000000))
  · norm_num [world13154, agent13154, scalar13154, tp13154, tm13154, ep13154, em13154, dsL]
  · norm_num [world13154, agent13154, scalar13154, tp13154, tm13154, ep13154, em13154, dsL]
  · norm_num [world13154, agent13154, scalar13154, tp13154, tm13154, ep13154, em13154, dsL]
  · norm_num [world13154, agent13154, scalar13154, tp13154, tm13154, ep13154, em13154, dsL]
  · norm_num [world13154, agent13154, scalar13154, tp13154, tm13154, ep13154, em13154, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13154, agent13154, tp13154, tm13154, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13154, agent13154, scalar13154, tp13154, tm13154, ep13154, em13154, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13154, agent13154, tp13154, tm13154, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13154, agent13154, scalar13154, tp13154, tm13154, ep13154, em13154, dsL]

theorem negative13154 :
    Eminus aL (agent13154.root+dsL) scalar13154.worldRadius world13154.frame
      agent13154.frame tm13154 ≤ -em13154 := by
  apply negative_check (lo := (34161726096293296901 / 50000000000000000000)) (hi := (68323452192586593803 / 100000000000000000000))
    (y := (-((71594405777918264991 / 100000000000000000000)))) (u := (24436525205206279779 / 50000000000000000000))
  · norm_num [world13154, agent13154, scalar13154, tp13154, tm13154, ep13154, em13154, dsL]
  · norm_num [world13154, agent13154, scalar13154, tp13154, tm13154, ep13154, em13154, dsL]
  · norm_num [world13154, agent13154, scalar13154, tp13154, tm13154, ep13154, em13154, dsL]
  · norm_num [world13154, agent13154, scalar13154, tp13154, tm13154, ep13154, em13154, dsL]
  · norm_num [world13154, agent13154, scalar13154, tp13154, tm13154, ep13154, em13154, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13154, agent13154, tp13154, tm13154, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13154, agent13154, tp13154, tm13154, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13154, agent13154, scalar13154, tp13154, tm13154, ep13154, em13154, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13154, agent13154, tp13154, tm13154, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13154, agent13154, scalar13154, tp13154, tm13154, ep13154, em13154, dsL]

theorem tails13154 :
    exp (-((13154:ℝ)*ep13154)) ≤ scalar13154.upperTail ∧
    exp (-((13154:ℝ)*em13154)) ≤ scalar13154.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13154:ℝ)) (by norm_num [ep13154]) ?_)
      (show bp13154^8 ≤ scalar13154.upperTail by norm_num [bp13154, scalar13154])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13154, bp13154, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13154:ℝ)) (by norm_num [em13154]) ?_)
      (show bm13154^8 ≤ scalar13154.lowerTail by norm_num [bm13154, scalar13154])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13154, bm13154, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13154 :
    agent13154.root+dsL+scalar13154.worldRadius < √(1/100/aL) ∧
    2*(agent13154.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13154, agent13154, scalar13154, tp13154, tm13154, ep13154, em13154, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13154, agent13154, scalar13154, tp13154, tm13154, ep13154, em13154, dsL]

noncomputable def master13154 : MasterCertificate 13154 world13154 agent13154 :=
  master scalar13154 dsL tp13154 tm13154 ep13154 em13154
    (by norm_num [dsL]) (by norm_num [tp13154]) (by norm_num [tm13154])
    (by norm_num [ep13154]) (by norm_num [em13154])
    positive13154 negative13154 tails13154.1 tails13154.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13154.1 tailGuards13154.2

theorem preserves13154 : master13154.toScalarCertificate = scalar13154 := rfl

noncomputable def tp13155 : ℝ := (2355206727 / 10000000000)
noncomputable def tm13155 : ℝ := (-((6148315473 / 10000000000)))
noncomputable def ep13155 : ℝ := (52561506330067499 / 100000000000000000000)
noncomputable def em13155 : ℝ := (51093148584674339 / 100000000000000000000)
noncomputable def bp13155 : ℝ := (21067145374783764187 / 50000000000000000000)
noncomputable def bm13155 : ℝ := (21582008836694851563 / 50000000000000000000)

theorem positive13155 :
    Eplus aL (agent13155.root+dsL) scalar13155.worldRadius world13155.frame
      agent13155.frame tp13155 ≤ -ep13155 := by
  apply positive_check (eT := (14463747165841920329 / 12500000000000000000)) (y := (38153076476105842179 / 100000000000000000000)) (u := (4576639741472862441 / 3125000000000000000))
  · norm_num [world13155, agent13155, scalar13155, tp13155, tm13155, ep13155, em13155, dsL]
  · norm_num [world13155, agent13155, scalar13155, tp13155, tm13155, ep13155, em13155, dsL]
  · norm_num [world13155, agent13155, scalar13155, tp13155, tm13155, ep13155, em13155, dsL]
  · norm_num [world13155, agent13155, scalar13155, tp13155, tm13155, ep13155, em13155, dsL]
  · norm_num [world13155, agent13155, scalar13155, tp13155, tm13155, ep13155, em13155, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13155, agent13155, tp13155, tm13155, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13155, agent13155, scalar13155, tp13155, tm13155, ep13155, em13155, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13155, agent13155, tp13155, tm13155, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13155, agent13155, scalar13155, tp13155, tm13155, ep13155, em13155, dsL]

theorem negative13155 :
    Eminus aL (agent13155.root+dsL) scalar13155.worldRadius world13155.frame
      agent13155.frame tm13155 ≤ -em13155 := by
  apply negative_check (lo := (68323358210631252641 / 100000000000000000000)) (hi := (34161679105315626321 / 50000000000000000000))
    (y := (-((14318859231352432813 / 20000000000000000000)))) (u := (4887310398564480613 / 10000000000000000000))
  · norm_num [world13155, agent13155, scalar13155, tp13155, tm13155, ep13155, em13155, dsL]
  · norm_num [world13155, agent13155, scalar13155, tp13155, tm13155, ep13155, em13155, dsL]
  · norm_num [world13155, agent13155, scalar13155, tp13155, tm13155, ep13155, em13155, dsL]
  · norm_num [world13155, agent13155, scalar13155, tp13155, tm13155, ep13155, em13155, dsL]
  · norm_num [world13155, agent13155, scalar13155, tp13155, tm13155, ep13155, em13155, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13155, agent13155, tp13155, tm13155, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13155, agent13155, tp13155, tm13155, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13155, agent13155, scalar13155, tp13155, tm13155, ep13155, em13155, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13155, agent13155, tp13155, tm13155, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13155, agent13155, scalar13155, tp13155, tm13155, ep13155, em13155, dsL]

theorem tails13155 :
    exp (-((13155:ℝ)*ep13155)) ≤ scalar13155.upperTail ∧
    exp (-((13155:ℝ)*em13155)) ≤ scalar13155.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13155:ℝ)) (by norm_num [ep13155]) ?_)
      (show bp13155^8 ≤ scalar13155.upperTail by norm_num [bp13155, scalar13155])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13155, bp13155, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13155:ℝ)) (by norm_num [em13155]) ?_)
      (show bm13155^8 ≤ scalar13155.lowerTail by norm_num [bm13155, scalar13155])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13155, bm13155, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13155 :
    agent13155.root+dsL+scalar13155.worldRadius < √(1/100/aL) ∧
    2*(agent13155.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13155, agent13155, scalar13155, tp13155, tm13155, ep13155, em13155, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13155, agent13155, scalar13155, tp13155, tm13155, ep13155, em13155, dsL]

noncomputable def master13155 : MasterCertificate 13155 world13155 agent13155 :=
  master scalar13155 dsL tp13155 tm13155 ep13155 em13155
    (by norm_num [dsL]) (by norm_num [tp13155]) (by norm_num [tm13155])
    (by norm_num [ep13155]) (by norm_num [em13155])
    positive13155 negative13155 tails13155.1 tails13155.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13155.1 tailGuards13155.2

theorem preserves13155 : master13155.toScalarCertificate = scalar13155 := rfl

noncomputable def tp13156 : ℝ := (18842223 / 80000000)
noncomputable def tm13156 : ℝ := (-((6148465901 / 10000000000)))
noncomputable def ep13156 : ℝ := (52563627091752849 / 100000000000000000000)
noncomputable def em13156 : ℝ := (25547470841082297 / 50000000000000000000)
noncomputable def bp13156 : ℝ := (2633128324252081701 / 6250000000000000000)
noncomputable def bm13156 : ℝ := (5394998541380810207 / 12500000000000000000)

theorem positive13156 :
    Eplus aL (agent13156.root+dsL) scalar13156.worldRadius world13156.frame
      agent13156.frame tp13156 ≤ -ep13156 := by
  apply positive_check (eT := (115710136149695304357 / 100000000000000000000)) (y := (953842820336783291 / 2500000000000000000)) (u := (73226701830948501081 / 50000000000000000000))
  · norm_num [world13156, agent13156, scalar13156, tp13156, tm13156, ep13156, em13156, dsL]
  · norm_num [world13156, agent13156, scalar13156, tp13156, tm13156, ep13156, em13156, dsL]
  · norm_num [world13156, agent13156, scalar13156, tp13156, tm13156, ep13156, em13156, dsL]
  · norm_num [world13156, agent13156, scalar13156, tp13156, tm13156, ep13156, em13156, dsL]
  · norm_num [world13156, agent13156, scalar13156, tp13156, tm13156, ep13156, em13156, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13156, agent13156, tp13156, tm13156, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13156, agent13156, scalar13156, tp13156, tm13156, ep13156, em13156, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13156, agent13156, tp13156, tm13156, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13156, agent13156, scalar13156, tp13156, tm13156, ep13156, em13156, dsL]

theorem negative13156 :
    Eminus aL (agent13156.root+dsL) scalar13156.worldRadius world13156.frame
      agent13156.frame tm13156 ≤ -em13156 := by
  apply negative_check (lo := (68323262838628521567 / 100000000000000000000)) (hi := (2135101963707141299 / 3125000000000000000))
    (y := (-((71594190252513839311 / 100000000000000000000)))) (u := (48873155744365622439 / 100000000000000000000))
  · norm_num [world13156, agent13156, scalar13156, tp13156, tm13156, ep13156, em13156, dsL]
  · norm_num [world13156, agent13156, scalar13156, tp13156, tm13156, ep13156, em13156, dsL]
  · norm_num [world13156, agent13156, scalar13156, tp13156, tm13156, ep13156, em13156, dsL]
  · norm_num [world13156, agent13156, scalar13156, tp13156, tm13156, ep13156, em13156, dsL]
  · norm_num [world13156, agent13156, scalar13156, tp13156, tm13156, ep13156, em13156, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13156, agent13156, tp13156, tm13156, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13156, agent13156, tp13156, tm13156, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13156, agent13156, scalar13156, tp13156, tm13156, ep13156, em13156, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13156, agent13156, tp13156, tm13156, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13156, agent13156, scalar13156, tp13156, tm13156, ep13156, em13156, dsL]

theorem tails13156 :
    exp (-((13156:ℝ)*ep13156)) ≤ scalar13156.upperTail ∧
    exp (-((13156:ℝ)*em13156)) ≤ scalar13156.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13156:ℝ)) (by norm_num [ep13156]) ?_)
      (show bp13156^8 ≤ scalar13156.upperTail by norm_num [bp13156, scalar13156])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13156, bp13156, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13156:ℝ)) (by norm_num [em13156]) ?_)
      (show bm13156^8 ≤ scalar13156.lowerTail by norm_num [bm13156, scalar13156])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13156, bm13156, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13156 :
    agent13156.root+dsL+scalar13156.worldRadius < √(1/100/aL) ∧
    2*(agent13156.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13156, agent13156, scalar13156, tp13156, tm13156, ep13156, em13156, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13156, agent13156, scalar13156, tp13156, tm13156, ep13156, em13156, dsL]

noncomputable def master13156 : MasterCertificate 13156 world13156 agent13156 :=
  master scalar13156 dsL tp13156 tm13156 ep13156 em13156
    (by norm_num [dsL]) (by norm_num [tp13156]) (by norm_num [tm13156])
    (by norm_num [ep13156]) (by norm_num [em13156])
    positive13156 negative13156 tails13156.1 tails13156.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13156.1 tailGuards13156.2

theorem preserves13156 : master13156.toScalarCertificate = scalar13156 := rfl

noncomputable def tp13157 : ℝ := (2355348899 / 10000000000)
noncomputable def tm13157 : ℝ := (-((6148616129 / 10000000000)))
noncomputable def ep13157 : ℝ := (52565745944516659 / 100000000000000000000)
noncomputable def em13157 : ℝ := (51096733021796667 / 100000000000000000000)
noncomputable def bp13157 : ℝ := (21062908575929230809 / 50000000000000000000)
noncomputable def bm13157 : ℝ := (43155960419029871439 / 100000000000000000000)

theorem positive13157 :
    Eplus aL (agent13157.root+dsL) scalar13157.worldRadius world13157.frame
      agent13157.frame tp13157 ≤ -ep13157 := by
  apply positive_check (eT := (57855147058373197033 / 50000000000000000000)) (y := (9538586862320151923 / 25000000000000000000)) (u := (73227166555294924081 / 50000000000000000000))
  · norm_num [world13157, agent13157, scalar13157, tp13157, tm13157, ep13157, em13157, dsL]
  · norm_num [world13157, agent13157, scalar13157, tp13157, tm13157, ep13157, em13157, dsL]
  · norm_num [world13157, agent13157, scalar13157, tp13157, tm13157, ep13157, em13157, dsL]
  · norm_num [world13157, agent13157, scalar13157, tp13157, tm13157, ep13157, em13157, dsL]
  · norm_num [world13157, agent13157, scalar13157, tp13157, tm13157, ep13157, em13157, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13157, agent13157, tp13157, tm13157, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13157, agent13157, scalar13157, tp13157, tm13157, ep13157, em13157, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13157, agent13157, tp13157, tm13157, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13157, agent13157, scalar13157, tp13157, tm13157, ep13157, em13157, dsL]

theorem negative13157 :
    Eminus aL (agent13157.root+dsL) scalar13157.worldRadius world13157.frame
      agent13157.frame tm13157 ≤ -em13157 := by
  apply negative_check (lo := (68323168256585682923 / 100000000000000000000)) (hi := (17080792064146420731 / 25000000000000000000))
    (y := (-((71594083034379658467 / 100000000000000000000)))) (u := (24436604072639709241 / 50000000000000000000))
  · norm_num [world13157, agent13157, scalar13157, tp13157, tm13157, ep13157, em13157, dsL]
  · norm_num [world13157, agent13157, scalar13157, tp13157, tm13157, ep13157, em13157, dsL]
  · norm_num [world13157, agent13157, scalar13157, tp13157, tm13157, ep13157, em13157, dsL]
  · norm_num [world13157, agent13157, scalar13157, tp13157, tm13157, ep13157, em13157, dsL]
  · norm_num [world13157, agent13157, scalar13157, tp13157, tm13157, ep13157, em13157, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13157, agent13157, tp13157, tm13157, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13157, agent13157, tp13157, tm13157, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13157, agent13157, scalar13157, tp13157, tm13157, ep13157, em13157, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13157, agent13157, tp13157, tm13157, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13157, agent13157, scalar13157, tp13157, tm13157, ep13157, em13157, dsL]

theorem tails13157 :
    exp (-((13157:ℝ)*ep13157)) ≤ scalar13157.upperTail ∧
    exp (-((13157:ℝ)*em13157)) ≤ scalar13157.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13157:ℝ)) (by norm_num [ep13157]) ?_)
      (show bp13157^8 ≤ scalar13157.upperTail by norm_num [bp13157, scalar13157])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13157, bp13157, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13157:ℝ)) (by norm_num [em13157]) ?_)
      (show bm13157^8 ≤ scalar13157.lowerTail by norm_num [bm13157, scalar13157])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13157, bm13157, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13157 :
    agent13157.root+dsL+scalar13157.worldRadius < √(1/100/aL) ∧
    2*(agent13157.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13157, agent13157, scalar13157, tp13157, tm13157, ep13157, em13157, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13157, agent13157, scalar13157, tp13157, tm13157, ep13157, em13157, dsL]

noncomputable def master13157 : MasterCertificate 13157 world13157 agent13157 :=
  master scalar13157 dsL tp13157 tm13157 ep13157 em13157
    (by norm_num [dsL]) (by norm_num [tp13157]) (by norm_num [tm13157])
    (by norm_num [ep13157]) (by norm_num [em13157])
    positive13157 negative13157 tails13157.1 tails13157.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13157.1 tailGuards13157.2

theorem preserves13157 : master13157.toScalarCertificate = scalar13157 := rfl

noncomputable def tp13158 : ℝ := (2355419929 / 10000000000)
noncomputable def tm13158 : ℝ := (-((6148766243 / 10000000000)))
noncomputable def ep13158 : ℝ := (13141965952757231 / 25000000000000000000)
noncomputable def em13158 : ℝ := (3193657715814553 / 6250000000000000000)
noncomputable def bp13158 : ℝ := (21060791000874596753 / 50000000000000000000)
noncomputable def bm13158 : ℝ := (21575966667197745083 / 50000000000000000000)

theorem positive13158 :
    Eplus aL (agent13158.root+dsL) scalar13158.worldRadius world13158.frame
      agent13158.frame tp13158 ≤ -ep13158 := by
  apply positive_check (eT := (57855226079904211713 / 50000000000000000000)) (y := (3815498244594831137 / 10000000000000000000)) (u := (29291052618735497147 / 20000000000000000000))
  · norm_num [world13158, agent13158, scalar13158, tp13158, tm13158, ep13158, em13158, dsL]
  · norm_num [world13158, agent13158, scalar13158, tp13158, tm13158, ep13158, em13158, dsL]
  · norm_num [world13158, agent13158, scalar13158, tp13158, tm13158, ep13158, em13158, dsL]
  · norm_num [world13158, agent13158, scalar13158, tp13158, tm13158, ep13158, em13158, dsL]
  · norm_num [world13158, agent13158, scalar13158, tp13158, tm13158, ep13158, em13158, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13158, agent13158, tp13158, tm13158, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13158, agent13158, scalar13158, tp13158, tm13158, ep13158, em13158, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13158, agent13158, tp13158, tm13158, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13158, agent13158, scalar13158, tp13158, tm13158, ep13158, em13158, dsL]

theorem negative13158 :
    Eminus aL (agent13158.root+dsL) scalar13158.worldRadius world13158.frame
      agent13158.frame tm13158 ≤ -em13158 := by
  apply negative_check (lo := (266887008204966483 / 390625000000000000)) (hi := (68323074100471419649 / 100000000000000000000))
    (y := (-((71593975170087744491 / 100000000000000000000)))) (u := (48873260862047751311 / 100000000000000000000))
  · norm_num [world13158, agent13158, scalar13158, tp13158, tm13158, ep13158, em13158, dsL]
  · norm_num [world13158, agent13158, scalar13158, tp13158, tm13158, ep13158, em13158, dsL]
  · norm_num [world13158, agent13158, scalar13158, tp13158, tm13158, ep13158, em13158, dsL]
  · norm_num [world13158, agent13158, scalar13158, tp13158, tm13158, ep13158, em13158, dsL]
  · norm_num [world13158, agent13158, scalar13158, tp13158, tm13158, ep13158, em13158, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13158, agent13158, tp13158, tm13158, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13158, agent13158, tp13158, tm13158, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13158, agent13158, scalar13158, tp13158, tm13158, ep13158, em13158, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13158, agent13158, tp13158, tm13158, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13158, agent13158, scalar13158, tp13158, tm13158, ep13158, em13158, dsL]

theorem tails13158 :
    exp (-((13158:ℝ)*ep13158)) ≤ scalar13158.upperTail ∧
    exp (-((13158:ℝ)*em13158)) ≤ scalar13158.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13158:ℝ)) (by norm_num [ep13158]) ?_)
      (show bp13158^8 ≤ scalar13158.upperTail by norm_num [bp13158, scalar13158])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13158, bp13158, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13158:ℝ)) (by norm_num [em13158]) ?_)
      (show bm13158^8 ≤ scalar13158.lowerTail by norm_num [bm13158, scalar13158])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13158, bm13158, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13158 :
    agent13158.root+dsL+scalar13158.worldRadius < √(1/100/aL) ∧
    2*(agent13158.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13158, agent13158, scalar13158, tp13158, tm13158, ep13158, em13158, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13158, agent13158, scalar13158, tp13158, tm13158, ep13158, em13158, dsL]

noncomputable def master13158 : MasterCertificate 13158 world13158 agent13158 :=
  master scalar13158 dsL tp13158 tm13158 ep13158 em13158
    (by norm_num [dsL]) (by norm_num [tp13158]) (by norm_num [tm13158])
    (by norm_num [ep13158]) (by norm_num [em13158])
    positive13158 negative13158 tails13158.1 tails13158.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13158.1 tailGuards13158.2

theorem preserves13158 : master13158.toScalarCertificate = scalar13158 := rfl

noncomputable def tp13159 : ℝ := (235549091 / 1000000000)
noncomputable def tm13159 : ℝ := (-((15372291 / 25000000)))
noncomputable def ep13159 : ℝ := (52569981012301643 / 100000000000000000000)
noncomputable def em13159 : ℝ := (51100313257819981 / 100000000000000000000)
noncomputable def bp13159 : ℝ := (42117347515289701973 / 100000000000000000000)
noncomputable def bm13159 : ℝ := (21573953438511480591 / 50000000000000000000)

theorem positive13159 :
    Eplus aL (agent13159.root+dsL) scalar13159.worldRadius world13159.frame
      agent13159.frame tp13159 ≤ -ep13159 := by
  apply positive_check (eT := (115710609884657575927 / 100000000000000000000)) (y := (4769452118584035451 / 12500000000000000000)) (u := (18307024044907415053 / 12500000000000000000))
  · norm_num [world13159, agent13159, scalar13159, tp13159, tm13159, ep13159, em13159, dsL]
  · norm_num [world13159, agent13159, scalar13159, tp13159, tm13159, ep13159, em13159, dsL]
  · norm_num [world13159, agent13159, scalar13159, tp13159, tm13159, ep13159, em13159, dsL]
  · norm_num [world13159, agent13159, scalar13159, tp13159, tm13159, ep13159, em13159, dsL]
  · norm_num [world13159, agent13159, scalar13159, tp13159, tm13159, ep13159, em13159, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13159, agent13159, tp13159, tm13159, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13159, agent13159, scalar13159, tp13159, tm13159, ep13159, em13159, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13159, agent13159, tp13159, tm13159, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13159, agent13159, scalar13159, tp13159, tm13159, ep13159, em13159, dsL]

theorem negative13159 :
    Eminus aL (agent13159.root+dsL) scalar13159.worldRadius world13159.frame
      agent13159.frame tm13159 ≤ -em13159 := by
  apply negative_check (lo := (68322979705688561741 / 100000000000000000000)) (hi := (34161489852844280871 / 50000000000000000000))
    (y := (-((8949233571829764251 / 12500000000000000000)))) (u := (610916411984346033 / 1250000000000000000))
  · norm_num [world13159, agent13159, scalar13159, tp13159, tm13159, ep13159, em13159, dsL]
  · norm_num [world13159, agent13159, scalar13159, tp13159, tm13159, ep13159, em13159, dsL]
  · norm_num [world13159, agent13159, scalar13159, tp13159, tm13159, ep13159, em13159, dsL]
  · norm_num [world13159, agent13159, scalar13159, tp13159, tm13159, ep13159, em13159, dsL]
  · norm_num [world13159, agent13159, scalar13159, tp13159, tm13159, ep13159, em13159, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13159, agent13159, tp13159, tm13159, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13159, agent13159, tp13159, tm13159, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13159, agent13159, scalar13159, tp13159, tm13159, ep13159, em13159, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13159, agent13159, tp13159, tm13159, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13159, agent13159, scalar13159, tp13159, tm13159, ep13159, em13159, dsL]

theorem tails13159 :
    exp (-((13159:ℝ)*ep13159)) ≤ scalar13159.upperTail ∧
    exp (-((13159:ℝ)*em13159)) ≤ scalar13159.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13159:ℝ)) (by norm_num [ep13159]) ?_)
      (show bp13159^8 ≤ scalar13159.upperTail by norm_num [bp13159, scalar13159])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13159, bp13159, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13159:ℝ)) (by norm_num [em13159]) ?_)
      (show bm13159^8 ≤ scalar13159.lowerTail by norm_num [bm13159, scalar13159])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13159, bm13159, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13159 :
    agent13159.root+dsL+scalar13159.worldRadius < √(1/100/aL) ∧
    2*(agent13159.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13159, agent13159, scalar13159, tp13159, tm13159, ep13159, em13159, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13159, agent13159, scalar13159, tp13159, tm13159, ep13159, em13159, dsL]

noncomputable def master13159 : MasterCertificate 13159 world13159 agent13159 :=
  master scalar13159 dsL tp13159 tm13159 ep13159 em13159
    (by norm_num [dsL]) (by norm_num [tp13159]) (by norm_num [tm13159])
    (by norm_num [ep13159]) (by norm_num [em13159])
    positive13159 negative13159 tails13159.1 tails13159.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13159.1 tailGuards13159.2

theorem preserves13159 : master13159.toScalarCertificate = scalar13159 := rfl

noncomputable def tp13160 : ℝ := (2355632293 / 10000000000)
noncomputable def tm13160 : ℝ := (-((3074639951 / 5000000000)))
noncomputable def ep13160 : ℝ := (52573421680247127 / 100000000000000000000)
noncomputable def em13160 : ℝ := (25551774733992187 / 50000000000000000000)
noncomputable def bp13160 : ℝ := (42112196395883532673 / 100000000000000000000)
noncomputable def bm13160 : ℝ := (43142854076271253123 / 100000000000000000000)

theorem positive13160 :
    Eplus aL (agent13160.root+dsL) scalar13160.worldRadius world13160.frame
      agent13160.frame tp13160 ≤ -ep13160 := by
  apply positive_check (eT := (57855636146372910403 / 50000000000000000000)) (y := (476944264602446123 / 1250000000000000000)) (u := (73228040687050401019 / 50000000000000000000))
  · norm_num [world13160, agent13160, scalar13160, tp13160, tm13160, ep13160, em13160, dsL]
  · norm_num [world13160, agent13160, scalar13160, tp13160, tm13160, ep13160, em13160, dsL]
  · norm_num [world13160, agent13160, scalar13160, tp13160, tm13160, ep13160, em13160, dsL]
  · norm_num [world13160, agent13160, scalar13160, tp13160, tm13160, ep13160, em13160, dsL]
  · norm_num [world13160, agent13160, scalar13160, tp13160, tm13160, ep13160, em13160, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13160, agent13160, tp13160, tm13160, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13160, agent13160, scalar13160, tp13160, tm13160, ep13160, em13160, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13160, agent13160, tp13160, tm13160, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13160, agent13160, scalar13160, tp13160, tm13160, ep13160, em13160, dsL]

theorem negative13160 :
    Eminus aL (agent13160.root+dsL) scalar13160.worldRadius world13160.frame
      agent13160.frame tm13160 ≤ -em13160 := by
  apply negative_check (lo := (34160991138793049579 / 50000000000000000000)) (hi := (68321982277586099159 / 100000000000000000000))
    (y := (-((71591909600624361403 / 100000000000000000000)))) (u := (24437135191813013079 / 50000000000000000000))
  · norm_num [world13160, agent13160, scalar13160, tp13160, tm13160, ep13160, em13160, dsL]
  · norm_num [world13160, agent13160, scalar13160, tp13160, tm13160, ep13160, em13160, dsL]
  · norm_num [world13160, agent13160, scalar13160, tp13160, tm13160, ep13160, em13160, dsL]
  · norm_num [world13160, agent13160, scalar13160, tp13160, tm13160, ep13160, em13160, dsL]
  · norm_num [world13160, agent13160, scalar13160, tp13160, tm13160, ep13160, em13160, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13160, agent13160, tp13160, tm13160, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13160, agent13160, tp13160, tm13160, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13160, agent13160, scalar13160, tp13160, tm13160, ep13160, em13160, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13160, agent13160, tp13160, tm13160, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13160, agent13160, scalar13160, tp13160, tm13160, ep13160, em13160, dsL]

theorem tails13160 :
    exp (-((13160:ℝ)*ep13160)) ≤ scalar13160.upperTail ∧
    exp (-((13160:ℝ)*em13160)) ≤ scalar13160.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13160:ℝ)) (by norm_num [ep13160]) ?_)
      (show bp13160^8 ≤ scalar13160.upperTail by norm_num [bp13160, scalar13160])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13160, bp13160, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13160:ℝ)) (by norm_num [em13160]) ?_)
      (show bm13160^8 ≤ scalar13160.lowerTail by norm_num [bm13160, scalar13160])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13160, bm13160, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13160 :
    agent13160.root+dsL+scalar13160.worldRadius < √(1/100/aL) ∧
    2*(agent13160.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13160, agent13160, scalar13160, tp13160, tm13160, ep13160, em13160, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13160, agent13160, scalar13160, tp13160, tm13160, ep13160, em13160, dsL]

noncomputable def master13160 : MasterCertificate 13160 world13160 agent13160 :=
  master scalar13160 dsL tp13160 tm13160 ep13160 em13160
    (by norm_num [dsL]) (by norm_num [tp13160]) (by norm_num [tm13160])
    (by norm_num [ep13160]) (by norm_num [em13160])
    positive13160 negative13160 tails13160.1 tails13160.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13160.1 tailGuards13160.2

theorem preserves13160 : master13160.toScalarCertificate = scalar13160 := rfl

noncomputable def tp13161 : ℝ := (294462903 / 1250000000)
noncomputable def tm13161 : ℝ := (-((3074714897 / 5000000000)))
noncomputable def ep13161 : ℝ := (3285971022223103 / 6250000000000000000)
noncomputable def em13161 : ℝ := (5110533692850223 / 10000000000000000000)
noncomputable def bp13161 : ℝ := (42107964087342103353 / 100000000000000000000)
noncomputable def bm13161 : ℝ := (21569414832863576943 / 50000000000000000000)

theorem positive13161 :
    Eplus aL (agent13161.root+dsL) scalar13161.worldRadius world13161.frame
      agent13161.frame tp13161 ≤ -ep13161 := by
  apply positive_check (eT := (23142285943083129267 / 20000000000000000000)) (y := (38156175450389642601 / 100000000000000000000)) (u := (14645701032189299103 / 10000000000000000000))
  · norm_num [world13161, agent13161, scalar13161, tp13161, tm13161, ep13161, em13161, dsL]
  · norm_num [world13161, agent13161, scalar13161, tp13161, tm13161, ep13161, em13161, dsL]
  · norm_num [world13161, agent13161, scalar13161, tp13161, tm13161, ep13161, em13161, dsL]
  · norm_num [world13161, agent13161, scalar13161, tp13161, tm13161, ep13161, em13161, dsL]
  · norm_num [world13161, agent13161, scalar13161, tp13161, tm13161, ep13161, em13161, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13161, agent13161, tp13161, tm13161, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13161, agent13161, scalar13161, tp13161, tm13161, ep13161, em13161, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13161, agent13161, tp13161, tm13161, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13161, agent13161, scalar13161, tp13161, tm13161, ep13161, em13161, dsL]

theorem negative13161 :
    Eminus aL (agent13161.root+dsL) scalar13161.worldRadius world13161.frame
      agent13161.frame tm13161 ≤ -em13161 := by
  apply negative_check (lo := (68321888911186136849 / 100000000000000000000)) (hi := (1366437778223722737 / 2000000000000000000))
    (y := (-((8948975179685790593 / 12500000000000000000)))) (u := (4887432324759915527 / 10000000000000000000))
  · norm_num [world13161, agent13161, scalar13161, tp13161, tm13161, ep13161, em13161, dsL]
  · norm_num [world13161, agent13161, scalar13161, tp13161, tm13161, ep13161, em13161, dsL]
  · norm_num [world13161, agent13161, scalar13161, tp13161, tm13161, ep13161, em13161, dsL]
  · norm_num [world13161, agent13161, scalar13161, tp13161, tm13161, ep13161, em13161, dsL]
  · norm_num [world13161, agent13161, scalar13161, tp13161, tm13161, ep13161, em13161, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13161, agent13161, tp13161, tm13161, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13161, agent13161, tp13161, tm13161, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13161, agent13161, scalar13161, tp13161, tm13161, ep13161, em13161, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13161, agent13161, tp13161, tm13161, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13161, agent13161, scalar13161, tp13161, tm13161, ep13161, em13161, dsL]

theorem tails13161 :
    exp (-((13161:ℝ)*ep13161)) ≤ scalar13161.upperTail ∧
    exp (-((13161:ℝ)*em13161)) ≤ scalar13161.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13161:ℝ)) (by norm_num [ep13161]) ?_)
      (show bp13161^8 ≤ scalar13161.upperTail by norm_num [bp13161, scalar13161])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13161, bp13161, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13161:ℝ)) (by norm_num [em13161]) ?_)
      (show bm13161^8 ≤ scalar13161.lowerTail by norm_num [bm13161, scalar13161])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13161, bm13161, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13161 :
    agent13161.root+dsL+scalar13161.worldRadius < √(1/100/aL) ∧
    2*(agent13161.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13161, agent13161, scalar13161, tp13161, tm13161, ep13161, em13161, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13161, agent13161, scalar13161, tp13161, tm13161, ep13161, em13161, dsL]

noncomputable def master13161 : MasterCertificate 13161 world13161 agent13161 :=
  master scalar13161 dsL tp13161 tm13161 ep13161 em13161
    (by norm_num [dsL]) (by norm_num [tp13161]) (by norm_num [tm13161])
    (by norm_num [ep13161]) (by norm_num [em13161])
    positive13161 negative13161 tails13161.1 tails13161.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13161.1 tailGuards13161.2

theorem preserves13161 : master13161.toScalarCertificate = scalar13161 := rfl

noncomputable def tp13162 : ℝ := (1177887041 / 5000000000)
noncomputable def tm13162 : ℝ := (-((1537394891 / 2500000000)))
noncomputable def ep13162 : ℝ := (52577650179694801 / 100000000000000000000)
noncomputable def em13162 : ℝ := (51107123623409597 / 100000000000000000000)
noncomputable def bp13162 : ℝ := (21051866285598004443 / 50000000000000000000)
noncomputable def bm13162 : ℝ := (43134805981164797149 / 100000000000000000000)

theorem positive13162 :
    Eplus aL (agent13162.root+dsL) scalar13162.worldRadius world13162.frame
      agent13162.frame tp13162 ≤ -ep13162 := by
  apply positive_check (eT := (115711586647852709257 / 100000000000000000000)) (y := (19078404282726535063 / 50000000000000000000)) (u := (146457937566222043203 / 100000000000000000000))
  · norm_num [world13162, agent13162, scalar13162, tp13162, tm13162, ep13162, em13162, dsL]
  · norm_num [world13162, agent13162, scalar13162, tp13162, tm13162, ep13162, em13162, dsL]
  · norm_num [world13162, agent13162, scalar13162, tp13162, tm13162, ep13162, em13162, dsL]
  · norm_num [world13162, agent13162, scalar13162, tp13162, tm13162, ep13162, em13162, dsL]
  · norm_num [world13162, agent13162, scalar13162, tp13162, tm13162, ep13162, em13162, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13162, agent13162, tp13162, tm13162, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13162, agent13162, scalar13162, tp13162, tm13162, ep13162, em13162, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13162, agent13162, tp13162, tm13162, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13162, agent13162, scalar13162, tp13162, tm13162, ep13162, em13162, dsL]

theorem negative13162 :
    Eminus aL (agent13162.root+dsL) scalar13162.worldRadius world13162.frame
      agent13162.frame tm13162 ≤ -em13162 := by
  apply negative_check (lo := (68321796004477000899 / 100000000000000000000)) (hi := (683217960044770009 / 1000000000000000000))
    (y := (-((17897923066287692867 / 25000000000000000000)))) (u := (9774875320973691243 / 20000000000000000000))
  · norm_num [world13162, agent13162, scalar13162, tp13162, tm13162, ep13162, em13162, dsL]
  · norm_num [world13162, agent13162, scalar13162, tp13162, tm13162, ep13162, em13162, dsL]
  · norm_num [world13162, agent13162, scalar13162, tp13162, tm13162, ep13162, em13162, dsL]
  · norm_num [world13162, agent13162, scalar13162, tp13162, tm13162, ep13162, em13162, dsL]
  · norm_num [world13162, agent13162, scalar13162, tp13162, tm13162, ep13162, em13162, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13162, agent13162, tp13162, tm13162, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13162, agent13162, tp13162, tm13162, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13162, agent13162, scalar13162, tp13162, tm13162, ep13162, em13162, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13162, agent13162, tp13162, tm13162, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13162, agent13162, scalar13162, tp13162, tm13162, ep13162, em13162, dsL]

theorem tails13162 :
    exp (-((13162:ℝ)*ep13162)) ≤ scalar13162.upperTail ∧
    exp (-((13162:ℝ)*em13162)) ≤ scalar13162.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13162:ℝ)) (by norm_num [ep13162]) ?_)
      (show bp13162^8 ≤ scalar13162.upperTail by norm_num [bp13162, scalar13162])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13162, bp13162, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13162:ℝ)) (by norm_num [em13162]) ?_)
      (show bm13162^8 ≤ scalar13162.lowerTail by norm_num [bm13162, scalar13162])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13162, bm13162, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13162 :
    agent13162.root+dsL+scalar13162.worldRadius < √(1/100/aL) ∧
    2*(agent13162.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13162, agent13162, scalar13162, tp13162, tm13162, ep13162, em13162, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13162, agent13162, scalar13162, tp13162, tm13162, ep13162, em13162, dsL]

noncomputable def master13162 : MasterCertificate 13162 world13162 agent13162 :=
  master scalar13162 dsL tp13162 tm13162 ep13162 em13162
    (by norm_num [dsL]) (by norm_num [tp13162]) (by norm_num [tm13162])
    (by norm_num [ep13162]) (by norm_num [em13162])
    positive13162 negative13162 tails13162.1 tails13162.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13162.1 tailGuards13162.2

theorem preserves13162 : master13162.toScalarCertificate = scalar13162 := rfl

noncomputable def tp13163 : ℝ := (1177922497 / 5000000000)
noncomputable def tm13163 : ℝ := (-((768716171 / 1250000000)))
noncomputable def ep13163 : ℝ := (52579762728615903 / 100000000000000000000)
noncomputable def em13163 : ℝ := (25554454554325217 / 50000000000000000000)
noncomputable def bp13163 : ℝ := (4209950214113340109 / 10000000000000000000)
noncomputable def bm13163 : ℝ := (43130783337705093439 / 100000000000000000000)

theorem positive13163 :
    Eplus aL (agent13163.root+dsL) scalar13163.worldRadius world13163.frame
      agent13163.frame tp13163 ≤ -ep13163 := by
  apply positive_check (eT := (115711744000393097977 / 100000000000000000000)) (y := (38157443181097428413 / 100000000000000000000)) (u := (146458867014155450817 / 100000000000000000000))
  · norm_num [world13163, agent13163, scalar13163, tp13163, tm13163, ep13163, em13163, dsL]
  · norm_num [world13163, agent13163, scalar13163, tp13163, tm13163, ep13163, em13163, dsL]
  · norm_num [world13163, agent13163, scalar13163, tp13163, tm13163, ep13163, em13163, dsL]
  · norm_num [world13163, agent13163, scalar13163, tp13163, tm13163, ep13163, em13163, dsL]
  · norm_num [world13163, agent13163, scalar13163, tp13163, tm13163, ep13163, em13163, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13163, agent13163, tp13163, tm13163, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13163, agent13163, scalar13163, tp13163, tm13163, ep13163, em13163, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13163, agent13163, tp13163, tm13163, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13163, agent13163, scalar13163, tp13163, tm13163, ep13163, em13163, dsL]

theorem negative13163 :
    Eminus aL (agent13163.root+dsL) scalar13163.worldRadius world13163.frame
      agent13163.frame tm13163 ≤ -em13163 := by
  apply negative_check (lo := (4270106431075073297 / 6250000000000000000)) (hi := (68321702897201172753 / 100000000000000000000))
    (y := (-((71591584433066473497 / 100000000000000000000)))) (u := (48874429307155851867 / 100000000000000000000))
  · norm_num [world13163, agent13163, scalar13163, tp13163, tm13163, ep13163, em13163, dsL]
  · norm_num [world13163, agent13163, scalar13163, tp13163, tm13163, ep13163, em13163, dsL]
  · norm_num [world13163, agent13163, scalar13163, tp13163, tm13163, ep13163, em13163, dsL]
  · norm_num [world13163, agent13163, scalar13163, tp13163, tm13163, ep13163, em13163, dsL]
  · norm_num [world13163, agent13163, scalar13163, tp13163, tm13163, ep13163, em13163, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13163, agent13163, tp13163, tm13163, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13163, agent13163, tp13163, tm13163, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13163, agent13163, scalar13163, tp13163, tm13163, ep13163, em13163, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13163, agent13163, tp13163, tm13163, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13163, agent13163, scalar13163, tp13163, tm13163, ep13163, em13163, dsL]

theorem tails13163 :
    exp (-((13163:ℝ)*ep13163)) ≤ scalar13163.upperTail ∧
    exp (-((13163:ℝ)*em13163)) ≤ scalar13163.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13163:ℝ)) (by norm_num [ep13163]) ?_)
      (show bp13163^8 ≤ scalar13163.upperTail by norm_num [bp13163, scalar13163])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13163, bp13163, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13163:ℝ)) (by norm_num [em13163]) ?_)
      (show bm13163^8 ≤ scalar13163.lowerTail by norm_num [bm13163, scalar13163])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13163, bm13163, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13163 :
    agent13163.root+dsL+scalar13163.worldRadius < √(1/100/aL) ∧
    2*(agent13163.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13163, agent13163, scalar13163, tp13163, tm13163, ep13163, em13163, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13163, agent13163, scalar13163, tp13163, tm13163, ep13163, em13163, dsL]

noncomputable def master13163 : MasterCertificate 13163 world13163 agent13163 :=
  master scalar13163 dsL tp13163 tm13163 ep13163 em13163
    (by norm_num [dsL]) (by norm_num [tp13163]) (by norm_num [tm13163])
    (by norm_num [ep13163]) (by norm_num [em13163])
    positive13163 negative13163 tails13163.1 tails13163.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13163.1 tailGuards13163.2

theorem preserves13163 : master13163.toScalarCertificate = scalar13163 := rfl

noncomputable def tp13164 : ℝ := (2355915797 / 10000000000)
noncomputable def tm13164 : ℝ := (-((768734877 / 1250000000)))
noncomputable def ep13164 : ℝ := (5258187394661987 / 10000000000000000000)
noncomputable def em13164 : ℝ := (51110693383590537 / 100000000000000000000)
noncomputable def bp13164 : ℝ := (10523818208926214981 / 25000000000000000000)
noncomputable def bm13164 : ℝ := (43126761735772461507 / 100000000000000000000)

theorem positive13164 :
    Eplus aL (agent13164.root+dsL) scalar13164.worldRadius world13164.frame
      agent13164.frame tp13164 ≤ -ep13164 := by
  apply positive_check (eT := (11571190060464887969 / 10000000000000000000)) (y := (19079038026107316083 / 50000000000000000000)) (u := (73229896956478200783 / 50000000000000000000))
  · norm_num [world13164, agent13164, scalar13164, tp13164, tm13164, ep13164, em13164, dsL]
  · norm_num [world13164, agent13164, scalar13164, tp13164, tm13164, ep13164, em13164, dsL]
  · norm_num [world13164, agent13164, scalar13164, tp13164, tm13164, ep13164, em13164, dsL]
  · norm_num [world13164, agent13164, scalar13164, tp13164, tm13164, ep13164, em13164, dsL]
  · norm_num [world13164, agent13164, scalar13164, tp13164, tm13164, ep13164, em13164, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13164, agent13164, tp13164, tm13164, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13164, agent13164, scalar13164, tp13164, tm13164, ep13164, em13164, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13164, agent13164, tp13164, tm13164, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13164, agent13164, scalar13164, tp13164, tm13164, ep13164, em13164, dsL]

theorem negative13164 :
    Eminus aL (agent13164.root+dsL) scalar13164.worldRadius world13164.frame
      agent13164.frame tm13164 ≤ -em13164 := by
  apply negative_check (lo := (68321610393539497163 / 100000000000000000000)) (hi := (17080402598384874291 / 25000000000000000000))
    (y := (-((35795737569311524657 / 50000000000000000000)))) (u := (9774896544844106161 / 20000000000000000000))
  · norm_num [world13164, agent13164, scalar13164, tp13164, tm13164, ep13164, em13164, dsL]
  · norm_num [world13164, agent13164, scalar13164, tp13164, tm13164, ep13164, em13164, dsL]
  · norm_num [world13164, agent13164, scalar13164, tp13164, tm13164, ep13164, em13164, dsL]
  · norm_num [world13164, agent13164, scalar13164, tp13164, tm13164, ep13164, em13164, dsL]
  · norm_num [world13164, agent13164, scalar13164, tp13164, tm13164, ep13164, em13164, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13164, agent13164, tp13164, tm13164, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13164, agent13164, tp13164, tm13164, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13164, agent13164, scalar13164, tp13164, tm13164, ep13164, em13164, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13164, agent13164, tp13164, tm13164, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13164, agent13164, scalar13164, tp13164, tm13164, ep13164, em13164, dsL]

theorem tails13164 :
    exp (-((13164:ℝ)*ep13164)) ≤ scalar13164.upperTail ∧
    exp (-((13164:ℝ)*em13164)) ≤ scalar13164.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13164:ℝ)) (by norm_num [ep13164]) ?_)
      (show bp13164^8 ≤ scalar13164.upperTail by norm_num [bp13164, scalar13164])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13164, bp13164, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13164:ℝ)) (by norm_num [em13164]) ?_)
      (show bm13164^8 ≤ scalar13164.lowerTail by norm_num [bm13164, scalar13164])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13164, bm13164, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13164 :
    agent13164.root+dsL+scalar13164.worldRadius < √(1/100/aL) ∧
    2*(agent13164.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13164, agent13164, scalar13164, tp13164, tm13164, ep13164, em13164, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13164, agent13164, scalar13164, tp13164, tm13164, ep13164, em13164, dsL]

noncomputable def master13164 : MasterCertificate 13164 world13164 agent13164 :=
  master scalar13164 dsL tp13164 tm13164 ep13164 em13164
    (by norm_num [dsL]) (by norm_num [tp13164]) (by norm_num [tm13164])
    (by norm_num [ep13164]) (by norm_num [em13164])
    positive13164 negative13164 tails13164.1 tails13164.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13164.1 tailGuards13164.2

theorem preserves13164 : master13164.toScalarCertificate = scalar13164 := rfl

noncomputable def tp13165 : ℝ := (471197319 / 2000000000)
noncomputable def tm13165 : ℝ := (-((1230005751 / 2000000000)))
noncomputable def ep13165 : ℝ := (52583984033993333 / 100000000000000000000)
noncomputable def em13165 : ℝ := (51112476599701831 / 100000000000000000000)
noncomputable def bp13165 : ℝ := (10522761129034056189 / 25000000000000000000)
noncomputable def bm13165 : ℝ := (43122741067850903157 / 100000000000000000000)

theorem positive13165 :
    Eplus aL (agent13165.root+dsL) scalar13165.worldRadius world13165.frame
      agent13165.frame tp13165 ≤ -ep13165 := by
  apply positive_check (eT := (57856028603042310201 / 50000000000000000000)) (y := (19079354622149986151 / 50000000000000000000)) (u := (146460721287715692571 / 100000000000000000000))
  · norm_num [world13165, agent13165, scalar13165, tp13165, tm13165, ep13165, em13165, dsL]
  · norm_num [world13165, agent13165, scalar13165, tp13165, tm13165, ep13165, em13165, dsL]
  · norm_num [world13165, agent13165, scalar13165, tp13165, tm13165, ep13165, em13165, dsL]
  · norm_num [world13165, agent13165, scalar13165, tp13165, tm13165, ep13165, em13165, dsL]
  · norm_num [world13165, agent13165, scalar13165, tp13165, tm13165, ep13165, em13165, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13165, agent13165, tp13165, tm13165, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13165, agent13165, scalar13165, tp13165, tm13165, ep13165, em13165, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13165, agent13165, tp13165, tm13165, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13165, agent13165, scalar13165, tp13165, tm13165, ep13165, em13165, dsL]

theorem negative13165 :
    Eminus aL (agent13165.root+dsL) scalar13165.worldRadius world13165.frame
      agent13165.frame tm13165 ≤ -em13165 := by
  apply negative_check (lo := (6832151744814440409 / 10000000000000000000)) (hi := (68321517448144404091 / 100000000000000000000))
    (y := (-((71591367443286279393 / 100000000000000000000)))) (u := (6109316919973454779 / 12500000000000000000))
  · norm_num [world13165, agent13165, scalar13165, tp13165, tm13165, ep13165, em13165, dsL]
  · norm_num [world13165, agent13165, scalar13165, tp13165, tm13165, ep13165, em13165, dsL]
  · norm_num [world13165, agent13165, scalar13165, tp13165, tm13165, ep13165, em13165, dsL]
  · norm_num [world13165, agent13165, scalar13165, tp13165, tm13165, ep13165, em13165, dsL]
  · norm_num [world13165, agent13165, scalar13165, tp13165, tm13165, ep13165, em13165, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13165, agent13165, tp13165, tm13165, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13165, agent13165, tp13165, tm13165, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13165, agent13165, scalar13165, tp13165, tm13165, ep13165, em13165, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13165, agent13165, tp13165, tm13165, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13165, agent13165, scalar13165, tp13165, tm13165, ep13165, em13165, dsL]

theorem tails13165 :
    exp (-((13165:ℝ)*ep13165)) ≤ scalar13165.upperTail ∧
    exp (-((13165:ℝ)*em13165)) ≤ scalar13165.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13165:ℝ)) (by norm_num [ep13165]) ?_)
      (show bp13165^8 ≤ scalar13165.upperTail by norm_num [bp13165, scalar13165])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13165, bp13165, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13165:ℝ)) (by norm_num [em13165]) ?_)
      (show bm13165^8 ≤ scalar13165.lowerTail by norm_num [bm13165, scalar13165])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13165, bm13165, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13165 :
    agent13165.root+dsL+scalar13165.worldRadius < √(1/100/aL) ∧
    2*(agent13165.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13165, agent13165, scalar13165, tp13165, tm13165, ep13165, em13165, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13165, agent13165, scalar13165, tp13165, tm13165, ep13165, em13165, dsL]

noncomputable def master13165 : MasterCertificate 13165 world13165 agent13165 :=
  master scalar13165 dsL tp13165 tm13165 ep13165 em13165
    (by norm_num [dsL]) (by norm_num [tp13165]) (by norm_num [tm13165])
    (by norm_num [ep13165]) (by norm_num [em13165])
    positive13165 negative13165 tails13165.1 tails13165.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13165.1 tailGuards13165.2

theorem preserves13165 : master13165.toScalarCertificate = scalar13165 := rfl

noncomputable def tp13166 : ℝ := (117802869 / 500000000)
noncomputable def tm13166 : ℝ := (-((1537544547 / 2500000000)))
noncomputable def ep13166 : ℝ := (5258609347044379 / 10000000000000000000)
noncomputable def em13166 : ℝ := (12778564800433207 / 25000000000000000000)
noncomputable def bp13166 : ℝ := (657606513283246693 / 1562500000000000000)
noncomputable def bm13166 : ℝ := (43118721018315043717 / 100000000000000000000)

theorem positive13166 :
    Eplus aL (agent13166.root+dsL) scalar13166.worldRadius world13166.frame
      agent13166.frame tp13166 ≤ -ep13166 := by
  apply positive_check (eT := (115712213747396234831 / 100000000000000000000)) (y := (38159342568638695681 / 100000000000000000000)) (u := (146461648862047551389 / 100000000000000000000))
  · norm_num [world13166, agent13166, scalar13166, tp13166, tm13166, ep13166, em13166, dsL]
  · norm_num [world13166, agent13166, scalar13166, tp13166, tm13166, ep13166, em13166, dsL]
  · norm_num [world13166, agent13166, scalar13166, tp13166, tm13166, ep13166, em13166, dsL]
  · norm_num [world13166, agent13166, scalar13166, tp13166, tm13166, ep13166, em13166, dsL]
  · norm_num [world13166, agent13166, scalar13166, tp13166, tm13166, ep13166, em13166, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13166, agent13166, tp13166, tm13166, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13166, agent13166, scalar13166, tp13166, tm13166, ep13166, em13166, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13166, agent13166, tp13166, tm13166, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13166, agent13166, scalar13166, tp13166, tm13166, ep13166, em13166, dsL]

theorem negative13166 :
    Eminus aL (agent13166.root+dsL) scalar13166.worldRadius world13166.frame
      agent13166.frame tm13166 ≤ -em13166 := by
  apply negative_check (lo := (68321425741050616173 / 100000000000000000000)) (hi := (34160712870525308087 / 50000000000000000000))
    (y := (-((4474453604858241771 / 6250000000000000000)))) (u := (48874589007221784927 / 100000000000000000000))
  · norm_num [world13166, agent13166, scalar13166, tp13166, tm13166, ep13166, em13166, dsL]
  · norm_num [world13166, agent13166, scalar13166, tp13166, tm13166, ep13166, em13166, dsL]
  · norm_num [world13166, agent13166, scalar13166, tp13166, tm13166, ep13166, em13166, dsL]
  · norm_num [world13166, agent13166, scalar13166, tp13166, tm13166, ep13166, em13166, dsL]
  · norm_num [world13166, agent13166, scalar13166, tp13166, tm13166, ep13166, em13166, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13166, agent13166, tp13166, tm13166, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13166, agent13166, tp13166, tm13166, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13166, agent13166, scalar13166, tp13166, tm13166, ep13166, em13166, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13166, agent13166, tp13166, tm13166, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13166, agent13166, scalar13166, tp13166, tm13166, ep13166, em13166, dsL]

theorem tails13166 :
    exp (-((13166:ℝ)*ep13166)) ≤ scalar13166.upperTail ∧
    exp (-((13166:ℝ)*em13166)) ≤ scalar13166.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13166:ℝ)) (by norm_num [ep13166]) ?_)
      (show bp13166^8 ≤ scalar13166.upperTail by norm_num [bp13166, scalar13166])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13166, bp13166, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13166:ℝ)) (by norm_num [em13166]) ?_)
      (show bm13166^8 ≤ scalar13166.lowerTail by norm_num [bm13166, scalar13166])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13166, bm13166, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13166 :
    agent13166.root+dsL+scalar13166.worldRadius < √(1/100/aL) ∧
    2*(agent13166.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13166, agent13166, scalar13166, tp13166, tm13166, ep13166, em13166, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13166, agent13166, scalar13166, tp13166, tm13166, ep13166, em13166, dsL]

noncomputable def master13166 : MasterCertificate 13166 world13166 agent13166 :=
  master scalar13166 dsL tp13166 tm13166 ep13166 em13166
    (by norm_num [dsL]) (by norm_num [tp13166]) (by norm_num [tm13166])
    (by norm_num [ep13166]) (by norm_num [em13166])
    positive13166 negative13166 tails13166.1 tails13166.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13166.1 tailGuards13166.2

theorem preserves13166 : master13166.toScalarCertificate = scalar13166 := rfl

noncomputable def tp13167 : ℝ := (2356128099 / 10000000000)
noncomputable def tm13167 : ℝ := (-((1537581889 / 2500000000)))
noncomputable def ep13167 : ℝ := (52588201436251643 / 100000000000000000000)
noncomputable def em13167 : ℝ := (25558020223441777 / 50000000000000000000)
noncomputable def bp13167 : ℝ := (10520647601357610743 / 25000000000000000000)
noncomputable def bm13167 : ℝ := (43114702114262444231 / 100000000000000000000)

theorem positive13167 :
    Eplus aL (agent13167.root+dsL) scalar13167.worldRadius world13167.frame
      agent13167.frame tp13167 ≤ -ep13167 := by
  apply positive_check (eT := (1808005778885623577 / 1562500000000000000)) (y := (38159975049045368743 / 100000000000000000000)) (u := (572119434399255327 / 390625000000000000))
  · norm_num [world13167, agent13167, scalar13167, tp13167, tm13167, ep13167, em13167, dsL]
  · norm_num [world13167, agent13167, scalar13167, tp13167, tm13167, ep13167, em13167, dsL]
  · norm_num [world13167, agent13167, scalar13167, tp13167, tm13167, ep13167, em13167, dsL]
  · norm_num [world13167, agent13167, scalar13167, tp13167, tm13167, ep13167, em13167, dsL]
  · norm_num [world13167, agent13167, scalar13167, tp13167, tm13167, ep13167, em13167, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13167, agent13167, tp13167, tm13167, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13167, agent13167, scalar13167, tp13167, tm13167, ep13167, em13167, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13167, agent13167, tp13167, tm13167, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13167, agent13167, scalar13167, tp13167, tm13167, ep13167, em13167, dsL]

theorem negative13167 :
    Eminus aL (agent13167.root+dsL) scalar13167.worldRadius world13167.frame
      agent13167.frame tm13167 ≤ -em13167 := by
  apply negative_check (lo := (8540166781548685441 / 12500000000000000000)) (hi := (68321334252389483529 / 100000000000000000000))
    (y := (-((8948893450686063631 / 12500000000000000000)))) (u := (24437321402303972899 / 50000000000000000000))
  · norm_num [world13167, agent13167, scalar13167, tp13167, tm13167, ep13167, em13167, dsL]
  · norm_num [world13167, agent13167, scalar13167, tp13167, tm13167, ep13167, em13167, dsL]
  · norm_num [world13167, agent13167, scalar13167, tp13167, tm13167, ep13167, em13167, dsL]
  · norm_num [world13167, agent13167, scalar13167, tp13167, tm13167, ep13167, em13167, dsL]
  · norm_num [world13167, agent13167, scalar13167, tp13167, tm13167, ep13167, em13167, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13167, agent13167, tp13167, tm13167, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13167, agent13167, tp13167, tm13167, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13167, agent13167, scalar13167, tp13167, tm13167, ep13167, em13167, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13167, agent13167, tp13167, tm13167, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13167, agent13167, scalar13167, tp13167, tm13167, ep13167, em13167, dsL]

theorem tails13167 :
    exp (-((13167:ℝ)*ep13167)) ≤ scalar13167.upperTail ∧
    exp (-((13167:ℝ)*em13167)) ≤ scalar13167.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13167:ℝ)) (by norm_num [ep13167]) ?_)
      (show bp13167^8 ≤ scalar13167.upperTail by norm_num [bp13167, scalar13167])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13167, bp13167, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13167:ℝ)) (by norm_num [em13167]) ?_)
      (show bm13167^8 ≤ scalar13167.lowerTail by norm_num [bm13167, scalar13167])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13167, bm13167, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13167 :
    agent13167.root+dsL+scalar13167.worldRadius < √(1/100/aL) ∧
    2*(agent13167.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13167, agent13167, scalar13167, tp13167, tm13167, ep13167, em13167, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13167, agent13167, scalar13167, tp13167, tm13167, ep13167, em13167, dsL]

noncomputable def master13167 : MasterCertificate 13167 world13167 agent13167 :=
  master scalar13167 dsL tp13167 tm13167 ep13167 em13167
    (by norm_num [dsL]) (by norm_num [tp13167]) (by norm_num [tm13167])
    (by norm_num [ep13167]) (by norm_num [em13167])
    positive13167 negative13167 tails13167.1 tails13167.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13167.1 tailGuards13167.2

theorem preserves13167 : master13167.toScalarCertificate = scalar13167 := rfl

noncomputable def tp13168 : ℝ := (471239759 / 2000000000)
noncomputable def tm13168 : ℝ := (-((6150476883 / 10000000000)))
noncomputable def ep13168 : ℝ := (26295154350195027 / 50000000000000000000)
noncomputable def em13168 : ℝ := (25558910513044777 / 50000000000000000000)
noncomputable def bp13168 : ℝ := (42078364649395169413 / 100000000000000000000)
noncomputable def bm13168 : ℝ := (43110683865372873701 / 100000000000000000000)

theorem positive13168 :
    Eplus aL (agent13168.root+dsL) scalar13168.worldRadius world13168.frame
      agent13168.frame tp13168 ≤ -ep13168 := by
  apply positive_check (eT := (57856262909075134859 / 50000000000000000000)) (y := (19080303692724805321 / 50000000000000000000)) (u := (14646350134531913703 / 10000000000000000000))
  · norm_num [world13168, agent13168, scalar13168, tp13168, tm13168, ep13168, em13168, dsL]
  · norm_num [world13168, agent13168, scalar13168, tp13168, tm13168, ep13168, em13168, dsL]
  · norm_num [world13168, agent13168, scalar13168, tp13168, tm13168, ep13168, em13168, dsL]
  · norm_num [world13168, agent13168, scalar13168, tp13168, tm13168, ep13168, em13168, dsL]
  · norm_num [world13168, agent13168, scalar13168, tp13168, tm13168, ep13168, em13168, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13168, agent13168, tp13168, tm13168, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13168, agent13168, scalar13168, tp13168, tm13168, ep13168, em13168, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13168, agent13168, tp13168, tm13168, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13168, agent13168, scalar13168, tp13168, tm13168, ep13168, em13168, dsL]

theorem negative13168 :
    Eminus aL (agent13168.root+dsL) scalar13168.worldRadius world13168.frame
      agent13168.frame tm13168 ≤ -em13168 := by
  apply negative_check (lo := (4270077680036016841 / 6250000000000000000)) (hi := (68321242880576269457 / 100000000000000000000))
    (y := (-((71591037586717009629 / 100000000000000000000)))) (u := (48874696575919113419 / 100000000000000000000))
  · norm_num [world13168, agent13168, scalar13168, tp13168, tm13168, ep13168, em13168, dsL]
  · norm_num [world13168, agent13168, scalar13168, tp13168, tm13168, ep13168, em13168, dsL]
  · norm_num [world13168, agent13168, scalar13168, tp13168, tm13168, ep13168, em13168, dsL]
  · norm_num [world13168, agent13168, scalar13168, tp13168, tm13168, ep13168, em13168, dsL]
  · norm_num [world13168, agent13168, scalar13168, tp13168, tm13168, ep13168, em13168, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13168, agent13168, tp13168, tm13168, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13168, agent13168, tp13168, tm13168, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13168, agent13168, scalar13168, tp13168, tm13168, ep13168, em13168, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13168, agent13168, tp13168, tm13168, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13168, agent13168, scalar13168, tp13168, tm13168, ep13168, em13168, dsL]

theorem tails13168 :
    exp (-((13168:ℝ)*ep13168)) ≤ scalar13168.upperTail ∧
    exp (-((13168:ℝ)*em13168)) ≤ scalar13168.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13168:ℝ)) (by norm_num [ep13168]) ?_)
      (show bp13168^8 ≤ scalar13168.upperTail by norm_num [bp13168, scalar13168])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13168, bp13168, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13168:ℝ)) (by norm_num [em13168]) ?_)
      (show bm13168^8 ≤ scalar13168.lowerTail by norm_num [bm13168, scalar13168])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13168, bm13168, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13168 :
    agent13168.root+dsL+scalar13168.worldRadius < √(1/100/aL) ∧
    2*(agent13168.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13168, agent13168, scalar13168, tp13168, tm13168, ep13168, em13168, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13168, agent13168, scalar13168, tp13168, tm13168, ep13168, em13168, dsL]

noncomputable def master13168 : MasterCertificate 13168 world13168 agent13168 :=
  master scalar13168 dsL tp13168 tm13168 ep13168 em13168
    (by norm_num [dsL]) (by norm_num [tp13168]) (by norm_num [tm13168])
    (by norm_num [ep13168]) (by norm_num [em13168])
    positive13168 negative13168 tails13168.1 tails13168.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13168.1 tailGuards13168.2

theorem preserves13168 : master13168.toScalarCertificate = scalar13168 := rfl

noncomputable def tp13169 : ℝ := (3681671 / 15625000)
noncomputable def tm13169 : ℝ := (-((384414139 / 625000000)))
noncomputable def ep13169 : ℝ := (13148103672320193 / 25000000000000000000)
noncomputable def em13169 : ℝ := (6389950056404293 / 12500000000000000000)
noncomputable def bp13169 : ℝ := (8414827995853339487 / 20000000000000000000)
noncomputable def bm13169 : ℝ := (43106666618003006713 / 100000000000000000000)

theorem positive13169 :
    Eplus aL (agent13169.root+dsL) scalar13169.worldRadius world13169.frame
      agent13169.frame tp13169 ≤ -ep13169 := by
  apply positive_check (eT := (115712681455121831781 / 100000000000000000000)) (y := (1526449563540388021 / 4000000000000000000)) (u := (146464426562661360253 / 100000000000000000000))
  · norm_num [world13169, agent13169, scalar13169, tp13169, tm13169, ep13169, em13169, dsL]
  · norm_num [world13169, agent13169, scalar13169, tp13169, tm13169, ep13169, em13169, dsL]
  · norm_num [world13169, agent13169, scalar13169, tp13169, tm13169, ep13169, em13169, dsL]
  · norm_num [world13169, agent13169, scalar13169, tp13169, tm13169, ep13169, em13169, dsL]
  · norm_num [world13169, agent13169, scalar13169, tp13169, tm13169, ep13169, em13169, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13169, agent13169, tp13169, tm13169, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13169, agent13169, scalar13169, tp13169, tm13169, ep13169, em13169, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13169, agent13169, tp13169, tm13169, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13169, agent13169, scalar13169, tp13169, tm13169, ep13169, em13169, dsL]

theorem negative13169 :
    Eminus aL (agent13169.root+dsL) scalar13169.worldRadius world13169.frame
      agent13169.frame tm13169 ≤ -em13169 := by
  apply negative_check (lo := (34160575696448806563 / 50000000000000000000)) (hi := (68321151392897613127 / 100000000000000000000))
    (y := (-((35795464070496608571 / 50000000000000000000)))) (u := (48874750067213804277 / 100000000000000000000))
  · norm_num [world13169, agent13169, scalar13169, tp13169, tm13169, ep13169, em13169, dsL]
  · norm_num [world13169, agent13169, scalar13169, tp13169, tm13169, ep13169, em13169, dsL]
  · norm_num [world13169, agent13169, scalar13169, tp13169, tm13169, ep13169, em13169, dsL]
  · norm_num [world13169, agent13169, scalar13169, tp13169, tm13169, ep13169, em13169, dsL]
  · norm_num [world13169, agent13169, scalar13169, tp13169, tm13169, ep13169, em13169, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13169, agent13169, tp13169, tm13169, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13169, agent13169, tp13169, tm13169, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13169, agent13169, scalar13169, tp13169, tm13169, ep13169, em13169, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13169, agent13169, tp13169, tm13169, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13169, agent13169, scalar13169, tp13169, tm13169, ep13169, em13169, dsL]

theorem tails13169 :
    exp (-((13169:ℝ)*ep13169)) ≤ scalar13169.upperTail ∧
    exp (-((13169:ℝ)*em13169)) ≤ scalar13169.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13169:ℝ)) (by norm_num [ep13169]) ?_)
      (show bp13169^8 ≤ scalar13169.upperTail by norm_num [bp13169, scalar13169])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13169, bp13169, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13169:ℝ)) (by norm_num [em13169]) ?_)
      (show bm13169^8 ≤ scalar13169.lowerTail by norm_num [bm13169, scalar13169])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13169, bm13169, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13169 :
    agent13169.root+dsL+scalar13169.worldRadius < √(1/100/aL) ∧
    2*(agent13169.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13169, agent13169, scalar13169, tp13169, tm13169, ep13169, em13169, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13169, agent13169, scalar13169, tp13169, tm13169, ep13169, em13169, dsL]

noncomputable def master13169 : MasterCertificate 13169 world13169 agent13169 :=
  master scalar13169 dsL tp13169 tm13169 ep13169 em13169
    (by norm_num [dsL]) (by norm_num [tp13169]) (by norm_num [tm13169])
    (by norm_num [ep13169]) (by norm_num [em13169])
    positive13169 negative13169 tails13169.1 tails13169.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13169.1 tailGuards13169.2

theorem preserves13169 : master13169.toScalarCertificate = scalar13169 := rfl

noncomputable def tp13170 : ℝ := (2356410471 / 10000000000)
noncomputable def tm13170 : ℝ := (-((1230197763 / 2000000000)))
noncomputable def ep13170 : ℝ := (26297921456889353 / 50000000000000000000)
noncomputable def em13170 : ℝ := (51122824876496661 / 100000000000000000000)
noncomputable def bp13170 : ℝ := (42068999773138121783 / 100000000000000000000)
noncomputable def bm13170 : ℝ := (43101624226048373017 / 100000000000000000000)

theorem positive13170 :
    Eplus aL (agent13170.root+dsL) scalar13170.worldRadius world13170.frame
      agent13170.frame tp13170 ≤ -ep13170 := by
  apply positive_check (eT := (185141346503782403 / 160000000000000000)) (y := (9540290529446585303 / 25000000000000000000)) (u := (146464313827976157259 / 100000000000000000000))
  · norm_num [world13170, agent13170, scalar13170, tp13170, tm13170, ep13170, em13170, dsL]
  · norm_num [world13170, agent13170, scalar13170, tp13170, tm13170, ep13170, em13170, dsL]
  · norm_num [world13170, agent13170, scalar13170, tp13170, tm13170, ep13170, em13170, dsL]
  · norm_num [world13170, agent13170, scalar13170, tp13170, tm13170, ep13170, em13170, dsL]
  · norm_num [world13170, agent13170, scalar13170, tp13170, tm13170, ep13170, em13170, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13170, agent13170, tp13170, tm13170, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13170, agent13170, scalar13170, tp13170, tm13170, ep13170, em13170, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13170, agent13170, tp13170, tm13170, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13170, agent13170, scalar13170, tp13170, tm13170, ep13170, em13170, dsL]

theorem negative13170 :
    Eminus aL (agent13170.root+dsL) scalar13170.worldRadius world13170.frame
      agent13170.frame tm13170 ≤ -em13170 := by
  apply negative_check (lo := (13664031497116164729 / 20000000000000000000)) (hi := (34160078742790411823 / 50000000000000000000))
    (y := (-((71588969588927767647 / 100000000000000000000)))) (u := (48875707314014786869 / 100000000000000000000))
  · norm_num [world13170, agent13170, scalar13170, tp13170, tm13170, ep13170, em13170, dsL]
  · norm_num [world13170, agent13170, scalar13170, tp13170, tm13170, ep13170, em13170, dsL]
  · norm_num [world13170, agent13170, scalar13170, tp13170, tm13170, ep13170, em13170, dsL]
  · norm_num [world13170, agent13170, scalar13170, tp13170, tm13170, ep13170, em13170, dsL]
  · norm_num [world13170, agent13170, scalar13170, tp13170, tm13170, ep13170, em13170, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13170, agent13170, tp13170, tm13170, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13170, agent13170, tp13170, tm13170, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13170, agent13170, scalar13170, tp13170, tm13170, ep13170, em13170, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13170, agent13170, tp13170, tm13170, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13170, agent13170, scalar13170, tp13170, tm13170, ep13170, em13170, dsL]

theorem tails13170 :
    exp (-((13170:ℝ)*ep13170)) ≤ scalar13170.upperTail ∧
    exp (-((13170:ℝ)*em13170)) ≤ scalar13170.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13170:ℝ)) (by norm_num [ep13170]) ?_)
      (show bp13170^8 ≤ scalar13170.upperTail by norm_num [bp13170, scalar13170])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13170, bp13170, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13170:ℝ)) (by norm_num [em13170]) ?_)
      (show bm13170^8 ≤ scalar13170.lowerTail by norm_num [bm13170, scalar13170])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13170, bm13170, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13170 :
    agent13170.root+dsL+scalar13170.worldRadius < √(1/100/aL) ∧
    2*(agent13170.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13170, agent13170, scalar13170, tp13170, tm13170, ep13170, em13170, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13170, agent13170, scalar13170, tp13170, tm13170, ep13170, em13170, dsL]

noncomputable def master13170 : MasterCertificate 13170 world13170 agent13170 :=
  master scalar13170 dsL tp13170 tm13170 ep13170 em13170
    (by norm_num [dsL]) (by norm_num [tp13170]) (by norm_num [tm13170])
    (by norm_num [ep13170]) (by norm_num [em13170])
    positive13170 negative13170 tails13170.1 tails13170.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13170.1 tailGuards13170.2

theorem preserves13170 : master13170.toScalarCertificate = scalar13170 := rfl

noncomputable def tp13171 : ℝ := (589120269 / 2500000000)
noncomputable def tm13171 : ℝ := (-((3075568939 / 5000000000)))
noncomputable def ep13171 : ℝ := (52597947191594301 / 100000000000000000000)
noncomputable def em13171 : ℝ := (12781150674128103 / 25000000000000000000)
noncomputable def bp13171 : ℝ := (21032388357887148421 / 50000000000000000000)
noncomputable def bm13171 : ℝ := (4309760850052303051 / 10000000000000000000)

theorem positive13171 :
    Eplus aL (agent13171.root+dsL) scalar13171.worldRadius world13171.frame
      agent13171.frame tp13171 ≤ -ep13171 := by
  apply positive_check (eT := (23142699394288926911 / 20000000000000000000)) (y := (38161793826385925453 / 100000000000000000000)) (u := (73232619529282154077 / 50000000000000000000))
  · norm_num [world13171, agent13171, scalar13171, tp13171, tm13171, ep13171, em13171, dsL]
  · norm_num [world13171, agent13171, scalar13171, tp13171, tm13171, ep13171, em13171, dsL]
  · norm_num [world13171, agent13171, scalar13171, tp13171, tm13171, ep13171, em13171, dsL]
  · norm_num [world13171, agent13171, scalar13171, tp13171, tm13171, ep13171, em13171, dsL]
  · norm_num [world13171, agent13171, scalar13171, tp13171, tm13171, ep13171, em13171, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13171, agent13171, tp13171, tm13171, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13171, agent13171, scalar13171, tp13171, tm13171, ep13171, em13171, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13171, agent13171, tp13171, tm13171, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13171, agent13171, scalar13171, tp13171, tm13171, ep13171, em13171, dsL]

theorem negative13171 :
    Eminus aL (agent13171.root+dsL) scalar13171.worldRadius world13171.frame
      agent13171.frame tm13171 ≤ -em13171 := by
  apply negative_check (lo := (68320067080904259973 / 100000000000000000000)) (hi := (34160033540452129987 / 50000000000000000000))
    (y := (-((71588858989868337531 / 100000000000000000000)))) (u := (39100609096093807 / 80000000000000000))
  · norm_num [world13171, agent13171, scalar13171, tp13171, tm13171, ep13171, em13171, dsL]
  · norm_num [world13171, agent13171, scalar13171, tp13171, tm13171, ep13171, em13171, dsL]
  · norm_num [world13171, agent13171, scalar13171, tp13171, tm13171, ep13171, em13171, dsL]
  · norm_num [world13171, agent13171, scalar13171, tp13171, tm13171, ep13171, em13171, dsL]
  · norm_num [world13171, agent13171, scalar13171, tp13171, tm13171, ep13171, em13171, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13171, agent13171, tp13171, tm13171, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13171, agent13171, tp13171, tm13171, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13171, agent13171, scalar13171, tp13171, tm13171, ep13171, em13171, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13171, agent13171, tp13171, tm13171, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13171, agent13171, scalar13171, tp13171, tm13171, ep13171, em13171, dsL]

theorem tails13171 :
    exp (-((13171:ℝ)*ep13171)) ≤ scalar13171.upperTail ∧
    exp (-((13171:ℝ)*em13171)) ≤ scalar13171.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13171:ℝ)) (by norm_num [ep13171]) ?_)
      (show bp13171^8 ≤ scalar13171.upperTail by norm_num [bp13171, scalar13171])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13171, bp13171, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13171:ℝ)) (by norm_num [em13171]) ?_)
      (show bm13171^8 ≤ scalar13171.lowerTail by norm_num [bm13171, scalar13171])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13171, bm13171, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13171 :
    agent13171.root+dsL+scalar13171.worldRadius < √(1/100/aL) ∧
    2*(agent13171.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13171, agent13171, scalar13171, tp13171, tm13171, ep13171, em13171, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13171, agent13171, scalar13171, tp13171, tm13171, ep13171, em13171, dsL]

noncomputable def master13171 : MasterCertificate 13171 world13171 agent13171 :=
  master scalar13171 dsL tp13171 tm13171 ep13171 em13171
    (by norm_num [dsL]) (by norm_num [tp13171]) (by norm_num [tm13171])
    (by norm_num [ep13171]) (by norm_num [em13171])
    positive13171 negative13171 tails13171.1 tails13171.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13171.1 tailGuards13171.2

theorem preserves13171 : master13171.toScalarCertificate = scalar13171 := rfl

noncomputable def tp13172 : ℝ := (1178275787 / 5000000000)
noncomputable def tm13172 : ℝ := (-((3075643469 / 5000000000)))
noncomputable def ep13172 : ℝ := (13150012418217187 / 25000000000000000000)
noncomputable def em13172 : ℝ := (51126378873645157 / 100000000000000000000)
noncomputable def bp13172 : ℝ := (42060555105223730611 / 100000000000000000000)
noncomputable def bm13172 : ℝ := (43093594123290950363 / 100000000000000000000)

theorem positive13172 :
    Eplus aL (agent13172.root+dsL) scalar13172.worldRadius world13172.frame
      agent13172.frame tp13172 ≤ -ep13172 := by
  apply positive_check (eT := (23142730328841925201 / 20000000000000000000)) (y := (954060596856779933 / 2500000000000000000)) (u := (146466161862612705667 / 100000000000000000000))
  · norm_num [world13172, agent13172, scalar13172, tp13172, tm13172, ep13172, em13172, dsL]
  · norm_num [world13172, agent13172, scalar13172, tp13172, tm13172, ep13172, em13172, dsL]
  · norm_num [world13172, agent13172, scalar13172, tp13172, tm13172, ep13172, em13172, dsL]
  · norm_num [world13172, agent13172, scalar13172, tp13172, tm13172, ep13172, em13172, dsL]
  · norm_num [world13172, agent13172, scalar13172, tp13172, tm13172, ep13172, em13172, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13172, agent13172, tp13172, tm13172, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13172, agent13172, scalar13172, tp13172, tm13172, ep13172, em13172, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13172, agent13172, tp13172, tm13172, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13172, agent13172, scalar13172, tp13172, tm13172, ep13172, em13172, dsL]

theorem negative13172 :
    Eminus aL (agent13172.root+dsL) scalar13172.worldRadius world13172.frame
      agent13172.frame tm13172 ≤ -em13172 := by
  apply negative_check (lo := (13663995326462706263 / 20000000000000000000)) (hi := (17079994158078382829 / 25000000000000000000))
    (y := (-((223714838321291371 / 312500000000000000)))) (u := (48875815488838443031 / 100000000000000000000))
  · norm_num [world13172, agent13172, scalar13172, tp13172, tm13172, ep13172, em13172, dsL]
  · norm_num [world13172, agent13172, scalar13172, tp13172, tm13172, ep13172, em13172, dsL]
  · norm_num [world13172, agent13172, scalar13172, tp13172, tm13172, ep13172, em13172, dsL]
  · norm_num [world13172, agent13172, scalar13172, tp13172, tm13172, ep13172, em13172, dsL]
  · norm_num [world13172, agent13172, scalar13172, tp13172, tm13172, ep13172, em13172, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13172, agent13172, tp13172, tm13172, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13172, agent13172, tp13172, tm13172, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13172, agent13172, scalar13172, tp13172, tm13172, ep13172, em13172, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13172, agent13172, tp13172, tm13172, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13172, agent13172, scalar13172, tp13172, tm13172, ep13172, em13172, dsL]

theorem tails13172 :
    exp (-((13172:ℝ)*ep13172)) ≤ scalar13172.upperTail ∧
    exp (-((13172:ℝ)*em13172)) ≤ scalar13172.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13172:ℝ)) (by norm_num [ep13172]) ?_)
      (show bp13172^8 ≤ scalar13172.upperTail by norm_num [bp13172, scalar13172])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13172, bp13172, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13172:ℝ)) (by norm_num [em13172]) ?_)
      (show bm13172^8 ≤ scalar13172.lowerTail by norm_num [bm13172, scalar13172])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13172, bm13172, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13172 :
    agent13172.root+dsL+scalar13172.worldRadius < √(1/100/aL) ∧
    2*(agent13172.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13172, agent13172, scalar13172, tp13172, tm13172, ep13172, em13172, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13172, agent13172, scalar13172, tp13172, tm13172, ep13172, em13172, dsL]

noncomputable def master13172 : MasterCertificate 13172 world13172 agent13172 :=
  master scalar13172 dsL tp13172 tm13172 ep13172 em13172
    (by norm_num [dsL]) (by norm_num [tp13172]) (by norm_num [tm13172])
    (by norm_num [ep13172]) (by norm_num [em13172])
    positive13172 negative13172 tails13172.1 tails13172.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13172.1 tailGuards13172.2

theorem preserves13172 : master13172.toScalarCertificate = scalar13172 := rfl

noncomputable def tp13173 : ℝ := (1178311053 / 5000000000)
noncomputable def tm13173 : ℝ := (-((384464741 / 625000000)))
noncomputable def ep13173 : ℝ := (26301075509389643 / 50000000000000000000)
noncomputable def em13173 : ℝ := (51128153988111619 / 100000000000000000000)
noncomputable def bp13173 : ℝ := (5257041810443412819 / 12500000000000000000)
noncomputable def bm13173 : ℝ := (43089580682632944603 / 100000000000000000000)

theorem positive13173 :
    Eplus aL (agent13173.root+dsL) scalar13173.worldRadius world13173.frame
      agent13173.frame tp13173 ≤ -ep13173 := by
  apply positive_check (eT := (57856903296846358243 / 50000000000000000000)) (y := (38163054921199307049 / 100000000000000000000)) (u := (73233543067872077721 / 50000000000000000000))
  · norm_num [world13173, agent13173, scalar13173, tp13173, tm13173, ep13173, em13173, dsL]
  · norm_num [world13173, agent13173, scalar13173, tp13173, tm13173, ep13173, em13173, dsL]
  · norm_num [world13173, agent13173, scalar13173, tp13173, tm13173, ep13173, em13173, dsL]
  · norm_num [world13173, agent13173, scalar13173, tp13173, tm13173, ep13173, em13173, dsL]
  · norm_num [world13173, agent13173, scalar13173, tp13173, tm13173, ep13173, em13173, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13173, agent13173, tp13173, tm13173, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13173, agent13173, scalar13173, tp13173, tm13173, ep13173, em13173, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13173, agent13173, tp13173, tm13173, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13173, agent13173, scalar13173, tp13173, tm13173, ep13173, em13173, dsL]

theorem negative13173 :
    Eminus aL (agent13173.root+dsL) scalar13173.worldRadius world13173.frame
      agent13173.frame tm13173 ≤ -em13173 := by
  apply negative_check (lo := (68319886727892780241 / 100000000000000000000)) (hi := (34159943363946390121 / 50000000000000000000))
    (y := (-((35794318452632888587 / 50000000000000000000)))) (u := (48875869915778177479 / 100000000000000000000))
  · norm_num [world13173, agent13173, scalar13173, tp13173, tm13173, ep13173, em13173, dsL]
  · norm_num [world13173, agent13173, scalar13173, tp13173, tm13173, ep13173, em13173, dsL]
  · norm_num [world13173, agent13173, scalar13173, tp13173, tm13173, ep13173, em13173, dsL]
  · norm_num [world13173, agent13173, scalar13173, tp13173, tm13173, ep13173, em13173, dsL]
  · norm_num [world13173, agent13173, scalar13173, tp13173, tm13173, ep13173, em13173, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13173, agent13173, tp13173, tm13173, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13173, agent13173, tp13173, tm13173, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13173, agent13173, scalar13173, tp13173, tm13173, ep13173, em13173, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13173, agent13173, tp13173, tm13173, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13173, agent13173, scalar13173, tp13173, tm13173, ep13173, em13173, dsL]

theorem tails13173 :
    exp (-((13173:ℝ)*ep13173)) ≤ scalar13173.upperTail ∧
    exp (-((13173:ℝ)*em13173)) ≤ scalar13173.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13173:ℝ)) (by norm_num [ep13173]) ?_)
      (show bp13173^8 ≤ scalar13173.upperTail by norm_num [bp13173, scalar13173])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13173, bp13173, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13173:ℝ)) (by norm_num [em13173]) ?_)
      (show bm13173^8 ≤ scalar13173.lowerTail by norm_num [bm13173, scalar13173])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13173, bm13173, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13173 :
    agent13173.root+dsL+scalar13173.worldRadius < √(1/100/aL) ∧
    2*(agent13173.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13173, agent13173, scalar13173, tp13173, tm13173, ep13173, em13173, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13173, agent13173, scalar13173, tp13173, tm13173, ep13173, em13173, dsL]

noncomputable def master13173 : MasterCertificate 13173 world13173 agent13173 :=
  master scalar13173 dsL tp13173 tm13173 ep13173 em13173
    (by norm_num [dsL]) (by norm_num [tp13173]) (by norm_num [tm13173])
    (by norm_num [ep13173]) (by norm_num [em13173])
    positive13173 negative13173 tails13173.1 tails13173.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13173.1 tailGuards13173.2

theorem preserves13173 : master13173.toScalarCertificate = scalar13173 := rfl

noncomputable def tp13174 : ℝ := (2356692591 / 10000000000)
noncomputable def tm13174 : ℝ := (-((615158467 / 1000000000)))
noncomputable def ep13174 : ℝ := (6575531404851439 / 12500000000000000000)
noncomputable def em13174 : ℝ := (3195620503000711 / 6250000000000000000)
noncomputable def bp13174 : ℝ := (1314128588879458657 / 3125000000000000000)
noncomputable def bm13174 : ℝ := (21542784086390965493 / 50000000000000000000)

theorem positive13174 :
    Eplus aL (agent13174.root+dsL) scalar13174.worldRadius world13174.frame
      agent13174.frame tp13174 ≤ -ep13174 := by
  apply positive_check (eT := (57856980619710371513 / 50000000000000000000)) (y := (38163685557325084243 / 100000000000000000000)) (u := (146468009813014218859 / 100000000000000000000))
  · norm_num [world13174, agent13174, scalar13174, tp13174, tm13174, ep13174, em13174, dsL]
  · norm_num [world13174, agent13174, scalar13174, tp13174, tm13174, ep13174, em13174, dsL]
  · norm_num [world13174, agent13174, scalar13174, tp13174, tm13174, ep13174, em13174, dsL]
  · norm_num [world13174, agent13174, scalar13174, tp13174, tm13174, ep13174, em13174, dsL]
  · norm_num [world13174, agent13174, scalar13174, tp13174, tm13174, ep13174, em13174, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13174, agent13174, tp13174, tm13174, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13174, agent13174, scalar13174, tp13174, tm13174, ep13174, em13174, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13174, agent13174, tp13174, tm13174, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13174, agent13174, scalar13174, tp13174, tm13174, ep13174, em13174, dsL]

theorem negative13174 :
    Eminus aL (agent13174.root+dsL) scalar13174.worldRadius world13174.frame
      agent13174.frame tm13174 ≤ -em13174 := by
  apply negative_check (lo := (68319797206815459773 / 100000000000000000000)) (hi := (34159898603407729887 / 50000000000000000000))
    (y := (-((17897131320125241259 / 25000000000000000000)))) (u := (24437962236691735373 / 50000000000000000000))
  · norm_num [world13174, agent13174, scalar13174, tp13174, tm13174, ep13174, em13174, dsL]
  · norm_num [world13174, agent13174, scalar13174, tp13174, tm13174, ep13174, em13174, dsL]
  · norm_num [world13174, agent13174, scalar13174, tp13174, tm13174, ep13174, em13174, dsL]
  · norm_num [world13174, agent13174, scalar13174, tp13174, tm13174, ep13174, em13174, dsL]
  · norm_num [world13174, agent13174, scalar13174, tp13174, tm13174, ep13174, em13174, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13174, agent13174, tp13174, tm13174, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13174, agent13174, tp13174, tm13174, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13174, agent13174, scalar13174, tp13174, tm13174, ep13174, em13174, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13174, agent13174, tp13174, tm13174, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13174, agent13174, scalar13174, tp13174, tm13174, ep13174, em13174, dsL]

theorem tails13174 :
    exp (-((13174:ℝ)*ep13174)) ≤ scalar13174.upperTail ∧
    exp (-((13174:ℝ)*em13174)) ≤ scalar13174.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13174:ℝ)) (by norm_num [ep13174]) ?_)
      (show bp13174^8 ≤ scalar13174.upperTail by norm_num [bp13174, scalar13174])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13174, bp13174, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13174:ℝ)) (by norm_num [em13174]) ?_)
      (show bm13174^8 ≤ scalar13174.lowerTail by norm_num [bm13174, scalar13174])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13174, bm13174, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13174 :
    agent13174.root+dsL+scalar13174.worldRadius < √(1/100/aL) ∧
    2*(agent13174.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13174, agent13174, scalar13174, tp13174, tm13174, ep13174, em13174, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13174, agent13174, scalar13174, tp13174, tm13174, ep13174, em13174, dsL]

noncomputable def master13174 : MasterCertificate 13174 world13174 agent13174 :=
  master scalar13174 dsL tp13174 tm13174 ep13174 em13174
    (by norm_num [dsL]) (by norm_num [tp13174]) (by norm_num [tm13174])
    (by norm_num [ep13174]) (by norm_num [em13174])
    positive13174 negative13174 tails13174.1 tails13174.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13174.1 tailGuards13174.2

theorem preserves13174 : master13174.toScalarCertificate = scalar13174 := rfl

end BstLean.Part268
