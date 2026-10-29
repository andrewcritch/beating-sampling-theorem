import BstLean.Part261Checker
import BstLean.Part281Scalar13
namespace BstLean.Part281
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12184 : ℝ := (95053337 / 400000000)
noncomputable def tm12184 : ℝ := (-((1229332767 / 2000000000)))
noncomputable def ep12184 : ℝ := (27348226864448369 / 50000000000000000000)
noncomputable def em12184 : ℝ := (52726758600318097 / 100000000000000000000)
noncomputable def bp12184 : ℝ := (21736568251958490941 / 50000000000000000000)
noncomputable def bm12184 : ℝ := (44797021485194194441 / 100000000000000000000)

theorem positive12184 :
    Eplus aL (agent12184.root+dsL) scalar12184.worldRadius world12184.frame
      agent12184.frame tp12184 ≤ -ep12184 := by
  apply positive_check (eT := (116234640191165194343 / 100000000000000000000)) (y := (3964846577455083333 / 10000000000000000000)) (u := (5946358520653590883 / 4000000000000000000))
  · norm_num [world12184, agent12184, scalar12184, tp12184, tm12184, ep12184, em12184, dsL]
  · norm_num [world12184, agent12184, scalar12184, tp12184, tm12184, ep12184, em12184, dsL]
  · norm_num [world12184, agent12184, scalar12184, tp12184, tm12184, ep12184, em12184, dsL]
  · norm_num [world12184, agent12184, scalar12184, tp12184, tm12184, ep12184, em12184, dsL]
  · norm_num [world12184, agent12184, scalar12184, tp12184, tm12184, ep12184, em12184, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12184, agent12184, tp12184, tm12184, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12184, agent12184, scalar12184, tp12184, tm12184, ep12184, em12184, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12184, agent12184, tp12184, tm12184, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12184, agent12184, scalar12184, tp12184, tm12184, ep12184, em12184, dsL]

theorem negative12184 :
    Eminus aL (agent12184.root+dsL) scalar12184.worldRadius world12184.frame
      agent12184.frame tm12184 ≤ -em12184 := by
  apply negative_check (lo := (33882224080231309597 / 50000000000000000000)) (hi := (13552889632092523839 / 20000000000000000000))
    (y := (-((73290013132727035139 / 100000000000000000000)))) (u := (48051341538426445389 / 100000000000000000000))
  · norm_num [world12184, agent12184, scalar12184, tp12184, tm12184, ep12184, em12184, dsL]
  · norm_num [world12184, agent12184, scalar12184, tp12184, tm12184, ep12184, em12184, dsL]
  · norm_num [world12184, agent12184, scalar12184, tp12184, tm12184, ep12184, em12184, dsL]
  · norm_num [world12184, agent12184, scalar12184, tp12184, tm12184, ep12184, em12184, dsL]
  · norm_num [world12184, agent12184, scalar12184, tp12184, tm12184, ep12184, em12184, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12184, agent12184, tp12184, tm12184, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12184, agent12184, tp12184, tm12184, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12184, agent12184, scalar12184, tp12184, tm12184, ep12184, em12184, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12184, agent12184, tp12184, tm12184, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12184, agent12184, scalar12184, tp12184, tm12184, ep12184, em12184, dsL]

theorem tails12184 :
    exp (-((12184:ℝ)*ep12184)) ≤ scalar12184.upperTail ∧
    exp (-((12184:ℝ)*em12184)) ≤ scalar12184.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12184:ℝ)) (by norm_num [ep12184]) ?_)
      (show bp12184^8 ≤ scalar12184.upperTail by norm_num [bp12184, scalar12184])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12184, bp12184, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12184:ℝ)) (by norm_num [em12184]) ?_)
      (show bm12184^8 ≤ scalar12184.lowerTail by norm_num [bm12184, scalar12184])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12184, bm12184, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12184 :
    agent12184.root+dsL+scalar12184.worldRadius < √(1/100/aL) ∧
    2*(agent12184.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12184, agent12184, scalar12184, tp12184, tm12184, ep12184, em12184, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12184, agent12184, scalar12184, tp12184, tm12184, ep12184, em12184, dsL]

noncomputable def master12184 : MasterCertificate 12184 world12184 agent12184 :=
  master scalar12184 dsL tp12184 tm12184 ep12184 em12184
    (by norm_num [dsL]) (by norm_num [tp12184]) (by norm_num [tm12184])
    (by norm_num [ep12184]) (by norm_num [em12184])
    positive12184 negative12184 tails12184.1 tails12184.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12184.1 tailGuards12184.2

theorem preserves12184 : master12184.toScalarCertificate = scalar12184 := rfl

noncomputable def tp12185 : ℝ := (475286111 / 2000000000)
noncomputable def tm12185 : ℝ := (-((3073440789 / 5000000000)))
noncomputable def ep12185 : ℝ := (10939858887550477 / 20000000000000000000)
noncomputable def em12185 : ℝ := (26364612710118263 / 50000000000000000000)
noncomputable def bp12185 : ℝ := (43468283515845812479 / 100000000000000000000)
noncomputable def bm12185 : ℝ := (44792386075536332559 / 100000000000000000000)

theorem positive12185 :
    Eplus aL (agent12185.root+dsL) scalar12185.worldRadius world12185.frame
      agent12185.frame tp12185 ≤ -ep12185 := by
  apply positive_check (eT := (14529367337151846089 / 12500000000000000000)) (y := (39649080051276966141 / 100000000000000000000)) (u := (148659876196555615729 / 100000000000000000000))
  · norm_num [world12185, agent12185, scalar12185, tp12185, tm12185, ep12185, em12185, dsL]
  · norm_num [world12185, agent12185, scalar12185, tp12185, tm12185, ep12185, em12185, dsL]
  · norm_num [world12185, agent12185, scalar12185, tp12185, tm12185, ep12185, em12185, dsL]
  · norm_num [world12185, agent12185, scalar12185, tp12185, tm12185, ep12185, em12185, dsL]
  · norm_num [world12185, agent12185, scalar12185, tp12185, tm12185, ep12185, em12185, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12185, agent12185, tp12185, tm12185, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12185, agent12185, scalar12185, tp12185, tm12185, ep12185, em12185, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12185, agent12185, tp12185, tm12185, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12185, agent12185, scalar12185, tp12185, tm12185, ep12185, em12185, dsL]

theorem negative12185 :
    Eminus aL (agent12185.root+dsL) scalar12185.worldRadius world12185.frame
      agent12185.frame tm12185 ≤ -em12185 := by
  apply negative_check (lo := (3388207085450623829 / 5000000000000000000)) (hi := (67764141709012476581 / 100000000000000000000))
    (y := (-((3664480153910002461 / 5000000000000000000)))) (u := (48051538575531680681 / 100000000000000000000))
  · norm_num [world12185, agent12185, scalar12185, tp12185, tm12185, ep12185, em12185, dsL]
  · norm_num [world12185, agent12185, scalar12185, tp12185, tm12185, ep12185, em12185, dsL]
  · norm_num [world12185, agent12185, scalar12185, tp12185, tm12185, ep12185, em12185, dsL]
  · norm_num [world12185, agent12185, scalar12185, tp12185, tm12185, ep12185, em12185, dsL]
  · norm_num [world12185, agent12185, scalar12185, tp12185, tm12185, ep12185, em12185, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12185, agent12185, tp12185, tm12185, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12185, agent12185, tp12185, tm12185, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12185, agent12185, scalar12185, tp12185, tm12185, ep12185, em12185, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12185, agent12185, tp12185, tm12185, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12185, agent12185, scalar12185, tp12185, tm12185, ep12185, em12185, dsL]

theorem tails12185 :
    exp (-((12185:ℝ)*ep12185)) ≤ scalar12185.upperTail ∧
    exp (-((12185:ℝ)*em12185)) ≤ scalar12185.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12185:ℝ)) (by norm_num [ep12185]) ?_)
      (show bp12185^8 ≤ scalar12185.upperTail by norm_num [bp12185, scalar12185])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12185, bp12185, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12185:ℝ)) (by norm_num [em12185]) ?_)
      (show bm12185^8 ≤ scalar12185.lowerTail by norm_num [bm12185, scalar12185])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12185, bm12185, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12185 :
    agent12185.root+dsL+scalar12185.worldRadius < √(1/100/aL) ∧
    2*(agent12185.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12185, agent12185, scalar12185, tp12185, tm12185, ep12185, em12185, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12185, agent12185, scalar12185, tp12185, tm12185, ep12185, em12185, dsL]

noncomputable def master12185 : MasterCertificate 12185 world12185 agent12185 :=
  master scalar12185 dsL tp12185 tm12185 ep12185 em12185
    (by norm_num [dsL]) (by norm_num [tp12185]) (by norm_num [tm12185])
    (by norm_num [ep12185]) (by norm_num [em12185])
    positive12185 negative12185 tails12185.1 tails12185.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12185.1 tailGuards12185.2

theorem preserves12185 : master12185.toScalarCertificate = scalar12185 := rfl

noncomputable def tp12186 : ℝ := (475305541 / 2000000000)
noncomputable def tm12186 : ℝ := (-((3073549653 / 5000000000)))
noncomputable def ep12186 : ℝ := (54702133277522461 / 100000000000000000000)
noncomputable def em12186 : ℝ := (52731690448333091 / 100000000000000000000)
noncomputable def bp12186 : ℝ := (43463431998296114743 / 100000000000000000000)
noncomputable def bm12186 : ℝ := (22393876045878355411 / 50000000000000000000)

theorem positive12186 :
    Eplus aL (agent12186.root+dsL) scalar12186.worldRadius world12186.frame
      agent12186.frame tp12186 ≤ -ep12186 := by
  apply positive_check (eT := (23247047477478108593 / 20000000000000000000)) (y := (39649695559288158659 / 100000000000000000000)) (u := (148660791212819030721 / 100000000000000000000))
  · norm_num [world12186, agent12186, scalar12186, tp12186, tm12186, ep12186, em12186, dsL]
  · norm_num [world12186, agent12186, scalar12186, tp12186, tm12186, ep12186, em12186, dsL]
  · norm_num [world12186, agent12186, scalar12186, tp12186, tm12186, ep12186, em12186, dsL]
  · norm_num [world12186, agent12186, scalar12186, tp12186, tm12186, ep12186, em12186, dsL]
  · norm_num [world12186, agent12186, scalar12186, tp12186, tm12186, ep12186, em12186, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12186, agent12186, tp12186, tm12186, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12186, agent12186, scalar12186, tp12186, tm12186, ep12186, em12186, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12186, agent12186, tp12186, tm12186, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12186, agent12186, scalar12186, tp12186, tm12186, ep12186, em12186, dsL]

theorem negative12186 :
    Eminus aL (agent12186.root+dsL) scalar12186.worldRadius world12186.frame
      agent12186.frame tm12186 ≤ -em12186 := by
  apply negative_check (lo := (33881917630937833631 / 50000000000000000000)) (hi := (67763835261875667263 / 100000000000000000000))
    (y := (-((73289194236507534501 / 100000000000000000000)))) (u := (48051735030656867203 / 100000000000000000000))
  · norm_num [world12186, agent12186, scalar12186, tp12186, tm12186, ep12186, em12186, dsL]
  · norm_num [world12186, agent12186, scalar12186, tp12186, tm12186, ep12186, em12186, dsL]
  · norm_num [world12186, agent12186, scalar12186, tp12186, tm12186, ep12186, em12186, dsL]
  · norm_num [world12186, agent12186, scalar12186, tp12186, tm12186, ep12186, em12186, dsL]
  · norm_num [world12186, agent12186, scalar12186, tp12186, tm12186, ep12186, em12186, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12186, agent12186, tp12186, tm12186, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12186, agent12186, tp12186, tm12186, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12186, agent12186, scalar12186, tp12186, tm12186, ep12186, em12186, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12186, agent12186, tp12186, tm12186, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12186, agent12186, scalar12186, tp12186, tm12186, ep12186, em12186, dsL]

theorem tails12186 :
    exp (-((12186:ℝ)*ep12186)) ≤ scalar12186.upperTail ∧
    exp (-((12186:ℝ)*em12186)) ≤ scalar12186.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12186:ℝ)) (by norm_num [ep12186]) ?_)
      (show bp12186^8 ≤ scalar12186.upperTail by norm_num [bp12186, scalar12186])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12186, bp12186, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12186:ℝ)) (by norm_num [em12186]) ?_)
      (show bm12186^8 ≤ scalar12186.lowerTail by norm_num [bm12186, scalar12186])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12186, bm12186, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12186 :
    agent12186.root+dsL+scalar12186.worldRadius < √(1/100/aL) ∧
    2*(agent12186.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12186, agent12186, scalar12186, tp12186, tm12186, ep12186, em12186, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12186, agent12186, scalar12186, tp12186, tm12186, ep12186, em12186, dsL]

noncomputable def master12186 : MasterCertificate 12186 world12186 agent12186 :=
  master scalar12186 dsL tp12186 tm12186 ep12186 em12186
    (by norm_num [dsL]) (by norm_num [tp12186]) (by norm_num [tm12186])
    (by norm_num [ep12186]) (by norm_num [em12186])
    positive12186 negative12186 tails12186.1 tails12186.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12186.1 tailGuards12186.2

theorem preserves12186 : master12186.toScalarCertificate = scalar12186 := rfl

noncomputable def tp12187 : ℝ := (2376624717 / 10000000000)
noncomputable def tm12187 : ℝ := (-((6147316907 / 10000000000)))
noncomputable def ep12187 : ℝ := (10940994128515373 / 20000000000000000000)
noncomputable def em12187 : ℝ := (52734154120320299 / 100000000000000000000)
noncomputable def bp12187 : ℝ := (8691716338022700361 / 20000000000000000000)
noncomputable def bm12187 : ℝ := (44783119236563394563 / 100000000000000000000)

theorem positive12187 :
    Eplus aL (agent12187.root+dsL) scalar12187.worldRadius world12187.frame
      agent12187.frame tp12187 ≤ -ep12187 := by
  apply positive_check (eT := (58117767549569580679 / 50000000000000000000)) (y := (39650309192767058713 / 100000000000000000000)) (u := (148661703448002797673 / 100000000000000000000))
  · norm_num [world12187, agent12187, scalar12187, tp12187, tm12187, ep12187, em12187, dsL]
  · norm_num [world12187, agent12187, scalar12187, tp12187, tm12187, ep12187, em12187, dsL]
  · norm_num [world12187, agent12187, scalar12187, tp12187, tm12187, ep12187, em12187, dsL]
  · norm_num [world12187, agent12187, scalar12187, tp12187, tm12187, ep12187, em12187, dsL]
  · norm_num [world12187, agent12187, scalar12187, tp12187, tm12187, ep12187, em12187, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12187, agent12187, tp12187, tm12187, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12187, agent12187, scalar12187, tp12187, tm12187, ep12187, em12187, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12187, agent12187, tp12187, tm12187, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12187, agent12187, scalar12187, tp12187, tm12187, ep12187, em12187, dsL]

theorem negative12187 :
    Eminus aL (agent12187.root+dsL) scalar12187.worldRadius world12187.frame
      agent12187.frame tm12187 ≤ -em12187 := by
  apply negative_check (lo := (4235220581214796977 / 6250000000000000000)) (hi := (67763529299436751633 / 100000000000000000000))
    (y := (-((36644392734586973597 / 50000000000000000000)))) (u := (24025965725427172493 / 50000000000000000000))
  · norm_num [world12187, agent12187, scalar12187, tp12187, tm12187, ep12187, em12187, dsL]
  · norm_num [world12187, agent12187, scalar12187, tp12187, tm12187, ep12187, em12187, dsL]
  · norm_num [world12187, agent12187, scalar12187, tp12187, tm12187, ep12187, em12187, dsL]
  · norm_num [world12187, agent12187, scalar12187, tp12187, tm12187, ep12187, em12187, dsL]
  · norm_num [world12187, agent12187, scalar12187, tp12187, tm12187, ep12187, em12187, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12187, agent12187, tp12187, tm12187, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12187, agent12187, tp12187, tm12187, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12187, agent12187, scalar12187, tp12187, tm12187, ep12187, em12187, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12187, agent12187, tp12187, tm12187, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12187, agent12187, scalar12187, tp12187, tm12187, ep12187, em12187, dsL]

theorem tails12187 :
    exp (-((12187:ℝ)*ep12187)) ≤ scalar12187.upperTail ∧
    exp (-((12187:ℝ)*em12187)) ≤ scalar12187.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12187:ℝ)) (by norm_num [ep12187]) ?_)
      (show bp12187^8 ≤ scalar12187.upperTail by norm_num [bp12187, scalar12187])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12187, bp12187, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12187:ℝ)) (by norm_num [em12187]) ?_)
      (show bm12187^8 ≤ scalar12187.lowerTail by norm_num [bm12187, scalar12187])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12187, bm12187, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12187 :
    agent12187.root+dsL+scalar12187.worldRadius < √(1/100/aL) ∧
    2*(agent12187.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12187, agent12187, scalar12187, tp12187, tm12187, ep12187, em12187, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12187, agent12187, scalar12187, tp12187, tm12187, ep12187, em12187, dsL]

noncomputable def master12187 : MasterCertificate 12187 world12187 agent12187 :=
  master scalar12187 dsL tp12187 tm12187 ep12187 em12187
    (by norm_num [dsL]) (by norm_num [tp12187]) (by norm_num [tm12187])
    (by norm_num [ep12187]) (by norm_num [em12187])
    positive12187 negative12187 tails12187.1 tails12187.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12187.1 tailGuards12187.2

theorem preserves12187 : master12187.toScalarCertificate = scalar12187 := rfl

noncomputable def tp12188 : ℝ := (1188360891 / 5000000000)
noncomputable def tm12188 : ℝ := (-((384220907 / 625000000)))
noncomputable def ep12188 : ℝ := (54707806922916533 / 100000000000000000000)
noncomputable def em12188 : ℝ := (26368308378979029 / 50000000000000000000)
noncomputable def bp12188 : ℝ := (10863433083266689501 / 25000000000000000000)
noncomputable def bm12188 : ℝ := (44778487290428358717 / 100000000000000000000)

theorem positive12188 :
    Eplus aL (agent12188.root+dsL) scalar12188.worldRadius world12188.frame
      agent12188.frame tp12188 ≤ -ep12188 := by
  apply positive_check (eT := (116235833237819413611 / 100000000000000000000)) (y := (1586036971122502987 / 4000000000000000000)) (u := (74331308923546467087 / 50000000000000000000))
  · norm_num [world12188, agent12188, scalar12188, tp12188, tm12188, ep12188, em12188, dsL]
  · norm_num [world12188, agent12188, scalar12188, tp12188, tm12188, ep12188, em12188, dsL]
  · norm_num [world12188, agent12188, scalar12188, tp12188, tm12188, ep12188, em12188, dsL]
  · norm_num [world12188, agent12188, scalar12188, tp12188, tm12188, ep12188, em12188, dsL]
  · norm_num [world12188, agent12188, scalar12188, tp12188, tm12188, ep12188, em12188, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12188, agent12188, tp12188, tm12188, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12188, agent12188, scalar12188, tp12188, tm12188, ep12188, em12188, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12188, agent12188, tp12188, tm12188, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12188, agent12188, scalar12188, tp12188, tm12188, ep12188, em12188, dsL]

theorem negative12188 :
    Eminus aL (agent12188.root+dsL) scalar12188.worldRadius world12188.frame
      agent12188.frame tm12188 ≤ -em12188 := by
  apply negative_check (lo := (67763223259834232613 / 100000000000000000000)) (hi := (33881611629917116307 / 50000000000000000000))
    (y := (-((9161047204527074567 / 12500000000000000000)))) (u := (6006515927858383009 / 12500000000000000000))
  · norm_num [world12188, agent12188, scalar12188, tp12188, tm12188, ep12188, em12188, dsL]
  · norm_num [world12188, agent12188, scalar12188, tp12188, tm12188, ep12188, em12188, dsL]
  · norm_num [world12188, agent12188, scalar12188, tp12188, tm12188, ep12188, em12188, dsL]
  · norm_num [world12188, agent12188, scalar12188, tp12188, tm12188, ep12188, em12188, dsL]
  · norm_num [world12188, agent12188, scalar12188, tp12188, tm12188, ep12188, em12188, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12188, agent12188, tp12188, tm12188, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12188, agent12188, tp12188, tm12188, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12188, agent12188, scalar12188, tp12188, tm12188, ep12188, em12188, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12188, agent12188, tp12188, tm12188, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12188, agent12188, scalar12188, tp12188, tm12188, ep12188, em12188, dsL]

theorem tails12188 :
    exp (-((12188:ℝ)*ep12188)) ≤ scalar12188.upperTail ∧
    exp (-((12188:ℝ)*em12188)) ≤ scalar12188.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12188:ℝ)) (by norm_num [ep12188]) ?_)
      (show bp12188^8 ≤ scalar12188.upperTail by norm_num [bp12188, scalar12188])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12188, bp12188, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12188:ℝ)) (by norm_num [em12188]) ?_)
      (show bm12188^8 ≤ scalar12188.lowerTail by norm_num [bm12188, scalar12188])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12188, bm12188, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12188 :
    agent12188.root+dsL+scalar12188.worldRadius < √(1/100/aL) ∧
    2*(agent12188.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12188, agent12188, scalar12188, tp12188, tm12188, ep12188, em12188, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12188, agent12188, scalar12188, tp12188, tm12188, ep12188, em12188, dsL]

noncomputable def master12188 : MasterCertificate 12188 world12188 agent12188 :=
  master scalar12188 dsL tp12188 tm12188 ep12188 em12188
    (by norm_num [dsL]) (by norm_num [tp12188]) (by norm_num [tm12188])
    (by norm_num [ep12188]) (by norm_num [em12188])
    positive12188 negative12188 tails12188.1 tails12188.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12188.1 tailGuards12188.2

theorem preserves12188 : master12188.toScalarCertificate = scalar12188 := rfl

noncomputable def tp12189 : ℝ := (2376818741 / 10000000000)
noncomputable def tm12189 : ℝ := (-((3073875897 / 5000000000)))
noncomputable def ep12189 : ℝ := (13677660274244759 / 25000000000000000000)
noncomputable def em12189 : ℝ := (52739077440514973 / 100000000000000000000)
noncomputable def bp12189 : ℝ := (21724442301703680089 / 50000000000000000000)
noncomputable def bm12189 : ℝ := (22386928440726046459 / 50000000000000000000)

theorem positive12189 :
    Eplus aL (agent12189.root+dsL) scalar12189.worldRadius world12189.frame
      agent12189.frame tp12189 ≤ -ep12189 := by
  apply positive_check (eT := (58118065316790832109 / 50000000000000000000)) (y := (19825769137534716219 / 50000000000000000000)) (u := (148663530633919070747 / 100000000000000000000))
  · norm_num [world12189, agent12189, scalar12189, tp12189, tm12189, ep12189, em12189, dsL]
  · norm_num [world12189, agent12189, scalar12189, tp12189, tm12189, ep12189, em12189, dsL]
  · norm_num [world12189, agent12189, scalar12189, tp12189, tm12189, ep12189, em12189, dsL]
  · norm_num [world12189, agent12189, scalar12189, tp12189, tm12189, ep12189, em12189, dsL]
  · norm_num [world12189, agent12189, scalar12189, tp12189, tm12189, ep12189, em12189, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12189, agent12189, tp12189, tm12189, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12189, agent12189, scalar12189, tp12189, tm12189, ep12189, em12189, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12189, agent12189, tp12189, tm12189, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12189, agent12189, scalar12189, tp12189, tm12189, ep12189, em12189, dsL]

theorem negative12189 :
    Eminus aL (agent12189.root+dsL) scalar12189.worldRadius world12189.frame
      agent12189.frame tm12189 ≤ -em12189 := by
  apply negative_check (lo := (13552583709123163237 / 20000000000000000000)) (hi := (33881459272807908093 / 50000000000000000000))
    (y := (-((14657593626318983399 / 20000000000000000000)))) (u := (24026162099476289681 / 50000000000000000000))
  · norm_num [world12189, agent12189, scalar12189, tp12189, tm12189, ep12189, em12189, dsL]
  · norm_num [world12189, agent12189, scalar12189, tp12189, tm12189, ep12189, em12189, dsL]
  · norm_num [world12189, agent12189, scalar12189, tp12189, tm12189, ep12189, em12189, dsL]
  · norm_num [world12189, agent12189, scalar12189, tp12189, tm12189, ep12189, em12189, dsL]
  · norm_num [world12189, agent12189, scalar12189, tp12189, tm12189, ep12189, em12189, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12189, agent12189, tp12189, tm12189, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12189, agent12189, tp12189, tm12189, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12189, agent12189, scalar12189, tp12189, tm12189, ep12189, em12189, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12189, agent12189, tp12189, tm12189, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12189, agent12189, scalar12189, tp12189, tm12189, ep12189, em12189, dsL]

theorem tails12189 :
    exp (-((12189:ℝ)*ep12189)) ≤ scalar12189.upperTail ∧
    exp (-((12189:ℝ)*em12189)) ≤ scalar12189.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12189:ℝ)) (by norm_num [ep12189]) ?_)
      (show bp12189^8 ≤ scalar12189.upperTail by norm_num [bp12189, scalar12189])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12189, bp12189, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12189:ℝ)) (by norm_num [em12189]) ?_)
      (show bm12189^8 ≤ scalar12189.lowerTail by norm_num [bm12189, scalar12189])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12189, bm12189, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12189 :
    agent12189.root+dsL+scalar12189.worldRadius < √(1/100/aL) ∧
    2*(agent12189.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12189, agent12189, scalar12189, tp12189, tm12189, ep12189, em12189, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12189, agent12189, scalar12189, tp12189, tm12189, ep12189, em12189, dsL]

noncomputable def master12189 : MasterCertificate 12189 world12189 agent12189 :=
  master scalar12189 dsL tp12189 tm12189 ep12189 em12189
    (by norm_num [dsL]) (by norm_num [tp12189]) (by norm_num [tm12189])
    (by norm_num [ep12189]) (by norm_num [em12189])
    positive12189 negative12189 tails12189.1 tails12189.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12189.1 tailGuards12189.2

theorem preserves12189 : master12189.toScalarCertificate = scalar12189 := rfl

noncomputable def tp12190 : ℝ := (1188457823 / 5000000000)
noncomputable def tm12190 : ℝ := (-((6147968999 / 10000000000)))
noncomputable def ep12190 : ℝ := (6839184273346187 / 12500000000000000000)
noncomputable def em12190 : ℝ := (5274153708924897 / 10000000000000000000)
noncomputable def bp12190 : ℝ := (10861009456127266783 / 25000000000000000000)
noncomputable def bm12190 : ℝ := (44769227381129497179 / 100000000000000000000)

theorem positive12190 :
    Eplus aL (agent12190.root+dsL) scalar12190.worldRadius world12190.frame
      agent12190.frame tp12190 ≤ -ep12190 := by
  apply positive_check (eT := (29059106917249659489 / 25000000000000000000)) (y := (19826075900218212271 / 50000000000000000000)) (u := (148664442725188928713 / 100000000000000000000))
  · norm_num [world12190, agent12190, scalar12190, tp12190, tm12190, ep12190, em12190, dsL]
  · norm_num [world12190, agent12190, scalar12190, tp12190, tm12190, ep12190, em12190, dsL]
  · norm_num [world12190, agent12190, scalar12190, tp12190, tm12190, ep12190, em12190, dsL]
  · norm_num [world12190, agent12190, scalar12190, tp12190, tm12190, ep12190, em12190, dsL]
  · norm_num [world12190, agent12190, scalar12190, tp12190, tm12190, ep12190, em12190, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12190, agent12190, tp12190, tm12190, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12190, agent12190, scalar12190, tp12190, tm12190, ep12190, em12190, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12190, agent12190, tp12190, tm12190, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12190, agent12190, scalar12190, tp12190, tm12190, ep12190, em12190, dsL]

theorem negative12190 :
    Eminus aL (agent12190.root+dsL) scalar12190.worldRadius world12190.frame
      agent12190.frame tm12190 ≤ -em12190 := by
  apply negative_check (lo := (847032676270141031 / 1250000000000000000)) (hi := (67762614101611282481 / 100000000000000000000))
    (y := (-((36643779385064426651 / 50000000000000000000)))) (u := (24026260453527010591 / 50000000000000000000))
  · norm_num [world12190, agent12190, scalar12190, tp12190, tm12190, ep12190, em12190, dsL]
  · norm_num [world12190, agent12190, scalar12190, tp12190, tm12190, ep12190, em12190, dsL]
  · norm_num [world12190, agent12190, scalar12190, tp12190, tm12190, ep12190, em12190, dsL]
  · norm_num [world12190, agent12190, scalar12190, tp12190, tm12190, ep12190, em12190, dsL]
  · norm_num [world12190, agent12190, scalar12190, tp12190, tm12190, ep12190, em12190, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12190, agent12190, tp12190, tm12190, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12190, agent12190, tp12190, tm12190, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12190, agent12190, scalar12190, tp12190, tm12190, ep12190, em12190, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12190, agent12190, tp12190, tm12190, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12190, agent12190, scalar12190, tp12190, tm12190, ep12190, em12190, dsL]

theorem tails12190 :
    exp (-((12190:ℝ)*ep12190)) ≤ scalar12190.upperTail ∧
    exp (-((12190:ℝ)*em12190)) ≤ scalar12190.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12190:ℝ)) (by norm_num [ep12190]) ?_)
      (show bp12190^8 ≤ scalar12190.upperTail by norm_num [bp12190, scalar12190])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12190, bp12190, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12190:ℝ)) (by norm_num [em12190]) ?_)
      (show bm12190^8 ≤ scalar12190.lowerTail by norm_num [bm12190, scalar12190])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12190, bm12190, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12190 :
    agent12190.root+dsL+scalar12190.worldRadius < √(1/100/aL) ∧
    2*(agent12190.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12190, agent12190, scalar12190, tp12190, tm12190, ep12190, em12190, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12190, agent12190, scalar12190, tp12190, tm12190, ep12190, em12190, dsL]

noncomputable def master12190 : MasterCertificate 12190 world12190 agent12190 :=
  master scalar12190 dsL tp12190 tm12190 ep12190 em12190
    (by norm_num [dsL]) (by norm_num [tp12190]) (by norm_num [tm12190])
    (by norm_num [ep12190]) (by norm_num [em12190])
    positive12190 negative12190 tails12190.1 tails12190.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12190.1 tailGuards12190.2

theorem preserves12190 : master12190.toScalarCertificate = scalar12190 := rfl

noncomputable def tp12191 : ℝ := (594253117 / 2500000000)
noncomputable def tm12191 : ℝ := (-((3074093073 / 5000000000)))
noncomputable def ep12191 : ℝ := (6839538210201359 / 12500000000000000000)
noncomputable def em12191 : ℝ := (52743995243919087 / 100000000000000000000)
noncomputable def bp12191 : ℝ := (43439192334398238091 / 100000000000000000000)
noncomputable def bm12191 : ℝ := (22382299551703825023 / 50000000000000000000)

theorem positive12191 :
    Eplus aL (agent12191.root+dsL) scalar12191.worldRadius world12191.frame
      agent12191.frame tp12191 ≤ -ep12191 := by
  apply positive_check (eT := (116236724130737590971 / 100000000000000000000)) (y := (39652764491476938199 / 100000000000000000000)) (u := (148665353581700300771 / 100000000000000000000))
  · norm_num [world12191, agent12191, scalar12191, tp12191, tm12191, ep12191, em12191, dsL]
  · norm_num [world12191, agent12191, scalar12191, tp12191, tm12191, ep12191, em12191, dsL]
  · norm_num [world12191, agent12191, scalar12191, tp12191, tm12191, ep12191, em12191, dsL]
  · norm_num [world12191, agent12191, scalar12191, tp12191, tm12191, ep12191, em12191, dsL]
  · norm_num [world12191, agent12191, scalar12191, tp12191, tm12191, ep12191, em12191, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12191, agent12191, tp12191, tm12191, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12191, agent12191, scalar12191, tp12191, tm12191, ep12191, em12191, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12191, agent12191, tp12191, tm12191, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12191, agent12191, scalar12191, tp12191, tm12191, ep12191, em12191, dsL]

theorem negative12191 :
    Eminus aL (agent12191.root+dsL) scalar12191.worldRadius world12191.frame
      agent12191.frame tm12191 ≤ -em12191 := by
  apply negative_check (lo := (67762309846287872371 / 100000000000000000000)) (hi := (16940577461571968093 / 25000000000000000000))
    (y := (-((36643575014079729761 / 50000000000000000000)))) (u := (48052717318275727307 / 100000000000000000000))
  · norm_num [world12191, agent12191, scalar12191, tp12191, tm12191, ep12191, em12191, dsL]
  · norm_num [world12191, agent12191, scalar12191, tp12191, tm12191, ep12191, em12191, dsL]
  · norm_num [world12191, agent12191, scalar12191, tp12191, tm12191, ep12191, em12191, dsL]
  · norm_num [world12191, agent12191, scalar12191, tp12191, tm12191, ep12191, em12191, dsL]
  · norm_num [world12191, agent12191, scalar12191, tp12191, tm12191, ep12191, em12191, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12191, agent12191, tp12191, tm12191, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12191, agent12191, tp12191, tm12191, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12191, agent12191, scalar12191, tp12191, tm12191, ep12191, em12191, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12191, agent12191, tp12191, tm12191, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12191, agent12191, scalar12191, tp12191, tm12191, ep12191, em12191, dsL]

theorem tails12191 :
    exp (-((12191:ℝ)*ep12191)) ≤ scalar12191.upperTail ∧
    exp (-((12191:ℝ)*em12191)) ≤ scalar12191.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12191:ℝ)) (by norm_num [ep12191]) ?_)
      (show bp12191^8 ≤ scalar12191.upperTail by norm_num [bp12191, scalar12191])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12191, bp12191, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12191:ℝ)) (by norm_num [em12191]) ?_)
      (show bm12191^8 ≤ scalar12191.lowerTail by norm_num [bm12191, scalar12191])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12191, bm12191, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12191 :
    agent12191.root+dsL+scalar12191.worldRadius < √(1/100/aL) ∧
    2*(agent12191.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12191, agent12191, scalar12191, tp12191, tm12191, ep12191, em12191, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12191, agent12191, scalar12191, tp12191, tm12191, ep12191, em12191, dsL]

noncomputable def master12191 : MasterCertificate 12191 world12191 agent12191 :=
  master scalar12191 dsL tp12191 tm12191 ep12191 em12191
    (by norm_num [dsL]) (by norm_num [tp12191]) (by norm_num [tm12191])
    (by norm_num [ep12191]) (by norm_num [em12191])
    positive12191 negative12191 tails12191.1 tails12191.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12191.1 tailGuards12191.2

theorem preserves12191 : master12191.toScalarCertificate = scalar12191 := rfl

noncomputable def tp12192 : ℝ := (1188554673 / 5000000000)
noncomputable def tm12192 : ℝ := (-((307420157 / 500000000)))
noncomputable def ep12192 : ℝ := (27359567611408893 / 50000000000000000000)
noncomputable def em12192 : ℝ := (1054929032036093 / 2000000000000000000)
noncomputable def bp12192 : ℝ := (43434348370452029093 / 100000000000000000000)
noncomputable def bm12192 : ℝ := (11189993063688898163 / 25000000000000000000)

theorem positive12192 :
    Eplus aL (agent12192.root+dsL) scalar12192.worldRadius world12192.frame
      agent12192.frame tp12192 ≤ -ep12192 := by
  apply positive_check (eT := (116237021041514223661 / 100000000000000000000)) (y := (19826689422093064411 / 50000000000000000000)) (u := (74333133457066598083 / 50000000000000000000))
  · norm_num [world12192, agent12192, scalar12192, tp12192, tm12192, ep12192, em12192, dsL]
  · norm_num [world12192, agent12192, scalar12192, tp12192, tm12192, ep12192, em12192, dsL]
  · norm_num [world12192, agent12192, scalar12192, tp12192, tm12192, ep12192, em12192, dsL]
  · norm_num [world12192, agent12192, scalar12192, tp12192, tm12192, ep12192, em12192, dsL]
  · norm_num [world12192, agent12192, scalar12192, tp12192, tm12192, ep12192, em12192, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12192, agent12192, tp12192, tm12192, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12192, agent12192, scalar12192, tp12192, tm12192, ep12192, em12192, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12192, agent12192, tp12192, tm12192, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12192, agent12192, scalar12192, tp12192, tm12192, ep12192, em12192, dsL]

theorem negative12192 :
    Eminus aL (agent12192.root+dsL) scalar12192.worldRadius world12192.frame
      agent12192.frame tm12192 ≤ -em12192 := by
  apply negative_check (lo := (67762006187074339483 / 100000000000000000000)) (hi := (16940501546768584871 / 25000000000000000000))
    (y := (-((73286740974816045573 / 100000000000000000000)))) (u := (12013228469981134923 / 25000000000000000000))
  · norm_num [world12192, agent12192, scalar12192, tp12192, tm12192, ep12192, em12192, dsL]
  · norm_num [world12192, agent12192, scalar12192, tp12192, tm12192, ep12192, em12192, dsL]
  · norm_num [world12192, agent12192, scalar12192, tp12192, tm12192, ep12192, em12192, dsL]
  · norm_num [world12192, agent12192, scalar12192, tp12192, tm12192, ep12192, em12192, dsL]
  · norm_num [world12192, agent12192, scalar12192, tp12192, tm12192, ep12192, em12192, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12192, agent12192, tp12192, tm12192, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12192, agent12192, tp12192, tm12192, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12192, agent12192, scalar12192, tp12192, tm12192, ep12192, em12192, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12192, agent12192, tp12192, tm12192, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12192, agent12192, scalar12192, tp12192, tm12192, ep12192, em12192, dsL]

theorem tails12192 :
    exp (-((12192:ℝ)*ep12192)) ≤ scalar12192.upperTail ∧
    exp (-((12192:ℝ)*em12192)) ≤ scalar12192.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12192:ℝ)) (by norm_num [ep12192]) ?_)
      (show bp12192^8 ≤ scalar12192.upperTail by norm_num [bp12192, scalar12192])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12192, bp12192, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12192:ℝ)) (by norm_num [em12192]) ?_)
      (show bm12192^8 ≤ scalar12192.lowerTail by norm_num [bm12192, scalar12192])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12192, bm12192, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12192 :
    agent12192.root+dsL+scalar12192.worldRadius < √(1/100/aL) ∧
    2*(agent12192.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12192, agent12192, scalar12192, tp12192, tm12192, ep12192, em12192, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12192, agent12192, scalar12192, tp12192, tm12192, ep12192, em12192, dsL]

noncomputable def master12192 : MasterCertificate 12192 world12192 agent12192 :=
  master scalar12192 dsL tp12192 tm12192 ep12192 em12192
    (by norm_num [dsL]) (by norm_num [tp12192]) (by norm_num [tm12192])
    (by norm_num [ep12192]) (by norm_num [em12192])
    positive12192 negative12192 tails12192.1 tails12192.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12192.1 tailGuards12192.2

theorem preserves12192 : master12192.toScalarCertificate = scalar12192 := rfl

noncomputable def tp12193 : ℝ := (2377206069 / 10000000000)
noncomputable def tm12193 : ℝ := (-((6148619903 / 10000000000)))
noncomputable def ep12193 : ℝ := (27360981524151171 / 50000000000000000000)
noncomputable def em12193 : ℝ := (52748906327035109 / 100000000000000000000)
noncomputable def bp12193 : ℝ := (4342950577511980427 / 10000000000000000000)
noncomputable def bm12193 : ℝ := (44755346723173459901 / 100000000000000000000)

theorem positive12193 :
    Eplus aL (agent12193.root+dsL) scalar12193.worldRadius world12193.frame
      agent12193.frame tp12193 ≤ -ep12193 := by
  apply positive_check (eT := (116237316848921230481 / 100000000000000000000)) (y := (3965399112132865253 / 10000000000000000000)) (u := (1161462321613209261 / 781250000000000000))
  · norm_num [world12193, agent12193, scalar12193, tp12193, tm12193, ep12193, em12193, dsL]
  · norm_num [world12193, agent12193, scalar12193, tp12193, tm12193, ep12193, em12193, dsL]
  · norm_num [world12193, agent12193, scalar12193, tp12193, tm12193, ep12193, em12193, dsL]
  · norm_num [world12193, agent12193, scalar12193, tp12193, tm12193, ep12193, em12193, dsL]
  · norm_num [world12193, agent12193, scalar12193, tp12193, tm12193, ep12193, em12193, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12193, agent12193, tp12193, tm12193, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12193, agent12193, scalar12193, tp12193, tm12193, ep12193, em12193, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12193, agent12193, tp12193, tm12193, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12193, agent12193, scalar12193, tp12193, tm12193, ep12193, em12193, dsL]

theorem negative12193 :
    Eminus aL (agent12193.root+dsL) scalar12193.worldRadius world12193.frame
      agent12193.frame tm12193 ≤ -em12193 := by
  apply negative_check (lo := (6776170345848318797 / 10000000000000000000)) (hi := (67761703458483187971 / 100000000000000000000))
    (y := (-((2931453229108281457 / 4000000000000000000)))) (u := (1922124440640755961 / 4000000000000000000))
  · norm_num [world12193, agent12193, scalar12193, tp12193, tm12193, ep12193, em12193, dsL]
  · norm_num [world12193, agent12193, scalar12193, tp12193, tm12193, ep12193, em12193, dsL]
  · norm_num [world12193, agent12193, scalar12193, tp12193, tm12193, ep12193, em12193, dsL]
  · norm_num [world12193, agent12193, scalar12193, tp12193, tm12193, ep12193, em12193, dsL]
  · norm_num [world12193, agent12193, scalar12193, tp12193, tm12193, ep12193, em12193, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12193, agent12193, tp12193, tm12193, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12193, agent12193, tp12193, tm12193, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12193, agent12193, scalar12193, tp12193, tm12193, ep12193, em12193, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12193, agent12193, tp12193, tm12193, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12193, agent12193, scalar12193, tp12193, tm12193, ep12193, em12193, dsL]

theorem tails12193 :
    exp (-((12193:ℝ)*ep12193)) ≤ scalar12193.upperTail ∧
    exp (-((12193:ℝ)*em12193)) ≤ scalar12193.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12193:ℝ)) (by norm_num [ep12193]) ?_)
      (show bp12193^8 ≤ scalar12193.upperTail by norm_num [bp12193, scalar12193])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12193, bp12193, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12193:ℝ)) (by norm_num [em12193]) ?_)
      (show bm12193^8 ≤ scalar12193.lowerTail by norm_num [bm12193, scalar12193])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12193, bm12193, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12193 :
    agent12193.root+dsL+scalar12193.worldRadius < √(1/100/aL) ∧
    2*(agent12193.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12193, agent12193, scalar12193, tp12193, tm12193, ep12193, em12193, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12193, agent12193, scalar12193, tp12193, tm12193, ep12193, em12193, dsL]

noncomputable def master12193 : MasterCertificate 12193 world12193 agent12193 :=
  master scalar12193 dsL tp12193 tm12193 ep12193 em12193
    (by norm_num [dsL]) (by norm_num [tp12193]) (by norm_num [tm12193])
    (by norm_num [ep12193]) (by norm_num [em12193])
    positive12193 negative12193 tails12193.1 tails12193.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12193.1 tailGuards12193.2

theorem preserves12193 : master12193.toScalarCertificate = scalar12193 := rfl

noncomputable def tp12194 : ℝ := (148581427 / 625000000)
noncomputable def tm12194 : ℝ := (-((3074418343 / 5000000000)))
noncomputable def ep12194 : ℝ := (5472478943144631 / 10000000000000000000)
noncomputable def em12194 : ℝ := (2637567985822729 / 5000000000000000000)
noncomputable def bp12194 : ℝ := (8684932873478421347 / 20000000000000000000)
noncomputable def bm12194 : ℝ := (44750722306144550379 / 100000000000000000000)

theorem positive12194 :
    Eplus aL (agent12194.root+dsL) scalar12194.worldRadius world12194.frame
      agent12194.frame tp12194 ≤ -ep12194 := by
  apply positive_check (eT := (116237612987629601629 / 100000000000000000000)) (y := (7930920922643763341 / 20000000000000000000)) (u := (74334044615181876961 / 50000000000000000000))
  · norm_num [world12194, agent12194, scalar12194, tp12194, tm12194, ep12194, em12194, dsL]
  · norm_num [world12194, agent12194, scalar12194, tp12194, tm12194, ep12194, em12194, dsL]
  · norm_num [world12194, agent12194, scalar12194, tp12194, tm12194, ep12194, em12194, dsL]
  · norm_num [world12194, agent12194, scalar12194, tp12194, tm12194, ep12194, em12194, dsL]
  · norm_num [world12194, agent12194, scalar12194, tp12194, tm12194, ep12194, em12194, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12194, agent12194, tp12194, tm12194, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12194, agent12194, scalar12194, tp12194, tm12194, ep12194, em12194, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12194, agent12194, tp12194, tm12194, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12194, agent12194, scalar12194, tp12194, tm12194, ep12194, em12194, dsL]

theorem negative12194 :
    Eminus aL (agent12194.root+dsL) scalar12194.worldRadius world12194.frame
      agent12194.frame tm12194 ≤ -em12194 := by
  apply negative_check (lo := (67761400583969724303 / 100000000000000000000)) (hi := (4235087536498107769 / 6250000000000000000))
    (y := (-((14657184312605887063 / 20000000000000000000)))) (u := (6006663454097238489 / 12500000000000000000))
  · norm_num [world12194, agent12194, scalar12194, tp12194, tm12194, ep12194, em12194, dsL]
  · norm_num [world12194, agent12194, scalar12194, tp12194, tm12194, ep12194, em12194, dsL]
  · norm_num [world12194, agent12194, scalar12194, tp12194, tm12194, ep12194, em12194, dsL]
  · norm_num [world12194, agent12194, scalar12194, tp12194, tm12194, ep12194, em12194, dsL]
  · norm_num [world12194, agent12194, scalar12194, tp12194, tm12194, ep12194, em12194, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12194, agent12194, tp12194, tm12194, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12194, agent12194, tp12194, tm12194, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12194, agent12194, scalar12194, tp12194, tm12194, ep12194, em12194, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12194, agent12194, tp12194, tm12194, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12194, agent12194, scalar12194, tp12194, tm12194, ep12194, em12194, dsL]

theorem tails12194 :
    exp (-((12194:ℝ)*ep12194)) ≤ scalar12194.upperTail ∧
    exp (-((12194:ℝ)*em12194)) ≤ scalar12194.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12194:ℝ)) (by norm_num [ep12194]) ?_)
      (show bp12194^8 ≤ scalar12194.upperTail by norm_num [bp12194, scalar12194])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12194, bp12194, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12194:ℝ)) (by norm_num [em12194]) ?_)
      (show bm12194^8 ≤ scalar12194.lowerTail by norm_num [bm12194, scalar12194])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12194, bm12194, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12194 :
    agent12194.root+dsL+scalar12194.worldRadius < √(1/100/aL) ∧
    2*(agent12194.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12194, agent12194, scalar12194, tp12194, tm12194, ep12194, em12194, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12194, agent12194, scalar12194, tp12194, tm12194, ep12194, em12194, dsL]

noncomputable def master12194 : MasterCertificate 12194 world12194 agent12194 :=
  master scalar12194 dsL tp12194 tm12194 ep12194 em12194
    (by norm_num [dsL]) (by norm_num [tp12194]) (by norm_num [tm12194])
    (by norm_num [ep12194]) (by norm_num [em12194])
    positive12194 negative12194 tails12194.1 tails12194.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12194.1 tailGuards12194.2

theorem preserves12194 : master12194.toScalarCertificate = scalar12194 := rfl

noncomputable def tp12195 : ℝ := (4754799 / 20000000)
noncomputable def tm12195 : ℝ := (-((6149053211 / 10000000000)))
noncomputable def ep12195 : ℝ := (10945522839807823 / 20000000000000000000)
noncomputable def em12195 : ℝ := (52753811602301461 / 100000000000000000000)
noncomputable def bp12195 : ℝ := (43419824261871758527 / 100000000000000000000)
noncomputable def bm12195 : ℝ := (22373049559038103797 / 50000000000000000000)

theorem positive12195 :
    Eplus aL (agent12195.root+dsL) scalar12195.worldRadius world12195.frame
      agent12195.frame tp12195 ≤ -ep12195 := by
  apply positive_check (eT := (116237908464426384877 / 100000000000000000000)) (y := (19827608580361652059 / 50000000000000000000)) (u := (74334499947911715031 / 50000000000000000000))
  · norm_num [world12195, agent12195, scalar12195, tp12195, tm12195, ep12195, em12195, dsL]
  · norm_num [world12195, agent12195, scalar12195, tp12195, tm12195, ep12195, em12195, dsL]
  · norm_num [world12195, agent12195, scalar12195, tp12195, tm12195, ep12195, em12195, dsL]
  · norm_num [world12195, agent12195, scalar12195, tp12195, tm12195, ep12195, em12195, dsL]
  · norm_num [world12195, agent12195, scalar12195, tp12195, tm12195, ep12195, em12195, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12195, agent12195, tp12195, tm12195, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12195, agent12195, scalar12195, tp12195, tm12195, ep12195, em12195, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12195, agent12195, tp12195, tm12195, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12195, agent12195, scalar12195, tp12195, tm12195, ep12195, em12195, dsL]

theorem negative12195 :
    Eminus aL (agent12195.root+dsL) scalar12195.worldRadius world12195.frame
      agent12195.frame tm12195 ≤ -em12195 := by
  apply negative_check (lo := (67761098755828851457 / 100000000000000000000)) (hi := (33880549377914425729 / 50000000000000000000))
    (y := (-((73285511486111153719 / 100000000000000000000)))) (u := (48053504688705020943 / 100000000000000000000))
  · norm_num [world12195, agent12195, scalar12195, tp12195, tm12195, ep12195, em12195, dsL]
  · norm_num [world12195, agent12195, scalar12195, tp12195, tm12195, ep12195, em12195, dsL]
  · norm_num [world12195, agent12195, scalar12195, tp12195, tm12195, ep12195, em12195, dsL]
  · norm_num [world12195, agent12195, scalar12195, tp12195, tm12195, ep12195, em12195, dsL]
  · norm_num [world12195, agent12195, scalar12195, tp12195, tm12195, ep12195, em12195, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12195, agent12195, tp12195, tm12195, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12195, agent12195, tp12195, tm12195, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12195, agent12195, scalar12195, tp12195, tm12195, ep12195, em12195, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12195, agent12195, tp12195, tm12195, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12195, agent12195, scalar12195, tp12195, tm12195, ep12195, em12195, dsL]

theorem tails12195 :
    exp (-((12195:ℝ)*ep12195)) ≤ scalar12195.upperTail ∧
    exp (-((12195:ℝ)*em12195)) ≤ scalar12195.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12195:ℝ)) (by norm_num [ep12195]) ?_)
      (show bp12195^8 ≤ scalar12195.upperTail by norm_num [bp12195, scalar12195])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12195, bp12195, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12195:ℝ)) (by norm_num [em12195]) ?_)
      (show bm12195^8 ≤ scalar12195.lowerTail by norm_num [bm12195, scalar12195])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12195, bm12195, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12195 :
    agent12195.root+dsL+scalar12195.worldRadius < √(1/100/aL) ∧
    2*(agent12195.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12195, agent12195, scalar12195, tp12195, tm12195, ep12195, em12195, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12195, agent12195, scalar12195, tp12195, tm12195, ep12195, em12195, dsL]

noncomputable def master12195 : MasterCertificate 12195 world12195 agent12195 :=
  master scalar12195 dsL tp12195 tm12195 ep12195 em12195
    (by norm_num [dsL]) (by norm_num [tp12195]) (by norm_num [tm12195])
    (by norm_num [ep12195]) (by norm_num [em12195])
    positive12195 negative12195 tails12195.1 tails12195.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12195.1 tailGuards12195.2

theorem preserves12195 : master12195.toScalarCertificate = scalar12195 := rfl

noncomputable def tp12196 : ℝ := (1188748057 / 5000000000)
noncomputable def tm12196 : ℝ := (-((3074634847 / 5000000000)))
noncomputable def ep12196 : ℝ := (27365218944215103 / 50000000000000000000)
noncomputable def em12196 : ℝ := (3297266403743643 / 6250000000000000000)
noncomputable def bp12196 : ℝ := (43414985102855766101 / 100000000000000000000)
noncomputable def bm12196 : ℝ := (2237073841736436061 / 5000000000000000000)

theorem positive12196 :
    Eplus aL (agent12196.root+dsL) scalar12196.worldRadius world12196.frame
      agent12196.frame tp12196 ≤ -ep12196 := by
  apply positive_check (eT := (116238203580989562139 / 100000000000000000000)) (y := (39655829234611447291 / 100000000000000000000)) (u := (148669909862736388089 / 100000000000000000000))
  · norm_num [world12196, agent12196, scalar12196, tp12196, tm12196, ep12196, em12196, dsL]
  · norm_num [world12196, agent12196, scalar12196, tp12196, tm12196, ep12196, em12196, dsL]
  · norm_num [world12196, agent12196, scalar12196, tp12196, tm12196, ep12196, em12196, dsL]
  · norm_num [world12196, agent12196, scalar12196, tp12196, tm12196, ep12196, em12196, dsL]
  · norm_num [world12196, agent12196, scalar12196, tp12196, tm12196, ep12196, em12196, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12196, agent12196, tp12196, tm12196, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12196, agent12196, scalar12196, tp12196, tm12196, ep12196, em12196, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12196, agent12196, tp12196, tm12196, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12196, agent12196, scalar12196, tp12196, tm12196, ep12196, em12196, dsL]

theorem negative12196 :
    Eminus aL (agent12196.root+dsL) scalar12196.worldRadius world12196.frame
      agent12196.frame tm12196 ≤ -em12196 := by
  apply negative_check (lo := (67760797047625226869 / 100000000000000000000)) (hi := (6776079704762522687 / 10000000000000000000))
    (y := (-((73285101889635034093 / 100000000000000000000)))) (u := (48053701514569973487 / 100000000000000000000))
  · norm_num [world12196, agent12196, scalar12196, tp12196, tm12196, ep12196, em12196, dsL]
  · norm_num [world12196, agent12196, scalar12196, tp12196, tm12196, ep12196, em12196, dsL]
  · norm_num [world12196, agent12196, scalar12196, tp12196, tm12196, ep12196, em12196, dsL]
  · norm_num [world12196, agent12196, scalar12196, tp12196, tm12196, ep12196, em12196, dsL]
  · norm_num [world12196, agent12196, scalar12196, tp12196, tm12196, ep12196, em12196, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12196, agent12196, tp12196, tm12196, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12196, agent12196, tp12196, tm12196, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12196, agent12196, scalar12196, tp12196, tm12196, ep12196, em12196, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12196, agent12196, tp12196, tm12196, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12196, agent12196, scalar12196, tp12196, tm12196, ep12196, em12196, dsL]

theorem tails12196 :
    exp (-((12196:ℝ)*ep12196)) ≤ scalar12196.upperTail ∧
    exp (-((12196:ℝ)*em12196)) ≤ scalar12196.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12196:ℝ)) (by norm_num [ep12196]) ?_)
      (show bp12196^8 ≤ scalar12196.upperTail by norm_num [bp12196, scalar12196])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12196, bp12196, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12196:ℝ)) (by norm_num [em12196]) ?_)
      (show bm12196^8 ≤ scalar12196.lowerTail by norm_num [bm12196, scalar12196])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12196, bm12196, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12196 :
    agent12196.root+dsL+scalar12196.worldRadius < √(1/100/aL) ∧
    2*(agent12196.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12196, agent12196, scalar12196, tp12196, tm12196, ep12196, em12196, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12196, agent12196, scalar12196, tp12196, tm12196, ep12196, em12196, dsL]

noncomputable def master12196 : MasterCertificate 12196 world12196 agent12196 :=
  master scalar12196 dsL tp12196 tm12196 ep12196 em12196
    (by norm_num [dsL]) (by norm_num [tp12196]) (by norm_num [tm12196])
    (by norm_num [ep12196]) (by norm_num [em12196])
    positive12196 negative12196 tails12196.1 tails12196.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12196.1 tailGuards12196.2

theorem preserves12196 : master12196.toScalarCertificate = scalar12196 := rfl

noncomputable def tp12197 : ℝ := (1188796363 / 5000000000)
noncomputable def tm12197 : ℝ := (-((6149486083 / 10000000000)))
noncomputable def ep12197 : ℝ := (54733259503979259 / 100000000000000000000)
noncomputable def em12197 : ℝ := (26379355691403263 / 50000000000000000000)
noncomputable def bp12197 : ℝ := (10852536887319992069 / 25000000000000000000)
noncomputable def bm12197 : ℝ := (22368428037173388839 / 50000000000000000000)

theorem positive12197 :
    Eplus aL (agent12197.root+dsL) scalar12197.worldRadius world12197.frame
      agent12197.frame tp12197 ≤ -ep12197 := by
  apply positive_check (eT := (4649539948794633327 / 4000000000000000000)) (y := (3965644197933912501 / 10000000000000000000)) (u := (148670820832561672161 / 100000000000000000000))
  · norm_num [world12197, agent12197, scalar12197, tp12197, tm12197, ep12197, em12197, dsL]
  · norm_num [world12197, agent12197, scalar12197, tp12197, tm12197, ep12197, em12197, dsL]
  · norm_num [world12197, agent12197, scalar12197, tp12197, tm12197, ep12197, em12197, dsL]
  · norm_num [world12197, agent12197, scalar12197, tp12197, tm12197, ep12197, em12197, dsL]
  · norm_num [world12197, agent12197, scalar12197, tp12197, tm12197, ep12197, em12197, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12197, agent12197, tp12197, tm12197, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12197, agent12197, scalar12197, tp12197, tm12197, ep12197, em12197, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12197, agent12197, tp12197, tm12197, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12197, agent12197, scalar12197, tp12197, tm12197, ep12197, em12197, dsL]

theorem negative12197 :
    Eminus aL (agent12197.root+dsL) scalar12197.worldRadius world12197.frame
      agent12197.frame tm12197 ≤ -em12197 := by
  apply negative_check (lo := (13552099136474864357 / 20000000000000000000)) (hi := (33880247841187160893 / 50000000000000000000))
    (y := (-((73284692428680652077 / 100000000000000000000)))) (u := (48053898276117641511 / 100000000000000000000))
  · norm_num [world12197, agent12197, scalar12197, tp12197, tm12197, ep12197, em12197, dsL]
  · norm_num [world12197, agent12197, scalar12197, tp12197, tm12197, ep12197, em12197, dsL]
  · norm_num [world12197, agent12197, scalar12197, tp12197, tm12197, ep12197, em12197, dsL]
  · norm_num [world12197, agent12197, scalar12197, tp12197, tm12197, ep12197, em12197, dsL]
  · norm_num [world12197, agent12197, scalar12197, tp12197, tm12197, ep12197, em12197, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12197, agent12197, tp12197, tm12197, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12197, agent12197, tp12197, tm12197, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12197, agent12197, scalar12197, tp12197, tm12197, ep12197, em12197, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12197, agent12197, tp12197, tm12197, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12197, agent12197, scalar12197, tp12197, tm12197, ep12197, em12197, dsL]

theorem tails12197 :
    exp (-((12197:ℝ)*ep12197)) ≤ scalar12197.upperTail ∧
    exp (-((12197:ℝ)*em12197)) ≤ scalar12197.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12197:ℝ)) (by norm_num [ep12197]) ?_)
      (show bp12197^8 ≤ scalar12197.upperTail by norm_num [bp12197, scalar12197])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12197, bp12197, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12197:ℝ)) (by norm_num [em12197]) ?_)
      (show bm12197^8 ≤ scalar12197.lowerTail by norm_num [bm12197, scalar12197])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12197, bm12197, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12197 :
    agent12197.root+dsL+scalar12197.worldRadius < √(1/100/aL) ∧
    2*(agent12197.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12197, agent12197, scalar12197, tp12197, tm12197, ep12197, em12197, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12197, agent12197, scalar12197, tp12197, tm12197, ep12197, em12197, dsL]

noncomputable def master12197 : MasterCertificate 12197 world12197 agent12197 :=
  master scalar12197 dsL tp12197 tm12197 ep12197 em12197
    (by norm_num [dsL]) (by norm_num [tp12197]) (by norm_num [tm12197])
    (by norm_num [ep12197]) (by norm_num [em12197])
    positive12197 negative12197 tails12197.1 tails12197.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12197.1 tailGuards12197.2

theorem preserves12197 : master12197.toScalarCertificate = scalar12197 := rfl

noncomputable def tp12198 : ℝ := (2377689199 / 10000000000)
noncomputable def tm12198 : ℝ := (-((3074851167 / 5000000000)))
noncomputable def ep12198 : ℝ := (27368039828316759 / 50000000000000000000)
noncomputable def em12198 : ℝ := (26380579480226943 / 50000000000000000000)
noncomputable def bp12198 : ℝ := (43405311196726814377 / 100000000000000000000)
noncomputable def bm12198 : ℝ := (44732236434859679737 / 100000000000000000000)

theorem positive12198 :
    Eplus aL (agent12198.root+dsL) scalar12198.worldRadius world12198.frame
      agent12198.frame tp12198 ≤ -ep12198 := by
  apply positive_check (eT := (116238792873212360701 / 100000000000000000000)) (y := (19828526414180316087 / 50000000000000000000)) (u := (148671728989589725869 / 100000000000000000000))
  · norm_num [world12198, agent12198, scalar12198, tp12198, tm12198, ep12198, em12198, dsL]
  · norm_num [world12198, agent12198, scalar12198, tp12198, tm12198, ep12198, em12198, dsL]
  · norm_num [world12198, agent12198, scalar12198, tp12198, tm12198, ep12198, em12198, dsL]
  · norm_num [world12198, agent12198, scalar12198, tp12198, tm12198, ep12198, em12198, dsL]
  · norm_num [world12198, agent12198, scalar12198, tp12198, tm12198, ep12198, em12198, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12198, agent12198, tp12198, tm12198, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12198, agent12198, scalar12198, tp12198, tm12198, ep12198, em12198, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12198, agent12198, tp12198, tm12198, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12198, agent12198, scalar12198, tp12198, tm12198, ep12198, em12198, dsL]

theorem negative12198 :
    Eminus aL (agent12198.root+dsL) scalar12198.worldRadius world12198.frame
      agent12198.frame tm12198 ≤ -em12198 := by
  apply negative_check (lo := (67760194848759830631 / 100000000000000000000)) (hi := (8470024356094978829 / 12500000000000000000))
    (y := (-((9160535365992304313 / 12500000000000000000)))) (u := (48054095057590657211 / 100000000000000000000))
  · norm_num [world12198, agent12198, scalar12198, tp12198, tm12198, ep12198, em12198, dsL]
  · norm_num [world12198, agent12198, scalar12198, tp12198, tm12198, ep12198, em12198, dsL]
  · norm_num [world12198, agent12198, scalar12198, tp12198, tm12198, ep12198, em12198, dsL]
  · norm_num [world12198, agent12198, scalar12198, tp12198, tm12198, ep12198, em12198, dsL]
  · norm_num [world12198, agent12198, scalar12198, tp12198, tm12198, ep12198, em12198, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12198, agent12198, tp12198, tm12198, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12198, agent12198, tp12198, tm12198, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12198, agent12198, scalar12198, tp12198, tm12198, ep12198, em12198, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12198, agent12198, tp12198, tm12198, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12198, agent12198, scalar12198, tp12198, tm12198, ep12198, em12198, dsL]

theorem tails12198 :
    exp (-((12198:ℝ)*ep12198)) ≤ scalar12198.upperTail ∧
    exp (-((12198:ℝ)*em12198)) ≤ scalar12198.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12198:ℝ)) (by norm_num [ep12198]) ?_)
      (show bp12198^8 ≤ scalar12198.upperTail by norm_num [bp12198, scalar12198])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12198, bp12198, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12198:ℝ)) (by norm_num [em12198]) ?_)
      (show bm12198^8 ≤ scalar12198.lowerTail by norm_num [bm12198, scalar12198])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12198, bm12198, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12198 :
    agent12198.root+dsL+scalar12198.worldRadius < √(1/100/aL) ∧
    2*(agent12198.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12198, agent12198, scalar12198, tp12198, tm12198, ep12198, em12198, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12198, agent12198, scalar12198, tp12198, tm12198, ep12198, em12198, dsL]

noncomputable def master12198 : MasterCertificate 12198 world12198 agent12198 :=
  master scalar12198 dsL tp12198 tm12198 ep12198 em12198
    (by norm_num [dsL]) (by norm_num [tp12198]) (by norm_num [tm12198])
    (by norm_num [ep12198]) (by norm_num [em12198])
    positive12198 negative12198 tails12198.1 tails12198.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12198.1 tailGuards12198.2

theorem preserves12198 : master12198.toScalarCertificate = scalar12198 := rfl

noncomputable def tp12199 : ℝ := (475557139 / 2000000000)
noncomputable def tm12199 : ℝ := (-((6149918453 / 10000000000)))
noncomputable def ep12199 : ℝ := (10947779618942783 / 20000000000000000000)
noncomputable def em12199 : ℝ := (52763604906841863 / 100000000000000000000)
noncomputable def bp12199 : ℝ := (1736019048468601469 / 4000000000000000000)
noncomputable def bm12199 : ℝ := (22363809055653436797 / 50000000000000000000)

theorem positive12199 :
    Eplus aL (agent12199.root+dsL) scalar12199.worldRadius world12199.frame
      agent12199.frame tp12199 ≤ -ep12199 := by
  apply positive_check (eT := (29059771808210004907 / 25000000000000000000)) (y := (39657664797900013639 / 100000000000000000000)) (u := (74336319409034373829 / 50000000000000000000))
  · norm_num [world12199, agent12199, scalar12199, tp12199, tm12199, ep12199, em12199, dsL]
  · norm_num [world12199, agent12199, scalar12199, tp12199, tm12199, ep12199, em12199, dsL]
  · norm_num [world12199, agent12199, scalar12199, tp12199, tm12199, ep12199, em12199, dsL]
  · norm_num [world12199, agent12199, scalar12199, tp12199, tm12199, ep12199, em12199, dsL]
  · norm_num [world12199, agent12199, scalar12199, tp12199, tm12199, ep12199, em12199, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12199, agent12199, tp12199, tm12199, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12199, agent12199, scalar12199, tp12199, tm12199, ep12199, em12199, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12199, agent12199, tp12199, tm12199, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12199, agent12199, scalar12199, tp12199, tm12199, ep12199, em12199, dsL]

theorem negative12199 :
    Eminus aL (agent12199.root+dsL) scalar12199.worldRadius world12199.frame
      agent12199.frame tm12199 ≤ -em12199 := by
  apply negative_check (lo := (33879947260475222881 / 50000000000000000000)) (hi := (67759894520950445763 / 100000000000000000000))
    (y := (-((1832096829869596099 / 2500000000000000000)))) (u := (48054291951553616263 / 100000000000000000000))
  · norm_num [world12199, agent12199, scalar12199, tp12199, tm12199, ep12199, em12199, dsL]
  · norm_num [world12199, agent12199, scalar12199, tp12199, tm12199, ep12199, em12199, dsL]
  · norm_num [world12199, agent12199, scalar12199, tp12199, tm12199, ep12199, em12199, dsL]
  · norm_num [world12199, agent12199, scalar12199, tp12199, tm12199, ep12199, em12199, dsL]
  · norm_num [world12199, agent12199, scalar12199, tp12199, tm12199, ep12199, em12199, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12199, agent12199, tp12199, tm12199, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12199, agent12199, tp12199, tm12199, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12199, agent12199, scalar12199, tp12199, tm12199, ep12199, em12199, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12199, agent12199, tp12199, tm12199, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12199, agent12199, scalar12199, tp12199, tm12199, ep12199, em12199, dsL]

theorem tails12199 :
    exp (-((12199:ℝ)*ep12199)) ≤ scalar12199.upperTail ∧
    exp (-((12199:ℝ)*em12199)) ≤ scalar12199.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12199:ℝ)) (by norm_num [ep12199]) ?_)
      (show bp12199^8 ≤ scalar12199.upperTail by norm_num [bp12199, scalar12199])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12199, bp12199, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12199:ℝ)) (by norm_num [em12199]) ?_)
      (show bm12199^8 ≤ scalar12199.lowerTail by norm_num [bm12199, scalar12199])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12199, bm12199, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12199 :
    agent12199.root+dsL+scalar12199.worldRadius < √(1/100/aL) ∧
    2*(agent12199.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12199, agent12199, scalar12199, tp12199, tm12199, ep12199, em12199, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12199, agent12199, scalar12199, tp12199, tm12199, ep12199, em12199, dsL]

noncomputable def master12199 : MasterCertificate 12199 world12199 agent12199 :=
  master scalar12199 dsL tp12199 tm12199 ep12199 em12199
    (by norm_num [dsL]) (by norm_num [tp12199]) (by norm_num [tm12199])
    (by norm_num [ep12199]) (by norm_num [em12199])
    positive12199 negative12199 tails12199.1 tails12199.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12199.1 tailGuards12199.2

theorem preserves12199 : master12199.toScalarCertificate = scalar12199 := rfl

noncomputable def tp12200 : ℝ := (14861763 / 62500000)
noncomputable def tm12200 : ℝ := (-((3075067227 / 5000000000)))
noncomputable def ep12200 : ℝ := (27370857793112747 / 50000000000000000000)
noncomputable def em12200 : ℝ := (26383024986604623 / 50000000000000000000)
noncomputable def bp12200 : ℝ := (5424455260741698171 / 12500000000000000000)
noncomputable def bm12200 : ℝ := (44723000591288638567 / 100000000000000000000)

theorem positive12200 :
    Eplus aL (agent12200.root+dsL) scalar12200.worldRadius world12200.frame
      agent12200.frame tp12200 ≤ -ep12200 := by
  apply positive_check (eT := (23247876162589994331 / 20000000000000000000)) (y := (19829137607715926827 / 50000000000000000000)) (u := (148673546344690990319 / 100000000000000000000))
  · norm_num [world12200, agent12200, scalar12200, tp12200, tm12200, ep12200, em12200, dsL]
  · norm_num [world12200, agent12200, scalar12200, tp12200, tm12200, ep12200, em12200, dsL]
  · norm_num [world12200, agent12200, scalar12200, tp12200, tm12200, ep12200, em12200, dsL]
  · norm_num [world12200, agent12200, scalar12200, tp12200, tm12200, ep12200, em12200, dsL]
  · norm_num [world12200, agent12200, scalar12200, tp12200, tm12200, ep12200, em12200, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12200, agent12200, tp12200, tm12200, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12200, agent12200, scalar12200, tp12200, tm12200, ep12200, em12200, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12200, agent12200, tp12200, tm12200, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12200, agent12200, scalar12200, tp12200, tm12200, ep12200, em12200, dsL]

theorem negative12200 :
    Eminus aL (agent12200.root+dsL) scalar12200.worldRadius world12200.frame
      agent12200.frame tm12200 ≤ -em12200 := by
  apply negative_check (lo := (67759594638979775853 / 100000000000000000000)) (hi := (33879797319489887927 / 50000000000000000000))
    (y := (-((18320865830954112001 / 25000000000000000000)))) (u := (9610897782509711213 / 20000000000000000000))
  · norm_num [world12200, agent12200, scalar12200, tp12200, tm12200, ep12200, em12200, dsL]
  · norm_num [world12200, agent12200, scalar12200, tp12200, tm12200, ep12200, em12200, dsL]
  · norm_num [world12200, agent12200, scalar12200, tp12200, tm12200, ep12200, em12200, dsL]
  · norm_num [world12200, agent12200, scalar12200, tp12200, tm12200, ep12200, em12200, dsL]
  · norm_num [world12200, agent12200, scalar12200, tp12200, tm12200, ep12200, em12200, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12200, agent12200, tp12200, tm12200, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12200, agent12200, tp12200, tm12200, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12200, agent12200, scalar12200, tp12200, tm12200, ep12200, em12200, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12200, agent12200, tp12200, tm12200, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12200, agent12200, scalar12200, tp12200, tm12200, ep12200, em12200, dsL]

theorem tails12200 :
    exp (-((12200:ℝ)*ep12200)) ≤ scalar12200.upperTail ∧
    exp (-((12200:ℝ)*em12200)) ≤ scalar12200.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12200:ℝ)) (by norm_num [ep12200]) ?_)
      (show bp12200^8 ≤ scalar12200.upperTail by norm_num [bp12200, scalar12200])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12200, bp12200, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12200:ℝ)) (by norm_num [em12200]) ?_)
      (show bm12200^8 ≤ scalar12200.lowerTail by norm_num [bm12200, scalar12200])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12200, bm12200, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12200 :
    agent12200.root+dsL+scalar12200.worldRadius < √(1/100/aL) ∧
    2*(agent12200.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12200, agent12200, scalar12200, tp12200, tm12200, ep12200, em12200, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12200, agent12200, scalar12200, tp12200, tm12200, ep12200, em12200, dsL]

noncomputable def master12200 : MasterCertificate 12200 world12200 agent12200 :=
  master scalar12200 dsL tp12200 tm12200 ep12200 em12200
    (by norm_num [dsL]) (by norm_num [tp12200]) (by norm_num [tm12200])
    (by norm_num [ep12200]) (by norm_num [em12200])
    positive12200 negative12200 tails12200.1 tails12200.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12200.1 tailGuards12200.2

theorem preserves12200 : master12200.toScalarCertificate = scalar12200 := rfl

noncomputable def tp12201 : ℝ := (2377978481 / 10000000000)
noncomputable def tm12201 : ℝ := (-((1230070067 / 2000000000)))
noncomputable def ep12201 : ℝ := (10948906194724231 / 20000000000000000000)
noncomputable def em12201 : ℝ := (52768493087226317 / 100000000000000000000)
noncomputable def bp12201 : ℝ := (1084770239634810799 / 2500000000000000000)
noncomputable def bm12201 : ℝ := (22359192303071535847 / 50000000000000000000)

theorem positive12201 :
    Eplus aL (agent12201.root+dsL) scalar12201.worldRadius world12201.frame
      agent12201.frame tp12201 ≤ -ep12201 := by
  apply positive_check (eT := (23247934909566448049 / 20000000000000000000)) (y := (7931777346526924791 / 20000000000000000000)) (u := (148674455511782710531 / 100000000000000000000))
  · norm_num [world12201, agent12201, scalar12201, tp12201, tm12201, ep12201, em12201, dsL]
  · norm_num [world12201, agent12201, scalar12201, tp12201, tm12201, ep12201, em12201, dsL]
  · norm_num [world12201, agent12201, scalar12201, tp12201, tm12201, ep12201, em12201, dsL]
  · norm_num [world12201, agent12201, scalar12201, tp12201, tm12201, ep12201, em12201, dsL]
  · norm_num [world12201, agent12201, scalar12201, tp12201, tm12201, ep12201, em12201, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12201, agent12201, tp12201, tm12201, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12201, agent12201, scalar12201, tp12201, tm12201, ep12201, em12201, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12201, agent12201, tp12201, tm12201, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12201, agent12201, scalar12201, tp12201, tm12201, ep12201, em12201, dsL]

theorem negative12201 :
    Eminus aL (agent12201.root+dsL) scalar12201.worldRadius world12201.frame
      agent12201.frame tm12201 ≤ -em12201 := by
  apply negative_check (lo := (8469911901416125093 / 12500000000000000000)) (hi := (13551859042265800149 / 20000000000000000000))
    (y := (-((916038171913191861 / 1250000000000000000)))) (u := (12013671432521897689 / 25000000000000000000))
  · norm_num [world12201, agent12201, scalar12201, tp12201, tm12201, ep12201, em12201, dsL]
  · norm_num [world12201, agent12201, scalar12201, tp12201, tm12201, ep12201, em12201, dsL]
  · norm_num [world12201, agent12201, scalar12201, tp12201, tm12201, ep12201, em12201, dsL]
  · norm_num [world12201, agent12201, scalar12201, tp12201, tm12201, ep12201, em12201, dsL]
  · norm_num [world12201, agent12201, scalar12201, tp12201, tm12201, ep12201, em12201, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12201, agent12201, tp12201, tm12201, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12201, agent12201, tp12201, tm12201, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12201, agent12201, scalar12201, tp12201, tm12201, ep12201, em12201, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12201, agent12201, tp12201, tm12201, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12201, agent12201, scalar12201, tp12201, tm12201, ep12201, em12201, dsL]

theorem tails12201 :
    exp (-((12201:ℝ)*ep12201)) ≤ scalar12201.upperTail ∧
    exp (-((12201:ℝ)*em12201)) ≤ scalar12201.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12201:ℝ)) (by norm_num [ep12201]) ?_)
      (show bp12201^8 ≤ scalar12201.upperTail by norm_num [bp12201, scalar12201])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12201, bp12201, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12201:ℝ)) (by norm_num [em12201]) ?_)
      (show bm12201^8 ≤ scalar12201.lowerTail by norm_num [bm12201, scalar12201])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12201, bm12201, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12201 :
    agent12201.root+dsL+scalar12201.worldRadius < √(1/100/aL) ∧
    2*(agent12201.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12201, agent12201, scalar12201, tp12201, tm12201, ep12201, em12201, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12201, agent12201, scalar12201, tp12201, tm12201, ep12201, em12201, dsL]

noncomputable def master12201 : MasterCertificate 12201 world12201 agent12201 :=
  master scalar12201 dsL tp12201 tm12201 ep12201 em12201
    (by norm_num [dsL]) (by norm_num [tp12201]) (by norm_num [tm12201])
    (by norm_num [ep12201]) (by norm_num [em12201])
    positive12201 negative12201 tails12201.1 tails12201.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12201.1 tailGuards12201.2

theorem preserves12201 : master12201.toScalarCertificate = scalar12201 := rfl

noncomputable def tp12202 : ℝ := (118903739 / 500000000)
noncomputable def tm12202 : ℝ := (-((615056603 / 1000000000)))
noncomputable def ep12202 : ℝ := (54747344323754401 / 100000000000000000000)
noncomputable def em12202 : ℝ := (8443349486427 / 16000000000000000)
noncomputable def bp12202 : ℝ := (21692989332885457761 / 50000000000000000000)
noncomputable def bm12202 : ℝ := (22356885063835397697 / 50000000000000000000)

theorem positive12202 :
    Eplus aL (agent12202.root+dsL) scalar12202.worldRadius world12202.frame
      agent12202.frame tp12202 ≤ -ep12202 := by
  apply positive_check (eT := (116239967569452916073 / 100000000000000000000)) (y := (9914874253938239861 / 25000000000000000000)) (u := (74337681424827319131 / 50000000000000000000))
  · norm_num [world12202, agent12202, scalar12202, tp12202, tm12202, ep12202, em12202, dsL]
  · norm_num [world12202, agent12202, scalar12202, tp12202, tm12202, ep12202, em12202, dsL]
  · norm_num [world12202, agent12202, scalar12202, tp12202, tm12202, ep12202, em12202, dsL]
  · norm_num [world12202, agent12202, scalar12202, tp12202, tm12202, ep12202, em12202, dsL]
  · norm_num [world12202, agent12202, scalar12202, tp12202, tm12202, ep12202, em12202, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12202, agent12202, tp12202, tm12202, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12202, agent12202, scalar12202, tp12202, tm12202, ep12202, em12202, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12202, agent12202, tp12202, tm12202, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12202, agent12202, scalar12202, tp12202, tm12202, ep12202, em12202, dsL]

theorem negative12202 :
    Eminus aL (agent12202.root+dsL) scalar12202.worldRadius world12202.frame
      agent12202.frame tm12202 ≤ -em12202 := by
  apply negative_check (lo := (33879498260512753627 / 50000000000000000000)) (hi := (13551799304205101451 / 20000000000000000000))
    (y := (-((18320660749330124019 / 25000000000000000000)))) (u := (12013720779467620781 / 25000000000000000000))
  · norm_num [world12202, agent12202, scalar12202, tp12202, tm12202, ep12202, em12202, dsL]
  · norm_num [world12202, agent12202, scalar12202, tp12202, tm12202, ep12202, em12202, dsL]
  · norm_num [world12202, agent12202, scalar12202, tp12202, tm12202, ep12202, em12202, dsL]
  · norm_num [world12202, agent12202, scalar12202, tp12202, tm12202, ep12202, em12202, dsL]
  · norm_num [world12202, agent12202, scalar12202, tp12202, tm12202, ep12202, em12202, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12202, agent12202, tp12202, tm12202, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12202, agent12202, tp12202, tm12202, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12202, agent12202, scalar12202, tp12202, tm12202, ep12202, em12202, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12202, agent12202, tp12202, tm12202, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12202, agent12202, scalar12202, tp12202, tm12202, ep12202, em12202, dsL]

theorem tails12202 :
    exp (-((12202:ℝ)*ep12202)) ≤ scalar12202.upperTail ∧
    exp (-((12202:ℝ)*em12202)) ≤ scalar12202.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12202:ℝ)) (by norm_num [ep12202]) ?_)
      (show bp12202^8 ≤ scalar12202.upperTail by norm_num [bp12202, scalar12202])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12202, bp12202, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12202:ℝ)) (by norm_num [em12202]) ?_)
      (show bm12202^8 ≤ scalar12202.lowerTail by norm_num [bm12202, scalar12202])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12202, bm12202, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12202 :
    agent12202.root+dsL+scalar12202.worldRadius < √(1/100/aL) ∧
    2*(agent12202.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12202, agent12202, scalar12202, tp12202, tm12202, ep12202, em12202, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12202, agent12202, scalar12202, tp12202, tm12202, ep12202, em12202, dsL]

noncomputable def master12202 : MasterCertificate 12202 world12202 agent12202 :=
  master scalar12202 dsL tp12202 tm12202 ep12202 em12202
    (by norm_num [dsL]) (by norm_num [tp12202]) (by norm_num [tm12202])
    (by norm_num [ep12202]) (by norm_num [em12202])
    positive12202 negative12202 tails12202.1 tails12202.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12202.1 tailGuards12202.2

theorem preserves12202 : master12202.toScalarCertificate = scalar12202 := rfl

noncomputable def tp12203 : ℝ := (47563421 / 200000000)
noncomputable def tm12203 : ℝ := (-((192211927 / 312500000)))
noncomputable def ep12203 : ℝ := (27375078530411807 / 50000000000000000000)
noncomputable def em12203 : ℝ := (10554674980495279 / 20000000000000000000)
noncomputable def bp12203 : ℝ := (43381148384564278227 / 100000000000000000000)
noncomputable def bm12203 : ℝ := (5588644531913438613 / 12500000000000000000)

theorem positive12203 :
    Eplus aL (agent12203.root+dsL) scalar12203.worldRadius world12203.frame
      agent12203.frame tp12203 ≤ -ep12203 := by
  apply positive_check (eT := (116240260414827778429 / 100000000000000000000)) (y := (19830053663505196551 / 50000000000000000000)) (u := (18584533779362509297 / 12500000000000000000))
  · norm_num [world12203, agent12203, scalar12203, tp12203, tm12203, ep12203, em12203, dsL]
  · norm_num [world12203, agent12203, scalar12203, tp12203, tm12203, ep12203, em12203, dsL]
  · norm_num [world12203, agent12203, scalar12203, tp12203, tm12203, ep12203, em12203, dsL]
  · norm_num [world12203, agent12203, scalar12203, tp12203, tm12203, ep12203, em12203, dsL]
  · norm_num [world12203, agent12203, scalar12203, tp12203, tm12203, ep12203, em12203, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12203, agent12203, tp12203, tm12203, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12203, agent12203, scalar12203, tp12203, tm12203, ep12203, em12203, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12203, agent12203, tp12203, tm12203, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12203, agent12203, scalar12203, tp12203, tm12203, ep12203, em12203, dsL]

theorem negative12203 :
    Eminus aL (agent12203.root+dsL) scalar12203.worldRadius world12203.frame
      agent12203.frame tm12203 ≤ -em12203 := by
  apply negative_check (lo := (67758698032026008967 / 100000000000000000000)) (hi := (8469837254003251121 / 12500000000000000000))
    (y := (-((36641116540948778373 / 50000000000000000000)))) (u := (48055080102651593967 / 100000000000000000000))
  · norm_num [world12203, agent12203, scalar12203, tp12203, tm12203, ep12203, em12203, dsL]
  · norm_num [world12203, agent12203, scalar12203, tp12203, tm12203, ep12203, em12203, dsL]
  · norm_num [world12203, agent12203, scalar12203, tp12203, tm12203, ep12203, em12203, dsL]
  · norm_num [world12203, agent12203, scalar12203, tp12203, tm12203, ep12203, em12203, dsL]
  · norm_num [world12203, agent12203, scalar12203, tp12203, tm12203, ep12203, em12203, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12203, agent12203, tp12203, tm12203, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12203, agent12203, tp12203, tm12203, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12203, agent12203, scalar12203, tp12203, tm12203, ep12203, em12203, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12203, agent12203, tp12203, tm12203, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12203, agent12203, scalar12203, tp12203, tm12203, ep12203, em12203, dsL]

theorem tails12203 :
    exp (-((12203:ℝ)*ep12203)) ≤ scalar12203.upperTail ∧
    exp (-((12203:ℝ)*em12203)) ≤ scalar12203.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12203:ℝ)) (by norm_num [ep12203]) ?_)
      (show bp12203^8 ≤ scalar12203.upperTail by norm_num [bp12203, scalar12203])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12203, bp12203, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12203:ℝ)) (by norm_num [em12203]) ?_)
      (show bm12203^8 ≤ scalar12203.lowerTail by norm_num [bm12203, scalar12203])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12203, bm12203, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12203 :
    agent12203.root+dsL+scalar12203.worldRadius < √(1/100/aL) ∧
    2*(agent12203.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12203, agent12203, scalar12203, tp12203, tm12203, ep12203, em12203, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12203, agent12203, scalar12203, tp12203, tm12203, ep12203, em12203, dsL]

noncomputable def master12203 : MasterCertificate 12203 world12203 agent12203 :=
  master scalar12203 dsL tp12203 tm12203 ep12203 em12203
    (by norm_num [dsL]) (by norm_num [tp12203]) (by norm_num [tm12203])
    (by norm_num [ep12203]) (by norm_num [em12203])
    positive12203 negative12203 tails12203.1 tails12203.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12203.1 tailGuards12203.2

theorem preserves12203 : master12203.toScalarCertificate = scalar12203 := rfl

noncomputable def tp12204 : ℝ := (2378267297 / 10000000000)
noncomputable def tm12204 : ℝ := (-((6150997239 / 10000000000)))
noncomputable def ep12204 : ℝ := (54752967851215079 / 100000000000000000000)
noncomputable def em12204 : ℝ := (26387906862389041 / 50000000000000000000)
noncomputable def bp12204 : ℝ := (43376319624238634261 / 100000000000000000000)
noncomputable def bm12204 : ℝ := (44704543806995396577 / 100000000000000000000)

theorem positive12204 :
    Eplus aL (agent12204.root+dsL) scalar12204.worldRadius world12204.frame
      agent12204.frame tp12204 ≤ -ep12204 := by
  apply positive_check (eT := (116240553128111880319 / 100000000000000000000)) (y := (19830358938183812649 / 50000000000000000000)) (u := (9292323623730216407 / 6250000000000000000))
  · norm_num [world12204, agent12204, scalar12204, tp12204, tm12204, ep12204, em12204, dsL]
  · norm_num [world12204, agent12204, scalar12204, tp12204, tm12204, ep12204, em12204, dsL]
  · norm_num [world12204, agent12204, scalar12204, tp12204, tm12204, ep12204, em12204, dsL]
  · norm_num [world12204, agent12204, scalar12204, tp12204, tm12204, ep12204, em12204, dsL]
  · norm_num [world12204, agent12204, scalar12204, tp12204, tm12204, ep12204, em12204, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12204, agent12204, tp12204, tm12204, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12204, agent12204, scalar12204, tp12204, tm12204, ep12204, em12204, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12204, agent12204, tp12204, tm12204, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12204, agent12204, scalar12204, tp12204, tm12204, ep12204, em12204, dsL]

theorem negative12204 :
    Eminus aL (agent12204.root+dsL) scalar12204.worldRadius world12204.frame
      agent12204.frame tm12204 ≤ -em12204 := by
  apply negative_check (lo := (33879199867861462947 / 50000000000000000000)) (hi := (13551679947144585179 / 20000000000000000000))
    (y := (-((18320455940928962593 / 25000000000000000000)))) (u := (24027638400617124469 / 50000000000000000000))
  · norm_num [world12204, agent12204, scalar12204, tp12204, tm12204, ep12204, em12204, dsL]
  · norm_num [world12204, agent12204, scalar12204, tp12204, tm12204, ep12204, em12204, dsL]
  · norm_num [world12204, agent12204, scalar12204, tp12204, tm12204, ep12204, em12204, dsL]
  · norm_num [world12204, agent12204, scalar12204, tp12204, tm12204, ep12204, em12204, dsL]
  · norm_num [world12204, agent12204, scalar12204, tp12204, tm12204, ep12204, em12204, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12204, agent12204, tp12204, tm12204, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12204, agent12204, tp12204, tm12204, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12204, agent12204, scalar12204, tp12204, tm12204, ep12204, em12204, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12204, agent12204, tp12204, tm12204, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12204, agent12204, scalar12204, tp12204, tm12204, ep12204, em12204, dsL]

theorem tails12204 :
    exp (-((12204:ℝ)*ep12204)) ≤ scalar12204.upperTail ∧
    exp (-((12204:ℝ)*em12204)) ≤ scalar12204.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12204:ℝ)) (by norm_num [ep12204]) ?_)
      (show bp12204^8 ≤ scalar12204.upperTail by norm_num [bp12204, scalar12204])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12204, bp12204, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12204:ℝ)) (by norm_num [em12204]) ?_)
      (show bm12204^8 ≤ scalar12204.lowerTail by norm_num [bm12204, scalar12204])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12204, bm12204, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12204 :
    agent12204.root+dsL+scalar12204.worldRadius < √(1/100/aL) ∧
    2*(agent12204.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12204, agent12204, scalar12204, tp12204, tm12204, ep12204, em12204, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12204, agent12204, scalar12204, tp12204, tm12204, ep12204, em12204, dsL]

noncomputable def master12204 : MasterCertificate 12204 world12204 agent12204 :=
  master scalar12204 dsL tp12204 tm12204 ep12204 em12204
    (by norm_num [dsL]) (by norm_num [tp12204]) (by norm_num [tm12204])
    (by norm_num [ep12204]) (by norm_num [em12204])
    positive12204 negative12204 tails12204.1 tails12204.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12204.1 tailGuards12204.2

theorem preserves12204 : master12204.toScalarCertificate = scalar12204 := rfl

noncomputable def tp12205 : ℝ := (2378363487 / 10000000000)
noncomputable def tm12205 : ℝ := (-((1537803151 / 2500000000)))
noncomputable def ep12205 : ℝ := (2737788878509221 / 5000000000000000000)
noncomputable def em12205 : ℝ := (5277825152521899 / 10000000000000000000)
noncomputable def bp12205 : ℝ := (43371491805577756613 / 100000000000000000000)
noncomputable def bm12205 : ℝ := (11174983064713203993 / 25000000000000000000)

theorem positive12205 :
    Eplus aL (agent12205.root+dsL) scalar12205.worldRadius world12205.frame
      agent12205.frame tp12205 ≤ -ep12205 := by
  apply positive_check (eT := (116240845459189480613 / 100000000000000000000)) (y := (19830663947622066801 / 50000000000000000000)) (u := (148678084941300514149 / 100000000000000000000))
  · norm_num [world12205, agent12205, scalar12205, tp12205, tm12205, ep12205, em12205, dsL]
  · norm_num [world12205, agent12205, scalar12205, tp12205, tm12205, ep12205, em12205, dsL]
  · norm_num [world12205, agent12205, scalar12205, tp12205, tm12205, ep12205, em12205, dsL]
  · norm_num [world12205, agent12205, scalar12205, tp12205, tm12205, ep12205, em12205, dsL]
  · norm_num [world12205, agent12205, scalar12205, tp12205, tm12205, ep12205, em12205, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12205, agent12205, tp12205, tm12205, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12205, agent12205, scalar12205, tp12205, tm12205, ep12205, em12205, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12205, agent12205, tp12205, tm12205, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12205, agent12205, scalar12205, tp12205, tm12205, ep12205, em12205, dsL]

theorem negative12205 :
    Eminus aL (agent12205.root+dsL) scalar12205.worldRadius world12205.frame
      agent12205.frame tm12205 ≤ -em12205 := by
  apply negative_check (lo := (1058720348118406849 / 1562500000000000000)) (hi := (67758102279578038337 / 100000000000000000000))
    (y := (-((9160176660344307317 / 12500000000000000000)))) (u := (24027737029700657743 / 50000000000000000000))
  · norm_num [world12205, agent12205, scalar12205, tp12205, tm12205, ep12205, em12205, dsL]
  · norm_num [world12205, agent12205, scalar12205, tp12205, tm12205, ep12205, em12205, dsL]
  · norm_num [world12205, agent12205, scalar12205, tp12205, tm12205, ep12205, em12205, dsL]
  · norm_num [world12205, agent12205, scalar12205, tp12205, tm12205, ep12205, em12205, dsL]
  · norm_num [world12205, agent12205, scalar12205, tp12205, tm12205, ep12205, em12205, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12205, agent12205, tp12205, tm12205, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12205, agent12205, tp12205, tm12205, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12205, agent12205, scalar12205, tp12205, tm12205, ep12205, em12205, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12205, agent12205, tp12205, tm12205, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12205, agent12205, scalar12205, tp12205, tm12205, ep12205, em12205, dsL]

theorem tails12205 :
    exp (-((12205:ℝ)*ep12205)) ≤ scalar12205.upperTail ∧
    exp (-((12205:ℝ)*em12205)) ≤ scalar12205.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12205:ℝ)) (by norm_num [ep12205]) ?_)
      (show bp12205^8 ≤ scalar12205.upperTail by norm_num [bp12205, scalar12205])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12205, bp12205, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12205:ℝ)) (by norm_num [em12205]) ?_)
      (show bm12205^8 ≤ scalar12205.lowerTail by norm_num [bm12205, scalar12205])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12205, bm12205, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12205 :
    agent12205.root+dsL+scalar12205.worldRadius < √(1/100/aL) ∧
    2*(agent12205.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12205, agent12205, scalar12205, tp12205, tm12205, ep12205, em12205, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12205, agent12205, scalar12205, tp12205, tm12205, ep12205, em12205, dsL]

noncomputable def master12205 : MasterCertificate 12205 world12205 agent12205 :=
  master scalar12205 dsL tp12205 tm12205 ep12205 em12205
    (by norm_num [dsL]) (by norm_num [tp12205]) (by norm_num [tm12205])
    (by norm_num [ep12205]) (by norm_num [em12205])
    positive12205 negative12205 tails12205.1 tails12205.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12205.1 tailGuards12205.2

theorem preserves12205 : master12205.toScalarCertificate = scalar12205 := rfl

noncomputable def tp12206 : ℝ := (2378459581 / 10000000000)
noncomputable def tm12206 : ℝ := (-((1230285563 / 2000000000)))
noncomputable def ep12206 : ℝ := (27379292370686537 / 50000000000000000000)
noncomputable def em12206 : ℝ := (10556137390935781 / 20000000000000000000)
noncomputable def bp12206 : ℝ := (21683332952709346201 / 50000000000000000000)
noncomputable def bm12206 : ℝ := (44695322530888155911 / 100000000000000000000)

theorem positive12206 :
    Eplus aL (agent12206.root+dsL) scalar12206.worldRadius world12206.frame
      agent12206.frame tp12206 ≤ -ep12206 := by
  apply positive_check (eT := (2906028428031832583 / 2500000000000000000)) (y := (19830968472665745469 / 50000000000000000000)) (u := (2323109226063504427 / 1562500000000000000))
  · norm_num [world12206, agent12206, scalar12206, tp12206, tm12206, ep12206, em12206, dsL]
  · norm_num [world12206, agent12206, scalar12206, tp12206, tm12206, ep12206, em12206, dsL]
  · norm_num [world12206, agent12206, scalar12206, tp12206, tm12206, ep12206, em12206, dsL]
  · norm_num [world12206, agent12206, scalar12206, tp12206, tm12206, ep12206, em12206, dsL]
  · norm_num [world12206, agent12206, scalar12206, tp12206, tm12206, ep12206, em12206, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12206, agent12206, tp12206, tm12206, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12206, agent12206, scalar12206, tp12206, tm12206, ep12206, em12206, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12206, agent12206, tp12206, tm12206, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12206, agent12206, scalar12206, tp12206, tm12206, ep12206, em12206, dsL]

theorem negative12206 :
    Eminus aL (agent12206.root+dsL) scalar12206.worldRadius world12206.frame
      agent12206.frame tm12206 ≤ -em12206 := by
  apply negative_check (lo := (3387890271168554287 / 5000000000000000000)) (hi := (67757805423371085741 / 100000000000000000000))
    (y := (-((73281002217935867117 / 100000000000000000000)))) (u := (9611134319790917707 / 20000000000000000000))
  · norm_num [world12206, agent12206, scalar12206, tp12206, tm12206, ep12206, em12206, dsL]
  · norm_num [world12206, agent12206, scalar12206, tp12206, tm12206, ep12206, em12206, dsL]
  · norm_num [world12206, agent12206, scalar12206, tp12206, tm12206, ep12206, em12206, dsL]
  · norm_num [world12206, agent12206, scalar12206, tp12206, tm12206, ep12206, em12206, dsL]
  · norm_num [world12206, agent12206, scalar12206, tp12206, tm12206, ep12206, em12206, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12206, agent12206, tp12206, tm12206, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12206, agent12206, tp12206, tm12206, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12206, agent12206, scalar12206, tp12206, tm12206, ep12206, em12206, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12206, agent12206, tp12206, tm12206, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12206, agent12206, scalar12206, tp12206, tm12206, ep12206, em12206, dsL]

theorem tails12206 :
    exp (-((12206:ℝ)*ep12206)) ≤ scalar12206.upperTail ∧
    exp (-((12206:ℝ)*em12206)) ≤ scalar12206.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12206:ℝ)) (by norm_num [ep12206]) ?_)
      (show bp12206^8 ≤ scalar12206.upperTail by norm_num [bp12206, scalar12206])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12206, bp12206, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12206:ℝ)) (by norm_num [em12206]) ?_)
      (show bm12206^8 ≤ scalar12206.lowerTail by norm_num [bm12206, scalar12206])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12206, bm12206, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12206 :
    agent12206.root+dsL+scalar12206.worldRadius < √(1/100/aL) ∧
    2*(agent12206.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12206, agent12206, scalar12206, tp12206, tm12206, ep12206, em12206, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12206, agent12206, scalar12206, tp12206, tm12206, ep12206, em12206, dsL]

noncomputable def master12206 : MasterCertificate 12206 world12206 agent12206 :=
  master scalar12206 dsL tp12206 tm12206 ep12206 em12206
    (by norm_num [dsL]) (by norm_num [tp12206]) (by norm_num [tm12206])
    (by norm_num [ep12206]) (by norm_num [em12206])
    positive12206 negative12206 tails12206.1 tails12206.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12206.1 tailGuards12206.2

theorem preserves12206 : master12206.toScalarCertificate = scalar12206 := rfl

noncomputable def tp12207 : ℝ := (1189277843 / 5000000000)
noncomputable def tm12207 : ℝ := (-((3075821439 / 5000000000)))
noncomputable def ep12207 : ℝ := (27380695392213631 / 50000000000000000000)
noncomputable def em12207 : ℝ := (2639156066490431 / 5000000000000000000)
noncomputable def bp12207 : ℝ := (1355057530760922193 / 3125000000000000000)
noncomputable def bm12207 : ℝ := (44690713725177399989 / 100000000000000000000)

theorem positive12207 :
    Eplus aL (agent12207.root+dsL) scalar12207.worldRadius world12207.frame
      agent12207.frame tp12207 ≤ -ep12207 := by
  apply positive_check (eT := (58120714450658571847 / 50000000000000000000)) (y := (39662546899382355123 / 100000000000000000000)) (u := (74339948672177594393 / 50000000000000000000))
  · norm_num [world12207, agent12207, scalar12207, tp12207, tm12207, ep12207, em12207, dsL]
  · norm_num [world12207, agent12207, scalar12207, tp12207, tm12207, ep12207, em12207, dsL]
  · norm_num [world12207, agent12207, scalar12207, tp12207, tm12207, ep12207, em12207, dsL]
  · norm_num [world12207, agent12207, scalar12207, tp12207, tm12207, ep12207, em12207, dsL]
  · norm_num [world12207, agent12207, scalar12207, tp12207, tm12207, ep12207, em12207, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12207, agent12207, tp12207, tm12207, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12207, agent12207, scalar12207, tp12207, tm12207, ep12207, em12207, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12207, agent12207, tp12207, tm12207, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12207, agent12207, scalar12207, tp12207, tm12207, ep12207, em12207, dsL]

theorem negative12207 :
    Eminus aL (agent12207.root+dsL) scalar12207.worldRadius world12207.frame
      agent12207.frame tm12207 ≤ -em12207 := by
  apply negative_check (lo := (33878754570718855507 / 50000000000000000000)) (hi := (13551501828287542203 / 20000000000000000000))
    (y := (-((36640295717374250897 / 50000000000000000000)))) (u := (24027934501989772791 / 50000000000000000000))
  · norm_num [world12207, agent12207, scalar12207, tp12207, tm12207, ep12207, em12207, dsL]
  · norm_num [world12207, agent12207, scalar12207, tp12207, tm12207, ep12207, em12207, dsL]
  · norm_num [world12207, agent12207, scalar12207, tp12207, tm12207, ep12207, em12207, dsL]
  · norm_num [world12207, agent12207, scalar12207, tp12207, tm12207, ep12207, em12207, dsL]
  · norm_num [world12207, agent12207, scalar12207, tp12207, tm12207, ep12207, em12207, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12207, agent12207, tp12207, tm12207, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12207, agent12207, tp12207, tm12207, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12207, agent12207, scalar12207, tp12207, tm12207, ep12207, em12207, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12207, agent12207, tp12207, tm12207, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12207, agent12207, scalar12207, tp12207, tm12207, ep12207, em12207, dsL]

theorem tails12207 :
    exp (-((12207:ℝ)*ep12207)) ≤ scalar12207.upperTail ∧
    exp (-((12207:ℝ)*em12207)) ≤ scalar12207.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12207:ℝ)) (by norm_num [ep12207]) ?_)
      (show bp12207^8 ≤ scalar12207.upperTail by norm_num [bp12207, scalar12207])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12207, bp12207, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12207:ℝ)) (by norm_num [em12207]) ?_)
      (show bm12207^8 ≤ scalar12207.lowerTail by norm_num [bm12207, scalar12207])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12207, bm12207, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12207 :
    agent12207.root+dsL+scalar12207.worldRadius < √(1/100/aL) ∧
    2*(agent12207.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12207, agent12207, scalar12207, tp12207, tm12207, ep12207, em12207, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12207, agent12207, scalar12207, tp12207, tm12207, ep12207, em12207, dsL]

noncomputable def master12207 : MasterCertificate 12207 world12207 agent12207 :=
  master scalar12207 dsL tp12207 tm12207 ep12207 em12207
    (by norm_num [dsL]) (by norm_num [tp12207]) (by norm_num [tm12207])
    (by norm_num [ep12207]) (by norm_num [em12207])
    positive12207 negative12207 tails12207.1 tails12207.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12207.1 tailGuards12207.2

theorem preserves12207 : master12207.toScalarCertificate = scalar12207 := rfl

noncomputable def tp12208 : ℝ := (2378651771 / 10000000000)
noncomputable def tm12208 : ℝ := (-((4806139 / 7812500)))
noncomputable def ep12208 : ℝ := (54764195913584131 / 100000000000000000000)
noncomputable def em12208 : ℝ := (13196388711373621 / 25000000000000000000)
noncomputable def bp12208 : ℝ := (43357016900601003387 / 100000000000000000000)
noncomputable def bm12208 : ℝ := (44686105708815017103 / 100000000000000000000)

theorem positive12208 :
    Eplus aL (agent12208.root+dsL) scalar12208.worldRadius world12208.frame
      agent12208.frame tp12208 ≤ -ep12208 := by
  apply positive_check (eT := (116241720571380301477 / 100000000000000000000)) (y := (19831578413302484269 / 50000000000000000000)) (u := (37170201046572295197 / 25000000000000000000))
  · norm_num [world12208, agent12208, scalar12208, tp12208, tm12208, ep12208, em12208, dsL]
  · norm_num [world12208, agent12208, scalar12208, tp12208, tm12208, ep12208, em12208, dsL]
  · norm_num [world12208, agent12208, scalar12208, tp12208, tm12208, ep12208, em12208, dsL]
  · norm_num [world12208, agent12208, scalar12208, tp12208, tm12208, ep12208, em12208, dsL]
  · norm_num [world12208, agent12208, scalar12208, tp12208, tm12208, ep12208, em12208, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12208, agent12208, tp12208, tm12208, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12208, agent12208, scalar12208, tp12208, tm12208, ep12208, em12208, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12208, agent12208, tp12208, tm12208, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12208, agent12208, scalar12208, tp12208, tm12208, ep12208, em12208, dsL]

theorem negative12208 :
    Eminus aL (agent12208.root+dsL) scalar12208.worldRadius world12208.frame
      agent12208.frame tm12208 ≤ -em12208 := by
  apply negative_check (lo := (33878606444583132239 / 50000000000000000000)) (hi := (67757212889166264479 / 100000000000000000000))
    (y := (-((7328018103315777821 / 10000000000000000000)))) (u := (48056066226435075727 / 100000000000000000000))
  · norm_num [world12208, agent12208, scalar12208, tp12208, tm12208, ep12208, em12208, dsL]
  · norm_num [world12208, agent12208, scalar12208, tp12208, tm12208, ep12208, em12208, dsL]
  · norm_num [world12208, agent12208, scalar12208, tp12208, tm12208, ep12208, em12208, dsL]
  · norm_num [world12208, agent12208, scalar12208, tp12208, tm12208, ep12208, em12208, dsL]
  · norm_num [world12208, agent12208, scalar12208, tp12208, tm12208, ep12208, em12208, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12208, agent12208, tp12208, tm12208, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12208, agent12208, tp12208, tm12208, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12208, agent12208, scalar12208, tp12208, tm12208, ep12208, em12208, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12208, agent12208, tp12208, tm12208, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12208, agent12208, scalar12208, tp12208, tm12208, ep12208, em12208, dsL]

theorem tails12208 :
    exp (-((12208:ℝ)*ep12208)) ≤ scalar12208.upperTail ∧
    exp (-((12208:ℝ)*em12208)) ≤ scalar12208.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12208:ℝ)) (by norm_num [ep12208]) ?_)
      (show bp12208^8 ≤ scalar12208.upperTail by norm_num [bp12208, scalar12208])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12208, bp12208, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12208:ℝ)) (by norm_num [em12208]) ?_)
      (show bm12208^8 ≤ scalar12208.lowerTail by norm_num [bm12208, scalar12208])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12208, bm12208, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12208 :
    agent12208.root+dsL+scalar12208.worldRadius < √(1/100/aL) ∧
    2*(agent12208.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12208, agent12208, scalar12208, tp12208, tm12208, ep12208, em12208, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12208, agent12208, scalar12208, tp12208, tm12208, ep12208, em12208, dsL]

noncomputable def master12208 : MasterCertificate 12208 world12208 agent12208 :=
  master scalar12208 dsL tp12208 tm12208 ep12208 em12208
    (by norm_num [dsL]) (by norm_num [tp12208]) (by norm_num [tm12208])
    (by norm_num [ep12208]) (by norm_num [em12208])
    positive12208 negative12208 tails12208.1 tails12208.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12208.1 tailGuards12208.2

theorem preserves12208 : master12208.toScalarCertificate = scalar12208 := rfl

end BstLean.Part281
