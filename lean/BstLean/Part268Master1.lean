import BstLean.Part261Checker
import BstLean.Part268Scalar1
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12375 : ℝ := (2284458401 / 10000000000)
noncomputable def tm12375 : ℝ := (-((2995814691 / 5000000000)))
noncomputable def ep12375 : ℝ := (12615635147518937 / 25000000000000000000)
noncomputable def em12375 : ℝ := (12317347947053711 / 25000000000000000000)
noncomputable def bp12375 : ℝ := (22906726033207623727 / 50000000000000000000)
noncomputable def bm12375 : ℝ := (583335752901737863 / 1250000000000000000)

theorem positive12375 :
    Eplus aL (agent12375.root+dsL) scalar12375.worldRadius world12375.frame
      agent12375.frame tp12375 ≤ -ep12375 := by
  apply positive_check (eT := (115485774918064881453 / 100000000000000000000)) (y := (18804206941420427847 / 50000000000000000000)) (u := (3641424206705122877 / 2500000000000000000))
  · norm_num [world12375, agent12375, scalar12375, tp12375, tm12375, ep12375, em12375, dsL]
  · norm_num [world12375, agent12375, scalar12375, tp12375, tm12375, ep12375, em12375, dsL]
  · norm_num [world12375, agent12375, scalar12375, tp12375, tm12375, ep12375, em12375, dsL]
  · norm_num [world12375, agent12375, scalar12375, tp12375, tm12375, ep12375, em12375, dsL]
  · norm_num [world12375, agent12375, scalar12375, tp12375, tm12375, ep12375, em12375, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12375, agent12375, tp12375, tm12375, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12375, agent12375, scalar12375, tp12375, tm12375, ep12375, em12375, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12375, agent12375, tp12375, tm12375, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12375, agent12375, scalar12375, tp12375, tm12375, ep12375, em12375, dsL]

theorem negative12375 :
    Eminus aL (agent12375.root+dsL) scalar12375.worldRadius world12375.frame
      agent12375.frame tm12375 ≤ -em12375 := by
  apply negative_check (lo := (68549072957492769127 / 100000000000000000000)) (hi := (8568634119686596141 / 12500000000000000000))
    (y := (-((1792652509052147259 / 2500000000000000000)))) (u := (48818492334866496551 / 100000000000000000000))
  · norm_num [world12375, agent12375, scalar12375, tp12375, tm12375, ep12375, em12375, dsL]
  · norm_num [world12375, agent12375, scalar12375, tp12375, tm12375, ep12375, em12375, dsL]
  · norm_num [world12375, agent12375, scalar12375, tp12375, tm12375, ep12375, em12375, dsL]
  · norm_num [world12375, agent12375, scalar12375, tp12375, tm12375, ep12375, em12375, dsL]
  · norm_num [world12375, agent12375, scalar12375, tp12375, tm12375, ep12375, em12375, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12375, agent12375, tp12375, tm12375, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12375, agent12375, tp12375, tm12375, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12375, agent12375, scalar12375, tp12375, tm12375, ep12375, em12375, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12375, agent12375, tp12375, tm12375, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12375, agent12375, scalar12375, tp12375, tm12375, ep12375, em12375, dsL]

theorem tails12375 :
    exp (-((12375:ℝ)*ep12375)) ≤ scalar12375.upperTail ∧
    exp (-((12375:ℝ)*em12375)) ≤ scalar12375.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12375:ℝ)) (by norm_num [ep12375]) ?_)
      (show bp12375^8 ≤ scalar12375.upperTail by norm_num [bp12375, scalar12375])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12375, bp12375, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12375:ℝ)) (by norm_num [em12375]) ?_)
      (show bm12375^8 ≤ scalar12375.lowerTail by norm_num [bm12375, scalar12375])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12375, bm12375, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12375 :
    agent12375.root+dsL+scalar12375.worldRadius < √(1/100/aL) ∧
    2*(agent12375.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12375, agent12375, scalar12375, tp12375, tm12375, ep12375, em12375, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12375, agent12375, scalar12375, tp12375, tm12375, ep12375, em12375, dsL]

noncomputable def master12375 : MasterCertificate 12375 world12375 agent12375 :=
  master scalar12375 dsL tp12375 tm12375 ep12375 em12375
    (by norm_num [dsL]) (by norm_num [tp12375]) (by norm_num [tm12375])
    (by norm_num [ep12375]) (by norm_num [em12375])
    positive12375 negative12375 tails12375.1 tails12375.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12375.1 tailGuards12375.2

theorem preserves12375 : master12375.toScalarCertificate = scalar12375 := rfl

noncomputable def tp12376 : ℝ := (571138879 / 2500000000)
noncomputable def tm12376 : ℝ := (-((2995919997 / 5000000000)))
noncomputable def ep12376 : ℝ := (25232781404019549 / 50000000000000000000)
noncomputable def em12376 : ℝ := (3079500570056031 / 6250000000000000000)
noncomputable def bp12376 : ℝ := (45808420564810635537 / 100000000000000000000)
noncomputable def bm12376 : ℝ := (9332419373587531143 / 20000000000000000000)

theorem positive12376 :
    Eplus aL (agent12376.root+dsL) scalar12376.worldRadius world12376.frame
      agent12376.frame tp12376 ≤ -ep12376 := by
  apply positive_check (eT := (57743048347655521631 / 50000000000000000000)) (y := (3760932867956761747 / 10000000000000000000)) (u := (145658300739477625559 / 100000000000000000000))
  · norm_num [world12376, agent12376, scalar12376, tp12376, tm12376, ep12376, em12376, dsL]
  · norm_num [world12376, agent12376, scalar12376, tp12376, tm12376, ep12376, em12376, dsL]
  · norm_num [world12376, agent12376, scalar12376, tp12376, tm12376, ep12376, em12376, dsL]
  · norm_num [world12376, agent12376, scalar12376, tp12376, tm12376, ep12376, em12376, dsL]
  · norm_num [world12376, agent12376, scalar12376, tp12376, tm12376, ep12376, em12376, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12376, agent12376, tp12376, tm12376, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12376, agent12376, scalar12376, tp12376, tm12376, ep12376, em12376, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12376, agent12376, tp12376, tm12376, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12376, agent12376, scalar12376, tp12376, tm12376, ep12376, em12376, dsL]

theorem negative12376 :
    Eminus aL (agent12376.root+dsL) scalar12376.worldRadius world12376.frame
      agent12376.frame tm12376 ≤ -em12376 := by
  apply negative_check (lo := (68548762530235525371 / 100000000000000000000)) (hi := (17137190632558881343 / 25000000000000000000))
    (y := (-((3585315185714545901 / 5000000000000000000)))) (u := (24409196530743404839 / 50000000000000000000))
  · norm_num [world12376, agent12376, scalar12376, tp12376, tm12376, ep12376, em12376, dsL]
  · norm_num [world12376, agent12376, scalar12376, tp12376, tm12376, ep12376, em12376, dsL]
  · norm_num [world12376, agent12376, scalar12376, tp12376, tm12376, ep12376, em12376, dsL]
  · norm_num [world12376, agent12376, scalar12376, tp12376, tm12376, ep12376, em12376, dsL]
  · norm_num [world12376, agent12376, scalar12376, tp12376, tm12376, ep12376, em12376, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12376, agent12376, tp12376, tm12376, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12376, agent12376, tp12376, tm12376, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12376, agent12376, scalar12376, tp12376, tm12376, ep12376, em12376, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12376, agent12376, tp12376, tm12376, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12376, agent12376, scalar12376, tp12376, tm12376, ep12376, em12376, dsL]

theorem tails12376 :
    exp (-((12376:ℝ)*ep12376)) ≤ scalar12376.upperTail ∧
    exp (-((12376:ℝ)*em12376)) ≤ scalar12376.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12376:ℝ)) (by norm_num [ep12376]) ?_)
      (show bp12376^8 ≤ scalar12376.upperTail by norm_num [bp12376, scalar12376])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12376, bp12376, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12376:ℝ)) (by norm_num [em12376]) ?_)
      (show bm12376^8 ≤ scalar12376.lowerTail by norm_num [bm12376, scalar12376])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12376, bm12376, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12376 :
    agent12376.root+dsL+scalar12376.worldRadius < √(1/100/aL) ∧
    2*(agent12376.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12376, agent12376, scalar12376, tp12376, tm12376, ep12376, em12376, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12376, agent12376, scalar12376, tp12376, tm12376, ep12376, em12376, dsL]

noncomputable def master12376 : MasterCertificate 12376 world12376 agent12376 :=
  master scalar12376 dsL tp12376 tm12376 ep12376 em12376
    (by norm_num [dsL]) (by norm_num [tp12376]) (by norm_num [tm12376])
    (by norm_num [ep12376]) (by norm_num [em12376])
    positive12376 negative12376 tails12376.1 tails12376.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12376.1 tailGuards12376.2

theorem preserves12376 : master12376.toScalarCertificate = scalar12376 := rfl

noncomputable def tp12377 : ℝ := (2284652529 / 10000000000)
noncomputable def tm12377 : ℝ := (-((239682023 / 400000000)))
noncomputable def ep12377 : ℝ := (6308573007480639 / 12500000000000000000)
noncomputable def em12377 : ℝ := (1231865639080089 / 2500000000000000000)
noncomputable def bp12377 : ℝ := (5725423744297375251 / 12500000000000000000)
noncomputable def bm12377 : ℝ := (46657334327360866981 / 100000000000000000000)

theorem positive12377 :
    Eplus aL (agent12377.root+dsL) scalar12377.worldRadius world12377.frame
      agent12377.frame tp12377 ≤ -ep12377 := by
  apply positive_check (eT := (3608950555064459573 / 3125000000000000000)) (y := (1504409680545653669 / 4000000000000000000)) (u := (145659631092444761183 / 100000000000000000000))
  · norm_num [world12377, agent12377, scalar12377, tp12377, tm12377, ep12377, em12377, dsL]
  · norm_num [world12377, agent12377, scalar12377, tp12377, tm12377, ep12377, em12377, dsL]
  · norm_num [world12377, agent12377, scalar12377, tp12377, tm12377, ep12377, em12377, dsL]
  · norm_num [world12377, agent12377, scalar12377, tp12377, tm12377, ep12377, em12377, dsL]
  · norm_num [world12377, agent12377, scalar12377, tp12377, tm12377, ep12377, em12377, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12377, agent12377, tp12377, tm12377, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12377, agent12377, scalar12377, tp12377, tm12377, ep12377, em12377, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12377, agent12377, tp12377, tm12377, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12377, agent12377, scalar12377, tp12377, tm12377, ep12377, em12377, dsL]

theorem negative12377 :
    Eminus aL (agent12377.root+dsL) scalar12377.worldRadius world12377.frame
      agent12377.frame tm12377 ≤ -em12377 := by
  apply negative_check (lo := (34274226090626361961 / 50000000000000000000)) (hi := (68548452181252723923 / 100000000000000000000))
    (y := (-((71706507590493117433 / 100000000000000000000)))) (u := (6102286691562814891 / 12500000000000000000))
  · norm_num [world12377, agent12377, scalar12377, tp12377, tm12377, ep12377, em12377, dsL]
  · norm_num [world12377, agent12377, scalar12377, tp12377, tm12377, ep12377, em12377, dsL]
  · norm_num [world12377, agent12377, scalar12377, tp12377, tm12377, ep12377, em12377, dsL]
  · norm_num [world12377, agent12377, scalar12377, tp12377, tm12377, ep12377, em12377, dsL]
  · norm_num [world12377, agent12377, scalar12377, tp12377, tm12377, ep12377, em12377, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12377, agent12377, tp12377, tm12377, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12377, agent12377, tp12377, tm12377, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12377, agent12377, scalar12377, tp12377, tm12377, ep12377, em12377, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12377, agent12377, tp12377, tm12377, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12377, agent12377, scalar12377, tp12377, tm12377, ep12377, em12377, dsL]

theorem tails12377 :
    exp (-((12377:ℝ)*ep12377)) ≤ scalar12377.upperTail ∧
    exp (-((12377:ℝ)*em12377)) ≤ scalar12377.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12377:ℝ)) (by norm_num [ep12377]) ?_)
      (show bp12377^8 ≤ scalar12377.upperTail by norm_num [bp12377, scalar12377])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12377, bp12377, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12377:ℝ)) (by norm_num [em12377]) ?_)
      (show bm12377^8 ≤ scalar12377.lowerTail by norm_num [bm12377, scalar12377])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12377, bm12377, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12377 :
    agent12377.root+dsL+scalar12377.worldRadius < √(1/100/aL) ∧
    2*(agent12377.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12377, agent12377, scalar12377, tp12377, tm12377, ep12377, em12377, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12377, agent12377, scalar12377, tp12377, tm12377, ep12377, em12377, dsL]

noncomputable def master12377 : MasterCertificate 12377 world12377 agent12377 :=
  master scalar12377 dsL tp12377 tm12377 ep12377 em12377
    (by norm_num [dsL]) (by norm_num [tp12377]) (by norm_num [tm12377])
    (by norm_num [ep12377]) (by norm_num [em12377])
    positive12377 negative12377 tails12377.1 tails12377.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12377.1 tailGuards12377.2

theorem preserves12377 : master12377.toScalarCertificate = scalar12377 := rfl

noncomputable def tp12378 : ℝ := (2284749483 / 10000000000)
noncomputable def tm12378 : ℝ := (-((1498065281 / 2500000000)))
noncomputable def ep12378 : ℝ := (10094320655091313 / 20000000000000000000)
noncomputable def em12378 : ℝ := (4927724010889207 / 10000000000000000000)
noncomputable def bp12378 : ℝ := (45798360993358613789 / 100000000000000000000)
noncomputable def bm12378 : ℝ := (46652573336750517257 / 100000000000000000000)

theorem positive12378 :
    Eplus aL (agent12378.root+dsL) scalar12378.worldRadius world12378.frame
      agent12378.frame tp12378 ≤ -ep12378 := by
  apply positive_check (eT := (115486738431354222211 / 100000000000000000000)) (y := (7522230978676987543 / 20000000000000000000)) (u := (145660960795780887727 / 100000000000000000000))
  · norm_num [world12378, agent12378, scalar12378, tp12378, tm12378, ep12378, em12378, dsL]
  · norm_num [world12378, agent12378, scalar12378, tp12378, tm12378, ep12378, em12378, dsL]
  · norm_num [world12378, agent12378, scalar12378, tp12378, tm12378, ep12378, em12378, dsL]
  · norm_num [world12378, agent12378, scalar12378, tp12378, tm12378, ep12378, em12378, dsL]
  · norm_num [world12378, agent12378, scalar12378, tp12378, tm12378, ep12378, em12378, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12378, agent12378, tp12378, tm12378, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12378, agent12378, scalar12378, tp12378, tm12378, ep12378, em12378, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12378, agent12378, tp12378, tm12378, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12378, agent12378, scalar12378, tp12378, tm12378, ep12378, em12378, dsL]

theorem negative12378 :
    Eminus aL (agent12378.root+dsL) scalar12378.worldRadius world12378.frame
      agent12378.frame tm12378 ≤ -em12378 := by
  apply negative_check (lo := (13709628382960479931 / 20000000000000000000)) (hi := (8568517739350299957 / 12500000000000000000))
    (y := (-((896333900148668189 / 1250000000000000000)))) (u := (48818193737565260163 / 100000000000000000000))
  · norm_num [world12378, agent12378, scalar12378, tp12378, tm12378, ep12378, em12378, dsL]
  · norm_num [world12378, agent12378, scalar12378, tp12378, tm12378, ep12378, em12378, dsL]
  · norm_num [world12378, agent12378, scalar12378, tp12378, tm12378, ep12378, em12378, dsL]
  · norm_num [world12378, agent12378, scalar12378, tp12378, tm12378, ep12378, em12378, dsL]
  · norm_num [world12378, agent12378, scalar12378, tp12378, tm12378, ep12378, em12378, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12378, agent12378, tp12378, tm12378, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12378, agent12378, tp12378, tm12378, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12378, agent12378, scalar12378, tp12378, tm12378, ep12378, em12378, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12378, agent12378, tp12378, tm12378, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12378, agent12378, scalar12378, tp12378, tm12378, ep12378, em12378, dsL]

theorem tails12378 :
    exp (-((12378:ℝ)*ep12378)) ≤ scalar12378.upperTail ∧
    exp (-((12378:ℝ)*em12378)) ≤ scalar12378.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12378:ℝ)) (by norm_num [ep12378]) ?_)
      (show bp12378^8 ≤ scalar12378.upperTail by norm_num [bp12378, scalar12378])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12378, bp12378, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12378:ℝ)) (by norm_num [em12378]) ?_)
      (show bm12378^8 ≤ scalar12378.lowerTail by norm_num [bm12378, scalar12378])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12378, bm12378, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12378 :
    agent12378.root+dsL+scalar12378.worldRadius < √(1/100/aL) ∧
    2*(agent12378.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12378, agent12378, scalar12378, tp12378, tm12378, ep12378, em12378, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12378, agent12378, scalar12378, tp12378, tm12378, ep12378, em12378, dsL]

noncomputable def master12378 : MasterCertificate 12378 world12378 agent12378 :=
  master scalar12378 dsL tp12378 tm12378 ep12378 em12378
    (by norm_num [dsL]) (by norm_num [tp12378]) (by norm_num [tm12378])
    (by norm_num [ep12378]) (by norm_num [em12378])
    positive12378 negative12378 tails12378.1 tails12378.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12378.1 tailGuards12378.2

theorem preserves12378 : master12378.toScalarCertificate = scalar12378 := rfl

noncomputable def tp12379 : ℝ := (2284846439 / 10000000000)
noncomputable def tm12379 : ℝ := (-((2996235693 / 5000000000)))
noncomputable def ep12379 : ℝ := (50474621389708231 / 100000000000000000000)
noncomputable def em12379 : ℝ := (49279853621975063 / 100000000000000000000)
noncomputable def bp12379 : ℝ := (915866660385165637 / 2000000000000000000)
noncomputable def bm12379 : ℝ := (46647813272404130889 / 100000000000000000000)

theorem positive12379 :
    Eplus aL (agent12379.root+dsL) scalar12379.worldRadius world12379.frame
      agent12379.frame tp12379 ≤ -ep12379 := by
  apply positive_check (eT := (115487059147169469013 / 100000000000000000000)) (y := (18806034149799634447 / 50000000000000000000)) (u := (145662291278124995847 / 100000000000000000000))
  · norm_num [world12379, agent12379, scalar12379, tp12379, tm12379, ep12379, em12379, dsL]
  · norm_num [world12379, agent12379, scalar12379, tp12379, tm12379, ep12379, em12379, dsL]
  · norm_num [world12379, agent12379, scalar12379, tp12379, tm12379, ep12379, em12379, dsL]
  · norm_num [world12379, agent12379, scalar12379, tp12379, tm12379, ep12379, em12379, dsL]
  · norm_num [world12379, agent12379, scalar12379, tp12379, tm12379, ep12379, em12379, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12379, agent12379, tp12379, tm12379, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12379, agent12379, scalar12379, tp12379, tm12379, ep12379, em12379, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12379, agent12379, tp12379, tm12379, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12379, agent12379, scalar12379, tp12379, tm12379, ep12379, em12379, dsL]

theorem negative12379 :
    Eminus aL (agent12379.root+dsL) scalar12379.worldRadius world12379.frame
      agent12379.frame tm12379 ≤ -em12379 := by
  apply negative_check (lo := (68547832832413040473 / 100000000000000000000)) (hi := (34273916416206520237 / 50000000000000000000))
    (y := (-((71706914723394914113 / 100000000000000000000)))) (u := (24409047388786025631 / 50000000000000000000))
  · norm_num [world12379, agent12379, scalar12379, tp12379, tm12379, ep12379, em12379, dsL]
  · norm_num [world12379, agent12379, scalar12379, tp12379, tm12379, ep12379, em12379, dsL]
  · norm_num [world12379, agent12379, scalar12379, tp12379, tm12379, ep12379, em12379, dsL]
  · norm_num [world12379, agent12379, scalar12379, tp12379, tm12379, ep12379, em12379, dsL]
  · norm_num [world12379, agent12379, scalar12379, tp12379, tm12379, ep12379, em12379, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12379, agent12379, tp12379, tm12379, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12379, agent12379, tp12379, tm12379, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12379, agent12379, scalar12379, tp12379, tm12379, ep12379, em12379, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12379, agent12379, tp12379, tm12379, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12379, agent12379, scalar12379, tp12379, tm12379, ep12379, em12379, dsL]

theorem tails12379 :
    exp (-((12379:ℝ)*ep12379)) ≤ scalar12379.upperTail ∧
    exp (-((12379:ℝ)*em12379)) ≤ scalar12379.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12379:ℝ)) (by norm_num [ep12379]) ?_)
      (show bp12379^8 ≤ scalar12379.upperTail by norm_num [bp12379, scalar12379])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12379, bp12379, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12379:ℝ)) (by norm_num [em12379]) ?_)
      (show bm12379^8 ≤ scalar12379.lowerTail by norm_num [bm12379, scalar12379])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12379, bm12379, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12379 :
    agent12379.root+dsL+scalar12379.worldRadius < √(1/100/aL) ∧
    2*(agent12379.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12379, agent12379, scalar12379, tp12379, tm12379, ep12379, em12379, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12379, agent12379, scalar12379, tp12379, tm12379, ep12379, em12379, dsL]

noncomputable def master12379 : MasterCertificate 12379 world12379 agent12379 :=
  master scalar12379 dsL tp12379 tm12379 ep12379 em12379
    (by norm_num [dsL]) (by norm_num [tp12379]) (by norm_num [tm12379])
    (by norm_num [ep12379]) (by norm_num [em12379])
    positive12379 negative12379 tails12379.1 tails12379.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12379.1 tailGuards12379.2

theorem preserves12379 : master12379.toScalarCertificate = scalar12379 := rfl

noncomputable def tp12380 : ℝ := (1142510249 / 5000000000)
noncomputable def tm12380 : ℝ := (-((5992914741 / 10000000000)))
noncomputable def ep12380 : ℝ := (50479126909883311 / 100000000000000000000)
noncomputable def em12380 : ℝ := (9856816912219003 / 20000000000000000000)
noncomputable def bp12380 : ℝ := (22893625663298844197 / 50000000000000000000)
noncomputable def bm12380 : ℝ := (23320942971727613099 / 50000000000000000000)

theorem positive12380 :
    Eplus aL (agent12380.root+dsL) scalar12380.worldRadius world12380.frame
      agent12380.frame tp12380 ≤ -ep12380 := by
  apply positive_check (eT := (115487941029422156917 / 100000000000000000000)) (y := (37612244968182863177 / 100000000000000000000)) (u := (72831274308929573527 / 50000000000000000000))
  · norm_num [world12380, agent12380, scalar12380, tp12380, tm12380, ep12380, em12380, dsL]
  · norm_num [world12380, agent12380, scalar12380, tp12380, tm12380, ep12380, em12380, dsL]
  · norm_num [world12380, agent12380, scalar12380, tp12380, tm12380, ep12380, em12380, dsL]
  · norm_num [world12380, agent12380, scalar12380, tp12380, tm12380, ep12380, em12380, dsL]
  · norm_num [world12380, agent12380, scalar12380, tp12380, tm12380, ep12380, em12380, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12380, agent12380, tp12380, tm12380, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12380, agent12380, scalar12380, tp12380, tm12380, ep12380, em12380, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12380, agent12380, tp12380, tm12380, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12380, agent12380, scalar12380, tp12380, tm12380, ep12380, em12380, dsL]

theorem negative12380 :
    Eminus aL (agent12380.root+dsL) scalar12380.worldRadius world12380.frame
      agent12380.frame tm12380 ≤ -em12380 := by
  apply negative_check (lo := (267759831303886323 / 390625000000000000)) (hi := (68546516813794898689 / 100000000000000000000))
    (y := (-((71705171833708055817 / 100000000000000000000)))) (u := (3051184101907871433 / 6250000000000000000))
  · norm_num [world12380, agent12380, scalar12380, tp12380, tm12380, ep12380, em12380, dsL]
  · norm_num [world12380, agent12380, scalar12380, tp12380, tm12380, ep12380, em12380, dsL]
  · norm_num [world12380, agent12380, scalar12380, tp12380, tm12380, ep12380, em12380, dsL]
  · norm_num [world12380, agent12380, scalar12380, tp12380, tm12380, ep12380, em12380, dsL]
  · norm_num [world12380, agent12380, scalar12380, tp12380, tm12380, ep12380, em12380, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12380, agent12380, tp12380, tm12380, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12380, agent12380, tp12380, tm12380, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12380, agent12380, scalar12380, tp12380, tm12380, ep12380, em12380, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12380, agent12380, tp12380, tm12380, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12380, agent12380, scalar12380, tp12380, tm12380, ep12380, em12380, dsL]

theorem tails12380 :
    exp (-((12380:ℝ)*ep12380)) ≤ scalar12380.upperTail ∧
    exp (-((12380:ℝ)*em12380)) ≤ scalar12380.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12380:ℝ)) (by norm_num [ep12380]) ?_)
      (show bp12380^8 ≤ scalar12380.upperTail by norm_num [bp12380, scalar12380])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12380, bp12380, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12380:ℝ)) (by norm_num [em12380]) ?_)
      (show bm12380^8 ≤ scalar12380.lowerTail by norm_num [bm12380, scalar12380])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12380, bm12380, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12380 :
    agent12380.root+dsL+scalar12380.worldRadius < √(1/100/aL) ∧
    2*(agent12380.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12380, agent12380, scalar12380, tp12380, tm12380, ep12380, em12380, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12380, agent12380, scalar12380, tp12380, tm12380, ep12380, em12380, dsL]

noncomputable def master12380 : MasterCertificate 12380 world12380 agent12380 :=
  master scalar12380 dsL tp12380 tm12380 ep12380 em12380
    (by norm_num [dsL]) (by norm_num [tp12380]) (by norm_num [tm12380])
    (by norm_num [ep12380]) (by norm_num [em12380])
    positive12380 negative12380 tails12380.1 tails12380.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12380.1 tailGuards12380.2

theorem preserves12380 : master12380.toScalarCertificate = scalar12380 := rfl

noncomputable def tp12381 : ℝ := (2285117343 / 10000000000)
noncomputable def tm12381 : ℝ := (-((1498281211 / 2500000000)))
noncomputable def ep12381 : ℝ := (5048214154188267 / 10000000000000000000)
noncomputable def em12381 : ℝ := (49286694832864019 / 100000000000000000000)
noncomputable def bp12381 : ℝ := (715347285366823101 / 1562500000000000000)
noncomputable def bm12381 : ℝ := (5829641075664923373 / 12500000000000000000)

theorem positive12381 :
    Eplus aL (agent12381.root+dsL) scalar12381.worldRadius world12381.frame
      agent12381.frame tp12381 ≤ -ep12381 := by
  apply positive_check (eT := (115488260989825436823 / 100000000000000000000)) (y := (37613157440459354509 / 100000000000000000000)) (u := (72831938877148253629 / 50000000000000000000))
  · norm_num [world12381, agent12381, scalar12381, tp12381, tm12381, ep12381, em12381, dsL]
  · norm_num [world12381, agent12381, scalar12381, tp12381, tm12381, ep12381, em12381, dsL]
  · norm_num [world12381, agent12381, scalar12381, tp12381, tm12381, ep12381, em12381, dsL]
  · norm_num [world12381, agent12381, scalar12381, tp12381, tm12381, ep12381, em12381, dsL]
  · norm_num [world12381, agent12381, scalar12381, tp12381, tm12381, ep12381, em12381, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12381, agent12381, tp12381, tm12381, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12381, agent12381, scalar12381, tp12381, tm12381, ep12381, em12381, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12381, agent12381, tp12381, tm12381, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12381, agent12381, scalar12381, tp12381, tm12381, ep12381, em12381, dsL]

theorem negative12381 :
    Eminus aL (agent12381.root+dsL) scalar12381.worldRadius world12381.frame
      agent12381.frame tm12381 ≤ -em12381 := by
  apply negative_check (lo := (68546208334642527581 / 100000000000000000000)) (hi := (34273104167321263791 / 50000000000000000000))
    (y := (-((14341074937332845803 / 20000000000000000000)))) (u := (48818846599952002077 / 100000000000000000000))
  · norm_num [world12381, agent12381, scalar12381, tp12381, tm12381, ep12381, em12381, dsL]
  · norm_num [world12381, agent12381, scalar12381, tp12381, tm12381, ep12381, em12381, dsL]
  · norm_num [world12381, agent12381, scalar12381, tp12381, tm12381, ep12381, em12381, dsL]
  · norm_num [world12381, agent12381, scalar12381, tp12381, tm12381, ep12381, em12381, dsL]
  · norm_num [world12381, agent12381, scalar12381, tp12381, tm12381, ep12381, em12381, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12381, agent12381, tp12381, tm12381, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12381, agent12381, tp12381, tm12381, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12381, agent12381, scalar12381, tp12381, tm12381, ep12381, em12381, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12381, agent12381, tp12381, tm12381, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12381, agent12381, scalar12381, tp12381, tm12381, ep12381, em12381, dsL]

theorem tails12381 :
    exp (-((12381:ℝ)*ep12381)) ≤ scalar12381.upperTail ∧
    exp (-((12381:ℝ)*em12381)) ≤ scalar12381.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12381:ℝ)) (by norm_num [ep12381]) ?_)
      (show bp12381^8 ≤ scalar12381.upperTail by norm_num [bp12381, scalar12381])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12381, bp12381, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12381:ℝ)) (by norm_num [em12381]) ?_)
      (show bm12381^8 ≤ scalar12381.lowerTail by norm_num [bm12381, scalar12381])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12381, bm12381, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12381 :
    agent12381.root+dsL+scalar12381.worldRadius < √(1/100/aL) ∧
    2*(agent12381.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12381, agent12381, scalar12381, tp12381, tm12381, ep12381, em12381, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12381, agent12381, scalar12381, tp12381, tm12381, ep12381, em12381, dsL]

noncomputable def master12381 : MasterCertificate 12381 world12381 agent12381 :=
  master scalar12381 dsL tp12381 tm12381 ep12381 em12381
    (by norm_num [dsL]) (by norm_num [tp12381]) (by norm_num [tm12381])
    (by norm_num [ep12381]) (by norm_num [em12381])
    positive12381 negative12381 tails12381.1 tails12381.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12381.1 tailGuards12381.2

theorem preserves12381 : master12381.toScalarCertificate = scalar12381 := rfl

noncomputable def tp12382 : ℝ := (2285214069 / 10000000000)
noncomputable def tm12382 : ℝ := (-((5993334739 / 10000000000)))
noncomputable def ep12382 : ℝ := (252425771411727 / 500000000000000000)
noncomputable def em12382 : ℝ := (12322325839671329 / 25000000000000000000)
noncomputable def bp12382 : ℝ := (1831088109881134583 / 4000000000000000000)
noncomputable def bm12382 : ℝ := (23316186354126314473 / 50000000000000000000)

theorem positive12382 :
    Eplus aL (agent12382.root+dsL) scalar12382.worldRadius world12382.frame
      agent12382.frame tp12382 ≤ -ep12382 := by
  apply positive_check (eT := (14436072514523423631 / 12500000000000000000)) (y := (37614068245788663011 / 100000000000000000000)) (u := (14566520447469988171 / 10000000000000000000))
  · norm_num [world12382, agent12382, scalar12382, tp12382, tm12382, ep12382, em12382, dsL]
  · norm_num [world12382, agent12382, scalar12382, tp12382, tm12382, ep12382, em12382, dsL]
  · norm_num [world12382, agent12382, scalar12382, tp12382, tm12382, ep12382, em12382, dsL]
  · norm_num [world12382, agent12382, scalar12382, tp12382, tm12382, ep12382, em12382, dsL]
  · norm_num [world12382, agent12382, scalar12382, tp12382, tm12382, ep12382, em12382, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12382, agent12382, tp12382, tm12382, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12382, agent12382, scalar12382, tp12382, tm12382, ep12382, em12382, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12382, agent12382, tp12382, tm12382, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12382, agent12382, scalar12382, tp12382, tm12382, ep12382, em12382, dsL]

theorem negative12382 :
    Eminus aL (agent12382.root+dsL) scalar12382.worldRadius world12382.frame
      agent12382.frame tm12382 ≤ -em12382 := by
  apply negative_check (lo := (6854590069814232987 / 10000000000000000000)) (hi := (68545900698142329871 / 100000000000000000000))
    (y := (-((35852788030654668691 / 50000000000000000000)))) (u := (12204687072817974959 / 25000000000000000000))
  · norm_num [world12382, agent12382, scalar12382, tp12382, tm12382, ep12382, em12382, dsL]
  · norm_num [world12382, agent12382, scalar12382, tp12382, tm12382, ep12382, em12382, dsL]
  · norm_num [world12382, agent12382, scalar12382, tp12382, tm12382, ep12382, em12382, dsL]
  · norm_num [world12382, agent12382, scalar12382, tp12382, tm12382, ep12382, em12382, dsL]
  · norm_num [world12382, agent12382, scalar12382, tp12382, tm12382, ep12382, em12382, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12382, agent12382, tp12382, tm12382, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12382, agent12382, tp12382, tm12382, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12382, agent12382, scalar12382, tp12382, tm12382, ep12382, em12382, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12382, agent12382, tp12382, tm12382, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12382, agent12382, scalar12382, tp12382, tm12382, ep12382, em12382, dsL]

theorem tails12382 :
    exp (-((12382:ℝ)*ep12382)) ≤ scalar12382.upperTail ∧
    exp (-((12382:ℝ)*em12382)) ≤ scalar12382.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12382:ℝ)) (by norm_num [ep12382]) ?_)
      (show bp12382^8 ≤ scalar12382.upperTail by norm_num [bp12382, scalar12382])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12382, bp12382, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12382:ℝ)) (by norm_num [em12382]) ?_)
      (show bm12382^8 ≤ scalar12382.lowerTail by norm_num [bm12382, scalar12382])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12382, bm12382, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12382 :
    agent12382.root+dsL+scalar12382.worldRadius < √(1/100/aL) ∧
    2*(agent12382.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12382, agent12382, scalar12382, tp12382, tm12382, ep12382, em12382, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12382, agent12382, scalar12382, tp12382, tm12382, ep12382, em12382, dsL]

noncomputable def master12382 : MasterCertificate 12382 world12382 agent12382 :=
  master scalar12382 dsL tp12382 tm12382 ep12382 em12382
    (by norm_num [dsL]) (by norm_num [tp12382]) (by norm_num [tm12382])
    (by norm_num [ep12382]) (by norm_num [em12382])
    positive12382 negative12382 tails12382.1 tails12382.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12382.1 tailGuards12382.2

theorem preserves12382 : master12382.toScalarCertificate = scalar12382 := rfl

noncomputable def tp12383 : ℝ := (457062159 / 2000000000)
noncomputable def tm12383 : ℝ := (-((599354467 / 1000000000)))
noncomputable def ep12383 : ℝ := (10097633118140323 / 20000000000000000000)
noncomputable def em12383 : ℝ := (49291910569712363 / 100000000000000000000)
noncomputable def bp12383 : ℝ := (9154436090336968021 / 20000000000000000000)
noncomputable def bm12383 : ℝ := (2331380897051940941 / 5000000000000000000)

theorem positive12383 :
    Eplus aL (agent12383.root+dsL) scalar12383.worldRadius world12383.frame
      agent12383.frame tp12383 ≤ -ep12383 := by
  apply positive_check (eT := (1443611240931768533 / 1250000000000000000)) (y := (37614979540291643513 / 100000000000000000000)) (u := (9104158244984342041 / 6250000000000000000))
  · norm_num [world12383, agent12383, scalar12383, tp12383, tm12383, ep12383, em12383, dsL]
  · norm_num [world12383, agent12383, scalar12383, tp12383, tm12383, ep12383, em12383, dsL]
  · norm_num [world12383, agent12383, scalar12383, tp12383, tm12383, ep12383, em12383, dsL]
  · norm_num [world12383, agent12383, scalar12383, tp12383, tm12383, ep12383, em12383, dsL]
  · norm_num [world12383, agent12383, scalar12383, tp12383, tm12383, ep12383, em12383, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12383, agent12383, tp12383, tm12383, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12383, agent12383, scalar12383, tp12383, tm12383, ep12383, em12383, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12383, agent12383, tp12383, tm12383, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12383, agent12383, scalar12383, tp12383, tm12383, ep12383, em12383, dsL]

theorem negative12383 :
    Eminus aL (agent12383.root+dsL) scalar12383.worldRadius world12383.frame
      agent12383.frame tm12383 ≤ -em12383 := by
  apply negative_check (lo := (68545592850351421797 / 100000000000000000000)) (hi := (34272796425175710899 / 50000000000000000000))
    (y := (-((1792644472546588699 / 2500000000000000000)))) (u := (48818649267152737723 / 100000000000000000000))
  · norm_num [world12383, agent12383, scalar12383, tp12383, tm12383, ep12383, em12383, dsL]
  · norm_num [world12383, agent12383, scalar12383, tp12383, tm12383, ep12383, em12383, dsL]
  · norm_num [world12383, agent12383, scalar12383, tp12383, tm12383, ep12383, em12383, dsL]
  · norm_num [world12383, agent12383, scalar12383, tp12383, tm12383, ep12383, em12383, dsL]
  · norm_num [world12383, agent12383, scalar12383, tp12383, tm12383, ep12383, em12383, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12383, agent12383, tp12383, tm12383, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12383, agent12383, tp12383, tm12383, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12383, agent12383, scalar12383, tp12383, tm12383, ep12383, em12383, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12383, agent12383, tp12383, tm12383, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12383, agent12383, scalar12383, tp12383, tm12383, ep12383, em12383, dsL]

theorem tails12383 :
    exp (-((12383:ℝ)*ep12383)) ≤ scalar12383.upperTail ∧
    exp (-((12383:ℝ)*em12383)) ≤ scalar12383.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12383:ℝ)) (by norm_num [ep12383]) ?_)
      (show bp12383^8 ≤ scalar12383.upperTail by norm_num [bp12383, scalar12383])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12383, bp12383, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12383:ℝ)) (by norm_num [em12383]) ?_)
      (show bm12383^8 ≤ scalar12383.lowerTail by norm_num [bm12383, scalar12383])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12383, bm12383, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12383 :
    agent12383.root+dsL+scalar12383.worldRadius < √(1/100/aL) ∧
    2*(agent12383.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12383, agent12383, scalar12383, tp12383, tm12383, ep12383, em12383, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12383, agent12383, scalar12383, tp12383, tm12383, ep12383, em12383, dsL]

noncomputable def master12383 : MasterCertificate 12383 world12383 agent12383 :=
  master scalar12383 dsL tp12383 tm12383 ep12383 em12383
    (by norm_num [dsL]) (by norm_num [tp12383]) (by norm_num [tm12383])
    (by norm_num [ep12383]) (by norm_num [em12383])
    positive12383 negative12383 tails12383.1 tails12383.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12383.1 tailGuards12383.2

theorem preserves12383 : master12383.toScalarCertificate = scalar12383 := rfl

noncomputable def tp12384 : ℝ := (2285407489 / 10000000000)
noncomputable def tm12384 : ℝ := (-((1198750911 / 2000000000)))
noncomputable def ep12384 : ℝ := (12622793915989663 / 25000000000000000000)
noncomputable def em12384 : ℝ := (49294516601402051 / 100000000000000000000)
noncomputable def bp12384 : ℝ := (9153431847567205769 / 20000000000000000000)
noncomputable def bm12384 : ℝ := (4662286420589890599 / 10000000000000000000)

theorem positive12384 :
    Eplus aL (agent12384.root+dsL) scalar12384.worldRadius world12384.frame
      agent12384.frame tp12384 ≤ -ep12384 := by
  apply positive_check (eT := (115489218231974452499 / 100000000000000000000)) (y := (37615890808634579273 / 100000000000000000000)) (u := (29133571867757855061 / 20000000000000000000))
  · norm_num [world12384, agent12384, scalar12384, tp12384, tm12384, ep12384, em12384, dsL]
  · norm_num [world12384, agent12384, scalar12384, tp12384, tm12384, ep12384, em12384, dsL]
  · norm_num [world12384, agent12384, scalar12384, tp12384, tm12384, ep12384, em12384, dsL]
  · norm_num [world12384, agent12384, scalar12384, tp12384, tm12384, ep12384, em12384, dsL]
  · norm_num [world12384, agent12384, scalar12384, tp12384, tm12384, ep12384, em12384, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12384, agent12384, tp12384, tm12384, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12384, agent12384, scalar12384, tp12384, tm12384, ep12384, em12384, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12384, agent12384, tp12384, tm12384, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12384, agent12384, scalar12384, tp12384, tm12384, ep12384, em12384, dsL]

theorem negative12384 :
    Eminus aL (agent12384.root+dsL) scalar12384.worldRadius world12384.frame
      agent12384.frame tm12384 ≤ -em12384 := by
  apply negative_check (lo := (13709057029104975593 / 20000000000000000000)) (hi := (34272642572762438983 / 50000000000000000000))
    (y := (-((71705982278471627981 / 100000000000000000000)))) (u := (9763709996308141919 / 20000000000000000000))
  · norm_num [world12384, agent12384, scalar12384, tp12384, tm12384, ep12384, em12384, dsL]
  · norm_num [world12384, agent12384, scalar12384, tp12384, tm12384, ep12384, em12384, dsL]
  · norm_num [world12384, agent12384, scalar12384, tp12384, tm12384, ep12384, em12384, dsL]
  · norm_num [world12384, agent12384, scalar12384, tp12384, tm12384, ep12384, em12384, dsL]
  · norm_num [world12384, agent12384, scalar12384, tp12384, tm12384, ep12384, em12384, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12384, agent12384, tp12384, tm12384, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12384, agent12384, tp12384, tm12384, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12384, agent12384, scalar12384, tp12384, tm12384, ep12384, em12384, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12384, agent12384, tp12384, tm12384, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12384, agent12384, scalar12384, tp12384, tm12384, ep12384, em12384, dsL]

theorem tails12384 :
    exp (-((12384:ℝ)*ep12384)) ≤ scalar12384.upperTail ∧
    exp (-((12384:ℝ)*em12384)) ≤ scalar12384.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12384:ℝ)) (by norm_num [ep12384]) ?_)
      (show bp12384^8 ≤ scalar12384.upperTail by norm_num [bp12384, scalar12384])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12384, bp12384, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12384:ℝ)) (by norm_num [em12384]) ?_)
      (show bm12384^8 ≤ scalar12384.lowerTail by norm_num [bm12384, scalar12384])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12384, bm12384, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12384 :
    agent12384.root+dsL+scalar12384.worldRadius < √(1/100/aL) ∧
    2*(agent12384.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12384, agent12384, scalar12384, tp12384, tm12384, ep12384, em12384, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12384, agent12384, scalar12384, tp12384, tm12384, ep12384, em12384, dsL]

noncomputable def master12384 : MasterCertificate 12384 world12384 agent12384 :=
  master scalar12384 dsL tp12384 tm12384 ep12384 em12384
    (by norm_num [dsL]) (by norm_num [tp12384]) (by norm_num [tm12384])
    (by norm_num [ep12384]) (by norm_num [em12384])
    positive12384 negative12384 tails12384.1 tails12384.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12384.1 tailGuards12384.2

theorem preserves12384 : master12384.toScalarCertificate = scalar12384 := rfl

noncomputable def tp12385 : ℝ := (1142752079 / 5000000000)
noncomputable def tm12385 : ℝ := (-((5993964091 / 10000000000)))
noncomputable def ep12385 : ℝ := (5049418431112871 / 10000000000000000000)
noncomputable def em12385 : ℝ := (385133760294101 / 781250000000000000)
noncomputable def bp12385 : ℝ := (11440534810191283123 / 25000000000000000000)
noncomputable def bm12385 : ℝ := (145681598753291687 / 312500000000000000)

theorem positive12385 :
    Eplus aL (agent12385.root+dsL) scalar12385.worldRadius world12385.frame
      agent12385.frame tp12385 ≤ -ep12385 := by
  apply positive_check (eT := (3609048032483571229 / 3125000000000000000)) (y := (37616802021977444061 / 100000000000000000000)) (u := (145669186689807326471 / 100000000000000000000))
  · norm_num [world12385, agent12385, scalar12385, tp12385, tm12385, ep12385, em12385, dsL]
  · norm_num [world12385, agent12385, scalar12385, tp12385, tm12385, ep12385, em12385, dsL]
  · norm_num [world12385, agent12385, scalar12385, tp12385, tm12385, ep12385, em12385, dsL]
  · norm_num [world12385, agent12385, scalar12385, tp12385, tm12385, ep12385, em12385, dsL]
  · norm_num [world12385, agent12385, scalar12385, tp12385, tm12385, ep12385, em12385, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12385, agent12385, tp12385, tm12385, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12385, agent12385, scalar12385, tp12385, tm12385, ep12385, em12385, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12385, agent12385, tp12385, tm12385, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12385, agent12385, scalar12385, tp12385, tm12385, ep12385, em12385, dsL]

theorem negative12385 :
    Eminus aL (agent12385.root+dsL) scalar12385.worldRadius world12385.frame
      agent12385.frame tm12385 ≤ -em12385 := by
  apply negative_check (lo := (68544978892259509293 / 100000000000000000000)) (hi := (34272489446129754647 / 50000000000000000000))
    (y := (-((8963272864434609073 / 12500000000000000000)))) (u := (48818452033562282771 / 100000000000000000000))
  · norm_num [world12385, agent12385, scalar12385, tp12385, tm12385, ep12385, em12385, dsL]
  · norm_num [world12385, agent12385, scalar12385, tp12385, tm12385, ep12385, em12385, dsL]
  · norm_num [world12385, agent12385, scalar12385, tp12385, tm12385, ep12385, em12385, dsL]
  · norm_num [world12385, agent12385, scalar12385, tp12385, tm12385, ep12385, em12385, dsL]
  · norm_num [world12385, agent12385, scalar12385, tp12385, tm12385, ep12385, em12385, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12385, agent12385, tp12385, tm12385, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12385, agent12385, tp12385, tm12385, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12385, agent12385, scalar12385, tp12385, tm12385, ep12385, em12385, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12385, agent12385, tp12385, tm12385, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12385, agent12385, scalar12385, tp12385, tm12385, ep12385, em12385, dsL]

theorem tails12385 :
    exp (-((12385:ℝ)*ep12385)) ≤ scalar12385.upperTail ∧
    exp (-((12385:ℝ)*em12385)) ≤ scalar12385.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12385:ℝ)) (by norm_num [ep12385]) ?_)
      (show bp12385^8 ≤ scalar12385.upperTail by norm_num [bp12385, scalar12385])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12385, bp12385, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12385:ℝ)) (by norm_num [em12385]) ?_)
      (show bm12385^8 ≤ scalar12385.lowerTail by norm_num [bm12385, scalar12385])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12385, bm12385, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12385 :
    agent12385.root+dsL+scalar12385.worldRadius < √(1/100/aL) ∧
    2*(agent12385.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12385, agent12385, scalar12385, tp12385, tm12385, ep12385, em12385, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12385, agent12385, scalar12385, tp12385, tm12385, ep12385, em12385, dsL]

noncomputable def master12385 : MasterCertificate 12385 world12385 agent12385 :=
  master scalar12385 dsL tp12385 tm12385 ep12385 em12385
    (by norm_num [dsL]) (by norm_num [tp12385]) (by norm_num [tm12385])
    (by norm_num [ep12385]) (by norm_num [em12385])
    positive12385 negative12385 tails12385.1 tails12385.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12385.1 tailGuards12385.2

theorem preserves12385 : master12385.toScalarCertificate = scalar12385 := rfl

noncomputable def tp12386 : ℝ := (1142800353 / 5000000000)
noncomputable def tm12386 : ℝ := (-((5994173603 / 10000000000)))
noncomputable def ep12386 : ℝ := (394509307788317 / 781250000000000000)
noncomputable def em12386 : ℝ := (12324931144009469 / 25000000000000000000)
noncomputable def bp12386 : ℝ := (22878560278146802361 / 50000000000000000000)
noncomputable def bm12386 : ℝ := (9322672045851260491 / 20000000000000000000)

theorem positive12386 :
    Eplus aL (agent12386.root+dsL) scalar12386.worldRadius world12386.frame
      agent12386.frame tp12386 ≤ -ep12386 := by
  apply positive_check (eT := (115489854998429612697 / 100000000000000000000)) (y := (7523542326979294889 / 20000000000000000000)) (u := (7283525586078741219 / 5000000000000000000))
  · norm_num [world12386, agent12386, scalar12386, tp12386, tm12386, ep12386, em12386, dsL]
  · norm_num [world12386, agent12386, scalar12386, tp12386, tm12386, ep12386, em12386, dsL]
  · norm_num [world12386, agent12386, scalar12386, tp12386, tm12386, ep12386, em12386, dsL]
  · norm_num [world12386, agent12386, scalar12386, tp12386, tm12386, ep12386, em12386, dsL]
  · norm_num [world12386, agent12386, scalar12386, tp12386, tm12386, ep12386, em12386, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12386, agent12386, tp12386, tm12386, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12386, agent12386, scalar12386, tp12386, tm12386, ep12386, em12386, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12386, agent12386, tp12386, tm12386, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12386, agent12386, scalar12386, tp12386, tm12386, ep12386, em12386, dsL]

theorem negative12386 :
    Eminus aL (agent12386.root+dsL) scalar12386.worldRadius world12386.frame
      agent12386.frame tm12386 ≤ -em12386 := by
  apply negative_check (lo := (17136168171714813991 / 25000000000000000000)) (hi := (13708934537371851193 / 20000000000000000000))
    (y := (-((71706384301018200857 / 100000000000000000000)))) (u := (48818353720357381221 / 100000000000000000000))
  · norm_num [world12386, agent12386, scalar12386, tp12386, tm12386, ep12386, em12386, dsL]
  · norm_num [world12386, agent12386, scalar12386, tp12386, tm12386, ep12386, em12386, dsL]
  · norm_num [world12386, agent12386, scalar12386, tp12386, tm12386, ep12386, em12386, dsL]
  · norm_num [world12386, agent12386, scalar12386, tp12386, tm12386, ep12386, em12386, dsL]
  · norm_num [world12386, agent12386, scalar12386, tp12386, tm12386, ep12386, em12386, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12386, agent12386, tp12386, tm12386, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12386, agent12386, tp12386, tm12386, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12386, agent12386, scalar12386, tp12386, tm12386, ep12386, em12386, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12386, agent12386, tp12386, tm12386, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12386, agent12386, scalar12386, tp12386, tm12386, ep12386, em12386, dsL]

theorem tails12386 :
    exp (-((12386:ℝ)*ep12386)) ≤ scalar12386.upperTail ∧
    exp (-((12386:ℝ)*em12386)) ≤ scalar12386.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12386:ℝ)) (by norm_num [ep12386]) ?_)
      (show bp12386^8 ≤ scalar12386.upperTail by norm_num [bp12386, scalar12386])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12386, bp12386, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12386:ℝ)) (by norm_num [em12386]) ?_)
      (show bm12386^8 ≤ scalar12386.lowerTail by norm_num [bm12386, scalar12386])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12386, bm12386, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12386 :
    agent12386.root+dsL+scalar12386.worldRadius < √(1/100/aL) ∧
    2*(agent12386.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12386, agent12386, scalar12386, tp12386, tm12386, ep12386, em12386, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12386, agent12386, scalar12386, tp12386, tm12386, ep12386, em12386, dsL]

noncomputable def master12386 : MasterCertificate 12386 world12386 agent12386 :=
  master scalar12386 dsL tp12386 tm12386 ep12386 em12386
    (by norm_num [dsL]) (by norm_num [tp12386]) (by norm_num [tm12386])
    (by norm_num [ep12386]) (by norm_num [em12386])
    positive12386 negative12386 tails12386.1 tails12386.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12386.1 tailGuards12386.2

theorem preserves12386 : master12386.toScalarCertificate = scalar12386 := rfl

noncomputable def tp12387 : ℝ := (571424311 / 2500000000)
noncomputable def tm12387 : ℝ := (-((749297861 / 1250000000)))
noncomputable def ep12387 : ℝ := (50500196456034661 / 100000000000000000000)
noncomputable def em12387 : ℝ := (49302325946497519 / 100000000000000000000)
noncomputable def bp12387 : ℝ := (45752103513969043139 / 100000000000000000000)
noncomputable def bm12387 : ℝ := (11652152600216301557 / 25000000000000000000)

theorem positive12387 :
    Eplus aL (agent12387.root+dsL) scalar12387.worldRadius world12387.frame
      agent12387.frame tp12387 ≤ -ep12387 := by
  apply positive_check (eT := (115490172916643354003 / 100000000000000000000)) (y := (37618621657372487021 / 100000000000000000000)) (u := (72835918681002108513 / 50000000000000000000))
  · norm_num [world12387, agent12387, scalar12387, tp12387, tm12387, ep12387, em12387, dsL]
  · norm_num [world12387, agent12387, scalar12387, tp12387, tm12387, ep12387, em12387, dsL]
  · norm_num [world12387, agent12387, scalar12387, tp12387, tm12387, ep12387, em12387, dsL]
  · norm_num [world12387, agent12387, scalar12387, tp12387, tm12387, ep12387, em12387, dsL]
  · norm_num [world12387, agent12387, scalar12387, tp12387, tm12387, ep12387, em12387, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12387, agent12387, tp12387, tm12387, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12387, agent12387, scalar12387, tp12387, tm12387, ep12387, em12387, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12387, agent12387, tp12387, tm12387, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12387, agent12387, scalar12387, tp12387, tm12387, ep12387, em12387, dsL]

theorem negative12387 :
    Eminus aL (agent12387.root+dsL) scalar12387.worldRadius world12387.frame
      agent12387.frame tm12387 ≤ -em12387 := by
  apply negative_check (lo := (34272183702989076549 / 50000000000000000000)) (hi := (68544367405978153099 / 100000000000000000000))
    (y := (-((14341316861496139189 / 20000000000000000000)))) (u := (48818256080592699747 / 100000000000000000000))
  · norm_num [world12387, agent12387, scalar12387, tp12387, tm12387, ep12387, em12387, dsL]
  · norm_num [world12387, agent12387, scalar12387, tp12387, tm12387, ep12387, em12387, dsL]
  · norm_num [world12387, agent12387, scalar12387, tp12387, tm12387, ep12387, em12387, dsL]
  · norm_num [world12387, agent12387, scalar12387, tp12387, tm12387, ep12387, em12387, dsL]
  · norm_num [world12387, agent12387, scalar12387, tp12387, tm12387, ep12387, em12387, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12387, agent12387, tp12387, tm12387, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12387, agent12387, tp12387, tm12387, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12387, agent12387, scalar12387, tp12387, tm12387, ep12387, em12387, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12387, agent12387, tp12387, tm12387, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12387, agent12387, scalar12387, tp12387, tm12387, ep12387, em12387, dsL]

theorem tails12387 :
    exp (-((12387:ℝ)*ep12387)) ≤ scalar12387.upperTail ∧
    exp (-((12387:ℝ)*em12387)) ≤ scalar12387.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12387:ℝ)) (by norm_num [ep12387]) ?_)
      (show bp12387^8 ≤ scalar12387.upperTail by norm_num [bp12387, scalar12387])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12387, bp12387, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12387:ℝ)) (by norm_num [em12387]) ?_)
      (show bm12387^8 ≤ scalar12387.lowerTail by norm_num [bm12387, scalar12387])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12387, bm12387, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12387 :
    agent12387.root+dsL+scalar12387.worldRadius < √(1/100/aL) ∧
    2*(agent12387.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12387, agent12387, scalar12387, tp12387, tm12387, ep12387, em12387, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12387, agent12387, scalar12387, tp12387, tm12387, ep12387, em12387, dsL]

noncomputable def master12387 : MasterCertificate 12387 world12387 agent12387 :=
  master scalar12387 dsL tp12387 tm12387 ep12387 em12387
    (by norm_num [dsL]) (by norm_num [tp12387]) (by norm_num [tm12387])
    (by norm_num [ep12387]) (by norm_num [em12387])
    positive12387 negative12387 tails12387.1 tails12387.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12387.1 tailGuards12387.2

theorem preserves12387 : master12387.toScalarCertificate = scalar12387 := rfl

noncomputable def tp12388 : ℝ := (571448439 / 2500000000)
noncomputable def tm12388 : ℝ := (-((5854094 / 9765625)))
noncomputable def ep12388 : ℝ := (50503200093897603 / 100000000000000000000)
noncomputable def em12388 : ℝ := (24652463002904939 / 50000000000000000000)
noncomputable def bp12388 : ℝ := (714798245076144659 / 1562500000000000000)
noncomputable def bm12388 : ℝ := (23301930849796500681 / 50000000000000000000)

theorem positive12388 :
    Eplus aL (agent12388.root+dsL) scalar12388.worldRadius world12388.frame
      agent12388.frame tp12388 ≤ -ep12388 := by
  apply positive_check (eT := (14436311334706318831 / 12500000000000000000)) (y := (37619531606454425929 / 100000000000000000000)) (u := (145673162907581821883 / 100000000000000000000))
  · norm_num [world12388, agent12388, scalar12388, tp12388, tm12388, ep12388, em12388, dsL]
  · norm_num [world12388, agent12388, scalar12388, tp12388, tm12388, ep12388, em12388, dsL]
  · norm_num [world12388, agent12388, scalar12388, tp12388, tm12388, ep12388, em12388, dsL]
  · norm_num [world12388, agent12388, scalar12388, tp12388, tm12388, ep12388, em12388, dsL]
  · norm_num [world12388, agent12388, scalar12388, tp12388, tm12388, ep12388, em12388, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12388, agent12388, tp12388, tm12388, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12388, agent12388, scalar12388, tp12388, tm12388, ep12388, em12388, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12388, agent12388, tp12388, tm12388, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12388, agent12388, scalar12388, tp12388, tm12388, ep12388, em12388, dsL]

theorem negative12388 :
    Eminus aL (agent12388.root+dsL) scalar12388.worldRadius world12388.frame
      agent12388.frame tm12388 ≤ -em12388 := by
  apply negative_check (lo := (34272030855410626419 / 50000000000000000000)) (hi := (68544061710821252839 / 100000000000000000000))
    (y := (-((71706785826362778621 / 100000000000000000000)))) (u := (48818157702687918939 / 100000000000000000000))
  · norm_num [world12388, agent12388, scalar12388, tp12388, tm12388, ep12388, em12388, dsL]
  · norm_num [world12388, agent12388, scalar12388, tp12388, tm12388, ep12388, em12388, dsL]
  · norm_num [world12388, agent12388, scalar12388, tp12388, tm12388, ep12388, em12388, dsL]
  · norm_num [world12388, agent12388, scalar12388, tp12388, tm12388, ep12388, em12388, dsL]
  · norm_num [world12388, agent12388, scalar12388, tp12388, tm12388, ep12388, em12388, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12388, agent12388, tp12388, tm12388, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12388, agent12388, tp12388, tm12388, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12388, agent12388, scalar12388, tp12388, tm12388, ep12388, em12388, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12388, agent12388, tp12388, tm12388, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12388, agent12388, scalar12388, tp12388, tm12388, ep12388, em12388, dsL]

theorem tails12388 :
    exp (-((12388:ℝ)*ep12388)) ≤ scalar12388.upperTail ∧
    exp (-((12388:ℝ)*em12388)) ≤ scalar12388.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12388:ℝ)) (by norm_num [ep12388]) ?_)
      (show bp12388^8 ≤ scalar12388.upperTail by norm_num [bp12388, scalar12388])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12388, bp12388, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12388:ℝ)) (by norm_num [em12388]) ?_)
      (show bm12388^8 ≤ scalar12388.lowerTail by norm_num [bm12388, scalar12388])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12388, bm12388, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12388 :
    agent12388.root+dsL+scalar12388.worldRadius < √(1/100/aL) ∧
    2*(agent12388.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12388, agent12388, scalar12388, tp12388, tm12388, ep12388, em12388, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12388, agent12388, scalar12388, tp12388, tm12388, ep12388, em12388, dsL]

noncomputable def master12388 : MasterCertificate 12388 world12388 agent12388 :=
  master scalar12388 dsL tp12388 tm12388 ep12388 em12388
    (by norm_num [dsL]) (by norm_num [tp12388]) (by norm_num [tm12388])
    (by norm_num [ep12388]) (by norm_num [em12388])
    positive12388 negative12388 tails12388.1 tails12388.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12388.1 tailGuards12388.2

theorem preserves12388 : master12388.toScalarCertificate = scalar12388 := rfl

noncomputable def tp12389 : ℝ := (1142945103 / 5000000000)
noncomputable def tm12389 : ℝ := (-((1198960277 / 2000000000)))
noncomputable def ep12389 : ℝ := (12626550622816441 / 25000000000000000000)
noncomputable def em12389 : ℝ := (49307524887424547 / 100000000000000000000)
noncomputable def bp12389 : ℝ := (22871036470458668257 / 50000000000000000000)
noncomputable def bm12389 : ℝ := (2329955701455980641 / 5000000000000000000)

theorem positive12389 :
    Eplus aL (agent12389.root+dsL) scalar12389.worldRadius world12389.frame
      agent12389.frame tp12389 ≤ -ep12389 := by
  apply positive_check (eT := (115490808019493929739 / 100000000000000000000)) (y := (37620441099794852113 / 100000000000000000000)) (u := (145674487801322155561 / 100000000000000000000))
  · norm_num [world12389, agent12389, scalar12389, tp12389, tm12389, ep12389, em12389, dsL]
  · norm_num [world12389, agent12389, scalar12389, tp12389, tm12389, ep12389, em12389, dsL]
  · norm_num [world12389, agent12389, scalar12389, tp12389, tm12389, ep12389, em12389, dsL]
  · norm_num [world12389, agent12389, scalar12389, tp12389, tm12389, ep12389, em12389, dsL]
  · norm_num [world12389, agent12389, scalar12389, tp12389, tm12389, ep12389, em12389, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12389, agent12389, tp12389, tm12389, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12389, agent12389, scalar12389, tp12389, tm12389, ep12389, em12389, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12389, agent12389, tp12389, tm12389, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12389, agent12389, scalar12389, tp12389, tm12389, ep12389, em12389, dsL]

theorem negative12389 :
    Eminus aL (agent12389.root+dsL) scalar12389.worldRadius world12389.frame
      agent12389.frame tm12389 ≤ -em12389 := by
  apply negative_check (lo := (68543756992021732231 / 100000000000000000000)) (hi := (8567969624002716529 / 12500000000000000000))
    (y := (-((71706986392394131197 / 100000000000000000000)))) (u := (488180597901446249 / 1000000000000000000))
  · norm_num [world12389, agent12389, scalar12389, tp12389, tm12389, ep12389, em12389, dsL]
  · norm_num [world12389, agent12389, scalar12389, tp12389, tm12389, ep12389, em12389, dsL]
  · norm_num [world12389, agent12389, scalar12389, tp12389, tm12389, ep12389, em12389, dsL]
  · norm_num [world12389, agent12389, scalar12389, tp12389, tm12389, ep12389, em12389, dsL]
  · norm_num [world12389, agent12389, scalar12389, tp12389, tm12389, ep12389, em12389, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12389, agent12389, tp12389, tm12389, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12389, agent12389, tp12389, tm12389, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12389, agent12389, scalar12389, tp12389, tm12389, ep12389, em12389, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12389, agent12389, tp12389, tm12389, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12389, agent12389, scalar12389, tp12389, tm12389, ep12389, em12389, dsL]

theorem tails12389 :
    exp (-((12389:ℝ)*ep12389)) ≤ scalar12389.upperTail ∧
    exp (-((12389:ℝ)*em12389)) ≤ scalar12389.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12389:ℝ)) (by norm_num [ep12389]) ?_)
      (show bp12389^8 ≤ scalar12389.upperTail by norm_num [bp12389, scalar12389])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12389, bp12389, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12389:ℝ)) (by norm_num [em12389]) ?_)
      (show bm12389^8 ≤ scalar12389.lowerTail by norm_num [bm12389, scalar12389])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12389, bm12389, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12389 :
    agent12389.root+dsL+scalar12389.worldRadius < √(1/100/aL) ∧
    2*(agent12389.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12389, agent12389, scalar12389, tp12389, tm12389, ep12389, em12389, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12389, agent12389, scalar12389, tp12389, tm12389, ep12389, em12389, dsL]

noncomputable def master12389 : MasterCertificate 12389 world12389 agent12389 :=
  master scalar12389 dsL tp12389 tm12389 ep12389 em12389
    (by norm_num [dsL]) (by norm_num [tp12389]) (by norm_num [tm12389])
    (by norm_num [ep12389]) (by norm_num [em12389])
    positive12389 negative12389 tails12389.1 tails12389.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12389.1 tailGuards12389.2

theorem preserves12389 : master12389.toScalarCertificate = scalar12389 := rfl

noncomputable def tp12390 : ℝ := (285757967 / 1250000000)
noncomputable def tm12390 : ℝ := (-((5995243371 / 10000000000)))
noncomputable def ep12390 : ℝ := (50510690728329501 / 100000000000000000000)
noncomputable def em12390 : ℝ := (197246958129591 / 400000000000000000)
noncomputable def bp12390 : ℝ := (22868002958465779539 / 50000000000000000000)
noncomputable def bm12390 : ℝ := (46593200570441576159 / 100000000000000000000)

theorem positive12390 :
    Eplus aL (agent12390.root+dsL) scalar12390.worldRadius world12390.frame
      agent12390.frame tp12390 ≤ -ep12390 := by
  apply positive_check (eT := (115491686248960025407 / 100000000000000000000)) (y := (37620614988184518653 / 100000000000000000000)) (u := (4552335659767605863 / 3125000000000000000))
  · norm_num [world12390, agent12390, scalar12390, tp12390, tm12390, ep12390, em12390, dsL]
  · norm_num [world12390, agent12390, scalar12390, tp12390, tm12390, ep12390, em12390, dsL]
  · norm_num [world12390, agent12390, scalar12390, tp12390, tm12390, ep12390, em12390, dsL]
  · norm_num [world12390, agent12390, scalar12390, tp12390, tm12390, ep12390, em12390, dsL]
  · norm_num [world12390, agent12390, scalar12390, tp12390, tm12390, ep12390, em12390, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12390, agent12390, tp12390, tm12390, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12390, agent12390, scalar12390, tp12390, tm12390, ep12390, em12390, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12390, agent12390, tp12390, tm12390, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12390, agent12390, scalar12390, tp12390, tm12390, ep12390, em12390, dsL]

theorem negative12390 :
    Eminus aL (agent12390.root+dsL) scalar12390.worldRadius world12390.frame
      agent12390.frame tm12390 ≤ -em12390 := by
  apply negative_check (lo := (17135611662146374549 / 25000000000000000000)) (hi := (68542446648585498197 / 100000000000000000000))
    (y := (-((35852621121045962569 / 50000000000000000000)))) (u := (12204727814476850759 / 25000000000000000000))
  · norm_num [world12390, agent12390, scalar12390, tp12390, tm12390, ep12390, em12390, dsL]
  · norm_num [world12390, agent12390, scalar12390, tp12390, tm12390, ep12390, em12390, dsL]
  · norm_num [world12390, agent12390, scalar12390, tp12390, tm12390, ep12390, em12390, dsL]
  · norm_num [world12390, agent12390, scalar12390, tp12390, tm12390, ep12390, em12390, dsL]
  · norm_num [world12390, agent12390, scalar12390, tp12390, tm12390, ep12390, em12390, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12390, agent12390, tp12390, tm12390, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12390, agent12390, tp12390, tm12390, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12390, agent12390, scalar12390, tp12390, tm12390, ep12390, em12390, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12390, agent12390, tp12390, tm12390, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12390, agent12390, scalar12390, tp12390, tm12390, ep12390, em12390, dsL]

theorem tails12390 :
    exp (-((12390:ℝ)*ep12390)) ≤ scalar12390.upperTail ∧
    exp (-((12390:ℝ)*em12390)) ≤ scalar12390.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12390:ℝ)) (by norm_num [ep12390]) ?_)
      (show bp12390^8 ≤ scalar12390.upperTail by norm_num [bp12390, scalar12390])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12390, bp12390, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12390:ℝ)) (by norm_num [em12390]) ?_)
      (show bm12390^8 ≤ scalar12390.lowerTail by norm_num [bm12390, scalar12390])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12390, bm12390, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12390 :
    agent12390.root+dsL+scalar12390.worldRadius < √(1/100/aL) ∧
    2*(agent12390.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12390, agent12390, scalar12390, tp12390, tm12390, ep12390, em12390, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12390, agent12390, scalar12390, tp12390, tm12390, ep12390, em12390, dsL]

noncomputable def master12390 : MasterCertificate 12390 world12390 agent12390 :=
  master scalar12390 dsL tp12390 tm12390 ep12390 em12390
    (by norm_num [dsL]) (by norm_num [tp12390]) (by norm_num [tm12390])
    (by norm_num [ep12390]) (by norm_num [em12390])
    positive12390 negative12390 tails12390.1 tails12390.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12390.1 tailGuards12390.2

theorem preserves12390 : master12390.toScalarCertificate = scalar12390 := rfl

noncomputable def tp12391 : ℝ := (2286160057 / 10000000000)
noncomputable def tm12391 : ℝ := (-((5995452311 / 10000000000)))
noncomputable def ep12391 : ℝ := (25256844901062887 / 50000000000000000000)
noncomputable def em12391 : ℝ := (24657167668098879 / 50000000000000000000)
noncomputable def bp12391 : ℝ := (22865496985218074797 / 50000000000000000000)
noncomputable def bm12391 : ℝ := (11647113876876407837 / 25000000000000000000)

theorem positive12391 :
    Eplus aL (agent12391.root+dsL) scalar12391.worldRadius world12391.frame
      agent12391.frame tp12391 ≤ -ep12391 := by
  apply positive_check (eT := (57746001352384937863 / 50000000000000000000)) (y := (37621523074272621999 / 100000000000000000000)) (u := (72838031985313823651 / 50000000000000000000))
  · norm_num [world12391, agent12391, scalar12391, tp12391, tm12391, ep12391, em12391, dsL]
  · norm_num [world12391, agent12391, scalar12391, tp12391, tm12391, ep12391, em12391, dsL]
  · norm_num [world12391, agent12391, scalar12391, tp12391, tm12391, ep12391, em12391, dsL]
  · norm_num [world12391, agent12391, scalar12391, tp12391, tm12391, ep12391, em12391, dsL]
  · norm_num [world12391, agent12391, scalar12391, tp12391, tm12391, ep12391, em12391, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12391, agent12391, tp12391, tm12391, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12391, agent12391, scalar12391, tp12391, tm12391, ep12391, em12391, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12391, agent12391, tp12391, tm12391, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12391, agent12391, scalar12391, tp12391, tm12391, ep12391, em12391, dsL]

theorem negative12391 :
    Eminus aL (agent12391.root+dsL) scalar12391.worldRadius world12391.frame
      agent12391.frame tm12391 ≤ -em12391 := by
  apply negative_check (lo := (68542142661950102809 / 100000000000000000000)) (hi := (6854214266195010281 / 10000000000000000000))
    (y := (-((71705442357333109877 / 100000000000000000000)))) (u := (48818813563923145819 / 100000000000000000000))
  · norm_num [world12391, agent12391, scalar12391, tp12391, tm12391, ep12391, em12391, dsL]
  · norm_num [world12391, agent12391, scalar12391, tp12391, tm12391, ep12391, em12391, dsL]
  · norm_num [world12391, agent12391, scalar12391, tp12391, tm12391, ep12391, em12391, dsL]
  · norm_num [world12391, agent12391, scalar12391, tp12391, tm12391, ep12391, em12391, dsL]
  · norm_num [world12391, agent12391, scalar12391, tp12391, tm12391, ep12391, em12391, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12391, agent12391, tp12391, tm12391, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12391, agent12391, tp12391, tm12391, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12391, agent12391, scalar12391, tp12391, tm12391, ep12391, em12391, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12391, agent12391, tp12391, tm12391, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12391, agent12391, scalar12391, tp12391, tm12391, ep12391, em12391, dsL]

theorem tails12391 :
    exp (-((12391:ℝ)*ep12391)) ≤ scalar12391.upperTail ∧
    exp (-((12391:ℝ)*em12391)) ≤ scalar12391.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12391:ℝ)) (by norm_num [ep12391]) ?_)
      (show bp12391^8 ≤ scalar12391.upperTail by norm_num [bp12391, scalar12391])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12391, bp12391, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12391:ℝ)) (by norm_num [em12391]) ?_)
      (show bm12391^8 ≤ scalar12391.lowerTail by norm_num [bm12391, scalar12391])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12391, bm12391, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12391 :
    agent12391.root+dsL+scalar12391.worldRadius < √(1/100/aL) ∧
    2*(agent12391.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12391, agent12391, scalar12391, tp12391, tm12391, ep12391, em12391, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12391, agent12391, scalar12391, tp12391, tm12391, ep12391, em12391, dsL]

noncomputable def master12391 : MasterCertificate 12391 world12391 agent12391 :=
  master scalar12391 dsL tp12391 tm12391 ep12391 em12391
    (by norm_num [dsL]) (by norm_num [tp12391]) (by norm_num [tm12391])
    (by norm_num [ep12391]) (by norm_num [em12391])
    positive12391 negative12391 tails12391.1 tails12391.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12391.1 tailGuards12391.2

theorem preserves12391 : master12391.toScalarCertificate = scalar12391 := rfl

noncomputable def tp12392 : ℝ := (2286256339 / 10000000000)
noncomputable def tm12392 : ℝ := (-((749457643 / 1250000000)))
noncomputable def ep12392 : ℝ := (3157292995307513 / 6250000000000000000)
noncomputable def em12392 : ℝ := (49316930263541533 / 100000000000000000000)
noncomputable def bp12392 : ℝ := (11431495725980626953 / 25000000000000000000)
noncomputable def bm12392 : ℝ := (46583711257937385483 / 100000000000000000000)

theorem positive12392 :
    Eplus aL (agent12392.root+dsL) scalar12392.worldRadius world12392.frame
      agent12392.frame tp12392 ≤ -ep12392 := by
  apply positive_check (eT := (57746159454423316159 / 50000000000000000000)) (y := (37622430807730833427 / 100000000000000000000)) (u := (145677386327002640719 / 100000000000000000000))
  · norm_num [world12392, agent12392, scalar12392, tp12392, tm12392, ep12392, em12392, dsL]
  · norm_num [world12392, agent12392, scalar12392, tp12392, tm12392, ep12392, em12392, dsL]
  · norm_num [world12392, agent12392, scalar12392, tp12392, tm12392, ep12392, em12392, dsL]
  · norm_num [world12392, agent12392, scalar12392, tp12392, tm12392, ep12392, em12392, dsL]
  · norm_num [world12392, agent12392, scalar12392, tp12392, tm12392, ep12392, em12392, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12392, agent12392, tp12392, tm12392, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12392, agent12392, scalar12392, tp12392, tm12392, ep12392, em12392, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12392, agent12392, tp12392, tm12392, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12392, agent12392, scalar12392, tp12392, tm12392, ep12392, em12392, dsL]

theorem negative12392 :
    Eminus aL (agent12392.root+dsL) scalar12392.worldRadius world12392.frame
      agent12392.frame tm12392 ≤ -em12392 := by
  apply negative_check (lo := (68541839081486151851 / 100000000000000000000)) (hi := (17135459770371537963 / 25000000000000000000))
    (y := (-((14341128448202992171 / 20000000000000000000)))) (u := (4881871598317868231 / 10000000000000000000))
  · norm_num [world12392, agent12392, scalar12392, tp12392, tm12392, ep12392, em12392, dsL]
  · norm_num [world12392, agent12392, scalar12392, tp12392, tm12392, ep12392, em12392, dsL]
  · norm_num [world12392, agent12392, scalar12392, tp12392, tm12392, ep12392, em12392, dsL]
  · norm_num [world12392, agent12392, scalar12392, tp12392, tm12392, ep12392, em12392, dsL]
  · norm_num [world12392, agent12392, scalar12392, tp12392, tm12392, ep12392, em12392, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12392, agent12392, tp12392, tm12392, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12392, agent12392, tp12392, tm12392, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12392, agent12392, scalar12392, tp12392, tm12392, ep12392, em12392, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12392, agent12392, tp12392, tm12392, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12392, agent12392, scalar12392, tp12392, tm12392, ep12392, em12392, dsL]

theorem tails12392 :
    exp (-((12392:ℝ)*ep12392)) ≤ scalar12392.upperTail ∧
    exp (-((12392:ℝ)*em12392)) ≤ scalar12392.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12392:ℝ)) (by norm_num [ep12392]) ?_)
      (show bp12392^8 ≤ scalar12392.upperTail by norm_num [bp12392, scalar12392])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12392, bp12392, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12392:ℝ)) (by norm_num [em12392]) ?_)
      (show bm12392^8 ≤ scalar12392.lowerTail by norm_num [bm12392, scalar12392])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12392, bm12392, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12392 :
    agent12392.root+dsL+scalar12392.worldRadius < √(1/100/aL) ∧
    2*(agent12392.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12392, agent12392, scalar12392, tp12392, tm12392, ep12392, em12392, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12392, agent12392, scalar12392, tp12392, tm12392, ep12392, em12392, dsL]

noncomputable def master12392 : MasterCertificate 12392 world12392 agent12392 :=
  master scalar12392 dsL tp12392 tm12392 ep12392 em12392
    (by norm_num [dsL]) (by norm_num [tp12392]) (by norm_num [tm12392])
    (by norm_num [ep12392]) (by norm_num [em12392])
    positive12392 negative12392 tails12392.1 tails12392.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12392.1 tailGuards12392.2

theorem preserves12392 : master12392.toScalarCertificate = scalar12392 := rfl

noncomputable def tp12393 : ℝ := (142897041 / 625000000)
noncomputable def tm12393 : ℝ := (-((2997934917 / 5000000000)))
noncomputable def ep12393 : ℝ := (10103936804263829 / 20000000000000000000)
noncomputable def em12393 : ℝ := (24659761651756727 / 50000000000000000000)
noncomputable def bp12393 : ℝ := (4572097347905924069 / 10000000000000000000)
noncomputable def bm12393 : ℝ := (23289484275591324713 / 50000000000000000000)

theorem positive12393 :
    Eplus aL (agent12393.root+dsL) scalar12393.worldRadius world12393.frame
      agent12393.frame tp12393 ≤ -ep12393 := by
  apply positive_check (eT := (57746317699814493829 / 50000000000000000000)) (y := (2351458734022914547 / 6250000000000000000)) (u := (145678710448154743773 / 100000000000000000000))
  · norm_num [world12393, agent12393, scalar12393, tp12393, tm12393, ep12393, em12393, dsL]
  · norm_num [world12393, agent12393, scalar12393, tp12393, tm12393, ep12393, em12393, dsL]
  · norm_num [world12393, agent12393, scalar12393, tp12393, tm12393, ep12393, em12393, dsL]
  · norm_num [world12393, agent12393, scalar12393, tp12393, tm12393, ep12393, em12393, dsL]
  · norm_num [world12393, agent12393, scalar12393, tp12393, tm12393, ep12393, em12393, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12393, agent12393, tp12393, tm12393, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12393, agent12393, scalar12393, tp12393, tm12393, ep12393, em12393, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12393, agent12393, tp12393, tm12393, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12393, agent12393, scalar12393, tp12393, tm12393, ep12393, em12393, dsL]

theorem negative12393 :
    Eminus aL (agent12393.root+dsL) scalar12393.worldRadius world12393.frame
      agent12393.frame tm12393 ≤ -em12393 := by
  apply negative_check (lo := (34270768031297087211 / 50000000000000000000)) (hi := (68541536062594174423 / 100000000000000000000))
    (y := (-((17926460392482596011 / 25000000000000000000)))) (u := (195274474693834291 / 400000000000000000))
  · norm_num [world12393, agent12393, scalar12393, tp12393, tm12393, ep12393, em12393, dsL]
  · norm_num [world12393, agent12393, scalar12393, tp12393, tm12393, ep12393, em12393, dsL]
  · norm_num [world12393, agent12393, scalar12393, tp12393, tm12393, ep12393, em12393, dsL]
  · norm_num [world12393, agent12393, scalar12393, tp12393, tm12393, ep12393, em12393, dsL]
  · norm_num [world12393, agent12393, scalar12393, tp12393, tm12393, ep12393, em12393, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12393, agent12393, tp12393, tm12393, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12393, agent12393, tp12393, tm12393, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12393, agent12393, scalar12393, tp12393, tm12393, ep12393, em12393, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12393, agent12393, tp12393, tm12393, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12393, agent12393, scalar12393, tp12393, tm12393, ep12393, em12393, dsL]

theorem tails12393 :
    exp (-((12393:ℝ)*ep12393)) ≤ scalar12393.upperTail ∧
    exp (-((12393:ℝ)*em12393)) ≤ scalar12393.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12393:ℝ)) (by norm_num [ep12393]) ?_)
      (show bp12393^8 ≤ scalar12393.upperTail by norm_num [bp12393, scalar12393])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12393, bp12393, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12393:ℝ)) (by norm_num [em12393]) ?_)
      (show bm12393^8 ≤ scalar12393.lowerTail by norm_num [bm12393, scalar12393])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12393, bm12393, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12393 :
    agent12393.root+dsL+scalar12393.worldRadius < √(1/100/aL) ∧
    2*(agent12393.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12393, agent12393, scalar12393, tp12393, tm12393, ep12393, em12393, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12393, agent12393, scalar12393, tp12393, tm12393, ep12393, em12393, dsL]

noncomputable def master12393 : MasterCertificate 12393 world12393 agent12393 :=
  master scalar12393 dsL tp12393 tm12393 ep12393 em12393
    (by norm_num [dsL]) (by norm_num [tp12393]) (by norm_num [tm12393])
    (by norm_num [ep12393]) (by norm_num [em12393])
    positive12393 negative12393 tails12393.1 tails12393.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12393.1 tailGuards12393.2

theorem preserves12393 : master12393.toScalarCertificate = scalar12393 := rfl

noncomputable def tp12394 : ℝ := (571612199 / 2500000000)
noncomputable def tm12394 : ℝ := (-((2998039217 / 5000000000)))
noncomputable def ep12394 : ℝ := (25261339280702769 / 50000000000000000000)
noncomputable def em12394 : ℝ := (49322114890460689 / 100000000000000000000)
noncomputable def bp12394 : ℝ := (22857982681418042469 / 50000000000000000000)
noncomputable def bm12394 : ℝ := (465742270737944713 / 1000000000000000000)

theorem positive12394 :
    Eplus aL (agent12394.root+dsL) scalar12394.worldRadius world12394.frame
      agent12394.frame tp12394 ≤ -ep12394 := by
  apply positive_check (eT := (115492950634607594691 / 100000000000000000000)) (y := (9406061522372861803 / 25000000000000000000)) (u := (145680030806028273767 / 100000000000000000000))
  · norm_num [world12394, agent12394, scalar12394, tp12394, tm12394, ep12394, em12394, dsL]
  · norm_num [world12394, agent12394, scalar12394, tp12394, tm12394, ep12394, em12394, dsL]
  · norm_num [world12394, agent12394, scalar12394, tp12394, tm12394, ep12394, em12394, dsL]
  · norm_num [world12394, agent12394, scalar12394, tp12394, tm12394, ep12394, em12394, dsL]
  · norm_num [world12394, agent12394, scalar12394, tp12394, tm12394, ep12394, em12394, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12394, agent12394, tp12394, tm12394, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12394, agent12394, scalar12394, tp12394, tm12394, ep12394, em12394, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12394, agent12394, tp12394, tm12394, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12394, agent12394, scalar12394, tp12394, tm12394, ep12394, em12394, dsL]

theorem negative12394 :
    Eminus aL (agent12394.root+dsL) scalar12394.worldRadius world12394.frame
      agent12394.frame tm12394 ≤ -em12394 := by
  apply negative_check (lo := (34270616688223846989 / 50000000000000000000)) (hi := (68541233376447693979 / 100000000000000000000))
    (y := (-((17926510248440478401 / 25000000000000000000)))) (u := (24409260658797894881 / 50000000000000000000))
  · norm_num [world12394, agent12394, scalar12394, tp12394, tm12394, ep12394, em12394, dsL]
  · norm_num [world12394, agent12394, scalar12394, tp12394, tm12394, ep12394, em12394, dsL]
  · norm_num [world12394, agent12394, scalar12394, tp12394, tm12394, ep12394, em12394, dsL]
  · norm_num [world12394, agent12394, scalar12394, tp12394, tm12394, ep12394, em12394, dsL]
  · norm_num [world12394, agent12394, scalar12394, tp12394, tm12394, ep12394, em12394, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12394, agent12394, tp12394, tm12394, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12394, agent12394, tp12394, tm12394, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12394, agent12394, scalar12394, tp12394, tm12394, ep12394, em12394, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12394, agent12394, tp12394, tm12394, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12394, agent12394, scalar12394, tp12394, tm12394, ep12394, em12394, dsL]

theorem tails12394 :
    exp (-((12394:ℝ)*ep12394)) ≤ scalar12394.upperTail ∧
    exp (-((12394:ℝ)*em12394)) ≤ scalar12394.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12394:ℝ)) (by norm_num [ep12394]) ?_)
      (show bp12394^8 ≤ scalar12394.upperTail by norm_num [bp12394, scalar12394])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12394, bp12394, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12394:ℝ)) (by norm_num [em12394]) ?_)
      (show bm12394^8 ≤ scalar12394.lowerTail by norm_num [bm12394, scalar12394])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12394, bm12394, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12394 :
    agent12394.root+dsL+scalar12394.worldRadius < √(1/100/aL) ∧
    2*(agent12394.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12394, agent12394, scalar12394, tp12394, tm12394, ep12394, em12394, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12394, agent12394, scalar12394, tp12394, tm12394, ep12394, em12394, dsL]

noncomputable def master12394 : MasterCertificate 12394 world12394 agent12394 :=
  master scalar12394 dsL tp12394 tm12394 ep12394 em12394
    (by norm_num [dsL]) (by norm_num [tp12394]) (by norm_num [tm12394])
    (by norm_num [ep12394]) (by norm_num [em12394])
    positive12394 negative12394 tails12394.1 tails12394.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12394.1 tailGuards12394.2

theorem preserves12394 : master12394.toScalarCertificate = scalar12394 := rfl

noncomputable def tp12395 : ℝ := (571636239 / 2500000000)
noncomputable def tm12395 : ℝ := (-((5996286883 / 10000000000)))
noncomputable def ep12395 : ℝ := (6315708961243609 / 12500000000000000000)
noncomputable def em12395 : ℝ := (12331176293750773 / 25000000000000000000)
noncomputable def bp12395 : ℝ := (22855479226339654309 / 50000000000000000000)
noncomputable def bm12395 : ℝ := (46569486717071824763 / 100000000000000000000)

theorem positive12395 :
    Eplus aL (agent12395.root+dsL) scalar12395.worldRadius world12395.frame
      agent12395.frame tp12395 ≤ -ep12395 := by
  apply positive_check (eT := (115493266047153918539 / 100000000000000000000)) (y := (4703144146538218251 / 12500000000000000000)) (u := (36420338062636217359 / 25000000000000000000))
  · norm_num [world12395, agent12395, scalar12395, tp12395, tm12395, ep12395, em12395, dsL]
  · norm_num [world12395, agent12395, scalar12395, tp12395, tm12395, ep12395, em12395, dsL]
  · norm_num [world12395, agent12395, scalar12395, tp12395, tm12395, ep12395, em12395, dsL]
  · norm_num [world12395, agent12395, scalar12395, tp12395, tm12395, ep12395, em12395, dsL]
  · norm_num [world12395, agent12395, scalar12395, tp12395, tm12395, ep12395, em12395, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12395, agent12395, tp12395, tm12395, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12395, agent12395, scalar12395, tp12395, tm12395, ep12395, em12395, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12395, agent12395, tp12395, tm12395, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12395, agent12395, scalar12395, tp12395, tm12395, ep12395, em12395, dsL]

theorem negative12395 :
    Eminus aL (agent12395.root+dsL) scalar12395.worldRadius world12395.frame
      agent12395.frame tm12395 ≤ -em12395 := by
  apply negative_check (lo := (68540931286389046921 / 100000000000000000000)) (hi := (34270465643194523461 / 50000000000000000000))
    (y := (-((35853119811578076913 / 50000000000000000000)))) (u := (48818424349758922933 / 100000000000000000000))
  · norm_num [world12395, agent12395, scalar12395, tp12395, tm12395, ep12395, em12395, dsL]
  · norm_num [world12395, agent12395, scalar12395, tp12395, tm12395, ep12395, em12395, dsL]
  · norm_num [world12395, agent12395, scalar12395, tp12395, tm12395, ep12395, em12395, dsL]
  · norm_num [world12395, agent12395, scalar12395, tp12395, tm12395, ep12395, em12395, dsL]
  · norm_num [world12395, agent12395, scalar12395, tp12395, tm12395, ep12395, em12395, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12395, agent12395, tp12395, tm12395, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12395, agent12395, tp12395, tm12395, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12395, agent12395, scalar12395, tp12395, tm12395, ep12395, em12395, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12395, agent12395, tp12395, tm12395, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12395, agent12395, scalar12395, tp12395, tm12395, ep12395, em12395, dsL]

theorem tails12395 :
    exp (-((12395:ℝ)*ep12395)) ≤ scalar12395.upperTail ∧
    exp (-((12395:ℝ)*em12395)) ≤ scalar12395.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12395:ℝ)) (by norm_num [ep12395]) ?_)
      (show bp12395^8 ≤ scalar12395.upperTail by norm_num [bp12395, scalar12395])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12395, bp12395, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12395:ℝ)) (by norm_num [em12395]) ?_)
      (show bm12395^8 ≤ scalar12395.lowerTail by norm_num [bm12395, scalar12395])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12395, bm12395, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12395 :
    agent12395.root+dsL+scalar12395.worldRadius < √(1/100/aL) ∧
    2*(agent12395.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12395, agent12395, scalar12395, tp12395, tm12395, ep12395, em12395, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12395, agent12395, scalar12395, tp12395, tm12395, ep12395, em12395, dsL]

noncomputable def master12395 : MasterCertificate 12395 world12395 agent12395 :=
  master scalar12395 dsL tp12395 tm12395 ep12395 em12395
    (by norm_num [dsL]) (by norm_num [tp12395]) (by norm_num [tm12395])
    (by norm_num [ep12395]) (by norm_num [em12395])
    positive12395 negative12395 tails12395.1 tails12395.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12395.1 tailGuards12395.2

theorem preserves12395 : master12395.toScalarCertificate = scalar12395 := rfl

noncomputable def tp12396 : ℝ := (2286641077 / 10000000000)
noncomputable def tm12396 : ℝ := (-((2998247609 / 5000000000)))
noncomputable def ep12396 : ℝ := (2021146548927333 / 4000000000000000000)
noncomputable def em12396 : ℝ := (12331823608296883 / 25000000000000000000)
noncomputable def bp12396 : ℝ := (45705952524593338429 / 100000000000000000000)
noncomputable def bm12396 : ℝ := (23282373640912321563 / 50000000000000000000)

theorem positive12396 :
    Eplus aL (agent12396.root+dsL) scalar12396.worldRadius world12396.frame
      agent12396.frame tp12396 ≤ -ep12396 := by
  apply positive_check (eT := (28873395301997968499 / 25000000000000000000)) (y := (37626060052882341853 / 100000000000000000000)) (u := (5827306936496912919 / 4000000000000000000))
  · norm_num [world12396, agent12396, scalar12396, tp12396, tm12396, ep12396, em12396, dsL]
  · norm_num [world12396, agent12396, scalar12396, tp12396, tm12396, ep12396, em12396, dsL]
  · norm_num [world12396, agent12396, scalar12396, tp12396, tm12396, ep12396, em12396, dsL]
  · norm_num [world12396, agent12396, scalar12396, tp12396, tm12396, ep12396, em12396, dsL]
  · norm_num [world12396, agent12396, scalar12396, tp12396, tm12396, ep12396, em12396, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12396, agent12396, tp12396, tm12396, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12396, agent12396, scalar12396, tp12396, tm12396, ep12396, em12396, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12396, agent12396, tp12396, tm12396, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12396, agent12396, scalar12396, tp12396, tm12396, ep12396, em12396, dsL]

theorem negative12396 :
    Eminus aL (agent12396.root+dsL) scalar12396.worldRadius world12396.frame
      agent12396.frame tm12396 ≤ -em12396 := by
  apply negative_check (lo := (34270314816321439021 / 50000000000000000000)) (hi := (68540629632642878043 / 100000000000000000000))
    (y := (-((2240826194960446993 / 3125000000000000000)))) (u := (48818327388859446721 / 100000000000000000000))
  · norm_num [world12396, agent12396, scalar12396, tp12396, tm12396, ep12396, em12396, dsL]
  · norm_num [world12396, agent12396, scalar12396, tp12396, tm12396, ep12396, em12396, dsL]
  · norm_num [world12396, agent12396, scalar12396, tp12396, tm12396, ep12396, em12396, dsL]
  · norm_num [world12396, agent12396, scalar12396, tp12396, tm12396, ep12396, em12396, dsL]
  · norm_num [world12396, agent12396, scalar12396, tp12396, tm12396, ep12396, em12396, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12396, agent12396, tp12396, tm12396, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12396, agent12396, tp12396, tm12396, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12396, agent12396, scalar12396, tp12396, tm12396, ep12396, em12396, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12396, agent12396, tp12396, tm12396, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12396, agent12396, scalar12396, tp12396, tm12396, ep12396, em12396, dsL]

theorem tails12396 :
    exp (-((12396:ℝ)*ep12396)) ≤ scalar12396.upperTail ∧
    exp (-((12396:ℝ)*em12396)) ≤ scalar12396.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12396:ℝ)) (by norm_num [ep12396]) ?_)
      (show bp12396^8 ≤ scalar12396.upperTail by norm_num [bp12396, scalar12396])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12396, bp12396, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12396:ℝ)) (by norm_num [em12396]) ?_)
      (show bm12396^8 ≤ scalar12396.lowerTail by norm_num [bm12396, scalar12396])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12396, bm12396, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12396 :
    agent12396.root+dsL+scalar12396.worldRadius < √(1/100/aL) ∧
    2*(agent12396.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12396, agent12396, scalar12396, tp12396, tm12396, ep12396, em12396, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12396, agent12396, scalar12396, tp12396, tm12396, ep12396, em12396, dsL]

noncomputable def master12396 : MasterCertificate 12396 world12396 agent12396 :=
  master scalar12396 dsL tp12396 tm12396 ep12396 em12396
    (by norm_num [dsL]) (by norm_num [tp12396]) (by norm_num [tm12396])
    (by norm_num [ep12396]) (by norm_num [em12396])
    positive12396 negative12396 tails12396.1 tails12396.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12396.1 tailGuards12396.2

theorem preserves12396 : master12396.toScalarCertificate = scalar12396 := rfl

noncomputable def tp12397 : ℝ := (571684283 / 2500000000)
noncomputable def tm12397 : ℝ := (-((1499175839 / 2500000000)))
noncomputable def ep12397 : ℝ := (50531653414062557 / 100000000000000000000)
noncomputable def em12397 : ℝ := (24664940764241509 / 50000000000000000000)
noncomputable def bp12397 : ℝ := (11425237115428305719 / 25000000000000000000)
noncomputable def bm12397 : ℝ := (727500149813474973 / 1562500000000000000)

theorem positive12397 :
    Eplus aL (agent12397.root+dsL) scalar12397.worldRadius world12397.frame
      agent12397.frame tp12397 ≤ -ep12397 := by
  apply positive_check (eT := (115493895920715050441 / 100000000000000000000)) (y := (18813483124166125207 / 50000000000000000000)) (u := (72841996794081134353 / 50000000000000000000))
  · norm_num [world12397, agent12397, scalar12397, tp12397, tm12397, ep12397, em12397, dsL]
  · norm_num [world12397, agent12397, scalar12397, tp12397, tm12397, ep12397, em12397, dsL]
  · norm_num [world12397, agent12397, scalar12397, tp12397, tm12397, ep12397, em12397, dsL]
  · norm_num [world12397, agent12397, scalar12397, tp12397, tm12397, ep12397, em12397, dsL]
  · norm_num [world12397, agent12397, scalar12397, tp12397, tm12397, ep12397, em12397, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12397, agent12397, tp12397, tm12397, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12397, agent12397, scalar12397, tp12397, tm12397, ep12397, em12397, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12397, agent12397, tp12397, tm12397, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12397, agent12397, scalar12397, tp12397, tm12397, ep12397, em12397, dsL]

theorem negative12397 :
    Eminus aL (agent12397.root+dsL) scalar12397.worldRadius world12397.frame
      agent12397.frame tm12397 ≤ -em12397 := by
  apply negative_check (lo := (68540328773514261711 / 100000000000000000000)) (hi := (4283770548344641357 / 6250000000000000000))
    (y := (-((71706635349458788791 / 100000000000000000000)))) (u := (48818231162795485051 / 100000000000000000000))
  · norm_num [world12397, agent12397, scalar12397, tp12397, tm12397, ep12397, em12397, dsL]
  · norm_num [world12397, agent12397, scalar12397, tp12397, tm12397, ep12397, em12397, dsL]
  · norm_num [world12397, agent12397, scalar12397, tp12397, tm12397, ep12397, em12397, dsL]
  · norm_num [world12397, agent12397, scalar12397, tp12397, tm12397, ep12397, em12397, dsL]
  · norm_num [world12397, agent12397, scalar12397, tp12397, tm12397, ep12397, em12397, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12397, agent12397, tp12397, tm12397, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12397, agent12397, tp12397, tm12397, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12397, agent12397, scalar12397, tp12397, tm12397, ep12397, em12397, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12397, agent12397, tp12397, tm12397, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12397, agent12397, scalar12397, tp12397, tm12397, ep12397, em12397, dsL]

theorem tails12397 :
    exp (-((12397:ℝ)*ep12397)) ≤ scalar12397.upperTail ∧
    exp (-((12397:ℝ)*em12397)) ≤ scalar12397.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12397:ℝ)) (by norm_num [ep12397]) ?_)
      (show bp12397^8 ≤ scalar12397.upperTail by norm_num [bp12397, scalar12397])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12397, bp12397, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12397:ℝ)) (by norm_num [em12397]) ?_)
      (show bm12397^8 ≤ scalar12397.lowerTail by norm_num [bm12397, scalar12397])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12397, bm12397, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12397 :
    agent12397.root+dsL+scalar12397.worldRadius < √(1/100/aL) ∧
    2*(agent12397.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12397, agent12397, scalar12397, tp12397, tm12397, ep12397, em12397, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12397, agent12397, scalar12397, tp12397, tm12397, ep12397, em12397, dsL]

noncomputable def master12397 : MasterCertificate 12397 world12397 agent12397 :=
  master scalar12397 dsL tp12397 tm12397 ep12397 em12397
    (by norm_num [dsL]) (by norm_num [tp12397]) (by norm_num [tm12397])
    (by norm_num [ep12397]) (by norm_num [em12397])
    positive12397 negative12397 tails12397.1 tails12397.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12397.1 tailGuards12397.2

theorem preserves12397 : master12397.toScalarCertificate = scalar12397 := rfl

noncomputable def tp12398 : ℝ := (1143416577 / 5000000000)
noncomputable def tm12398 : ℝ := (-((1199382301 / 2000000000)))
noncomputable def ep12398 : ℝ := (50534642339837619 / 100000000000000000000)
noncomputable def em12398 : ℝ := (24666233942737527 / 50000000000000000000)
noncomputable def bp12398 : ℝ := (9139189029396252543 / 20000000000000000000)
noncomputable def bm12398 : ℝ := (23277636303952292189 / 50000000000000000000)

theorem positive12398 :
    Eplus aL (agent12398.root+dsL) scalar12398.worldRadius world12398.frame
      agent12398.frame tp12398 ≤ -ep12398 := by
  apply positive_check (eT := (7218388151586680929 / 6250000000000000000)) (y := (37627872449838580301 / 100000000000000000000)) (u := (145685313784688457537 / 100000000000000000000))
  · norm_num [world12398, agent12398, scalar12398, tp12398, tm12398, ep12398, em12398, dsL]
  · norm_num [world12398, agent12398, scalar12398, tp12398, tm12398, ep12398, em12398, dsL]
  · norm_num [world12398, agent12398, scalar12398, tp12398, tm12398, ep12398, em12398, dsL]
  · norm_num [world12398, agent12398, scalar12398, tp12398, tm12398, ep12398, em12398, dsL]
  · norm_num [world12398, agent12398, scalar12398, tp12398, tm12398, ep12398, em12398, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12398, agent12398, tp12398, tm12398, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12398, agent12398, scalar12398, tp12398, tm12398, ep12398, em12398, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12398, agent12398, tp12398, tm12398, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12398, agent12398, scalar12398, tp12398, tm12398, ep12398, em12398, dsL]

theorem negative12398 :
    Eminus aL (agent12398.root+dsL) scalar12398.worldRadius world12398.frame
      agent12398.frame tm12398 ≤ -em12398 := by
  apply negative_check (lo := (34270013905491797601 / 50000000000000000000)) (hi := (68540027810983595203 / 100000000000000000000))
    (y := (-((71706834092475619393 / 100000000000000000000)))) (u := (9763626828013304351 / 20000000000000000000))
  · norm_num [world12398, agent12398, scalar12398, tp12398, tm12398, ep12398, em12398, dsL]
  · norm_num [world12398, agent12398, scalar12398, tp12398, tm12398, ep12398, em12398, dsL]
  · norm_num [world12398, agent12398, scalar12398, tp12398, tm12398, ep12398, em12398, dsL]
  · norm_num [world12398, agent12398, scalar12398, tp12398, tm12398, ep12398, em12398, dsL]
  · norm_num [world12398, agent12398, scalar12398, tp12398, tm12398, ep12398, em12398, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12398, agent12398, tp12398, tm12398, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12398, agent12398, tp12398, tm12398, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12398, agent12398, scalar12398, tp12398, tm12398, ep12398, em12398, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12398, agent12398, tp12398, tm12398, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12398, agent12398, scalar12398, tp12398, tm12398, ep12398, em12398, dsL]

theorem tails12398 :
    exp (-((12398:ℝ)*ep12398)) ≤ scalar12398.upperTail ∧
    exp (-((12398:ℝ)*em12398)) ≤ scalar12398.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12398:ℝ)) (by norm_num [ep12398]) ?_)
      (show bp12398^8 ≤ scalar12398.upperTail by norm_num [bp12398, scalar12398])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12398, bp12398, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12398:ℝ)) (by norm_num [em12398]) ?_)
      (show bm12398^8 ≤ scalar12398.lowerTail by norm_num [bm12398, scalar12398])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12398, bm12398, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12398 :
    agent12398.root+dsL+scalar12398.worldRadius < √(1/100/aL) ∧
    2*(agent12398.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12398, agent12398, scalar12398, tp12398, tm12398, ep12398, em12398, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12398, agent12398, scalar12398, tp12398, tm12398, ep12398, em12398, dsL]

noncomputable def master12398 : MasterCertificate 12398 world12398 agent12398 :=
  master scalar12398 dsL tp12398 tm12398 ep12398 em12398
    (by norm_num [dsL]) (by norm_num [tp12398]) (by norm_num [tm12398])
    (by norm_num [ep12398]) (by norm_num [em12398])
    positive12398 negative12398 tails12398.1 tails12398.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12398.1 tailGuards12398.2

theorem preserves12398 : master12398.toScalarCertificate = scalar12398 := rfl

noncomputable def tp12399 : ℝ := (142933069 / 625000000)
noncomputable def tm12399 : ℝ := (-((374819969 / 625000000)))
noncomputable def ep12399 : ℝ := (1579300903852223 / 3125000000000000000)
noncomputable def em12399 : ℝ := (49335052079701381 / 100000000000000000000)
noncomputable def bp12399 : ℝ := (45690943697327386479 / 100000000000000000000)
noncomputable def bm12399 : ℝ := (23275268684537228561 / 50000000000000000000)

theorem positive12399 :
    Eplus aL (agent12399.root+dsL) scalar12399.worldRadius world12399.frame
      agent12399.frame tp12399 ≤ -ep12399 := by
  apply positive_check (eT := (115494524438359578957 / 100000000000000000000)) (y := (37628777859789007253 / 100000000000000000000)) (u := (145686632839987194787 / 100000000000000000000))
  · norm_num [world12399, agent12399, scalar12399, tp12399, tm12399, ep12399, em12399, dsL]
  · norm_num [world12399, agent12399, scalar12399, tp12399, tm12399, ep12399, em12399, dsL]
  · norm_num [world12399, agent12399, scalar12399, tp12399, tm12399, ep12399, em12399, dsL]
  · norm_num [world12399, agent12399, scalar12399, tp12399, tm12399, ep12399, em12399, dsL]
  · norm_num [world12399, agent12399, scalar12399, tp12399, tm12399, ep12399, em12399, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12399, agent12399, tp12399, tm12399, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12399, agent12399, scalar12399, tp12399, tm12399, ep12399, em12399, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12399, agent12399, tp12399, tm12399, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12399, agent12399, scalar12399, tp12399, tm12399, ep12399, em12399, dsL]

theorem negative12399 :
    Eminus aL (agent12399.root+dsL) scalar12399.worldRadius world12399.frame
      agent12399.frame tm12399 ≤ -em12399 := by
  apply negative_check (lo := (34269863720023819389 / 50000000000000000000)) (hi := (68539727440047638779 / 100000000000000000000))
    (y := (-((71707031792248729663 / 100000000000000000000)))) (u := (48818037626821493441 / 100000000000000000000))
  · norm_num [world12399, agent12399, scalar12399, tp12399, tm12399, ep12399, em12399, dsL]
  · norm_num [world12399, agent12399, scalar12399, tp12399, tm12399, ep12399, em12399, dsL]
  · norm_num [world12399, agent12399, scalar12399, tp12399, tm12399, ep12399, em12399, dsL]
  · norm_num [world12399, agent12399, scalar12399, tp12399, tm12399, ep12399, em12399, dsL]
  · norm_num [world12399, agent12399, scalar12399, tp12399, tm12399, ep12399, em12399, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12399, agent12399, tp12399, tm12399, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12399, agent12399, tp12399, tm12399, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12399, agent12399, scalar12399, tp12399, tm12399, ep12399, em12399, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12399, agent12399, tp12399, tm12399, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12399, agent12399, scalar12399, tp12399, tm12399, ep12399, em12399, dsL]

theorem tails12399 :
    exp (-((12399:ℝ)*ep12399)) ≤ scalar12399.upperTail ∧
    exp (-((12399:ℝ)*em12399)) ≤ scalar12399.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12399:ℝ)) (by norm_num [ep12399]) ?_)
      (show bp12399^8 ≤ scalar12399.upperTail by norm_num [bp12399, scalar12399])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12399, bp12399, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12399:ℝ)) (by norm_num [em12399]) ?_)
      (show bm12399^8 ≤ scalar12399.lowerTail by norm_num [bm12399, scalar12399])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12399, bm12399, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12399 :
    agent12399.root+dsL+scalar12399.worldRadius < √(1/100/aL) ∧
    2*(agent12399.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12399, agent12399, scalar12399, tp12399, tm12399, ep12399, em12399, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12399, agent12399, scalar12399, tp12399, tm12399, ep12399, em12399, dsL]

noncomputable def master12399 : MasterCertificate 12399 world12399 agent12399 :=
  master scalar12399 dsL tp12399 tm12399 ep12399 em12399
    (by norm_num [dsL]) (by norm_num [tp12399]) (by norm_num [tm12399])
    (by norm_num [ep12399]) (by norm_num [em12399])
    positive12399 negative12399 tails12399.1 tails12399.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12399.1 tailGuards12399.2

theorem preserves12399 : master12399.toScalarCertificate = scalar12399 := rfl

end BstLean.Part268
