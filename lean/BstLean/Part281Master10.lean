import BstLean.Part261Checker
import BstLean.Part281Scalar10
namespace BstLean.Part281
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12109 : ℝ := (592233953 / 2500000000)
noncomputable def tm12109 : ℝ := (-((1226014009 / 2000000000)))
noncomputable def ep12109 : ℝ := (54479517622390541 / 100000000000000000000)
noncomputable def em12109 : ℝ := (52538217050163931 / 100000000000000000000)
noncomputable def bp12109 : ℝ := (5480043537328541083 / 12500000000000000000)
noncomputable def bm12109 : ℝ := (5643458328940196131 / 12500000000000000000)

theorem positive12109 :
    Eplus aL (agent12109.root+dsL) scalar12109.worldRadius world12109.frame
      agent12109.frame tp12109 ≤ -ep12109 := by
  apply positive_check (eT := (116211526520268892963 / 100000000000000000000)) (y := (39601224430693959533 / 100000000000000000000)) (u := (37147187777569234489 / 25000000000000000000))
  · norm_num [world12109, agent12109, scalar12109, tp12109, tm12109, ep12109, em12109, dsL]
  · norm_num [world12109, agent12109, scalar12109, tp12109, tm12109, ep12109, em12109, dsL]
  · norm_num [world12109, agent12109, scalar12109, tp12109, tm12109, ep12109, em12109, dsL]
  · norm_num [world12109, agent12109, scalar12109, tp12109, tm12109, ep12109, em12109, dsL]
  · norm_num [world12109, agent12109, scalar12109, tp12109, tm12109, ep12109, em12109, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12109, agent12109, tp12109, tm12109, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12109, agent12109, scalar12109, tp12109, tm12109, ep12109, em12109, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12109, agent12109, tp12109, tm12109, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12109, agent12109, scalar12109, tp12109, tm12109, ep12109, em12109, dsL]

theorem negative12109 :
    Eminus aL (agent12109.root+dsL) scalar12109.worldRadius world12109.frame
      agent12109.frame tm12109 ≤ -em12109 := by
  apply negative_check (lo := (33894195247623897947 / 50000000000000000000)) (hi := (13557678099049559179 / 20000000000000000000))
    (y := (-((14663915048922059717 / 20000000000000000000)))) (u := (9607427729304055889 / 20000000000000000000))
  · norm_num [world12109, agent12109, scalar12109, tp12109, tm12109, ep12109, em12109, dsL]
  · norm_num [world12109, agent12109, scalar12109, tp12109, tm12109, ep12109, em12109, dsL]
  · norm_num [world12109, agent12109, scalar12109, tp12109, tm12109, ep12109, em12109, dsL]
  · norm_num [world12109, agent12109, scalar12109, tp12109, tm12109, ep12109, em12109, dsL]
  · norm_num [world12109, agent12109, scalar12109, tp12109, tm12109, ep12109, em12109, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12109, agent12109, tp12109, tm12109, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12109, agent12109, tp12109, tm12109, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12109, agent12109, scalar12109, tp12109, tm12109, ep12109, em12109, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12109, agent12109, tp12109, tm12109, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12109, agent12109, scalar12109, tp12109, tm12109, ep12109, em12109, dsL]

theorem tails12109 :
    exp (-((12109:ℝ)*ep12109)) ≤ scalar12109.upperTail ∧
    exp (-((12109:ℝ)*em12109)) ≤ scalar12109.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12109:ℝ)) (by norm_num [ep12109]) ?_)
      (show bp12109^8 ≤ scalar12109.upperTail by norm_num [bp12109, scalar12109])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12109, bp12109, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12109:ℝ)) (by norm_num [em12109]) ?_)
      (show bm12109^8 ≤ scalar12109.lowerTail by norm_num [bm12109, scalar12109])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12109, bm12109, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12109 :
    agent12109.root+dsL+scalar12109.worldRadius < √(1/100/aL) ∧
    2*(agent12109.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12109, agent12109, scalar12109, tp12109, tm12109, ep12109, em12109, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12109, agent12109, scalar12109, tp12109, tm12109, ep12109, em12109, dsL]

noncomputable def master12109 : MasterCertificate 12109 world12109 agent12109 :=
  master scalar12109 dsL tp12109 tm12109 ep12109 em12109
    (by norm_num [dsL]) (by norm_num [tp12109]) (by norm_num [tm12109])
    (by norm_num [ep12109]) (by norm_num [em12109])
    positive12109 negative12109 tails12109.1 tails12109.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12109.1 tailGuards12109.2

theorem preserves12109 : master12109.toScalarCertificate = scalar12109 := rfl

noncomputable def tp12110 : ℝ := (592259037 / 2500000000)
noncomputable def tm12110 : ℝ := (-((6130295259 / 10000000000)))
noncomputable def ep12110 : ℝ := (54482466149439433 / 100000000000000000000)
noncomputable def em12110 : ℝ := (6567597849218389 / 12500000000000000000)
noncomputable def bp12110 : ℝ := (43835406335255299327 / 100000000000000000000)
noncomputable def bm12110 : ℝ := (22571474209010568103 / 50000000000000000000)

theorem positive12110 :
    Eplus aL (agent12110.root+dsL) scalar12110.worldRadius world12110.frame
      agent12110.frame tp12110 ≤ -ep12110 := by
  apply positive_check (eT := (116211845870907297281 / 100000000000000000000)) (y := (39601866267496025821 / 100000000000000000000)) (u := (14858970481062589103 / 10000000000000000000))
  · norm_num [world12110, agent12110, scalar12110, tp12110, tm12110, ep12110, em12110, dsL]
  · norm_num [world12110, agent12110, scalar12110, tp12110, tm12110, ep12110, em12110, dsL]
  · norm_num [world12110, agent12110, scalar12110, tp12110, tm12110, ep12110, em12110, dsL]
  · norm_num [world12110, agent12110, scalar12110, tp12110, tm12110, ep12110, em12110, dsL]
  · norm_num [world12110, agent12110, scalar12110, tp12110, tm12110, ep12110, em12110, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12110, agent12110, tp12110, tm12110, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12110, agent12110, scalar12110, tp12110, tm12110, ep12110, em12110, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12110, agent12110, tp12110, tm12110, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12110, agent12110, scalar12110, tp12110, tm12110, ep12110, em12110, dsL]

theorem negative12110 :
    Eminus aL (agent12110.root+dsL) scalar12110.worldRadius world12110.frame
      agent12110.frame tm12110 ≤ -em12110 := by
  apply negative_check (lo := (33894028224534065347 / 50000000000000000000)) (hi := (13557611289813626139 / 20000000000000000000))
    (y := (-((73319187142815996573 / 100000000000000000000)))) (u := (48037325079879073307 / 100000000000000000000))
  · norm_num [world12110, agent12110, scalar12110, tp12110, tm12110, ep12110, em12110, dsL]
  · norm_num [world12110, agent12110, scalar12110, tp12110, tm12110, ep12110, em12110, dsL]
  · norm_num [world12110, agent12110, scalar12110, tp12110, tm12110, ep12110, em12110, dsL]
  · norm_num [world12110, agent12110, scalar12110, tp12110, tm12110, ep12110, em12110, dsL]
  · norm_num [world12110, agent12110, scalar12110, tp12110, tm12110, ep12110, em12110, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12110, agent12110, tp12110, tm12110, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12110, agent12110, tp12110, tm12110, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12110, agent12110, scalar12110, tp12110, tm12110, ep12110, em12110, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12110, agent12110, tp12110, tm12110, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12110, agent12110, scalar12110, tp12110, tm12110, ep12110, em12110, dsL]

theorem tails12110 :
    exp (-((12110:ℝ)*ep12110)) ≤ scalar12110.upperTail ∧
    exp (-((12110:ℝ)*em12110)) ≤ scalar12110.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12110:ℝ)) (by norm_num [ep12110]) ?_)
      (show bp12110^8 ≤ scalar12110.upperTail by norm_num [bp12110, scalar12110])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12110, bp12110, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12110:ℝ)) (by norm_num [em12110]) ?_)
      (show bm12110^8 ≤ scalar12110.lowerTail by norm_num [bm12110, scalar12110])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12110, bm12110, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12110 :
    agent12110.root+dsL+scalar12110.worldRadius < √(1/100/aL) ∧
    2*(agent12110.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12110, agent12110, scalar12110, tp12110, tm12110, ep12110, em12110, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12110, agent12110, scalar12110, tp12110, tm12110, ep12110, em12110, dsL]

noncomputable def master12110 : MasterCertificate 12110 world12110 agent12110 :=
  master scalar12110 dsL tp12110 tm12110 ep12110 em12110
    (by norm_num [dsL]) (by norm_num [tp12110]) (by norm_num [tm12110])
    (by norm_num [ep12110]) (by norm_num [em12110])
    positive12110 negative12110 tails12110.1 tails12110.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12110.1 tailGuards12110.2

theorem preserves12110 : master12110.toScalarCertificate = scalar12110 := rfl

noncomputable def tp12111 : ℝ := (1184568219 / 5000000000)
noncomputable def tm12111 : ℝ := (-((6130520643 / 10000000000)))
noncomputable def ep12111 : ℝ := (13621353335735011 / 25000000000000000000)
noncomputable def em12111 : ℝ := (52543347264909491 / 100000000000000000000)
noncomputable def bp12111 : ℝ := (10957616372686038257 / 25000000000000000000)
noncomputable def bm12111 : ℝ := (45138231277562146857 / 100000000000000000000)

theorem positive12111 :
    Eplus aL (agent12111.root+dsL) scalar12111.worldRadius world12111.frame
      agent12111.frame tp12111 ≤ -ep12111 := by
  apply positive_check (eT := (116212164919203487191 / 100000000000000000000)) (y := (39602508071628222461 / 100000000000000000000)) (u := (148590658468551689131 / 100000000000000000000))
  · norm_num [world12111, agent12111, scalar12111, tp12111, tm12111, ep12111, em12111, dsL]
  · norm_num [world12111, agent12111, scalar12111, tp12111, tm12111, ep12111, em12111, dsL]
  · norm_num [world12111, agent12111, scalar12111, tp12111, tm12111, ep12111, em12111, dsL]
  · norm_num [world12111, agent12111, scalar12111, tp12111, tm12111, ep12111, em12111, dsL]
  · norm_num [world12111, agent12111, scalar12111, tp12111, tm12111, ep12111, em12111, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12111, agent12111, tp12111, tm12111, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12111, agent12111, scalar12111, tp12111, tm12111, ep12111, em12111, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12111, agent12111, tp12111, tm12111, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12111, agent12111, scalar12111, tp12111, tm12111, ep12111, em12111, dsL]

theorem negative12111 :
    Eminus aL (agent12111.root+dsL) scalar12111.worldRadius world12111.frame
      agent12111.frame tm12111 ≤ -em12111 := by
  apply negative_check (lo := (67787721612543900223 / 100000000000000000000)) (hi := (1059183150195998441 / 1562500000000000000))
    (y := (-((73318802373375616103 / 100000000000000000000)))) (u := (48037509913181547709 / 100000000000000000000))
  · norm_num [world12111, agent12111, scalar12111, tp12111, tm12111, ep12111, em12111, dsL]
  · norm_num [world12111, agent12111, scalar12111, tp12111, tm12111, ep12111, em12111, dsL]
  · norm_num [world12111, agent12111, scalar12111, tp12111, tm12111, ep12111, em12111, dsL]
  · norm_num [world12111, agent12111, scalar12111, tp12111, tm12111, ep12111, em12111, dsL]
  · norm_num [world12111, agent12111, scalar12111, tp12111, tm12111, ep12111, em12111, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12111, agent12111, tp12111, tm12111, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12111, agent12111, tp12111, tm12111, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12111, agent12111, scalar12111, tp12111, tm12111, ep12111, em12111, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12111, agent12111, tp12111, tm12111, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12111, agent12111, scalar12111, tp12111, tm12111, ep12111, em12111, dsL]

theorem tails12111 :
    exp (-((12111:ℝ)*ep12111)) ≤ scalar12111.upperTail ∧
    exp (-((12111:ℝ)*em12111)) ≤ scalar12111.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12111:ℝ)) (by norm_num [ep12111]) ?_)
      (show bp12111^8 ≤ scalar12111.upperTail by norm_num [bp12111, scalar12111])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12111, bp12111, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12111:ℝ)) (by norm_num [em12111]) ?_)
      (show bm12111^8 ≤ scalar12111.lowerTail by norm_num [bm12111, scalar12111])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12111, bm12111, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12111 :
    agent12111.root+dsL+scalar12111.worldRadius < √(1/100/aL) ∧
    2*(agent12111.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12111, agent12111, scalar12111, tp12111, tm12111, ep12111, em12111, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12111, agent12111, scalar12111, tp12111, tm12111, ep12111, em12111, dsL]

noncomputable def master12111 : MasterCertificate 12111 world12111 agent12111 :=
  master scalar12111 dsL tp12111 tm12111 ep12111 em12111
    (by norm_num [dsL]) (by norm_num [tp12111]) (by norm_num [tm12111])
    (by norm_num [ep12111]) (by norm_num [em12111])
    positive12111 negative12111 tails12111.1 tails12111.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12111.1 tailGuards12111.2

theorem preserves12111 : master12111.toScalarCertificate = scalar12111 := rfl

noncomputable def tp12112 : ℝ := (236923669 / 1000000000)
noncomputable def tm12112 : ℝ := (-((1532686423 / 2500000000)))
noncomputable def ep12112 : ℝ := (27244179267570979 / 50000000000000000000)
noncomputable def em12112 : ℝ := (10509181977069559 / 20000000000000000000)
noncomputable def bp12112 : ℝ := (21912763104063012981 / 50000000000000000000)
noncomputable def bm12112 : ℝ := (11283378901323409721 / 25000000000000000000)

theorem positive12112 :
    Eplus aL (agent12112.root+dsL) scalar12112.worldRadius world12112.frame
      agent12112.frame tp12112 ≤ -ep12112 := by
  apply positive_check (eT := (116212483724202428159 / 100000000000000000000)) (y := (9900787442641139577 / 25000000000000000000)) (u := (3714790299407147437 / 2500000000000000000))
  · norm_num [world12112, agent12112, scalar12112, tp12112, tm12112, ep12112, em12112, dsL]
  · norm_num [world12112, agent12112, scalar12112, tp12112, tm12112, ep12112, em12112, dsL]
  · norm_num [world12112, agent12112, scalar12112, tp12112, tm12112, ep12112, em12112, dsL]
  · norm_num [world12112, agent12112, scalar12112, tp12112, tm12112, ep12112, em12112, dsL]
  · norm_num [world12112, agent12112, scalar12112, tp12112, tm12112, ep12112, em12112, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12112, agent12112, tp12112, tm12112, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12112, agent12112, scalar12112, tp12112, tm12112, ep12112, em12112, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12112, agent12112, tp12112, tm12112, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12112, agent12112, scalar12112, tp12112, tm12112, ep12112, em12112, dsL]

theorem negative12112 :
    Eminus aL (agent12112.root+dsL) scalar12112.worldRadius world12112.frame
      agent12112.frame tm12112 ≤ -em12112 := by
  apply negative_check (lo := (8473423519572279429 / 12500000000000000000)) (hi := (67787388156578235433 / 100000000000000000000))
    (y := (-((36659207571830568307 / 50000000000000000000)))) (u := (48037695929054181711 / 100000000000000000000))
  · norm_num [world12112, agent12112, scalar12112, tp12112, tm12112, ep12112, em12112, dsL]
  · norm_num [world12112, agent12112, scalar12112, tp12112, tm12112, ep12112, em12112, dsL]
  · norm_num [world12112, agent12112, scalar12112, tp12112, tm12112, ep12112, em12112, dsL]
  · norm_num [world12112, agent12112, scalar12112, tp12112, tm12112, ep12112, em12112, dsL]
  · norm_num [world12112, agent12112, scalar12112, tp12112, tm12112, ep12112, em12112, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12112, agent12112, tp12112, tm12112, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12112, agent12112, tp12112, tm12112, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12112, agent12112, scalar12112, tp12112, tm12112, ep12112, em12112, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12112, agent12112, tp12112, tm12112, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12112, agent12112, scalar12112, tp12112, tm12112, ep12112, em12112, dsL]

theorem tails12112 :
    exp (-((12112:ℝ)*ep12112)) ≤ scalar12112.upperTail ∧
    exp (-((12112:ℝ)*em12112)) ≤ scalar12112.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12112:ℝ)) (by norm_num [ep12112]) ?_)
      (show bp12112^8 ≤ scalar12112.upperTail by norm_num [bp12112, scalar12112])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12112, bp12112, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12112:ℝ)) (by norm_num [em12112]) ?_)
      (show bm12112^8 ≤ scalar12112.lowerTail by norm_num [bm12112, scalar12112])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12112, bm12112, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12112 :
    agent12112.root+dsL+scalar12112.worldRadius < √(1/100/aL) ∧
    2*(agent12112.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12112, agent12112, scalar12112, tp12112, tm12112, ep12112, em12112, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12112, agent12112, scalar12112, tp12112, tm12112, ep12112, em12112, dsL]

noncomputable def master12112 : MasterCertificate 12112 world12112 agent12112 :=
  master scalar12112 dsL tp12112 tm12112 ep12112 em12112
    (by norm_num [dsL]) (by norm_num [tp12112]) (by norm_num [tm12112])
    (by norm_num [ep12112]) (by norm_num [em12112])
    positive12112 negative12112 tails12112.1 tails12112.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12112.1 tailGuards12112.2

theorem preserves12112 : master12112.toScalarCertificate = scalar12112 := rfl

noncomputable def tp12113 : ℝ := (2369336831 / 10000000000)
noncomputable def tm12113 : ℝ := (-((6130970677 / 10000000000)))
noncomputable def ep12113 : ℝ := (3405706409710127 / 6250000000000000000)
noncomputable def em12113 : ℝ := (13137117849773553 / 25000000000000000000)
noncomputable def bp12113 : ℝ := (43820587937076780821 / 100000000000000000000)
noncomputable def bm12113 : ℝ := (5641100111596205169 / 12500000000000000000)

theorem positive12113 :
    Eplus aL (agent12113.root+dsL) scalar12113.worldRadius world12113.frame
      agent12113.frame tp12113 ≤ -ep12113 := by
  apply positive_check (eT := (29053200436972057503 / 25000000000000000000)) (y := (9900947526516442901 / 25000000000000000000)) (u := (148592563464175560869 / 100000000000000000000))
  · norm_num [world12113, agent12113, scalar12113, tp12113, tm12113, ep12113, em12113, dsL]
  · norm_num [world12113, agent12113, scalar12113, tp12113, tm12113, ep12113, em12113, dsL]
  · norm_num [world12113, agent12113, scalar12113, tp12113, tm12113, ep12113, em12113, dsL]
  · norm_num [world12113, agent12113, scalar12113, tp12113, tm12113, ep12113, em12113, dsL]
  · norm_num [world12113, agent12113, scalar12113, tp12113, tm12113, ep12113, em12113, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12113, agent12113, tp12113, tm12113, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12113, agent12113, scalar12113, tp12113, tm12113, ep12113, em12113, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12113, agent12113, tp12113, tm12113, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12113, agent12113, scalar12113, tp12113, tm12113, ep12113, em12113, dsL]

theorem negative12113 :
    Eminus aL (agent12113.root+dsL) scalar12113.worldRadius world12113.frame
      agent12113.frame tm12113 ≤ -em12113 := by
  apply negative_check (lo := (67787054916155729077 / 100000000000000000000)) (hi := (33893527458077864539 / 50000000000000000000))
    (y := (-((73318028659086464887 / 100000000000000000000)))) (u := (6004735198462218249 / 12500000000000000000))
  · norm_num [world12113, agent12113, scalar12113, tp12113, tm12113, ep12113, em12113, dsL]
  · norm_num [world12113, agent12113, scalar12113, tp12113, tm12113, ep12113, em12113, dsL]
  · norm_num [world12113, agent12113, scalar12113, tp12113, tm12113, ep12113, em12113, dsL]
  · norm_num [world12113, agent12113, scalar12113, tp12113, tm12113, ep12113, em12113, dsL]
  · norm_num [world12113, agent12113, scalar12113, tp12113, tm12113, ep12113, em12113, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12113, agent12113, tp12113, tm12113, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12113, agent12113, tp12113, tm12113, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12113, agent12113, scalar12113, tp12113, tm12113, ep12113, em12113, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12113, agent12113, tp12113, tm12113, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12113, agent12113, scalar12113, tp12113, tm12113, ep12113, em12113, dsL]

theorem tails12113 :
    exp (-((12113:ℝ)*ep12113)) ≤ scalar12113.upperTail ∧
    exp (-((12113:ℝ)*em12113)) ≤ scalar12113.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12113:ℝ)) (by norm_num [ep12113]) ?_)
      (show bp12113^8 ≤ scalar12113.upperTail by norm_num [bp12113, scalar12113])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12113, bp12113, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12113:ℝ)) (by norm_num [em12113]) ?_)
      (show bm12113^8 ≤ scalar12113.lowerTail by norm_num [bm12113, scalar12113])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12113, bm12113, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12113 :
    agent12113.root+dsL+scalar12113.worldRadius < √(1/100/aL) ∧
    2*(agent12113.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12113, agent12113, scalar12113, tp12113, tm12113, ep12113, em12113, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12113, agent12113, scalar12113, tp12113, tm12113, ep12113, em12113, dsL]

noncomputable def master12113 : MasterCertificate 12113 world12113 agent12113 :=
  master scalar12113 dsL tp12113 tm12113 ep12113 em12113
    (by norm_num [dsL]) (by norm_num [tp12113]) (by norm_num [tm12113])
    (by norm_num [ep12113]) (by norm_num [em12113])
    positive12113 negative12113 tails12113.1 tails12113.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12113.1 tailGuards12113.2

theorem preserves12113 : master12113.toScalarCertificate = scalar12113 := rfl

noncomputable def tp12114 : ℝ := (2369437003 / 10000000000)
noncomputable def tm12114 : ℝ := (-((766399439 / 1250000000)))
noncomputable def ep12114 : ℝ := (54494244423161739 / 100000000000000000000)
noncomputable def em12114 : ℝ := (26275515452771261 / 50000000000000000000)
noncomputable def bp12114 : ℝ := (43815651328072343871 / 100000000000000000000)
noncomputable def bm12114 : ℝ := (5640510969419518259 / 12500000000000000000)

theorem positive12114 :
    Eplus aL (agent12114.root+dsL) scalar12114.worldRadius world12114.frame
      agent12114.frame tp12114 ≤ -ep12114 := by
  apply positive_check (eT := (116213120036770102733 / 100000000000000000000)) (y := (39604431737648105941 / 100000000000000000000)) (u := (9287094805253154091 / 6250000000000000000))
  · norm_num [world12114, agent12114, scalar12114, tp12114, tm12114, ep12114, em12114, dsL]
  · norm_num [world12114, agent12114, scalar12114, tp12114, tm12114, ep12114, em12114, dsL]
  · norm_num [world12114, agent12114, scalar12114, tp12114, tm12114, ep12114, em12114, dsL]
  · norm_num [world12114, agent12114, scalar12114, tp12114, tm12114, ep12114, em12114, dsL]
  · norm_num [world12114, agent12114, scalar12114, tp12114, tm12114, ep12114, em12114, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12114, agent12114, tp12114, tm12114, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12114, agent12114, scalar12114, tp12114, tm12114, ep12114, em12114, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12114, agent12114, tp12114, tm12114, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12114, agent12114, scalar12114, tp12114, tm12114, ep12114, em12114, dsL]

theorem negative12114 :
    Eminus aL (agent12114.root+dsL) scalar12114.worldRadius world12114.frame
      agent12114.frame tm12114 ≤ -em12114 := by
  apply negative_check (lo := (67786722260965206471 / 100000000000000000000)) (hi := (8473340282620650809 / 12500000000000000000))
    (y := (-((73317641819101059021 / 100000000000000000000)))) (u := (48038067417791301451 / 100000000000000000000))
  · norm_num [world12114, agent12114, scalar12114, tp12114, tm12114, ep12114, em12114, dsL]
  · norm_num [world12114, agent12114, scalar12114, tp12114, tm12114, ep12114, em12114, dsL]
  · norm_num [world12114, agent12114, scalar12114, tp12114, tm12114, ep12114, em12114, dsL]
  · norm_num [world12114, agent12114, scalar12114, tp12114, tm12114, ep12114, em12114, dsL]
  · norm_num [world12114, agent12114, scalar12114, tp12114, tm12114, ep12114, em12114, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12114, agent12114, tp12114, tm12114, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12114, agent12114, tp12114, tm12114, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12114, agent12114, scalar12114, tp12114, tm12114, ep12114, em12114, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12114, agent12114, tp12114, tm12114, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12114, agent12114, scalar12114, tp12114, tm12114, ep12114, em12114, dsL]

theorem tails12114 :
    exp (-((12114:ℝ)*ep12114)) ≤ scalar12114.upperTail ∧
    exp (-((12114:ℝ)*em12114)) ≤ scalar12114.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12114:ℝ)) (by norm_num [ep12114]) ?_)
      (show bp12114^8 ≤ scalar12114.upperTail by norm_num [bp12114, scalar12114])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12114, bp12114, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12114:ℝ)) (by norm_num [em12114]) ?_)
      (show bm12114^8 ≤ scalar12114.lowerTail by norm_num [bm12114, scalar12114])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12114, bm12114, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12114 :
    agent12114.root+dsL+scalar12114.worldRadius < √(1/100/aL) ∧
    2*(agent12114.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12114, agent12114, scalar12114, tp12114, tm12114, ep12114, em12114, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12114, agent12114, scalar12114, tp12114, tm12114, ep12114, em12114, dsL]

noncomputable def master12114 : MasterCertificate 12114 world12114 agent12114 :=
  master scalar12114 dsL tp12114 tm12114 ep12114 em12114
    (by norm_num [dsL]) (by norm_num [tp12114]) (by norm_num [tm12114])
    (by norm_num [ep12114]) (by norm_num [em12114])
    positive12114 negative12114 tails12114.1 tails12114.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12114.1 tailGuards12114.2

theorem preserves12114 : master12114.toScalarCertificate = scalar12114 := rfl

noncomputable def tp12115 : ℝ := (2369537057 / 10000000000)
noncomputable def tm12115 : ℝ := (-((613142023 / 1000000000)))
noncomputable def ep12115 : ℝ := (10899436957568671 / 20000000000000000000)
noncomputable def em12115 : ℝ := (52553589018581543 / 100000000000000000000)
noncomputable def bp12115 : ℝ := (14019429104078351 / 32000000000000000)
noncomputable def bm12115 : ℝ := (22559687886773154081 / 50000000000000000000)

theorem positive12115 :
    Eplus aL (agent12115.root+dsL) scalar12115.worldRadius world12115.frame
      agent12115.frame tp12115 ≤ -ep12115 := by
  apply positive_check (eT := (116213437492804301711 / 100000000000000000000)) (y := (39605071770969072163 / 100000000000000000000)) (u := (148594467935114837557 / 100000000000000000000))
  · norm_num [world12115, agent12115, scalar12115, tp12115, tm12115, ep12115, em12115, dsL]
  · norm_num [world12115, agent12115, scalar12115, tp12115, tm12115, ep12115, em12115, dsL]
  · norm_num [world12115, agent12115, scalar12115, tp12115, tm12115, ep12115, em12115, dsL]
  · norm_num [world12115, agent12115, scalar12115, tp12115, tm12115, ep12115, em12115, dsL]
  · norm_num [world12115, agent12115, scalar12115, tp12115, tm12115, ep12115, em12115, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12115, agent12115, tp12115, tm12115, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12115, agent12115, scalar12115, tp12115, tm12115, ep12115, em12115, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12115, agent12115, tp12115, tm12115, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12115, agent12115, scalar12115, tp12115, tm12115, ep12115, em12115, dsL]

theorem negative12115 :
    Eminus aL (agent12115.root+dsL) scalar12115.worldRadius world12115.frame
      agent12115.frame tm12115 ≤ -em12115 := by
  apply negative_check (lo := (67786390049089025133 / 100000000000000000000)) (hi := (33893195024544512567 / 50000000000000000000))
    (y := (-((2932690191163260631 / 4000000000000000000)))) (u := (24019126672348314501 / 50000000000000000000))
  · norm_num [world12115, agent12115, scalar12115, tp12115, tm12115, ep12115, em12115, dsL]
  · norm_num [world12115, agent12115, scalar12115, tp12115, tm12115, ep12115, em12115, dsL]
  · norm_num [world12115, agent12115, scalar12115, tp12115, tm12115, ep12115, em12115, dsL]
  · norm_num [world12115, agent12115, scalar12115, tp12115, tm12115, ep12115, em12115, dsL]
  · norm_num [world12115, agent12115, scalar12115, tp12115, tm12115, ep12115, em12115, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12115, agent12115, tp12115, tm12115, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12115, agent12115, tp12115, tm12115, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12115, agent12115, scalar12115, tp12115, tm12115, ep12115, em12115, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12115, agent12115, tp12115, tm12115, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12115, agent12115, scalar12115, tp12115, tm12115, ep12115, em12115, dsL]

theorem tails12115 :
    exp (-((12115:ℝ)*ep12115)) ≤ scalar12115.upperTail ∧
    exp (-((12115:ℝ)*em12115)) ≤ scalar12115.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12115:ℝ)) (by norm_num [ep12115]) ?_)
      (show bp12115^8 ≤ scalar12115.upperTail by norm_num [bp12115, scalar12115])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12115, bp12115, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12115:ℝ)) (by norm_num [em12115]) ?_)
      (show bm12115^8 ≤ scalar12115.lowerTail by norm_num [bm12115, scalar12115])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12115, bm12115, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12115 :
    agent12115.root+dsL+scalar12115.worldRadius < √(1/100/aL) ∧
    2*(agent12115.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12115, agent12115, scalar12115, tp12115, tm12115, ep12115, em12115, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12115, agent12115, scalar12115, tp12115, tm12115, ep12115, em12115, dsL]

noncomputable def master12115 : MasterCertificate 12115 world12115 agent12115 :=
  master scalar12115 dsL tp12115 tm12115 ep12115 em12115
    (by norm_num [dsL]) (by norm_num [tp12115]) (by norm_num [tm12115])
    (by norm_num [ep12115]) (by norm_num [em12115])
    positive12115 negative12115 tails12115.1 tails12115.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12115.1 tailGuards12115.2

theorem preserves12115 : master12115.toScalarCertificate = scalar12115 := rfl

noncomputable def tp12116 : ℝ := (2369637093 / 10000000000)
noncomputable def tm12116 : ℝ := (-((245265797 / 400000000)))
noncomputable def ep12116 : ℝ := (27250061668386047 / 50000000000000000000)
noncomputable def em12116 : ℝ := (13139036354007489 / 25000000000000000000)
noncomputable def bp12116 : ℝ := (21902891005482211463 / 50000000000000000000)
noncomputable def bm12116 : ℝ := (22557332583725383637 / 50000000000000000000)

theorem positive12116 :
    Eplus aL (agent12116.root+dsL) scalar12116.worldRadius world12116.frame
      agent12116.frame tp12116 ≤ -ep12116 := by
  apply positive_check (eT := (7263359678311165097 / 6250000000000000000)) (y := (9901428081420504919 / 25000000000000000000)) (u := (148595419767030874061 / 100000000000000000000))
  · norm_num [world12116, agent12116, scalar12116, tp12116, tm12116, ep12116, em12116, dsL]
  · norm_num [world12116, agent12116, scalar12116, tp12116, tm12116, ep12116, em12116, dsL]
  · norm_num [world12116, agent12116, scalar12116, tp12116, tm12116, ep12116, em12116, dsL]
  · norm_num [world12116, agent12116, scalar12116, tp12116, tm12116, ep12116, em12116, dsL]
  · norm_num [world12116, agent12116, scalar12116, tp12116, tm12116, ep12116, em12116, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12116, agent12116, tp12116, tm12116, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12116, agent12116, scalar12116, tp12116, tm12116, ep12116, em12116, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12116, agent12116, tp12116, tm12116, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12116, agent12116, scalar12116, tp12116, tm12116, ep12116, em12116, dsL]

theorem negative12116 :
    Eminus aL (agent12116.root+dsL) scalar12116.worldRadius world12116.frame
      agent12116.frame tm12116 ≤ -em12116 := by
  apply negative_check (lo := (13557211575284953391 / 20000000000000000000)) (hi := (16946514469106191739 / 25000000000000000000))
    (y := (-((4582304315619290259 / 6250000000000000000)))) (u := (24019219321305645653 / 50000000000000000000))
  · norm_num [world12116, agent12116, scalar12116, tp12116, tm12116, ep12116, em12116, dsL]
  · norm_num [world12116, agent12116, scalar12116, tp12116, tm12116, ep12116, em12116, dsL]
  · norm_num [world12116, agent12116, scalar12116, tp12116, tm12116, ep12116, em12116, dsL]
  · norm_num [world12116, agent12116, scalar12116, tp12116, tm12116, ep12116, em12116, dsL]
  · norm_num [world12116, agent12116, scalar12116, tp12116, tm12116, ep12116, em12116, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12116, agent12116, tp12116, tm12116, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12116, agent12116, tp12116, tm12116, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12116, agent12116, scalar12116, tp12116, tm12116, ep12116, em12116, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12116, agent12116, tp12116, tm12116, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12116, agent12116, scalar12116, tp12116, tm12116, ep12116, em12116, dsL]

theorem tails12116 :
    exp (-((12116:ℝ)*ep12116)) ≤ scalar12116.upperTail ∧
    exp (-((12116:ℝ)*em12116)) ≤ scalar12116.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12116:ℝ)) (by norm_num [ep12116]) ?_)
      (show bp12116^8 ≤ scalar12116.upperTail by norm_num [bp12116, scalar12116])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12116, bp12116, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12116:ℝ)) (by norm_num [em12116]) ?_)
      (show bm12116^8 ≤ scalar12116.lowerTail by norm_num [bm12116, scalar12116])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12116, bm12116, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12116 :
    agent12116.root+dsL+scalar12116.worldRadius < √(1/100/aL) ∧
    2*(agent12116.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12116, agent12116, scalar12116, tp12116, tm12116, ep12116, em12116, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12116, agent12116, scalar12116, tp12116, tm12116, ep12116, em12116, dsL]

noncomputable def master12116 : MasterCertificate 12116 world12116 agent12116 :=
  master scalar12116 dsL tp12116 tm12116 ep12116 em12116
    (by norm_num [dsL]) (by norm_num [tp12116]) (by norm_num [tm12116])
    (by norm_num [ep12116]) (by norm_num [em12116])
    positive12116 negative12116 tails12116.1 tails12116.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12116.1 tailGuards12116.2

theorem preserves12116 : master12116.toScalarCertificate = scalar12116 := rfl

noncomputable def tp12117 : ℝ := (2369737053 / 10000000000)
noncomputable def tm12117 : ℝ := (-((306593469 / 500000000)))
noncomputable def ep12117 : ℝ := (27251530189152087 / 50000000000000000000)
noncomputable def em12117 : ℝ := (5255870041662019 / 10000000000000000000)
noncomputable def bp12117 : ℝ := (43800849305599238253 / 100000000000000000000)
noncomputable def bm12117 : ℝ := (22554977859629355353 / 50000000000000000000)

theorem positive12117 :
    Eplus aL (agent12117.root+dsL) scalar12117.worldRadius world12117.frame
      agent12117.frame tp12117 ≤ -ep12117 := by
  apply positive_check (eT := (58107035844911081211 / 50000000000000000000)) (y := (19803176018740751193 / 50000000000000000000)) (u := (1485963703525051151 / 1000000000000000000))
  · norm_num [world12117, agent12117, scalar12117, tp12117, tm12117, ep12117, em12117, dsL]
  · norm_num [world12117, agent12117, scalar12117, tp12117, tm12117, ep12117, em12117, dsL]
  · norm_num [world12117, agent12117, scalar12117, tp12117, tm12117, ep12117, em12117, dsL]
  · norm_num [world12117, agent12117, scalar12117, tp12117, tm12117, ep12117, em12117, dsL]
  · norm_num [world12117, agent12117, scalar12117, tp12117, tm12117, ep12117, em12117, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12117, agent12117, tp12117, tm12117, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12117, agent12117, scalar12117, tp12117, tm12117, ep12117, em12117, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12117, agent12117, tp12117, tm12117, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12117, agent12117, scalar12117, tp12117, tm12117, ep12117, em12117, dsL]

theorem negative12117 :
    Eminus aL (agent12117.root+dsL) scalar12117.worldRadius world12117.frame
      agent12117.frame tm12117 ≤ -em12117 := by
  apply negative_check (lo := (67785726675799228127 / 100000000000000000000)) (hi := (2118303958618725879 / 3125000000000000000))
    (y := (-((18329120478978473523 / 25000000000000000000)))) (u := (48038624616097807061 / 100000000000000000000))
  · norm_num [world12117, agent12117, scalar12117, tp12117, tm12117, ep12117, em12117, dsL]
  · norm_num [world12117, agent12117, scalar12117, tp12117, tm12117, ep12117, em12117, dsL]
  · norm_num [world12117, agent12117, scalar12117, tp12117, tm12117, ep12117, em12117, dsL]
  · norm_num [world12117, agent12117, scalar12117, tp12117, tm12117, ep12117, em12117, dsL]
  · norm_num [world12117, agent12117, scalar12117, tp12117, tm12117, ep12117, em12117, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12117, agent12117, tp12117, tm12117, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12117, agent12117, tp12117, tm12117, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12117, agent12117, scalar12117, tp12117, tm12117, ep12117, em12117, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12117, agent12117, tp12117, tm12117, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12117, agent12117, scalar12117, tp12117, tm12117, ep12117, em12117, dsL]

theorem tails12117 :
    exp (-((12117:ℝ)*ep12117)) ≤ scalar12117.upperTail ∧
    exp (-((12117:ℝ)*em12117)) ≤ scalar12117.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12117:ℝ)) (by norm_num [ep12117]) ?_)
      (show bp12117^8 ≤ scalar12117.upperTail by norm_num [bp12117, scalar12117])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12117, bp12117, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12117:ℝ)) (by norm_num [em12117]) ?_)
      (show bm12117^8 ≤ scalar12117.lowerTail by norm_num [bm12117, scalar12117])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12117, bm12117, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12117 :
    agent12117.root+dsL+scalar12117.worldRadius < √(1/100/aL) ∧
    2*(agent12117.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12117, agent12117, scalar12117, tp12117, tm12117, ep12117, em12117, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12117, agent12117, scalar12117, tp12117, tm12117, ep12117, em12117, dsL]

noncomputable def master12117 : MasterCertificate 12117 world12117 agent12117 :=
  master scalar12117 dsL tp12117 tm12117 ep12117 em12117
    (by norm_num [dsL]) (by norm_num [tp12117]) (by norm_num [tm12117])
    (by norm_num [ep12117]) (by norm_num [em12117])
    positive12117 negative12117 tails12117.1 tails12117.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12117.1 tailGuards12117.2

theorem preserves12117 : master12117.toScalarCertificate = scalar12117 := rfl

noncomputable def tp12118 : ℝ := (2369836917 / 10000000000)
noncomputable def tm12118 : ℝ := (-((1533023437 / 2500000000)))
noncomputable def ep12118 : ℝ := (13626499032060989 / 25000000000000000000)
noncomputable def em12118 : ℝ := (26280627086766009 / 50000000000000000000)
noncomputable def bp12118 : ℝ := (43795917690940833451 / 100000000000000000000)
noncomputable def bm12118 : ℝ := (22552623662144591049 / 50000000000000000000)

theorem positive12118 :
    Eplus aL (agent12118.root+dsL) scalar12118.worldRadius world12118.frame
      agent12118.frame tp12118 ≤ -ep12118 := by
  apply positive_check (eT := (29053596964014195313 / 25000000000000000000)) (y := (7921398141444111159 / 20000000000000000000)) (u := (74298659697793255271 / 50000000000000000000))
  · norm_num [world12118, agent12118, scalar12118, tp12118, tm12118, ep12118, em12118, dsL]
  · norm_num [world12118, agent12118, scalar12118, tp12118, tm12118, ep12118, em12118, dsL]
  · norm_num [world12118, agent12118, scalar12118, tp12118, tm12118, ep12118, em12118, dsL]
  · norm_num [world12118, agent12118, scalar12118, tp12118, tm12118, ep12118, em12118, dsL]
  · norm_num [world12118, agent12118, scalar12118, tp12118, tm12118, ep12118, em12118, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12118, agent12118, tp12118, tm12118, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12118, agent12118, scalar12118, tp12118, tm12118, ep12118, em12118, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12118, agent12118, tp12118, tm12118, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12118, agent12118, scalar12118, tp12118, tm12118, ep12118, em12118, dsL]

theorem negative12118 :
    Eminus aL (agent12118.root+dsL) scalar12118.worldRadius world12118.frame
      agent12118.frame tm12118 ≤ -em12118 := by
  apply negative_check (lo := (33892697894707306377 / 50000000000000000000)) (hi := (13557079157882922551 / 20000000000000000000))
    (y := (-((9164511896634550347 / 12500000000000000000)))) (u := (4803881040239699653 / 10000000000000000000))
  · norm_num [world12118, agent12118, scalar12118, tp12118, tm12118, ep12118, em12118, dsL]
  · norm_num [world12118, agent12118, scalar12118, tp12118, tm12118, ep12118, em12118, dsL]
  · norm_num [world12118, agent12118, scalar12118, tp12118, tm12118, ep12118, em12118, dsL]
  · norm_num [world12118, agent12118, scalar12118, tp12118, tm12118, ep12118, em12118, dsL]
  · norm_num [world12118, agent12118, scalar12118, tp12118, tm12118, ep12118, em12118, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12118, agent12118, tp12118, tm12118, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12118, agent12118, tp12118, tm12118, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12118, agent12118, scalar12118, tp12118, tm12118, ep12118, em12118, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12118, agent12118, tp12118, tm12118, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12118, agent12118, scalar12118, tp12118, tm12118, ep12118, em12118, dsL]

theorem tails12118 :
    exp (-((12118:ℝ)*ep12118)) ≤ scalar12118.upperTail ∧
    exp (-((12118:ℝ)*em12118)) ≤ scalar12118.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12118:ℝ)) (by norm_num [ep12118]) ?_)
      (show bp12118^8 ≤ scalar12118.upperTail by norm_num [bp12118, scalar12118])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12118, bp12118, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12118:ℝ)) (by norm_num [em12118]) ?_)
      (show bm12118^8 ≤ scalar12118.lowerTail by norm_num [bm12118, scalar12118])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12118, bm12118, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12118 :
    agent12118.root+dsL+scalar12118.worldRadius < √(1/100/aL) ∧
    2*(agent12118.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12118, agent12118, scalar12118, tp12118, tm12118, ep12118, em12118, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12118, agent12118, scalar12118, tp12118, tm12118, ep12118, em12118, dsL]

noncomputable def master12118 : MasterCertificate 12118 world12118 agent12118 :=
  master scalar12118 dsL tp12118 tm12118 ep12118 em12118
    (by norm_num [dsL]) (by norm_num [tp12118]) (by norm_num [tm12118])
    (by norm_num [ep12118]) (by norm_num [em12118])
    positive12118 negative12118 tails12118.1 tails12118.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12118.1 tailGuards12118.2

theorem preserves12118 : master12118.toScalarCertificate = scalar12118 := rfl

noncomputable def tp12119 : ℝ := (1184968419 / 5000000000)
noncomputable def tm12119 : ℝ := (-((6132317973 / 10000000000)))
noncomputable def ep12119 : ℝ := (54508930340323111 / 100000000000000000000)
noncomputable def em12119 : ℝ := (52563806515300547 / 100000000000000000000)
noncomputable def bp12119 : ℝ := (21895493665163566583 / 50000000000000000000)
noncomputable def bm12119 : ℝ := (45100540099673043059 / 100000000000000000000)

theorem positive12119 :
    Eplus aL (agent12119.root+dsL) scalar12119.worldRadius world12119.frame
      agent12119.frame tp12119 ≤ -ep12119 := by
  apply positive_check (eT := (116214704479074332237 / 100000000000000000000)) (y := (39607631034278946657 / 100000000000000000000)) (u := (148598270907477034773 / 100000000000000000000))
  · norm_num [world12119, agent12119, scalar12119, tp12119, tm12119, ep12119, em12119, dsL]
  · norm_num [world12119, agent12119, scalar12119, tp12119, tm12119, ep12119, em12119, dsL]
  · norm_num [world12119, agent12119, scalar12119, tp12119, tm12119, ep12119, em12119, dsL]
  · norm_num [world12119, agent12119, scalar12119, tp12119, tm12119, ep12119, em12119, dsL]
  · norm_num [world12119, agent12119, scalar12119, tp12119, tm12119, ep12119, em12119, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12119, agent12119, tp12119, tm12119, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12119, agent12119, scalar12119, tp12119, tm12119, ep12119, em12119, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12119, agent12119, tp12119, tm12119, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12119, agent12119, scalar12119, tp12119, tm12119, ep12119, em12119, dsL]

theorem negative12119 :
    Eminus aL (agent12119.root+dsL) scalar12119.worldRadius world12119.frame
      agent12119.frame tm12119 ≤ -em12119 := by
  apply negative_check (lo := (8473133182255086823 / 12500000000000000000)) (hi := (13557013091608138917 / 20000000000000000000))
    (y := (-((36657854197157615717 / 50000000000000000000)))) (u := (12009749051668019469 / 25000000000000000000))
  · norm_num [world12119, agent12119, scalar12119, tp12119, tm12119, ep12119, em12119, dsL]
  · norm_num [world12119, agent12119, scalar12119, tp12119, tm12119, ep12119, em12119, dsL]
  · norm_num [world12119, agent12119, scalar12119, tp12119, tm12119, ep12119, em12119, dsL]
  · norm_num [world12119, agent12119, scalar12119, tp12119, tm12119, ep12119, em12119, dsL]
  · norm_num [world12119, agent12119, scalar12119, tp12119, tm12119, ep12119, em12119, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12119, agent12119, tp12119, tm12119, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12119, agent12119, tp12119, tm12119, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12119, agent12119, scalar12119, tp12119, tm12119, ep12119, em12119, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12119, agent12119, tp12119, tm12119, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12119, agent12119, scalar12119, tp12119, tm12119, ep12119, em12119, dsL]

theorem tails12119 :
    exp (-((12119:ℝ)*ep12119)) ≤ scalar12119.upperTail ∧
    exp (-((12119:ℝ)*em12119)) ≤ scalar12119.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12119:ℝ)) (by norm_num [ep12119]) ?_)
      (show bp12119^8 ≤ scalar12119.upperTail by norm_num [bp12119, scalar12119])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12119, bp12119, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12119:ℝ)) (by norm_num [em12119]) ?_)
      (show bm12119^8 ≤ scalar12119.lowerTail by norm_num [bm12119, scalar12119])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12119, bm12119, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12119 :
    agent12119.root+dsL+scalar12119.worldRadius < √(1/100/aL) ∧
    2*(agent12119.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12119, agent12119, scalar12119, tp12119, tm12119, ep12119, em12119, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12119, agent12119, scalar12119, tp12119, tm12119, ep12119, em12119, dsL]

noncomputable def master12119 : MasterCertificate 12119 world12119 agent12119 :=
  master scalar12119 dsL tp12119 tm12119 ep12119 em12119
    (by norm_num [dsL]) (by norm_num [tp12119]) (by norm_num [tm12119])
    (by norm_num [ep12119]) (by norm_num [em12119])
    positive12119 negative12119 tails12119.1 tails12119.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12119.1 tailGuards12119.2

theorem preserves12119 : master12119.toScalarCertificate = scalar12119 := rfl

noncomputable def tp12120 : ℝ := (474007331 / 2000000000)
noncomputable def tm12120 : ℝ := (-((3066271009 / 5000000000)))
noncomputable def ep12120 : ℝ := (13627965480647879 / 25000000000000000000)
noncomputable def em12120 : ℝ := (26283178205355327 / 50000000000000000000)
noncomputable def bp12120 : ℝ := (43786058948066843657 / 100000000000000000000)
noncomputable def bm12120 : ℝ := (45095834749913879879 / 100000000000000000000)

theorem positive12120 :
    Eplus aL (agent12120.root+dsL) scalar12120.worldRadius world12120.frame
      agent12120.frame tp12120 ≤ -ep12120 := by
  apply positive_check (eT := (116215020372540123059 / 100000000000000000000)) (y := (39608270276831731967 / 100000000000000000000)) (u := (74299610406946739169 / 50000000000000000000))
  · norm_num [world12120, agent12120, scalar12120, tp12120, tm12120, ep12120, em12120, dsL]
  · norm_num [world12120, agent12120, scalar12120, tp12120, tm12120, ep12120, em12120, dsL]
  · norm_num [world12120, agent12120, scalar12120, tp12120, tm12120, ep12120, em12120, dsL]
  · norm_num [world12120, agent12120, scalar12120, tp12120, tm12120, ep12120, em12120, dsL]
  · norm_num [world12120, agent12120, scalar12120, tp12120, tm12120, ep12120, em12120, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12120, agent12120, tp12120, tm12120, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12120, agent12120, scalar12120, tp12120, tm12120, ep12120, em12120, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12120, agent12120, tp12120, tm12120, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12120, agent12120, scalar12120, tp12120, tm12120, ep12120, em12120, dsL]

theorem negative12120 :
    Eminus aL (agent12120.root+dsL) scalar12120.worldRadius world12120.frame
      agent12120.frame tm12120 ≤ -em12120 := by
  apply negative_check (lo := (33892367920296695543 / 50000000000000000000)) (hi := (67784735840593391087 / 100000000000000000000))
    (y := (-((36657660416695407241 / 50000000000000000000)))) (u := (24019591193705319371 / 50000000000000000000))
  · norm_num [world12120, agent12120, scalar12120, tp12120, tm12120, ep12120, em12120, dsL]
  · norm_num [world12120, agent12120, scalar12120, tp12120, tm12120, ep12120, em12120, dsL]
  · norm_num [world12120, agent12120, scalar12120, tp12120, tm12120, ep12120, em12120, dsL]
  · norm_num [world12120, agent12120, scalar12120, tp12120, tm12120, ep12120, em12120, dsL]
  · norm_num [world12120, agent12120, scalar12120, tp12120, tm12120, ep12120, em12120, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12120, agent12120, tp12120, tm12120, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12120, agent12120, tp12120, tm12120, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12120, agent12120, scalar12120, tp12120, tm12120, ep12120, em12120, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12120, agent12120, tp12120, tm12120, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12120, agent12120, scalar12120, tp12120, tm12120, ep12120, em12120, dsL]

theorem tails12120 :
    exp (-((12120:ℝ)*ep12120)) ≤ scalar12120.upperTail ∧
    exp (-((12120:ℝ)*em12120)) ≤ scalar12120.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12120:ℝ)) (by norm_num [ep12120]) ?_)
      (show bp12120^8 ≤ scalar12120.upperTail by norm_num [bp12120, scalar12120])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12120, bp12120, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12120:ℝ)) (by norm_num [em12120]) ?_)
      (show bm12120^8 ≤ scalar12120.lowerTail by norm_num [bm12120, scalar12120])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12120, bm12120, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12120 :
    agent12120.root+dsL+scalar12120.worldRadius < √(1/100/aL) ∧
    2*(agent12120.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12120, agent12120, scalar12120, tp12120, tm12120, ep12120, em12120, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12120, agent12120, scalar12120, tp12120, tm12120, ep12120, em12120, dsL]

noncomputable def master12120 : MasterCertificate 12120 world12120 agent12120 :=
  master scalar12120 dsL tp12120 tm12120 ep12120 em12120
    (by norm_num [dsL]) (by norm_num [tp12120]) (by norm_num [tm12120])
    (by norm_num [ep12120]) (by norm_num [em12120])
    positive12120 negative12120 tails12120.1 tails12120.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12120.1 tailGuards12120.2

theorem preserves12120 : master12120.toScalarCertificate = scalar12120 := rfl

noncomputable def tp12121 : ℝ := (2370136441 / 10000000000)
noncomputable def tm12121 : ℝ := (-((6132765981 / 10000000000)))
noncomputable def ep12121 : ℝ := (54514792974505557 / 100000000000000000000)
noncomputable def em12121 : ℝ := (52568905807458621 / 100000000000000000000)
noncomputable def bp12121 : ℝ := (21890565575698826483 / 50000000000000000000)
noncomputable def bm12121 : ℝ := (22545564972150131361 / 50000000000000000000)

theorem positive12121 :
    Eplus aL (agent12121.root+dsL) scalar12121.worldRadius world12121.frame
      agent12121.frame tp12121 ≤ -ep12121 := by
  apply positive_check (eT := (14526917009294217701 / 12500000000000000000)) (y := (3960890938147849261 / 10000000000000000000)) (u := (148600170521453559381 / 100000000000000000000))
  · norm_num [world12121, agent12121, scalar12121, tp12121, tm12121, ep12121, em12121, dsL]
  · norm_num [world12121, agent12121, scalar12121, tp12121, tm12121, ep12121, em12121, dsL]
  · norm_num [world12121, agent12121, scalar12121, tp12121, tm12121, ep12121, em12121, dsL]
  · norm_num [world12121, agent12121, scalar12121, tp12121, tm12121, ep12121, em12121, dsL]
  · norm_num [world12121, agent12121, scalar12121, tp12121, tm12121, ep12121, em12121, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12121, agent12121, tp12121, tm12121, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12121, agent12121, scalar12121, tp12121, tm12121, ep12121, em12121, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12121, agent12121, tp12121, tm12121, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12121, agent12121, scalar12121, tp12121, tm12121, ep12121, em12121, dsL]

theorem negative12121 :
    Eminus aL (agent12121.root+dsL) scalar12121.worldRadius world12121.frame
      agent12121.frame tm12121 ≤ -em12121 := by
  apply negative_check (lo := (67784406515897441691 / 100000000000000000000)) (hi := (16946101628974360423 / 25000000000000000000))
    (y := (-((4582183354302587529 / 6250000000000000000)))) (u := (240196841892273583 / 500000000000000000))
  · norm_num [world12121, agent12121, scalar12121, tp12121, tm12121, ep12121, em12121, dsL]
  · norm_num [world12121, agent12121, scalar12121, tp12121, tm12121, ep12121, em12121, dsL]
  · norm_num [world12121, agent12121, scalar12121, tp12121, tm12121, ep12121, em12121, dsL]
  · norm_num [world12121, agent12121, scalar12121, tp12121, tm12121, ep12121, em12121, dsL]
  · norm_num [world12121, agent12121, scalar12121, tp12121, tm12121, ep12121, em12121, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12121, agent12121, tp12121, tm12121, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12121, agent12121, tp12121, tm12121, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12121, agent12121, scalar12121, tp12121, tm12121, ep12121, em12121, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12121, agent12121, tp12121, tm12121, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12121, agent12121, scalar12121, tp12121, tm12121, ep12121, em12121, dsL]

theorem tails12121 :
    exp (-((12121:ℝ)*ep12121)) ≤ scalar12121.upperTail ∧
    exp (-((12121:ℝ)*em12121)) ≤ scalar12121.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12121:ℝ)) (by norm_num [ep12121]) ?_)
      (show bp12121^8 ≤ scalar12121.upperTail by norm_num [bp12121, scalar12121])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12121, bp12121, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12121:ℝ)) (by norm_num [em12121]) ?_)
      (show bm12121^8 ≤ scalar12121.lowerTail by norm_num [bm12121, scalar12121])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12121, bm12121, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12121 :
    agent12121.root+dsL+scalar12121.worldRadius < √(1/100/aL) ∧
    2*(agent12121.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12121, agent12121, scalar12121, tp12121, tm12121, ep12121, em12121, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12121, agent12121, scalar12121, tp12121, tm12121, ep12121, em12121, dsL]

noncomputable def master12121 : MasterCertificate 12121 world12121 agent12121 :=
  master scalar12121 dsL tp12121 tm12121 ep12121 em12121
    (by norm_num [dsL]) (by norm_num [tp12121]) (by norm_num [tm12121])
    (by norm_num [ep12121]) (by norm_num [em12121])
    positive12121 negative12121 tails12121.1 tails12121.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12121.1 tailGuards12121.2

theorem preserves12121 : master12121.toScalarCertificate = scalar12121 := rfl

noncomputable def tp12122 : ℝ := (148139757 / 625000000)
noncomputable def tm12122 : ℝ := (-((153324743 / 250000000)))
noncomputable def ep12122 : ℝ := (54517721245271149 / 100000000000000000000)
noncomputable def em12122 : ℝ := (52571452601068301 / 100000000000000000000)
noncomputable def bp12122 : ℝ := (1368006419791503351 / 3125000000000000000)
noncomputable def bm12122 : ℝ := (22543213560283981019 / 50000000000000000000)

theorem positive12122 :
    Eplus aL (agent12122.root+dsL) scalar12122.worldRadius world12122.frame
      agent12122.frame tp12122 ≤ -ep12122 := by
  apply positive_check (eT := (58107825482815280661 / 50000000000000000000)) (y := (990238684072970309 / 2500000000000000000)) (u := (7430055928299297031 / 5000000000000000000))
  · norm_num [world12122, agent12122, scalar12122, tp12122, tm12122, ep12122, em12122, dsL]
  · norm_num [world12122, agent12122, scalar12122, tp12122, tm12122, ep12122, em12122, dsL]
  · norm_num [world12122, agent12122, scalar12122, tp12122, tm12122, ep12122, em12122, dsL]
  · norm_num [world12122, agent12122, scalar12122, tp12122, tm12122, ep12122, em12122, dsL]
  · norm_num [world12122, agent12122, scalar12122, tp12122, tm12122, ep12122, em12122, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12122, agent12122, tp12122, tm12122, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12122, agent12122, scalar12122, tp12122, tm12122, ep12122, em12122, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12122, agent12122, tp12122, tm12122, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12122, agent12122, scalar12122, tp12122, tm12122, ep12122, em12122, dsL]

theorem negative12122 :
    Eminus aL (agent12122.root+dsL) scalar12122.worldRadius world12122.frame
      agent12122.frame tm12122 ≤ -em12122 := by
  apply negative_check (lo := (4236504880883380077 / 6250000000000000000)) (hi := (67784078094134081233 / 100000000000000000000))
    (y := (-((73314545586458346091 / 100000000000000000000)))) (u := (960791096222841599 / 2000000000000000000))
  · norm_num [world12122, agent12122, scalar12122, tp12122, tm12122, ep12122, em12122, dsL]
  · norm_num [world12122, agent12122, scalar12122, tp12122, tm12122, ep12122, em12122, dsL]
  · norm_num [world12122, agent12122, scalar12122, tp12122, tm12122, ep12122, em12122, dsL]
  · norm_num [world12122, agent12122, scalar12122, tp12122, tm12122, ep12122, em12122, dsL]
  · norm_num [world12122, agent12122, scalar12122, tp12122, tm12122, ep12122, em12122, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12122, agent12122, tp12122, tm12122, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12122, agent12122, tp12122, tm12122, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12122, agent12122, scalar12122, tp12122, tm12122, ep12122, em12122, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12122, agent12122, tp12122, tm12122, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12122, agent12122, scalar12122, tp12122, tm12122, ep12122, em12122, dsL]

theorem tails12122 :
    exp (-((12122:ℝ)*ep12122)) ≤ scalar12122.upperTail ∧
    exp (-((12122:ℝ)*em12122)) ≤ scalar12122.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12122:ℝ)) (by norm_num [ep12122]) ?_)
      (show bp12122^8 ≤ scalar12122.upperTail by norm_num [bp12122, scalar12122])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12122, bp12122, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12122:ℝ)) (by norm_num [em12122]) ?_)
      (show bm12122^8 ≤ scalar12122.lowerTail by norm_num [bm12122, scalar12122])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12122, bm12122, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12122 :
    agent12122.root+dsL+scalar12122.worldRadius < √(1/100/aL) ∧
    2*(agent12122.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12122, agent12122, scalar12122, tp12122, tm12122, ep12122, em12122, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12122, agent12122, scalar12122, tp12122, tm12122, ep12122, em12122, dsL]

noncomputable def master12122 : MasterCertificate 12122 world12122 agent12122 :=
  master scalar12122 dsL tp12122 tm12122 ep12122 em12122
    (by norm_num [dsL]) (by norm_num [tp12122]) (by norm_num [tm12122])
    (by norm_num [ep12122]) (by norm_num [em12122])
    positive12122 negative12122 tails12122.1 tails12122.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12122.1 tailGuards12122.2

theorem preserves12122 : master12122.toScalarCertificate = scalar12122 := rfl

noncomputable def tp12123 : ℝ := (2370335741 / 10000000000)
noncomputable def tm12123 : ℝ := (-((6133213557 / 10000000000)))
noncomputable def ep12123 : ℝ := (27260324493116949 / 50000000000000000000)
noncomputable def em12123 : ℝ := (5257399889666113 / 10000000000000000000)
noncomputable def bp12123 : ℝ := (21885640150211252003 / 50000000000000000000)
noncomputable def bm12123 : ℝ := (2817607802531903499 / 6250000000000000000)

theorem positive12123 :
    Eplus aL (agent12123.root+dsL) scalar12123.worldRadius world12123.frame
      agent12123.frame tp12123 ≤ -ep12123 := by
  apply positive_check (eT := (7263497849014053657 / 6250000000000000000)) (y := (1237818281492112037 / 3125000000000000000)) (u := (37150516529088743739 / 25000000000000000000))
  · norm_num [world12123, agent12123, scalar12123, tp12123, tm12123, ep12123, em12123, dsL]
  · norm_num [world12123, agent12123, scalar12123, tp12123, tm12123, ep12123, em12123, dsL]
  · norm_num [world12123, agent12123, scalar12123, tp12123, tm12123, ep12123, em12123, dsL]
  · norm_num [world12123, agent12123, scalar12123, tp12123, tm12123, ep12123, em12123, dsL]
  · norm_num [world12123, agent12123, scalar12123, tp12123, tm12123, ep12123, em12123, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12123, agent12123, tp12123, tm12123, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12123, agent12123, scalar12123, tp12123, tm12123, ep12123, em12123, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12123, agent12123, tp12123, tm12123, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12123, agent12123, scalar12123, tp12123, tm12123, ep12123, em12123, dsL]

theorem negative12123 :
    Eminus aL (agent12123.root+dsL) scalar12123.worldRadius world12123.frame
      agent12123.frame tm12123 ≤ -em12123 := by
  apply negative_check (lo := (16945937297883767809 / 25000000000000000000)) (hi := (67783749191535071237 / 100000000000000000000))
    (y := (-((18328539914849225253 / 25000000000000000000)))) (u := (9607948041828408837 / 20000000000000000000))
  · norm_num [world12123, agent12123, scalar12123, tp12123, tm12123, ep12123, em12123, dsL]
  · norm_num [world12123, agent12123, scalar12123, tp12123, tm12123, ep12123, em12123, dsL]
  · norm_num [world12123, agent12123, scalar12123, tp12123, tm12123, ep12123, em12123, dsL]
  · norm_num [world12123, agent12123, scalar12123, tp12123, tm12123, ep12123, em12123, dsL]
  · norm_num [world12123, agent12123, scalar12123, tp12123, tm12123, ep12123, em12123, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12123, agent12123, tp12123, tm12123, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12123, agent12123, tp12123, tm12123, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12123, agent12123, scalar12123, tp12123, tm12123, ep12123, em12123, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12123, agent12123, tp12123, tm12123, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12123, agent12123, scalar12123, tp12123, tm12123, ep12123, em12123, dsL]

theorem tails12123 :
    exp (-((12123:ℝ)*ep12123)) ≤ scalar12123.upperTail ∧
    exp (-((12123:ℝ)*em12123)) ≤ scalar12123.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12123:ℝ)) (by norm_num [ep12123]) ?_)
      (show bp12123^8 ≤ scalar12123.upperTail by norm_num [bp12123, scalar12123])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12123, bp12123, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12123:ℝ)) (by norm_num [em12123]) ?_)
      (show bm12123^8 ≤ scalar12123.lowerTail by norm_num [bm12123, scalar12123])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12123, bm12123, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12123 :
    agent12123.root+dsL+scalar12123.worldRadius < √(1/100/aL) ∧
    2*(agent12123.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12123, agent12123, scalar12123, tp12123, tm12123, ep12123, em12123, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12123, agent12123, scalar12123, tp12123, tm12123, ep12123, em12123, dsL]

noncomputable def master12123 : MasterCertificate 12123 world12123 agent12123 :=
  master scalar12123 dsL tp12123 tm12123 ep12123 em12123
    (by norm_num [dsL]) (by norm_num [tp12123]) (by norm_num [tm12123])
    (by norm_num [ep12123]) (by norm_num [em12123])
    positive12123 negative12123 tails12123.1 tails12123.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12123.1 tailGuards12123.2

theorem preserves12123 : master12123.toScalarCertificate = scalar12123 := rfl

noncomputable def tp12124 : ℝ := (2370435397 / 10000000000)
noncomputable def tm12124 : ℝ := (-((3066718483 / 5000000000)))
noncomputable def ep12124 : ℝ := (13630893647757131 / 25000000000000000000)
noncomputable def em12124 : ℝ := (3286033949966503 / 6250000000000000000)
noncomputable def bp12124 : ℝ := (10941589204540888553 / 25000000000000000000)
noncomputable def bm12124 : ℝ := (45077024125286826553 / 100000000000000000000)

theorem positive12124 :
    Eplus aL (agent12124.root+dsL) scalar12124.worldRadius world12124.frame
      agent12124.frame tp12124 ≤ -ep12124 := by
  apply positive_check (eT := (2905407010964583569 / 2500000000000000000)) (y := (9902705968176504677 / 25000000000000000000)) (u := (7430150774295774603 / 5000000000000000000))
  · norm_num [world12124, agent12124, scalar12124, tp12124, tm12124, ep12124, em12124, dsL]
  · norm_num [world12124, agent12124, scalar12124, tp12124, tm12124, ep12124, em12124, dsL]
  · norm_num [world12124, agent12124, scalar12124, tp12124, tm12124, ep12124, em12124, dsL]
  · norm_num [world12124, agent12124, scalar12124, tp12124, tm12124, ep12124, em12124, dsL]
  · norm_num [world12124, agent12124, scalar12124, tp12124, tm12124, ep12124, em12124, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12124, agent12124, tp12124, tm12124, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12124, agent12124, scalar12124, tp12124, tm12124, ep12124, em12124, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12124, agent12124, tp12124, tm12124, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12124, agent12124, scalar12124, tp12124, tm12124, ep12124, em12124, dsL]

theorem negative12124 :
    Eminus aL (agent12124.root+dsL) scalar12124.worldRadius world12124.frame
      agent12124.frame tm12124 ≤ -em12124 := by
  apply negative_check (lo := (13556684413702044379 / 20000000000000000000)) (hi := (8472927758563777737 / 12500000000000000000))
    (y := (-((36656885325652114531 / 50000000000000000000)))) (u := (48039927087982642999 / 100000000000000000000))
  · norm_num [world12124, agent12124, scalar12124, tp12124, tm12124, ep12124, em12124, dsL]
  · norm_num [world12124, agent12124, scalar12124, tp12124, tm12124, ep12124, em12124, dsL]
  · norm_num [world12124, agent12124, scalar12124, tp12124, tm12124, ep12124, em12124, dsL]
  · norm_num [world12124, agent12124, scalar12124, tp12124, tm12124, ep12124, em12124, dsL]
  · norm_num [world12124, agent12124, scalar12124, tp12124, tm12124, ep12124, em12124, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12124, agent12124, tp12124, tm12124, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12124, agent12124, tp12124, tm12124, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12124, agent12124, scalar12124, tp12124, tm12124, ep12124, em12124, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12124, agent12124, tp12124, tm12124, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12124, agent12124, scalar12124, tp12124, tm12124, ep12124, em12124, dsL]

theorem tails12124 :
    exp (-((12124:ℝ)*ep12124)) ≤ scalar12124.upperTail ∧
    exp (-((12124:ℝ)*em12124)) ≤ scalar12124.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12124:ℝ)) (by norm_num [ep12124]) ?_)
      (show bp12124^8 ≤ scalar12124.upperTail by norm_num [bp12124, scalar12124])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12124, bp12124, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12124:ℝ)) (by norm_num [em12124]) ?_)
      (show bm12124^8 ≤ scalar12124.lowerTail by norm_num [bm12124, scalar12124])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12124, bm12124, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12124 :
    agent12124.root+dsL+scalar12124.worldRadius < √(1/100/aL) ∧
    2*(agent12124.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12124, agent12124, scalar12124, tp12124, tm12124, ep12124, em12124, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12124, agent12124, scalar12124, tp12124, tm12124, ep12124, em12124, dsL]

noncomputable def master12124 : MasterCertificate 12124 world12124 agent12124 :=
  master scalar12124 dsL tp12124 tm12124 ep12124 em12124
    (by norm_num [dsL]) (by norm_num [tp12124]) (by norm_num [tm12124])
    (by norm_num [ep12124]) (by norm_num [em12124])
    positive12124 negative12124 tails12124.1 tails12124.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12124.1 tailGuards12124.2

theorem preserves12124 : master12124.toScalarCertificate = scalar12124 := rfl

noncomputable def tp12125 : ℝ := (2370534931 / 10000000000)
noncomputable def tm12125 : ℝ := (-((6133660509 / 10000000000)))
noncomputable def ep12125 : ℝ := (27263249452937419 / 50000000000000000000)
noncomputable def em12125 : ℝ := (2103163450421479 / 4000000000000000000)
noncomputable def bp12125 : ℝ := (2188071721260316951 / 5000000000000000000)
noncomputable def bm12125 : ℝ := (11268081115444258221 / 25000000000000000000)

theorem positive12125 :
    Eplus aL (agent12125.root+dsL) scalar12125.worldRadius world12125.frame
      agent12125.frame tp12125 ≤ -ep12125 := by
  apply positive_check (eT := (29054148607717627797 / 25000000000000000000)) (y := (39611461225223354311 / 100000000000000000000)) (u := (148603962613993797277 / 100000000000000000000))
  · norm_num [world12125, agent12125, scalar12125, tp12125, tm12125, ep12125, em12125, dsL]
  · norm_num [world12125, agent12125, scalar12125, tp12125, tm12125, ep12125, em12125, dsL]
  · norm_num [world12125, agent12125, scalar12125, tp12125, tm12125, ep12125, em12125, dsL]
  · norm_num [world12125, agent12125, scalar12125, tp12125, tm12125, ep12125, em12125, dsL]
  · norm_num [world12125, agent12125, scalar12125, tp12125, tm12125, ep12125, em12125, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12125, agent12125, tp12125, tm12125, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12125, agent12125, scalar12125, tp12125, tm12125, ep12125, em12125, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12125, agent12125, tp12125, tm12125, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12125, agent12125, scalar12125, tp12125, tm12125, ep12125, em12125, dsL]

theorem negative12125 :
    Eminus aL (agent12125.root+dsL) scalar12125.worldRadius world12125.frame
      agent12125.frame tm12125 ≤ -em12125 := by
  apply negative_check (lo := (67783094309868948369 / 100000000000000000000)) (hi := (6778309430986894837 / 10000000000000000000))
    (y := (-((73313384190613939137 / 100000000000000000000)))) (u := (12010028185943806273 / 25000000000000000000))
  · norm_num [world12125, agent12125, scalar12125, tp12125, tm12125, ep12125, em12125, dsL]
  · norm_num [world12125, agent12125, scalar12125, tp12125, tm12125, ep12125, em12125, dsL]
  · norm_num [world12125, agent12125, scalar12125, tp12125, tm12125, ep12125, em12125, dsL]
  · norm_num [world12125, agent12125, scalar12125, tp12125, tm12125, ep12125, em12125, dsL]
  · norm_num [world12125, agent12125, scalar12125, tp12125, tm12125, ep12125, em12125, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12125, agent12125, tp12125, tm12125, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12125, agent12125, tp12125, tm12125, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12125, agent12125, scalar12125, tp12125, tm12125, ep12125, em12125, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12125, agent12125, tp12125, tm12125, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12125, agent12125, scalar12125, tp12125, tm12125, ep12125, em12125, dsL]

theorem tails12125 :
    exp (-((12125:ℝ)*ep12125)) ≤ scalar12125.upperTail ∧
    exp (-((12125:ℝ)*em12125)) ≤ scalar12125.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12125:ℝ)) (by norm_num [ep12125]) ?_)
      (show bp12125^8 ≤ scalar12125.upperTail by norm_num [bp12125, scalar12125])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12125, bp12125, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12125:ℝ)) (by norm_num [em12125]) ?_)
      (show bm12125^8 ≤ scalar12125.lowerTail by norm_num [bm12125, scalar12125])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12125, bm12125, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12125 :
    agent12125.root+dsL+scalar12125.worldRadius < √(1/100/aL) ∧
    2*(agent12125.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12125, agent12125, scalar12125, tp12125, tm12125, ep12125, em12125, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12125, agent12125, scalar12125, tp12125, tm12125, ep12125, em12125, dsL]

noncomputable def master12125 : MasterCertificate 12125 world12125 agent12125 :=
  master scalar12125 dsL tp12125 tm12125 ep12125 em12125
    (by norm_num [dsL]) (by norm_num [tp12125]) (by norm_num [tm12125])
    (by norm_num [ep12125]) (by norm_num [em12125])
    positive12125 negative12125 tails12125.1 tails12125.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12125.1 tailGuards12125.2

theorem preserves12125 : master12125.toScalarCertificate = scalar12125 := rfl

noncomputable def tp12126 : ℝ := (59265861 / 250000000)
noncomputable def tm12126 : ℝ := (-((191683869 / 312500000)))
noncomputable def ep12126 : ℝ := (1704044402311197 / 3125000000000000000)
noncomputable def em12126 : ℝ := (26290813590138701 / 50000000000000000000)
noncomputable def bp12126 : ℝ := (10939128455610134003 / 25000000000000000000)
noncomputable def bm12126 : ℝ := (2253381323224696881 / 5000000000000000000)

theorem positive12126 :
    Eplus aL (agent12126.root+dsL) scalar12126.worldRadius world12126.frame
      agent12126.frame tp12126 ≤ -ep12126 := by
  apply positive_check (eT := (11621690827578841697 / 10000000000000000000)) (y := (39612098700122658593 / 100000000000000000000)) (u := (29720981985994856119 / 20000000000000000000))
  · norm_num [world12126, agent12126, scalar12126, tp12126, tm12126, ep12126, em12126, dsL]
  · norm_num [world12126, agent12126, scalar12126, tp12126, tm12126, ep12126, em12126, dsL]
  · norm_num [world12126, agent12126, scalar12126, tp12126, tm12126, ep12126, em12126, dsL]
  · norm_num [world12126, agent12126, scalar12126, tp12126, tm12126, ep12126, em12126, dsL]
  · norm_num [world12126, agent12126, scalar12126, tp12126, tm12126, ep12126, em12126, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12126, agent12126, tp12126, tm12126, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12126, agent12126, scalar12126, tp12126, tm12126, ep12126, em12126, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12126, agent12126, tp12126, tm12126, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12126, agent12126, scalar12126, tp12126, tm12126, ep12126, em12126, dsL]

theorem negative12126 :
    Eminus aL (agent12126.root+dsL) scalar12126.worldRadius world12126.frame
      agent12126.frame tm12126 ≤ -em12126 := by
  apply negative_check (lo := (16945691885002641173 / 25000000000000000000)) (hi := (67782767540010564693 / 100000000000000000000))
    (y := (-((18328249036814387443 / 25000000000000000000)))) (u := (9608059832120563619 / 20000000000000000000))
  · norm_num [world12126, agent12126, scalar12126, tp12126, tm12126, ep12126, em12126, dsL]
  · norm_num [world12126, agent12126, scalar12126, tp12126, tm12126, ep12126, em12126, dsL]
  · norm_num [world12126, agent12126, scalar12126, tp12126, tm12126, ep12126, em12126, dsL]
  · norm_num [world12126, agent12126, scalar12126, tp12126, tm12126, ep12126, em12126, dsL]
  · norm_num [world12126, agent12126, scalar12126, tp12126, tm12126, ep12126, em12126, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12126, agent12126, tp12126, tm12126, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12126, agent12126, tp12126, tm12126, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12126, agent12126, scalar12126, tp12126, tm12126, ep12126, em12126, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12126, agent12126, tp12126, tm12126, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12126, agent12126, scalar12126, tp12126, tm12126, ep12126, em12126, dsL]

theorem tails12126 :
    exp (-((12126:ℝ)*ep12126)) ≤ scalar12126.upperTail ∧
    exp (-((12126:ℝ)*em12126)) ≤ scalar12126.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12126:ℝ)) (by norm_num [ep12126]) ?_)
      (show bp12126^8 ≤ scalar12126.upperTail by norm_num [bp12126, scalar12126])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12126, bp12126, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12126:ℝ)) (by norm_num [em12126]) ?_)
      (show bm12126^8 ≤ scalar12126.lowerTail by norm_num [bm12126, scalar12126])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12126, bm12126, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12126 :
    agent12126.root+dsL+scalar12126.worldRadius < √(1/100/aL) ∧
    2*(agent12126.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12126, agent12126, scalar12126, tp12126, tm12126, ep12126, em12126, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12126, agent12126, scalar12126, tp12126, tm12126, ep12126, em12126, dsL]

noncomputable def master12126 : MasterCertificate 12126 world12126 agent12126 :=
  master scalar12126 dsL tp12126 tm12126 ep12126 em12126
    (by norm_num [dsL]) (by norm_num [tp12126]) (by norm_num [tm12126])
    (by norm_num [ep12126]) (by norm_num [em12126])
    positive12126 negative12126 tails12126.1 tails12126.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12126.1 tailGuards12126.2

theorem preserves12126 : master12126.toScalarCertificate = scalar12126 := rfl

noncomputable def tp12127 : ℝ := (2370733911 / 10000000000)
noncomputable def tm12127 : ℝ := (-((6134107091 / 10000000000)))
noncomputable def ep12127 : ℝ := (13633085501281853 / 25000000000000000000)
noncomputable def em12127 : ℝ := (52584167284755113 / 100000000000000000000)
noncomputable def bp12127 : ℝ := (43751594008410848291 / 100000000000000000000)
noncomputable def bm12127 : ℝ := (11265732306886325563 / 25000000000000000000)

theorem positive12127 :
    Eplus aL (agent12127.root+dsL) scalar12127.worldRadius world12127.frame
      agent12127.frame tp12127 ≤ -ep12127 := by
  apply positive_check (eT := (23243444375510604049 / 20000000000000000000)) (y := (19806368114341330779 / 50000000000000000000)) (u := (148605857331736626061 / 100000000000000000000))
  · norm_num [world12127, agent12127, scalar12127, tp12127, tm12127, ep12127, em12127, dsL]
  · norm_num [world12127, agent12127, scalar12127, tp12127, tm12127, ep12127, em12127, dsL]
  · norm_num [world12127, agent12127, scalar12127, tp12127, tm12127, ep12127, em12127, dsL]
  · norm_num [world12127, agent12127, scalar12127, tp12127, tm12127, ep12127, em12127, dsL]
  · norm_num [world12127, agent12127, scalar12127, tp12127, tm12127, ep12127, em12127, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12127, agent12127, tp12127, tm12127, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12127, agent12127, scalar12127, tp12127, tm12127, ep12127, em12127, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12127, agent12127, tp12127, tm12127, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12127, agent12127, scalar12127, tp12127, tm12127, ep12127, em12127, dsL]

theorem negative12127 :
    Eminus aL (agent12127.root+dsL) scalar12127.worldRadius world12127.frame
      agent12127.frame tm12127 ≤ -em12127 := by
  apply negative_check (lo := (67782440779155505491 / 100000000000000000000)) (hi := (16945610194788876373 / 25000000000000000000))
    (y := (-((18328152433278670399 / 25000000000000000000)))) (u := (48040484795471710309 / 100000000000000000000))
  · norm_num [world12127, agent12127, scalar12127, tp12127, tm12127, ep12127, em12127, dsL]
  · norm_num [world12127, agent12127, scalar12127, tp12127, tm12127, ep12127, em12127, dsL]
  · norm_num [world12127, agent12127, scalar12127, tp12127, tm12127, ep12127, em12127, dsL]
  · norm_num [world12127, agent12127, scalar12127, tp12127, tm12127, ep12127, em12127, dsL]
  · norm_num [world12127, agent12127, scalar12127, tp12127, tm12127, ep12127, em12127, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12127, agent12127, tp12127, tm12127, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12127, agent12127, tp12127, tm12127, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12127, agent12127, scalar12127, tp12127, tm12127, ep12127, em12127, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12127, agent12127, tp12127, tm12127, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12127, agent12127, scalar12127, tp12127, tm12127, ep12127, em12127, dsL]

theorem tails12127 :
    exp (-((12127:ℝ)*ep12127)) ≤ scalar12127.upperTail ∧
    exp (-((12127:ℝ)*em12127)) ≤ scalar12127.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12127:ℝ)) (by norm_num [ep12127]) ?_)
      (show bp12127^8 ≤ scalar12127.upperTail by norm_num [bp12127, scalar12127])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12127, bp12127, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12127:ℝ)) (by norm_num [em12127]) ?_)
      (show bm12127^8 ≤ scalar12127.lowerTail by norm_num [bm12127, scalar12127])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12127, bm12127, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12127 :
    agent12127.root+dsL+scalar12127.worldRadius < √(1/100/aL) ∧
    2*(agent12127.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12127, agent12127, scalar12127, tp12127, tm12127, ep12127, em12127, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12127, agent12127, scalar12127, tp12127, tm12127, ep12127, em12127, dsL]

noncomputable def master12127 : MasterCertificate 12127 world12127 agent12127 :=
  master scalar12127 dsL tp12127 tm12127 ep12127 em12127
    (by norm_num [dsL]) (by norm_num [tp12127]) (by norm_num [tm12127])
    (by norm_num [ep12127]) (by norm_num [em12127])
    positive12127 negative12127 tails12127.1 tails12127.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12127.1 tailGuards12127.2

theorem preserves12127 : master12127.toScalarCertificate = scalar12127 := rfl

noncomputable def tp12128 : ℝ := (2370833309 / 10000000000)
noncomputable def tm12128 : ℝ := (-((383395637 / 625000000)))
noncomputable def ep12128 : ℝ := (5453526067389459 / 10000000000000000000)
noncomputable def em12128 : ℝ := (26293352556983231 / 50000000000000000000)
noncomputable def bp12128 : ℝ := (43746676061135647763 / 100000000000000000000)
noncomputable def bm12128 : ℝ := (45058233748236614563 / 100000000000000000000)

theorem positive12128 :
    Eplus aL (agent12128.root+dsL) scalar12128.worldRadius world12128.frame
      agent12128.frame tp12128 ≤ -ep12128 := by
  apply positive_check (eT := (116217534978334406221 / 100000000000000000000)) (y := (9903343267019835463 / 25000000000000000000)) (u := (18575850464424419733 / 12500000000000000000))
  · norm_num [world12128, agent12128, scalar12128, tp12128, tm12128, ep12128, em12128, dsL]
  · norm_num [world12128, agent12128, scalar12128, tp12128, tm12128, ep12128, em12128, dsL]
  · norm_num [world12128, agent12128, scalar12128, tp12128, tm12128, ep12128, em12128, dsL]
  · norm_num [world12128, agent12128, scalar12128, tp12128, tm12128, ep12128, em12128, dsL]
  · norm_num [world12128, agent12128, scalar12128, tp12128, tm12128, ep12128, em12128, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12128, agent12128, tp12128, tm12128, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12128, agent12128, scalar12128, tp12128, tm12128, ep12128, em12128, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12128, agent12128, tp12128, tm12128, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12128, agent12128, scalar12128, tp12128, tm12128, ep12128, em12128, dsL]

theorem negative12128 :
    Eminus aL (agent12128.root+dsL) scalar12128.worldRadius world12128.frame
      agent12128.frame tm12128 ≤ -em12128 := by
  apply negative_check (lo := (8472764342571380683 / 12500000000000000000)) (hi := (13556422948114209093 / 20000000000000000000))
    (y := (-((73312222215982897857 / 100000000000000000000)))) (u := (9608134192188239207 / 20000000000000000000))
  · norm_num [world12128, agent12128, scalar12128, tp12128, tm12128, ep12128, em12128, dsL]
  · norm_num [world12128, agent12128, scalar12128, tp12128, tm12128, ep12128, em12128, dsL]
  · norm_num [world12128, agent12128, scalar12128, tp12128, tm12128, ep12128, em12128, dsL]
  · norm_num [world12128, agent12128, scalar12128, tp12128, tm12128, ep12128, em12128, dsL]
  · norm_num [world12128, agent12128, scalar12128, tp12128, tm12128, ep12128, em12128, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12128, agent12128, tp12128, tm12128, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12128, agent12128, tp12128, tm12128, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12128, agent12128, scalar12128, tp12128, tm12128, ep12128, em12128, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12128, agent12128, tp12128, tm12128, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12128, agent12128, scalar12128, tp12128, tm12128, ep12128, em12128, dsL]

theorem tails12128 :
    exp (-((12128:ℝ)*ep12128)) ≤ scalar12128.upperTail ∧
    exp (-((12128:ℝ)*em12128)) ≤ scalar12128.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12128:ℝ)) (by norm_num [ep12128]) ?_)
      (show bp12128^8 ≤ scalar12128.upperTail by norm_num [bp12128, scalar12128])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12128, bp12128, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12128:ℝ)) (by norm_num [em12128]) ?_)
      (show bm12128^8 ≤ scalar12128.lowerTail by norm_num [bm12128, scalar12128])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12128, bm12128, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12128 :
    agent12128.root+dsL+scalar12128.worldRadius < √(1/100/aL) ∧
    2*(agent12128.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12128, agent12128, scalar12128, tp12128, tm12128, ep12128, em12128, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12128, agent12128, scalar12128, tp12128, tm12128, ep12128, em12128, dsL]

noncomputable def master12128 : MasterCertificate 12128 world12128 agent12128 :=
  master scalar12128 dsL tp12128 tm12128 ep12128 em12128
    (by norm_num [dsL]) (by norm_num [tp12128]) (by norm_num [tm12128])
    (by norm_num [ep12128]) (by norm_num [em12128])
    positive12128 negative12128 tails12128.1 tails12128.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12128.1 tailGuards12128.2

theorem preserves12128 : master12128.toScalarCertificate = scalar12128 := rfl

noncomputable def tp12129 : ℝ := (59273317 / 250000000)
noncomputable def tm12129 : ℝ := (-((3067276519 / 5000000000)))
noncomputable def ep12129 : ℝ := (54538178657910397 / 100000000000000000000)
noncomputable def em12129 : ℝ := (26294621142855883 / 50000000000000000000)
noncomputable def bp12129 : ℝ := (21870879400805915671 / 50000000000000000000)
noncomputable def bm12129 : ℝ := (45053538921437278583 / 100000000000000000000)

theorem positive12129 :
    Eplus aL (agent12129.root+dsL) scalar12129.worldRadius world12129.frame
      agent12129.frame tp12129 ≤ -ep12129 := by
  apply positive_check (eT := (23243569583407854657 / 20000000000000000000)) (y := (396140099984739297 / 1000000000000000000)) (u := (3715193756007774899 / 2500000000000000000))
  · norm_num [world12129, agent12129, scalar12129, tp12129, tm12129, ep12129, em12129, dsL]
  · norm_num [world12129, agent12129, scalar12129, tp12129, tm12129, ep12129, em12129, dsL]
  · norm_num [world12129, agent12129, scalar12129, tp12129, tm12129, ep12129, em12129, dsL]
  · norm_num [world12129, agent12129, scalar12129, tp12129, tm12129, ep12129, em12129, dsL]
  · norm_num [world12129, agent12129, scalar12129, tp12129, tm12129, ep12129, em12129, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12129, agent12129, tp12129, tm12129, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12129, agent12129, scalar12129, tp12129, tm12129, ep12129, em12129, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12129, agent12129, tp12129, tm12129, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12129, agent12129, scalar12129, tp12129, tm12129, ep12129, em12129, dsL]

theorem negative12129 :
    Eminus aL (agent12129.root+dsL) scalar12129.worldRadius world12129.frame
      agent12129.frame tm12129 ≤ -em12129 := by
  apply negative_check (lo := (16945447434471104099 / 25000000000000000000)) (hi := (67781789737884416397 / 100000000000000000000))
    (y := (-((73311833693852169077 / 100000000000000000000)))) (u := (48040857609942215989 / 100000000000000000000))
  · norm_num [world12129, agent12129, scalar12129, tp12129, tm12129, ep12129, em12129, dsL]
  · norm_num [world12129, agent12129, scalar12129, tp12129, tm12129, ep12129, em12129, dsL]
  · norm_num [world12129, agent12129, scalar12129, tp12129, tm12129, ep12129, em12129, dsL]
  · norm_num [world12129, agent12129, scalar12129, tp12129, tm12129, ep12129, em12129, dsL]
  · norm_num [world12129, agent12129, scalar12129, tp12129, tm12129, ep12129, em12129, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12129, agent12129, tp12129, tm12129, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12129, agent12129, tp12129, tm12129, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12129, agent12129, scalar12129, tp12129, tm12129, ep12129, em12129, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12129, agent12129, tp12129, tm12129, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12129, agent12129, scalar12129, tp12129, tm12129, ep12129, em12129, dsL]

theorem tails12129 :
    exp (-((12129:ℝ)*ep12129)) ≤ scalar12129.upperTail ∧
    exp (-((12129:ℝ)*em12129)) ≤ scalar12129.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12129:ℝ)) (by norm_num [ep12129]) ?_)
      (show bp12129^8 ≤ scalar12129.upperTail by norm_num [bp12129, scalar12129])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12129, bp12129, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12129:ℝ)) (by norm_num [em12129]) ?_)
      (show bm12129^8 ≤ scalar12129.lowerTail by norm_num [bm12129, scalar12129])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12129, bm12129, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12129 :
    agent12129.root+dsL+scalar12129.worldRadius < √(1/100/aL) ∧
    2*(agent12129.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12129, agent12129, scalar12129, tp12129, tm12129, ep12129, em12129, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12129, agent12129, scalar12129, tp12129, tm12129, ep12129, em12129, dsL]

noncomputable def master12129 : MasterCertificate 12129 world12129 agent12129 :=
  master scalar12129 dsL tp12129 tm12129 ep12129 em12129
    (by norm_num [dsL]) (by norm_num [tp12129]) (by norm_num [tm12129])
    (by norm_num [ep12129]) (by norm_num [em12129])
    positive12129 negative12129 tails12129.1 tails12129.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12129.1 tailGuards12129.2

theorem preserves12129 : master12129.toScalarCertificate = scalar12129 := rfl

noncomputable def tp12130 : ℝ := (2371031943 / 10000000000)
noncomputable def tm12130 : ℝ := (-((6134775893 / 10000000000)))
noncomputable def ep12130 : ℝ := (2727054727370571 / 5000000000000000000)
noncomputable def em12130 : ℝ := (13147944373244641 / 25000000000000000000)
noncomputable def bp12130 : ℝ := (10934210791185649027 / 25000000000000000000)
noncomputable def bm12130 : ℝ := (22524422819957643143 / 50000000000000000000)

theorem positive12130 :
    Eplus aL (agent12130.root+dsL) scalar12130.worldRadius world12130.frame
      agent12130.frame tp12130 ≤ -ep12130 := by
  apply positive_check (eT := (29054540024233133109 / 25000000000000000000)) (y := (39614645610420192463 / 100000000000000000000)) (u := (148608694811926497541 / 100000000000000000000))
  · norm_num [world12130, agent12130, scalar12130, tp12130, tm12130, ep12130, em12130, dsL]
  · norm_num [world12130, agent12130, scalar12130, tp12130, tm12130, ep12130, em12130, dsL]
  · norm_num [world12130, agent12130, scalar12130, tp12130, tm12130, ep12130, em12130, dsL]
  · norm_num [world12130, agent12130, scalar12130, tp12130, tm12130, ep12130, em12130, dsL]
  · norm_num [world12130, agent12130, scalar12130, tp12130, tm12130, ep12130, em12130, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12130, agent12130, tp12130, tm12130, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12130, agent12130, scalar12130, tp12130, tm12130, ep12130, em12130, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12130, agent12130, tp12130, tm12130, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12130, agent12130, scalar12130, tp12130, tm12130, ep12130, em12130, dsL]

theorem negative12130 :
    Eminus aL (agent12130.root+dsL) scalar12130.worldRadius world12130.frame
      agent12130.frame tm12130 ≤ -em12130 := by
  apply negative_check (lo := (8472683079589694363 / 12500000000000000000)) (hi := (13556292927343510981 / 20000000000000000000))
    (y := (-((73311445938821388031 / 100000000000000000000)))) (u := (9608208778229117207 / 20000000000000000000))
  · norm_num [world12130, agent12130, scalar12130, tp12130, tm12130, ep12130, em12130, dsL]
  · norm_num [world12130, agent12130, scalar12130, tp12130, tm12130, ep12130, em12130, dsL]
  · norm_num [world12130, agent12130, scalar12130, tp12130, tm12130, ep12130, em12130, dsL]
  · norm_num [world12130, agent12130, scalar12130, tp12130, tm12130, ep12130, em12130, dsL]
  · norm_num [world12130, agent12130, scalar12130, tp12130, tm12130, ep12130, em12130, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12130, agent12130, tp12130, tm12130, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12130, agent12130, tp12130, tm12130, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12130, agent12130, scalar12130, tp12130, tm12130, ep12130, em12130, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12130, agent12130, tp12130, tm12130, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12130, agent12130, scalar12130, tp12130, tm12130, ep12130, em12130, dsL]

theorem tails12130 :
    exp (-((12130:ℝ)*ep12130)) ≤ scalar12130.upperTail ∧
    exp (-((12130:ℝ)*em12130)) ≤ scalar12130.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12130:ℝ)) (by norm_num [ep12130]) ?_)
      (show bp12130^8 ≤ scalar12130.upperTail by norm_num [bp12130, scalar12130])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12130, bp12130, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12130:ℝ)) (by norm_num [em12130]) ?_)
      (show bm12130^8 ≤ scalar12130.lowerTail by norm_num [bm12130, scalar12130])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12130, bm12130, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12130 :
    agent12130.root+dsL+scalar12130.worldRadius < √(1/100/aL) ∧
    2*(agent12130.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12130, agent12130, scalar12130, tp12130, tm12130, ep12130, em12130, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12130, agent12130, scalar12130, tp12130, tm12130, ep12130, em12130, dsL]

noncomputable def master12130 : MasterCertificate 12130 world12130 agent12130 :=
  master scalar12130 dsL tp12130 tm12130 ep12130 em12130
    (by norm_num [dsL]) (by norm_num [tp12130]) (by norm_num [tm12130])
    (by norm_num [ep12130]) (by norm_num [em12130])
    positive12130 negative12130 tails12130.1 tails12130.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12130.1 tailGuards12130.2

theorem preserves12130 : master12130.toScalarCertificate = scalar12130 := rfl

noncomputable def tp12131 : ℝ := (148195701 / 625000000)
noncomputable def tm12131 : ℝ := (-((1226999703 / 2000000000)))
noncomputable def ep12131 : ℝ := (27272004377350227 / 50000000000000000000)
noncomputable def em12131 : ℝ := (52594311135099087 / 100000000000000000000)
noncomputable def bp12131 : ℝ := (43731928877034098329 / 100000000000000000000)
noncomputable def bm12131 : ℝ := (225220768154311251 / 500000000000000000)

theorem positive12131 :
    Eplus aL (agent12131.root+dsL) scalar12131.worldRadius world12131.frame
      agent12131.frame tp12131 ≤ -ep12131 := by
  apply positive_check (eT := (1815913631052583823 / 1562500000000000000)) (y := (19807641094458955023 / 50000000000000000000)) (u := (18576205103241808337 / 12500000000000000000))
  · norm_num [world12131, agent12131, scalar12131, tp12131, tm12131, ep12131, em12131, dsL]
  · norm_num [world12131, agent12131, scalar12131, tp12131, tm12131, ep12131, em12131, dsL]
  · norm_num [world12131, agent12131, scalar12131, tp12131, tm12131, ep12131, em12131, dsL]
  · norm_num [world12131, agent12131, scalar12131, tp12131, tm12131, ep12131, em12131, dsL]
  · norm_num [world12131, agent12131, scalar12131, tp12131, tm12131, ep12131, em12131, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12131, agent12131, tp12131, tm12131, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12131, agent12131, scalar12131, tp12131, tm12131, ep12131, em12131, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12131, agent12131, tp12131, tm12131, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12131, agent12131, scalar12131, tp12131, tm12131, ep12131, em12131, dsL]

theorem negative12131 :
    Eminus aL (agent12131.root+dsL) scalar12131.worldRadius world12131.frame
      agent12131.frame tm12131 ≤ -em12131 := by
  apply negative_check (lo := (8472642559602630697 / 12500000000000000000)) (hi := (67781140476821045577 / 100000000000000000000))
    (y := (-((7331105755554266309 / 10000000000000000000)))) (u := (960824609497786279 / 2000000000000000000))
  · norm_num [world12131, agent12131, scalar12131, tp12131, tm12131, ep12131, em12131, dsL]
  · norm_num [world12131, agent12131, scalar12131, tp12131, tm12131, ep12131, em12131, dsL]
  · norm_num [world12131, agent12131, scalar12131, tp12131, tm12131, ep12131, em12131, dsL]
  · norm_num [world12131, agent12131, scalar12131, tp12131, tm12131, ep12131, em12131, dsL]
  · norm_num [world12131, agent12131, scalar12131, tp12131, tm12131, ep12131, em12131, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12131, agent12131, tp12131, tm12131, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12131, agent12131, tp12131, tm12131, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12131, agent12131, scalar12131, tp12131, tm12131, ep12131, em12131, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12131, agent12131, tp12131, tm12131, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12131, agent12131, scalar12131, tp12131, tm12131, ep12131, em12131, dsL]

theorem tails12131 :
    exp (-((12131:ℝ)*ep12131)) ≤ scalar12131.upperTail ∧
    exp (-((12131:ℝ)*em12131)) ≤ scalar12131.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12131:ℝ)) (by norm_num [ep12131]) ?_)
      (show bp12131^8 ≤ scalar12131.upperTail by norm_num [bp12131, scalar12131])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12131, bp12131, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12131:ℝ)) (by norm_num [em12131]) ?_)
      (show bm12131^8 ≤ scalar12131.lowerTail by norm_num [bm12131, scalar12131])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12131, bm12131, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12131 :
    agent12131.root+dsL+scalar12131.worldRadius < √(1/100/aL) ∧
    2*(agent12131.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12131, agent12131, scalar12131, tp12131, tm12131, ep12131, em12131, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12131, agent12131, scalar12131, tp12131, tm12131, ep12131, em12131, dsL]

noncomputable def master12131 : MasterCertificate 12131 world12131 agent12131 :=
  master scalar12131 dsL tp12131 tm12131 ep12131 em12131
    (by norm_num [dsL]) (by norm_num [tp12131]) (by norm_num [tm12131])
    (by norm_num [ep12131]) (by norm_num [em12131])
    positive12131 negative12131 tails12131.1 tails12131.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12131.1 tailGuards12131.2

theorem preserves12131 : master12131.toScalarCertificate = scalar12131 := rfl

noncomputable def tp12132 : ℝ := (1185615207 / 5000000000)
noncomputable def tm12132 : ℝ := (-((6135221049 / 10000000000)))
noncomputable def ep12132 : ℝ := (27273460733697561 / 50000000000000000000)
noncomputable def em12132 : ℝ := (52596843392395897 / 100000000000000000000)
noncomputable def bp12132 : ℝ := (43727015814018497877 / 100000000000000000000)
noncomputable def bm12132 : ℝ := (11259865692770554471 / 25000000000000000000)

theorem positive12132 :
    Eplus aL (agent12132.root+dsL) scalar12132.worldRadius world12132.frame
      agent12132.frame tp12132 ≤ -ep12132 := by
  apply positive_check (eT := (58109392081071900661 / 50000000000000000000)) (y := (39615917937269857223 / 100000000000000000000)) (u := (74305292806140040411 / 50000000000000000000))
  · norm_num [world12132, agent12132, scalar12132, tp12132, tm12132, ep12132, em12132, dsL]
  · norm_num [world12132, agent12132, scalar12132, tp12132, tm12132, ep12132, em12132, dsL]
  · norm_num [world12132, agent12132, scalar12132, tp12132, tm12132, ep12132, em12132, dsL]
  · norm_num [world12132, agent12132, scalar12132, tp12132, tm12132, ep12132, em12132, dsL]
  · norm_num [world12132, agent12132, scalar12132, tp12132, tm12132, ep12132, em12132, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12132, agent12132, tp12132, tm12132, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12132, agent12132, scalar12132, tp12132, tm12132, ep12132, em12132, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12132, agent12132, tp12132, tm12132, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12132, agent12132, scalar12132, tp12132, tm12132, ep12132, em12132, dsL]

theorem negative12132 :
    Eminus aL (agent12132.root+dsL) scalar12132.worldRadius world12132.frame
      agent12132.frame tm12132 ≤ -em12132 := by
  apply negative_check (lo := (67780816635161628083 / 100000000000000000000)) (hi := (16945204158790407021 / 25000000000000000000))
    (y := (-((4581916827744208873 / 6250000000000000000)))) (u := (24020708512469598461 / 50000000000000000000))
  · norm_num [world12132, agent12132, scalar12132, tp12132, tm12132, ep12132, em12132, dsL]
  · norm_num [world12132, agent12132, scalar12132, tp12132, tm12132, ep12132, em12132, dsL]
  · norm_num [world12132, agent12132, scalar12132, tp12132, tm12132, ep12132, em12132, dsL]
  · norm_num [world12132, agent12132, scalar12132, tp12132, tm12132, ep12132, em12132, dsL]
  · norm_num [world12132, agent12132, scalar12132, tp12132, tm12132, ep12132, em12132, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12132, agent12132, tp12132, tm12132, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12132, agent12132, tp12132, tm12132, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12132, agent12132, scalar12132, tp12132, tm12132, ep12132, em12132, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12132, agent12132, tp12132, tm12132, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12132, agent12132, scalar12132, tp12132, tm12132, ep12132, em12132, dsL]

theorem tails12132 :
    exp (-((12132:ℝ)*ep12132)) ≤ scalar12132.upperTail ∧
    exp (-((12132:ℝ)*em12132)) ≤ scalar12132.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12132:ℝ)) (by norm_num [ep12132]) ?_)
      (show bp12132^8 ≤ scalar12132.upperTail by norm_num [bp12132, scalar12132])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12132, bp12132, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12132:ℝ)) (by norm_num [em12132]) ?_)
      (show bm12132^8 ≤ scalar12132.lowerTail by norm_num [bm12132, scalar12132])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12132, bm12132, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12132 :
    agent12132.root+dsL+scalar12132.worldRadius < √(1/100/aL) ∧
    2*(agent12132.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12132, agent12132, scalar12132, tp12132, tm12132, ep12132, em12132, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12132, agent12132, scalar12132, tp12132, tm12132, ep12132, em12132, dsL]

noncomputable def master12132 : MasterCertificate 12132 world12132 agent12132 :=
  master scalar12132 dsL tp12132 tm12132 ep12132 em12132
    (by norm_num [dsL]) (by norm_num [tp12132]) (by norm_num [tm12132])
    (by norm_num [ep12132]) (by norm_num [em12132])
    positive12132 negative12132 tails12132.1 tails12132.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12132.1 tailGuards12132.2

theorem preserves12132 : master12132.toScalarCertificate = scalar12132 := rfl

noncomputable def tp12133 : ℝ := (2371329631 / 10000000000)
noncomputable def tm12133 : ℝ := (-((3067721733 / 5000000000)))
noncomputable def ep12133 : ℝ := (27274916267031261 / 50000000000000000000)
noncomputable def em12133 : ℝ := (10519874821588589 / 20000000000000000000)
noncomputable def bp12133 : ℝ := (43722104076067351659 / 100000000000000000000)
noncomputable def bm12133 : ℝ := (45034773167733627857 / 100000000000000000000)

theorem positive12133 :
    Eplus aL (agent12133.root+dsL) scalar12133.worldRadius world12133.frame
      agent12133.frame tp12133 ≤ -ep12133 := by
  apply positive_check (eT := (116219096113713877993 / 100000000000000000000)) (y := (39616554706406264499 / 100000000000000000000)) (u := (37152882980408898423 / 25000000000000000000))
  · norm_num [world12133, agent12133, scalar12133, tp12133, tm12133, ep12133, em12133, dsL]
  · norm_num [world12133, agent12133, scalar12133, tp12133, tm12133, ep12133, em12133, dsL]
  · norm_num [world12133, agent12133, scalar12133, tp12133, tm12133, ep12133, em12133, dsL]
  · norm_num [world12133, agent12133, scalar12133, tp12133, tm12133, ep12133, em12133, dsL]
  · norm_num [world12133, agent12133, scalar12133, tp12133, tm12133, ep12133, em12133, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12133, agent12133, tp12133, tm12133, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12133, agent12133, scalar12133, tp12133, tm12133, ep12133, em12133, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12133, agent12133, tp12133, tm12133, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12133, agent12133, scalar12133, tp12133, tm12133, ep12133, em12133, dsL]

theorem negative12133 :
    Eminus aL (agent12133.root+dsL) scalar12133.worldRadius world12133.frame
      agent12133.frame tm12133 ≤ -em12133 := by
  apply negative_check (lo := (67780493236370988327 / 100000000000000000000)) (hi := (8472561654546373541 / 12500000000000000000))
    (y := (-((73310281015578863603 / 100000000000000000000)))) (u := (24020801767845766859 / 50000000000000000000))
  · norm_num [world12133, agent12133, scalar12133, tp12133, tm12133, ep12133, em12133, dsL]
  · norm_num [world12133, agent12133, scalar12133, tp12133, tm12133, ep12133, em12133, dsL]
  · norm_num [world12133, agent12133, scalar12133, tp12133, tm12133, ep12133, em12133, dsL]
  · norm_num [world12133, agent12133, scalar12133, tp12133, tm12133, ep12133, em12133, dsL]
  · norm_num [world12133, agent12133, scalar12133, tp12133, tm12133, ep12133, em12133, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12133, agent12133, tp12133, tm12133, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12133, agent12133, tp12133, tm12133, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12133, agent12133, scalar12133, tp12133, tm12133, ep12133, em12133, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12133, agent12133, tp12133, tm12133, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12133, agent12133, scalar12133, tp12133, tm12133, ep12133, em12133, dsL]

theorem tails12133 :
    exp (-((12133:ℝ)*ep12133)) ≤ scalar12133.upperTail ∧
    exp (-((12133:ℝ)*em12133)) ≤ scalar12133.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12133:ℝ)) (by norm_num [ep12133]) ?_)
      (show bp12133^8 ≤ scalar12133.upperTail by norm_num [bp12133, scalar12133])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12133, bp12133, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12133:ℝ)) (by norm_num [em12133]) ?_)
      (show bm12133^8 ≤ scalar12133.lowerTail by norm_num [bm12133, scalar12133])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12133, bm12133, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12133 :
    agent12133.root+dsL+scalar12133.worldRadius < √(1/100/aL) ∧
    2*(agent12133.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12133, agent12133, scalar12133, tp12133, tm12133, ep12133, em12133, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12133, agent12133, scalar12133, tp12133, tm12133, ep12133, em12133, dsL]

noncomputable def master12133 : MasterCertificate 12133 world12133 agent12133 :=
  master scalar12133 dsL tp12133 tm12133 ep12133 em12133
    (by norm_num [dsL]) (by norm_num [tp12133]) (by norm_num [tm12133])
    (by norm_num [ep12133]) (by norm_num [em12133])
    positive12133 negative12133 tails12133.1 tails12133.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12133.1 tailGuards12133.2

theorem preserves12133 : master12133.toScalarCertificate = scalar12133 := rfl

end BstLean.Part281
