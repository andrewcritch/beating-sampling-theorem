import BstLean.Part261Checker
import BstLean.Part268Scalar14
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12700 : ℝ := (2316496897 / 10000000000)
noncomputable def tm12700 : ℝ := (-((757865267 / 1250000000)))
noncomputable def ep12700 : ℝ := (51424892312653373 / 100000000000000000000)
noncomputable def em12700 : ℝ := (50109858254174451 / 100000000000000000000)
noncomputable def bp12700 : ℝ := (22101662677389596349 / 50000000000000000000)
noncomputable def bm12700 : ℝ := (45135820898154066903 / 100000000000000000000)

theorem positive12700 :
    Eplus aL (agent12700.root+dsL) scalar12700.worldRadius world12700.frame
      agent12700.frame tp12700 ≤ -ep12700 := by
  apply positive_check (eT := (2889885739241590703 / 2500000000000000000)) (y := (18930659980751940803 / 50000000000000000000)) (u := (36506452452423481559 / 25000000000000000000))
  · norm_num [world12700, agent12700, scalar12700, tp12700, tm12700, ep12700, em12700, dsL]
  · norm_num [world12700, agent12700, scalar12700, tp12700, tm12700, ep12700, em12700, dsL]
  · norm_num [world12700, agent12700, scalar12700, tp12700, tm12700, ep12700, em12700, dsL]
  · norm_num [world12700, agent12700, scalar12700, tp12700, tm12700, ep12700, em12700, dsL]
  · norm_num [world12700, agent12700, scalar12700, tp12700, tm12700, ep12700, em12700, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12700, agent12700, tp12700, tm12700, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12700, agent12700, scalar12700, tp12700, tm12700, ep12700, em12700, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12700, agent12700, tp12700, tm12700, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12700, agent12700, scalar12700, tp12700, tm12700, ep12700, em12700, dsL]

theorem negative12700 :
    Eminus aL (agent12700.root+dsL) scalar12700.worldRadius world12700.frame
      agent12700.frame tm12700 ≤ -em12700 := by
  apply negative_check (lo := (68433165582556986951 / 100000000000000000000)) (hi := (8554145697819623369 / 12500000000000000000))
    (y := (-((14337513783954206649 / 20000000000000000000)))) (u := (12206884985978212151 / 25000000000000000000))
  · norm_num [world12700, agent12700, scalar12700, tp12700, tm12700, ep12700, em12700, dsL]
  · norm_num [world12700, agent12700, scalar12700, tp12700, tm12700, ep12700, em12700, dsL]
  · norm_num [world12700, agent12700, scalar12700, tp12700, tm12700, ep12700, em12700, dsL]
  · norm_num [world12700, agent12700, scalar12700, tp12700, tm12700, ep12700, em12700, dsL]
  · norm_num [world12700, agent12700, scalar12700, tp12700, tm12700, ep12700, em12700, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12700, agent12700, tp12700, tm12700, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12700, agent12700, tp12700, tm12700, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12700, agent12700, scalar12700, tp12700, tm12700, ep12700, em12700, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12700, agent12700, tp12700, tm12700, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12700, agent12700, scalar12700, tp12700, tm12700, ep12700, em12700, dsL]

theorem tails12700 :
    exp (-((12700:ℝ)*ep12700)) ≤ scalar12700.upperTail ∧
    exp (-((12700:ℝ)*em12700)) ≤ scalar12700.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12700:ℝ)) (by norm_num [ep12700]) ?_)
      (show bp12700^8 ≤ scalar12700.upperTail by norm_num [bp12700, scalar12700])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12700, bp12700, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12700:ℝ)) (by norm_num [em12700]) ?_)
      (show bm12700^8 ≤ scalar12700.lowerTail by norm_num [bm12700, scalar12700])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12700, bm12700, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12700 :
    agent12700.root+dsL+scalar12700.worldRadius < √(1/100/aL) ∧
    2*(agent12700.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12700, agent12700, scalar12700, tp12700, tm12700, ep12700, em12700, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12700, agent12700, scalar12700, tp12700, tm12700, ep12700, em12700, dsL]

noncomputable def master12700 : MasterCertificate 12700 world12700 agent12700 :=
  master scalar12700 dsL tp12700 tm12700 ep12700 em12700
    (by norm_num [dsL]) (by norm_num [tp12700]) (by norm_num [tm12700])
    (by norm_num [ep12700]) (by norm_num [em12700])
    positive12700 negative12700 tails12700.1 tails12700.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12700.1 tailGuards12700.2

theorem preserves12700 : master12700.toScalarCertificate = scalar12700 := rfl

noncomputable def tp12701 : ℝ := (1158291089 / 5000000000)
noncomputable def tm12701 : ℝ := (-((6063105123 / 10000000000)))
noncomputable def ep12701 : ℝ := (6428439344848419 / 12500000000000000000)
noncomputable def em12701 : ℝ := (50112108147822179 / 100000000000000000000)
noncomputable def bp12701 : ℝ := (22099321887710579663 / 50000000000000000000)
noncomputable def bm12701 : ℝ := (11282845420912816823 / 25000000000000000000)

theorem positive12701 :
    Eplus aL (agent12701.root+dsL) scalar12701.worldRadius world12701.frame
      agent12701.frame tp12701 ≤ -ep12701 := by
  apply positive_check (eT := (57797837822026010021 / 50000000000000000000)) (y := (37862113404718364009 / 100000000000000000000)) (u := (73013484223084904701 / 50000000000000000000))
  · norm_num [world12701, agent12701, scalar12701, tp12701, tm12701, ep12701, em12701, dsL]
  · norm_num [world12701, agent12701, scalar12701, tp12701, tm12701, ep12701, em12701, dsL]
  · norm_num [world12701, agent12701, scalar12701, tp12701, tm12701, ep12701, em12701, dsL]
  · norm_num [world12701, agent12701, scalar12701, tp12701, tm12701, ep12701, em12701, dsL]
  · norm_num [world12701, agent12701, scalar12701, tp12701, tm12701, ep12701, em12701, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12701, agent12701, tp12701, tm12701, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12701, agent12701, scalar12701, tp12701, tm12701, ep12701, em12701, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12701, agent12701, tp12701, tm12701, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12701, agent12701, scalar12701, tp12701, tm12701, ep12701, em12701, dsL]

theorem negative12701 :
    Eminus aL (agent12701.root+dsL) scalar12701.worldRadius world12701.frame
      agent12701.frame tm12701 ≤ -em12701 := by
  apply negative_check (lo := (68432956485474414089 / 100000000000000000000)) (hi := (6843295648547441409 / 10000000000000000000))
    (y := (-((8960955031547269361 / 12500000000000000000)))) (u := (9765501022793607161 / 20000000000000000000))
  · norm_num [world12701, agent12701, scalar12701, tp12701, tm12701, ep12701, em12701, dsL]
  · norm_num [world12701, agent12701, scalar12701, tp12701, tm12701, ep12701, em12701, dsL]
  · norm_num [world12701, agent12701, scalar12701, tp12701, tm12701, ep12701, em12701, dsL]
  · norm_num [world12701, agent12701, scalar12701, tp12701, tm12701, ep12701, em12701, dsL]
  · norm_num [world12701, agent12701, scalar12701, tp12701, tm12701, ep12701, em12701, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12701, agent12701, tp12701, tm12701, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12701, agent12701, tp12701, tm12701, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12701, agent12701, scalar12701, tp12701, tm12701, ep12701, em12701, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12701, agent12701, tp12701, tm12701, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12701, agent12701, scalar12701, tp12701, tm12701, ep12701, em12701, dsL]

theorem tails12701 :
    exp (-((12701:ℝ)*ep12701)) ≤ scalar12701.upperTail ∧
    exp (-((12701:ℝ)*em12701)) ≤ scalar12701.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12701:ℝ)) (by norm_num [ep12701]) ?_)
      (show bp12701^8 ≤ scalar12701.upperTail by norm_num [bp12701, scalar12701])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12701, bp12701, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12701:ℝ)) (by norm_num [em12701]) ?_)
      (show bm12701^8 ≤ scalar12701.lowerTail by norm_num [bm12701, scalar12701])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12701, bm12701, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12701 :
    agent12701.root+dsL+scalar12701.worldRadius < √(1/100/aL) ∧
    2*(agent12701.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12701, agent12701, scalar12701, tp12701, tm12701, ep12701, em12701, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12701, agent12701, scalar12701, tp12701, tm12701, ep12701, em12701, dsL]

noncomputable def master12701 : MasterCertificate 12701 world12701 agent12701 :=
  master scalar12701 dsL tp12701 tm12701 ep12701 em12701
    (by norm_num [dsL]) (by norm_num [tp12701]) (by norm_num [tm12701])
    (by norm_num [ep12701]) (by norm_num [em12701])
    positive12701 negative12701 tails12701.1 tails12701.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12701.1 tailGuards12701.2

theorem preserves12701 : master12701.toScalarCertificate = scalar12701 := rfl

noncomputable def tp12702 : ℝ := (579166867 / 2500000000)
noncomputable def tm12702 : ℝ := (-((3031644121 / 5000000000)))
noncomputable def ep12702 : ℝ := (10286027161595223 / 20000000000000000000)
noncomputable def em12702 : ℝ := (25057178370101039 / 50000000000000000000)
noncomputable def bp12702 : ℝ := (172632669462386803 / 390625000000000000)
noncomputable def bm12702 : ℝ := (1805077743371639601 / 4000000000000000000)

theorem positive12702 :
    Eplus aL (agent12702.root+dsL) scalar12702.worldRadius world12702.frame
      agent12702.frame tp12702 ≤ -ep12702 := by
  apply positive_check (eT := (23119184363252444169 / 20000000000000000000)) (y := (9465726868804557341 / 25000000000000000000)) (u := (146028128007851950657 / 100000000000000000000))
  · norm_num [world12702, agent12702, scalar12702, tp12702, tm12702, ep12702, em12702, dsL]
  · norm_num [world12702, agent12702, scalar12702, tp12702, tm12702, ep12702, em12702, dsL]
  · norm_num [world12702, agent12702, scalar12702, tp12702, tm12702, ep12702, em12702, dsL]
  · norm_num [world12702, agent12702, scalar12702, tp12702, tm12702, ep12702, em12702, dsL]
  · norm_num [world12702, agent12702, scalar12702, tp12702, tm12702, ep12702, em12702, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12702, agent12702, tp12702, tm12702, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12702, agent12702, scalar12702, tp12702, tm12702, ep12702, em12702, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12702, agent12702, tp12702, tm12702, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12702, agent12702, scalar12702, tp12702, tm12702, ep12702, em12702, dsL]

theorem negative12702 :
    Eminus aL (agent12702.root+dsL) scalar12702.worldRadius world12702.frame
      agent12702.frame tm12702 ≤ -em12702 := by
  apply negative_check (lo := (17108186691597442491 / 25000000000000000000)) (hi := (13686549353277953993 / 20000000000000000000))
    (y := (-((17921928429287932843 / 25000000000000000000)))) (u := (48827469242965137059 / 100000000000000000000))
  · norm_num [world12702, agent12702, scalar12702, tp12702, tm12702, ep12702, em12702, dsL]
  · norm_num [world12702, agent12702, scalar12702, tp12702, tm12702, ep12702, em12702, dsL]
  · norm_num [world12702, agent12702, scalar12702, tp12702, tm12702, ep12702, em12702, dsL]
  · norm_num [world12702, agent12702, scalar12702, tp12702, tm12702, ep12702, em12702, dsL]
  · norm_num [world12702, agent12702, scalar12702, tp12702, tm12702, ep12702, em12702, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12702, agent12702, tp12702, tm12702, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12702, agent12702, tp12702, tm12702, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12702, agent12702, scalar12702, tp12702, tm12702, ep12702, em12702, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12702, agent12702, tp12702, tm12702, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12702, agent12702, scalar12702, tp12702, tm12702, ep12702, em12702, dsL]

theorem tails12702 :
    exp (-((12702:ℝ)*ep12702)) ≤ scalar12702.upperTail ∧
    exp (-((12702:ℝ)*em12702)) ≤ scalar12702.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12702:ℝ)) (by norm_num [ep12702]) ?_)
      (show bp12702^8 ≤ scalar12702.upperTail by norm_num [bp12702, scalar12702])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12702, bp12702, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12702:ℝ)) (by norm_num [em12702]) ?_)
      (show bm12702^8 ≤ scalar12702.lowerTail by norm_num [bm12702, scalar12702])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12702, bm12702, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12702 :
    agent12702.root+dsL+scalar12702.worldRadius < √(1/100/aL) ∧
    2*(agent12702.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12702, agent12702, scalar12702, tp12702, tm12702, ep12702, em12702, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12702, agent12702, scalar12702, tp12702, tm12702, ep12702, em12702, dsL]

noncomputable def master12702 : MasterCertificate 12702 world12702 agent12702 :=
  master scalar12702 dsL tp12702 tm12702 ep12702 em12702
    (by norm_num [dsL]) (by norm_num [tp12702]) (by norm_num [tm12702])
    (by norm_num [ep12702]) (by norm_num [em12702])
    positive12702 negative12702 tails12702.1 tails12702.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12702.1 tailGuards12702.2

theorem preserves12702 : master12702.toScalarCertificate = scalar12702 := rfl

noncomputable def tp12703 : ℝ := (144797043 / 625000000)
noncomputable def tm12703 : ℝ := (-((6063471077 / 10000000000)))
noncomputable def ep12703 : ℝ := (6429094433116307 / 12500000000000000000)
noncomputable def em12703 : ℝ := (25058302017682003 / 50000000000000000000)
noncomputable def bp12703 : ℝ := (44189284172282973773 / 100000000000000000000)
noncomputable def bm12703 : ℝ := (2820156662321789109 / 6250000000000000000)

theorem positive12703 :
    Eplus aL (agent12703.root+dsL) scalar12703.worldRadius world12703.frame
      agent12703.frame tp12703 ≤ -ep12703 := by
  apply positive_check (eT := (115596167514926285103 / 100000000000000000000)) (y := (946592519647571469 / 2500000000000000000)) (u := (18253660808648636743 / 12500000000000000000))
  · norm_num [world12703, agent12703, scalar12703, tp12703, tm12703, ep12703, em12703, dsL]
  · norm_num [world12703, agent12703, scalar12703, tp12703, tm12703, ep12703, em12703, dsL]
  · norm_num [world12703, agent12703, scalar12703, tp12703, tm12703, ep12703, em12703, dsL]
  · norm_num [world12703, agent12703, scalar12703, tp12703, tm12703, ep12703, em12703, dsL]
  · norm_num [world12703, agent12703, scalar12703, tp12703, tm12703, ep12703, em12703, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12703, agent12703, tp12703, tm12703, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12703, agent12703, scalar12703, tp12703, tm12703, ep12703, em12703, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12703, agent12703, tp12703, tm12703, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12703, agent12703, scalar12703, tp12703, tm12703, ep12703, em12703, dsL]

theorem negative12703 :
    Eminus aL (agent12703.root+dsL) scalar12703.worldRadius world12703.frame
      agent12703.frame tm12703 ≤ -em12703 := by
  apply negative_check (lo := (68432538206374291807 / 100000000000000000000)) (hi := (2138516818949196619 / 3125000000000000000))
    (y := (-((35843892634705778897 / 50000000000000000000)))) (u := (24413717152909988413 / 50000000000000000000))
  · norm_num [world12703, agent12703, scalar12703, tp12703, tm12703, ep12703, em12703, dsL]
  · norm_num [world12703, agent12703, scalar12703, tp12703, tm12703, ep12703, em12703, dsL]
  · norm_num [world12703, agent12703, scalar12703, tp12703, tm12703, ep12703, em12703, dsL]
  · norm_num [world12703, agent12703, scalar12703, tp12703, tm12703, ep12703, em12703, dsL]
  · norm_num [world12703, agent12703, scalar12703, tp12703, tm12703, ep12703, em12703, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12703, agent12703, tp12703, tm12703, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12703, agent12703, tp12703, tm12703, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12703, agent12703, scalar12703, tp12703, tm12703, ep12703, em12703, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12703, agent12703, tp12703, tm12703, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12703, agent12703, scalar12703, tp12703, tm12703, ep12703, em12703, dsL]

theorem tails12703 :
    exp (-((12703:ℝ)*ep12703)) ≤ scalar12703.upperTail ∧
    exp (-((12703:ℝ)*em12703)) ≤ scalar12703.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12703:ℝ)) (by norm_num [ep12703]) ?_)
      (show bp12703^8 ≤ scalar12703.upperTail by norm_num [bp12703, scalar12703])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12703, bp12703, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12703:ℝ)) (by norm_num [em12703]) ?_)
      (show bm12703^8 ≤ scalar12703.lowerTail by norm_num [bm12703, scalar12703])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12703, bm12703, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12703 :
    agent12703.root+dsL+scalar12703.worldRadius < √(1/100/aL) ∧
    2*(agent12703.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12703, agent12703, scalar12703, tp12703, tm12703, ep12703, em12703, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12703, agent12703, scalar12703, tp12703, tm12703, ep12703, em12703, dsL]

noncomputable def master12703 : MasterCertificate 12703 world12703 agent12703 :=
  master scalar12703 dsL tp12703 tm12703 ep12703 em12703
    (by norm_num [dsL]) (by norm_num [tp12703]) (by norm_num [tm12703])
    (by norm_num [ep12703]) (by norm_num [em12703])
    positive12703 negative12703 tails12703.1 tails12703.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12703.1 tailGuards12703.2

theorem preserves12703 : master12703.toScalarCertificate = scalar12703 := rfl

noncomputable def tp12704 : ℝ := (2316837923 / 10000000000)
noncomputable def tm12704 : ℝ := (-((6063653833 / 10000000000)))
noncomputable def ep12704 : ℝ := (1285884346674799 / 2500000000000000000)
noncomputable def em12704 : ℝ := (12529712544435823 / 25000000000000000000)
noncomputable def bp12704 : ℝ := (5523075756093869527 / 12500000000000000000)
noncomputable def bm12704 : ℝ := (22559035309358552543 / 50000000000000000000)

theorem positive12704 :
    Eplus aL (agent12704.root+dsL) scalar12704.worldRadius world12704.frame
      agent12704.frame tp12704 ≤ -ep12704 := by
  apply positive_check (eT := (11559641335477546057 / 10000000000000000000)) (y := (37864494677124777201 / 100000000000000000000)) (u := (29206089157495531989 / 20000000000000000000))
  · norm_num [world12704, agent12704, scalar12704, tp12704, tm12704, ep12704, em12704, dsL]
  · norm_num [world12704, agent12704, scalar12704, tp12704, tm12704, ep12704, em12704, dsL]
  · norm_num [world12704, agent12704, scalar12704, tp12704, tm12704, ep12704, em12704, dsL]
  · norm_num [world12704, agent12704, scalar12704, tp12704, tm12704, ep12704, em12704, dsL]
  · norm_num [world12704, agent12704, scalar12704, tp12704, tm12704, ep12704, em12704, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12704, agent12704, tp12704, tm12704, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12704, agent12704, scalar12704, tp12704, tm12704, ep12704, em12704, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12704, agent12704, tp12704, tm12704, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12704, agent12704, scalar12704, tp12704, tm12704, ep12704, em12704, dsL]

theorem negative12704 :
    Eminus aL (agent12704.root+dsL) scalar12704.worldRadius world12704.frame
      agent12704.frame tm12704 ≤ -em12704 := by
  apply negative_check (lo := (8554041240962014913 / 12500000000000000000)) (hi := (13686465985539223861 / 20000000000000000000))
    (y := (-((71687856614517880559 / 100000000000000000000)))) (u := (48827399469847483543 / 100000000000000000000))
  · norm_num [world12704, agent12704, scalar12704, tp12704, tm12704, ep12704, em12704, dsL]
  · norm_num [world12704, agent12704, scalar12704, tp12704, tm12704, ep12704, em12704, dsL]
  · norm_num [world12704, agent12704, scalar12704, tp12704, tm12704, ep12704, em12704, dsL]
  · norm_num [world12704, agent12704, scalar12704, tp12704, tm12704, ep12704, em12704, dsL]
  · norm_num [world12704, agent12704, scalar12704, tp12704, tm12704, ep12704, em12704, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12704, agent12704, tp12704, tm12704, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12704, agent12704, tp12704, tm12704, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12704, agent12704, scalar12704, tp12704, tm12704, ep12704, em12704, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12704, agent12704, tp12704, tm12704, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12704, agent12704, scalar12704, tp12704, tm12704, ep12704, em12704, dsL]

theorem tails12704 :
    exp (-((12704:ℝ)*ep12704)) ≤ scalar12704.upperTail ∧
    exp (-((12704:ℝ)*em12704)) ≤ scalar12704.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12704:ℝ)) (by norm_num [ep12704]) ?_)
      (show bp12704^8 ≤ scalar12704.upperTail by norm_num [bp12704, scalar12704])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12704, bp12704, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12704:ℝ)) (by norm_num [em12704]) ?_)
      (show bm12704^8 ≤ scalar12704.lowerTail by norm_num [bm12704, scalar12704])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12704, bm12704, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12704 :
    agent12704.root+dsL+scalar12704.worldRadius < √(1/100/aL) ∧
    2*(agent12704.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12704, agent12704, scalar12704, tp12704, tm12704, ep12704, em12704, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12704, agent12704, scalar12704, tp12704, tm12704, ep12704, em12704, dsL]

noncomputable def master12704 : MasterCertificate 12704 world12704 agent12704 :=
  master scalar12704 dsL tp12704 tm12704 ep12704 em12704
    (by norm_num [dsL]) (by norm_num [tp12704]) (by norm_num [tm12704])
    (by norm_num [ep12704]) (by norm_num [em12704])
    positive12704 negative12704 tails12704.1 tails12704.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12704.1 tailGuards12704.2

theorem preserves12704 : master12704.toScalarCertificate = scalar12704 := rfl

noncomputable def tp12705 : ℝ := (2316923031 / 10000000000)
noncomputable def tm12705 : ℝ := (-((1515959099 / 2500000000)))
noncomputable def ep12705 : ℝ := (51437990405168751 / 100000000000000000000)
noncomputable def em12705 : ℝ := (25060547293257589 / 50000000000000000000)
noncomputable def bp12705 : ℝ := (44179929439031170671 / 100000000000000000000)
noncomputable def bm12705 : ℝ := (4511363606511796989 / 10000000000000000000)

theorem positive12705 :
    Eplus aL (agent12705.root+dsL) scalar12705.worldRadius world12705.frame
      agent12705.frame tp12705 ≤ -ep12705 := by
  apply positive_check (eT := (57798329154473863769 / 50000000000000000000)) (y := (9466321714117112589 / 25000000000000000000)) (u := (146031602615086730799 / 100000000000000000000))
  · norm_num [world12705, agent12705, scalar12705, tp12705, tm12705, ep12705, em12705, dsL]
  · norm_num [world12705, agent12705, scalar12705, tp12705, tm12705, ep12705, em12705, dsL]
  · norm_num [world12705, agent12705, scalar12705, tp12705, tm12705, ep12705, em12705, dsL]
  · norm_num [world12705, agent12705, scalar12705, tp12705, tm12705, ep12705, em12705, dsL]
  · norm_num [world12705, agent12705, scalar12705, tp12705, tm12705, ep12705, em12705, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12705, agent12705, tp12705, tm12705, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12705, agent12705, scalar12705, tp12705, tm12705, ep12705, em12705, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12705, agent12705, tp12705, tm12705, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12705, agent12705, scalar12705, tp12705, tm12705, ep12705, em12705, dsL]

theorem negative12705 :
    Eminus aL (agent12705.root+dsL) scalar12705.worldRadius world12705.frame
      agent12705.frame tm12705 ≤ -em12705 := by
  apply negative_check (lo := (8554015302297152703 / 12500000000000000000)) (hi := (547456979347017773 / 800000000000000000))
    (y := (-((35843963401549731549 / 50000000000000000000)))) (u := (48827365198600399269 / 100000000000000000000))
  · norm_num [world12705, agent12705, scalar12705, tp12705, tm12705, ep12705, em12705, dsL]
  · norm_num [world12705, agent12705, scalar12705, tp12705, tm12705, ep12705, em12705, dsL]
  · norm_num [world12705, agent12705, scalar12705, tp12705, tm12705, ep12705, em12705, dsL]
  · norm_num [world12705, agent12705, scalar12705, tp12705, tm12705, ep12705, em12705, dsL]
  · norm_num [world12705, agent12705, scalar12705, tp12705, tm12705, ep12705, em12705, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12705, agent12705, tp12705, tm12705, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12705, agent12705, tp12705, tm12705, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12705, agent12705, scalar12705, tp12705, tm12705, ep12705, em12705, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12705, agent12705, tp12705, tm12705, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12705, agent12705, scalar12705, tp12705, tm12705, ep12705, em12705, dsL]

theorem tails12705 :
    exp (-((12705:ℝ)*ep12705)) ≤ scalar12705.upperTail ∧
    exp (-((12705:ℝ)*em12705)) ≤ scalar12705.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12705:ℝ)) (by norm_num [ep12705]) ?_)
      (show bp12705^8 ≤ scalar12705.upperTail by norm_num [bp12705, scalar12705])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12705, bp12705, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12705:ℝ)) (by norm_num [em12705]) ?_)
      (show bm12705^8 ≤ scalar12705.lowerTail by norm_num [bm12705, scalar12705])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12705, bm12705, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12705 :
    agent12705.root+dsL+scalar12705.worldRadius < √(1/100/aL) ∧
    2*(agent12705.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12705, agent12705, scalar12705, tp12705, tm12705, ep12705, em12705, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12705, agent12705, scalar12705, tp12705, tm12705, ep12705, em12705, dsL]

noncomputable def master12705 : MasterCertificate 12705 world12705 agent12705 :=
  master scalar12705 dsL tp12705 tm12705 ep12705 em12705
    (by norm_num [dsL]) (by norm_num [tp12705]) (by norm_num [tm12705])
    (by norm_num [ep12705]) (by norm_num [em12705])
    positive12705 negative12705 tails12705.1 tails12705.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12705.1 tailGuards12705.2

theorem preserves12705 : master12705.toScalarCertificate = scalar12705 := rfl

noncomputable def tp12706 : ℝ := (1158504081 / 5000000000)
noncomputable def tm12706 : ℝ := (-((6064018967 / 10000000000)))
noncomputable def ep12706 : ℝ := (5144060649469783 / 10000000000000000000)
noncomputable def em12706 : ℝ := (50123338571424569 / 100000000000000000000)
noncomputable def bp12706 : ℝ := (22087626675053595007 / 50000000000000000000)
noncomputable def bm12706 : ℝ := (45109201997947374863 / 100000000000000000000)

theorem positive12706 :
    Eplus aL (agent12706.root+dsL) scalar12706.worldRadius world12706.frame
      agent12706.frame tp12706 ≤ -ep12706 := by
  apply positive_check (eT := (57798451731070919887 / 50000000000000000000)) (y := (18933039905134821297 / 50000000000000000000)) (u := (14603276058282167759 / 10000000000000000000))
  · norm_num [world12706, agent12706, scalar12706, tp12706, tm12706, ep12706, em12706, dsL]
  · norm_num [world12706, agent12706, scalar12706, tp12706, tm12706, ep12706, em12706, dsL]
  · norm_num [world12706, agent12706, scalar12706, tp12706, tm12706, ep12706, em12706, dsL]
  · norm_num [world12706, agent12706, scalar12706, tp12706, tm12706, ep12706, em12706, dsL]
  · norm_num [world12706, agent12706, scalar12706, tp12706, tm12706, ep12706, em12706, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12706, agent12706, tp12706, tm12706, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12706, agent12706, scalar12706, tp12706, tm12706, ep12706, em12706, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12706, agent12706, tp12706, tm12706, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12706, agent12706, scalar12706, tp12706, tm12706, ep12706, em12706, dsL]

theorem negative12706 :
    Eminus aL (agent12706.root+dsL) scalar12706.worldRadius world12706.frame
      agent12706.frame tm12706 ≤ -em12706 := by
  apply negative_check (lo := (68431914817965204917 / 100000000000000000000)) (hi := (34215957408982602459 / 50000000000000000000))
    (y := (-((35843999086651408079 / 50000000000000000000)))) (u := (6103416293802875087 / 12500000000000000000))
  · norm_num [world12706, agent12706, scalar12706, tp12706, tm12706, ep12706, em12706, dsL]
  · norm_num [world12706, agent12706, scalar12706, tp12706, tm12706, ep12706, em12706, dsL]
  · norm_num [world12706, agent12706, scalar12706, tp12706, tm12706, ep12706, em12706, dsL]
  · norm_num [world12706, agent12706, scalar12706, tp12706, tm12706, ep12706, em12706, dsL]
  · norm_num [world12706, agent12706, scalar12706, tp12706, tm12706, ep12706, em12706, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12706, agent12706, tp12706, tm12706, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12706, agent12706, tp12706, tm12706, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12706, agent12706, scalar12706, tp12706, tm12706, ep12706, em12706, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12706, agent12706, tp12706, tm12706, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12706, agent12706, scalar12706, tp12706, tm12706, ep12706, em12706, dsL]

theorem tails12706 :
    exp (-((12706:ℝ)*ep12706)) ≤ scalar12706.upperTail ∧
    exp (-((12706:ℝ)*em12706)) ≤ scalar12706.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12706:ℝ)) (by norm_num [ep12706]) ?_)
      (show bp12706^8 ≤ scalar12706.upperTail by norm_num [bp12706, scalar12706])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12706, bp12706, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12706:ℝ)) (by norm_num [em12706]) ?_)
      (show bm12706^8 ≤ scalar12706.lowerTail by norm_num [bm12706, scalar12706])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12706, bm12706, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12706 :
    agent12706.root+dsL+scalar12706.worldRadius < √(1/100/aL) ∧
    2*(agent12706.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12706, agent12706, scalar12706, tp12706, tm12706, ep12706, em12706, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12706, agent12706, scalar12706, tp12706, tm12706, ep12706, em12706, dsL]

noncomputable def master12706 : MasterCertificate 12706 world12706 agent12706 :=
  master scalar12706 dsL tp12706 tm12706 ep12706 em12706
    (by norm_num [dsL]) (by norm_num [tp12706]) (by norm_num [tm12706])
    (by norm_num [ep12706]) (by norm_num [em12706])
    positive12706 negative12706 tails12706.1 tails12706.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12706.1 tailGuards12706.2

theorem preserves12706 : master12706.toScalarCertificate = scalar12706 := rfl

noncomputable def tp12707 : ℝ := (1158546603 / 5000000000)
noncomputable def tm12707 : ℝ := (-((3032100679 / 5000000000)))
noncomputable def ep12707 : ℝ := (25721610195314263 / 50000000000000000000)
noncomputable def em12707 : ℝ := (50125580534625947 / 100000000000000000000)
noncomputable def bp12707 : ℝ := (5521322375780050473 / 12500000000000000000)
noncomputable def bm12707 : ℝ := (22552384780984160409 / 50000000000000000000)

theorem positive12707 :
    Eplus aL (agent12707.root+dsL) scalar12707.worldRadius world12707.frame
      agent12707.frame tp12707 ≤ -ep12707 := by
  apply positive_check (eT := (11559714801895042903 / 10000000000000000000)) (y := (18933435825689652921 / 50000000000000000000)) (u := (36508479233707944433 / 25000000000000000000))
  · norm_num [world12707, agent12707, scalar12707, tp12707, tm12707, ep12707, em12707, dsL]
  · norm_num [world12707, agent12707, scalar12707, tp12707, tm12707, ep12707, em12707, dsL]
  · norm_num [world12707, agent12707, scalar12707, tp12707, tm12707, ep12707, em12707, dsL]
  · norm_num [world12707, agent12707, scalar12707, tp12707, tm12707, ep12707, em12707, dsL]
  · norm_num [world12707, agent12707, scalar12707, tp12707, tm12707, ep12707, em12707, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12707, agent12707, tp12707, tm12707, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12707, agent12707, scalar12707, tp12707, tm12707, ep12707, em12707, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12707, agent12707, tp12707, tm12707, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12707, agent12707, scalar12707, tp12707, tm12707, ep12707, em12707, dsL]

theorem negative12707 :
    Eminus aL (agent12707.root+dsL) scalar12707.worldRadius world12707.frame
      agent12707.frame tm12707 ≤ -em12707 := by
  apply negative_check (lo := (68431707931209096961 / 100000000000000000000)) (hi := (34215853965604548481 / 50000000000000000000))
    (y := (-((71688068097349366627 / 100000000000000000000)))) (u := (24413648104194866931 / 50000000000000000000))
  · norm_num [world12707, agent12707, scalar12707, tp12707, tm12707, ep12707, em12707, dsL]
  · norm_num [world12707, agent12707, scalar12707, tp12707, tm12707, ep12707, em12707, dsL]
  · norm_num [world12707, agent12707, scalar12707, tp12707, tm12707, ep12707, em12707, dsL]
  · norm_num [world12707, agent12707, scalar12707, tp12707, tm12707, ep12707, em12707, dsL]
  · norm_num [world12707, agent12707, scalar12707, tp12707, tm12707, ep12707, em12707, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12707, agent12707, tp12707, tm12707, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12707, agent12707, tp12707, tm12707, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12707, agent12707, scalar12707, tp12707, tm12707, ep12707, em12707, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12707, agent12707, tp12707, tm12707, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12707, agent12707, scalar12707, tp12707, tm12707, ep12707, em12707, dsL]

theorem tails12707 :
    exp (-((12707:ℝ)*ep12707)) ≤ scalar12707.upperTail ∧
    exp (-((12707:ℝ)*em12707)) ≤ scalar12707.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12707:ℝ)) (by norm_num [ep12707]) ?_)
      (show bp12707^8 ≤ scalar12707.upperTail by norm_num [bp12707, scalar12707])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12707, bp12707, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12707:ℝ)) (by norm_num [em12707]) ?_)
      (show bm12707^8 ≤ scalar12707.lowerTail by norm_num [bm12707, scalar12707])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12707, bm12707, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12707 :
    agent12707.root+dsL+scalar12707.worldRadius < √(1/100/aL) ∧
    2*(agent12707.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12707, agent12707, scalar12707, tp12707, tm12707, ep12707, em12707, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12707, agent12707, scalar12707, tp12707, tm12707, ep12707, em12707, dsL]

noncomputable def master12707 : MasterCertificate 12707 world12707 agent12707 :=
  master scalar12707 dsL tp12707 tm12707 ep12707 em12707
    (by norm_num [dsL]) (by norm_num [tp12707]) (by norm_num [tm12707])
    (by norm_num [ep12707]) (by norm_num [em12707])
    positive12707 negative12707 tails12707.1 tails12707.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12707.1 tailGuards12707.2

theorem preserves12707 : master12707.toScalarCertificate = scalar12707 := rfl

noncomputable def tp12708 : ℝ := (11585891 / 50000000)
noncomputable def tm12708 : ℝ := (-((1212876727 / 2000000000)))
noncomputable def ep12708 : ℝ := (51445833370919743 / 100000000000000000000)
noncomputable def em12708 : ℝ := (12531955410384943 / 25000000000000000000)
noncomputable def bp12708 : ℝ := (11041476377690085983 / 25000000000000000000)
noncomputable def bm12708 : ℝ := (11275084480549576991 / 25000000000000000000)

theorem positive12708 :
    Eplus aL (agent12708.root+dsL) scalar12708.worldRadius world12708.frame
      agent12708.frame tp12708 ≤ -ep12708 := by
  apply positive_check (eT := (5779869612346543419 / 5000000000000000000)) (y := (4733457879257761991 / 12500000000000000000)) (u := (73017536313267183009 / 50000000000000000000))
  · norm_num [world12708, agent12708, scalar12708, tp12708, tm12708, ep12708, em12708, dsL]
  · norm_num [world12708, agent12708, scalar12708, tp12708, tm12708, ep12708, em12708, dsL]
  · norm_num [world12708, agent12708, scalar12708, tp12708, tm12708, ep12708, em12708, dsL]
  · norm_num [world12708, agent12708, scalar12708, tp12708, tm12708, ep12708, em12708, dsL]
  · norm_num [world12708, agent12708, scalar12708, tp12708, tm12708, ep12708, em12708, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12708, agent12708, tp12708, tm12708, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12708, agent12708, scalar12708, tp12708, tm12708, ep12708, em12708, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12708, agent12708, tp12708, tm12708, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12708, agent12708, scalar12708, tp12708, tm12708, ep12708, em12708, dsL]

theorem negative12708 :
    Eminus aL (agent12708.root+dsL) scalar12708.worldRadius world12708.frame
      agent12708.frame tm12708 ≤ -em12708 := by
  apply negative_check (lo := (68431501475571512043 / 100000000000000000000)) (hi := (17107875368892878011 / 25000000000000000000))
    (y := (-((7168813788833744091 / 10000000000000000000)))) (u := (48827262131349151423 / 100000000000000000000))
  · norm_num [world12708, agent12708, scalar12708, tp12708, tm12708, ep12708, em12708, dsL]
  · norm_num [world12708, agent12708, scalar12708, tp12708, tm12708, ep12708, em12708, dsL]
  · norm_num [world12708, agent12708, scalar12708, tp12708, tm12708, ep12708, em12708, dsL]
  · norm_num [world12708, agent12708, scalar12708, tp12708, tm12708, ep12708, em12708, dsL]
  · norm_num [world12708, agent12708, scalar12708, tp12708, tm12708, ep12708, em12708, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12708, agent12708, tp12708, tm12708, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12708, agent12708, tp12708, tm12708, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12708, agent12708, scalar12708, tp12708, tm12708, ep12708, em12708, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12708, agent12708, tp12708, tm12708, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12708, agent12708, scalar12708, tp12708, tm12708, ep12708, em12708, dsL]

theorem tails12708 :
    exp (-((12708:ℝ)*ep12708)) ≤ scalar12708.upperTail ∧
    exp (-((12708:ℝ)*em12708)) ≤ scalar12708.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12708:ℝ)) (by norm_num [ep12708]) ?_)
      (show bp12708^8 ≤ scalar12708.upperTail by norm_num [bp12708, scalar12708])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12708, bp12708, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12708:ℝ)) (by norm_num [em12708]) ?_)
      (show bm12708^8 ≤ scalar12708.lowerTail by norm_num [bm12708, scalar12708])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12708, bm12708, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12708 :
    agent12708.root+dsL+scalar12708.worldRadius < √(1/100/aL) ∧
    2*(agent12708.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12708, agent12708, scalar12708, tp12708, tm12708, ep12708, em12708, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12708, agent12708, scalar12708, tp12708, tm12708, ep12708, em12708, dsL]

noncomputable def master12708 : MasterCertificate 12708 world12708 agent12708 :=
  master scalar12708 dsL tp12708 tm12708 ep12708 em12708
    (by norm_num [dsL]) (by norm_num [tp12708]) (by norm_num [tm12708])
    (by norm_num [ep12708]) (by norm_num [em12708])
    positive12708 negative12708 tails12708.1 tails12708.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12708.1 tailGuards12708.2

theorem preserves12708 : master12708.toScalarCertificate = scalar12708 := rfl

noncomputable def tp12709 : ℝ := (2317263197 / 10000000000)
noncomputable def tm12709 : ℝ := (-((1212913193 / 2000000000)))
noncomputable def ep12709 : ℝ := (51448444624740781 / 100000000000000000000)
noncomputable def em12709 : ℝ := (6266257644932797 / 12500000000000000000)
noncomputable def bp12709 : ℝ := (44161233432497472133 / 100000000000000000000)
noncomputable def bm12709 : ℝ := (45095907603545502671 / 100000000000000000000)

theorem positive12709 :
    Eplus aL (agent12709.root+dsL) scalar12709.worldRadius world12709.frame
      agent12709.frame tp12709 ≤ -ep12709 := by
  apply positive_check (eT := (115597636529336438353 / 100000000000000000000)) (y := (295847303396298371 / 781250000000000000)) (u := (73018114468893534699 / 50000000000000000000))
  · norm_num [world12709, agent12709, scalar12709, tp12709, tm12709, ep12709, em12709, dsL]
  · norm_num [world12709, agent12709, scalar12709, tp12709, tm12709, ep12709, em12709, dsL]
  · norm_num [world12709, agent12709, scalar12709, tp12709, tm12709, ep12709, em12709, dsL]
  · norm_num [world12709, agent12709, scalar12709, tp12709, tm12709, ep12709, em12709, dsL]
  · norm_num [world12709, agent12709, scalar12709, tp12709, tm12709, ep12709, em12709, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12709, agent12709, tp12709, tm12709, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12709, agent12709, scalar12709, tp12709, tm12709, ep12709, em12709, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12709, agent12709, tp12709, tm12709, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12709, agent12709, scalar12709, tp12709, tm12709, ep12709, em12709, dsL]

theorem negative12709 :
    Eminus aL (agent12709.root+dsL) scalar12709.worldRadius world12709.frame
      agent12709.frame tm12709 ≤ -em12709 := by
  apply negative_check (lo := (68431294736182328653 / 100000000000000000000)) (hi := (34215647368091164327 / 50000000000000000000))
    (y := (-((8961026078191275313 / 12500000000000000000)))) (u := (48827227592326833331 / 100000000000000000000))
  · norm_num [world12709, agent12709, scalar12709, tp12709, tm12709, ep12709, em12709, dsL]
  · norm_num [world12709, agent12709, scalar12709, tp12709, tm12709, ep12709, em12709, dsL]
  · norm_num [world12709, agent12709, scalar12709, tp12709, tm12709, ep12709, em12709, dsL]
  · norm_num [world12709, agent12709, scalar12709, tp12709, tm12709, ep12709, em12709, dsL]
  · norm_num [world12709, agent12709, scalar12709, tp12709, tm12709, ep12709, em12709, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12709, agent12709, tp12709, tm12709, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12709, agent12709, tp12709, tm12709, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12709, agent12709, scalar12709, tp12709, tm12709, ep12709, em12709, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12709, agent12709, tp12709, tm12709, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12709, agent12709, scalar12709, tp12709, tm12709, ep12709, em12709, dsL]

theorem tails12709 :
    exp (-((12709:ℝ)*ep12709)) ≤ scalar12709.upperTail ∧
    exp (-((12709:ℝ)*em12709)) ≤ scalar12709.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12709:ℝ)) (by norm_num [ep12709]) ?_)
      (show bp12709^8 ≤ scalar12709.upperTail by norm_num [bp12709, scalar12709])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12709, bp12709, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12709:ℝ)) (by norm_num [em12709]) ?_)
      (show bm12709^8 ≤ scalar12709.lowerTail by norm_num [bm12709, scalar12709])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12709, bm12709, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12709 :
    agent12709.root+dsL+scalar12709.worldRadius < √(1/100/aL) ∧
    2*(agent12709.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12709, agent12709, scalar12709, tp12709, tm12709, ep12709, em12709, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12709, agent12709, scalar12709, tp12709, tm12709, ep12709, em12709, dsL]

noncomputable def master12709 : MasterCertificate 12709 world12709 agent12709 :=
  master scalar12709 dsL tp12709 tm12709 ep12709 em12709
    (by norm_num [dsL]) (by norm_num [tp12709]) (by norm_num [tm12709])
    (by norm_num [ep12709]) (by norm_num [em12709])
    positive12709 negative12709 tails12709.1 tails12709.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12709.1 tailGuards12709.2

theorem preserves12709 : master12709.toScalarCertificate = scalar12709 := rfl

noncomputable def tp12710 : ℝ := (289677803 / 1250000000)
noncomputable def tm12710 : ℝ := (-((1516243203 / 2500000000)))
noncomputable def ep12710 : ℝ := (25726237730104911 / 50000000000000000000)
noncomputable def em12710 : ℝ := (50133847120231667 / 100000000000000000000)
noncomputable def bp12710 : ℝ := (44155565681861134939 / 100000000000000000000)
noncomputable def bm12710 : ℝ := (2818148101483919119 / 6250000000000000000)

theorem positive12710 :
    Eplus aL (agent12710.root+dsL) scalar12710.worldRadius world12710.frame
      agent12710.frame tp12710 ≤ -ep12710 := by
  apply positive_check (eT := (57799208783347448339 / 50000000000000000000)) (y := (37868520919818369937 / 100000000000000000000)) (u := (146036325445995465631 / 100000000000000000000))
  · norm_num [world12710, agent12710, scalar12710, tp12710, tm12710, ep12710, em12710, dsL]
  · norm_num [world12710, agent12710, scalar12710, tp12710, tm12710, ep12710, em12710, dsL]
  · norm_num [world12710, agent12710, scalar12710, tp12710, tm12710, ep12710, em12710, dsL]
  · norm_num [world12710, agent12710, scalar12710, tp12710, tm12710, ep12710, em12710, dsL]
  · norm_num [world12710, agent12710, scalar12710, tp12710, tm12710, ep12710, em12710, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12710, agent12710, tp12710, tm12710, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12710, agent12710, scalar12710, tp12710, tm12710, ep12710, em12710, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12710, agent12710, tp12710, tm12710, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12710, agent12710, scalar12710, tp12710, tm12710, ep12710, em12710, dsL]

theorem negative12710 :
    Eminus aL (agent12710.root+dsL) scalar12710.worldRadius world12710.frame
      agent12710.frame tm12710 ≤ -em12710 := by
  apply negative_check (lo := (68430126949930285279 / 100000000000000000000)) (hi := (427688293437064283 / 625000000000000000))
    (y := (-((71686372984343162067 / 100000000000000000000)))) (u := (48828123893253417371 / 100000000000000000000))
  · norm_num [world12710, agent12710, scalar12710, tp12710, tm12710, ep12710, em12710, dsL]
  · norm_num [world12710, agent12710, scalar12710, tp12710, tm12710, ep12710, em12710, dsL]
  · norm_num [world12710, agent12710, scalar12710, tp12710, tm12710, ep12710, em12710, dsL]
  · norm_num [world12710, agent12710, scalar12710, tp12710, tm12710, ep12710, em12710, dsL]
  · norm_num [world12710, agent12710, scalar12710, tp12710, tm12710, ep12710, em12710, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12710, agent12710, tp12710, tm12710, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12710, agent12710, tp12710, tm12710, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12710, agent12710, scalar12710, tp12710, tm12710, ep12710, em12710, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12710, agent12710, tp12710, tm12710, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12710, agent12710, scalar12710, tp12710, tm12710, ep12710, em12710, dsL]

theorem tails12710 :
    exp (-((12710:ℝ)*ep12710)) ≤ scalar12710.upperTail ∧
    exp (-((12710:ℝ)*em12710)) ≤ scalar12710.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12710:ℝ)) (by norm_num [ep12710]) ?_)
      (show bp12710^8 ≤ scalar12710.upperTail by norm_num [bp12710, scalar12710])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12710, bp12710, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12710:ℝ)) (by norm_num [em12710]) ?_)
      (show bm12710^8 ≤ scalar12710.lowerTail by norm_num [bm12710, scalar12710])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12710, bm12710, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12710 :
    agent12710.root+dsL+scalar12710.worldRadius < √(1/100/aL) ∧
    2*(agent12710.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12710, agent12710, scalar12710, tp12710, tm12710, ep12710, em12710, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12710, agent12710, scalar12710, tp12710, tm12710, ep12710, em12710, dsL]

noncomputable def master12710 : MasterCertificate 12710 world12710 agent12710 :=
  master scalar12710 dsL tp12710 tm12710 ep12710 em12710
    (by norm_num [dsL]) (by norm_num [tp12710]) (by norm_num [tm12710])
    (by norm_num [ep12710]) (by norm_num [em12710])
    positive12710 negative12710 tails12710.1 tails12710.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12710.1 tailGuards12710.2

theorem preserves12710 : master12710.toScalarCertificate = scalar12710 := rfl

noncomputable def tp12711 : ℝ := (2317507323 / 10000000000)
noncomputable def tm12711 : ℝ := (-((3032577393 / 5000000000)))
noncomputable def ep12711 : ℝ := (10291016713262577 / 20000000000000000000)
noncomputable def em12711 : ℝ := (25068041855854883 / 50000000000000000000)
noncomputable def bp12711 : ℝ := (4415089625073567419 / 10000000000000000000)
noncomputable def bm12711 : ℝ := (9017188357735777661 / 20000000000000000000)

theorem positive12711 :
    Eplus aL (agent12711.root+dsL) scalar12711.worldRadius world12711.frame
      agent12711.frame tp12711 ≤ -ep12711 := by
  apply positive_check (eT := (115598661195201201931 / 100000000000000000000)) (y := (295853999240184957 / 781250000000000000)) (u := (146037480572962908169 / 100000000000000000000))
  · norm_num [world12711, agent12711, scalar12711, tp12711, tm12711, ep12711, em12711, dsL]
  · norm_num [world12711, agent12711, scalar12711, tp12711, tm12711, ep12711, em12711, dsL]
  · norm_num [world12711, agent12711, scalar12711, tp12711, tm12711, ep12711, em12711, dsL]
  · norm_num [world12711, agent12711, scalar12711, tp12711, tm12711, ep12711, em12711, dsL]
  · norm_num [world12711, agent12711, scalar12711, tp12711, tm12711, ep12711, em12711, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12711, agent12711, tp12711, tm12711, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12711, agent12711, scalar12711, tp12711, tm12711, ep12711, em12711, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12711, agent12711, tp12711, tm12711, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12711, agent12711, scalar12711, tp12711, tm12711, ep12711, em12711, dsL]

theorem negative12711 :
    Eminus aL (agent12711.root+dsL) scalar12711.worldRadius world12711.frame
      agent12711.frame tm12711 ≤ -em12711 := by
  apply negative_check (lo := (17107480411185699711 / 25000000000000000000)) (hi := (13685984328948559769 / 20000000000000000000))
    (y := (-((71686441715905543577 / 100000000000000000000)))) (u := (24414045166466258613 / 50000000000000000000))
  · norm_num [world12711, agent12711, scalar12711, tp12711, tm12711, ep12711, em12711, dsL]
  · norm_num [world12711, agent12711, scalar12711, tp12711, tm12711, ep12711, em12711, dsL]
  · norm_num [world12711, agent12711, scalar12711, tp12711, tm12711, ep12711, em12711, dsL]
  · norm_num [world12711, agent12711, scalar12711, tp12711, tm12711, ep12711, em12711, dsL]
  · norm_num [world12711, agent12711, scalar12711, tp12711, tm12711, ep12711, em12711, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12711, agent12711, tp12711, tm12711, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12711, agent12711, tp12711, tm12711, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12711, agent12711, scalar12711, tp12711, tm12711, ep12711, em12711, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12711, agent12711, tp12711, tm12711, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12711, agent12711, scalar12711, tp12711, tm12711, ep12711, em12711, dsL]

theorem tails12711 :
    exp (-((12711:ℝ)*ep12711)) ≤ scalar12711.upperTail ∧
    exp (-((12711:ℝ)*em12711)) ≤ scalar12711.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12711:ℝ)) (by norm_num [ep12711]) ?_)
      (show bp12711^8 ≤ scalar12711.upperTail by norm_num [bp12711, scalar12711])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12711, bp12711, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12711:ℝ)) (by norm_num [em12711]) ?_)
      (show bm12711^8 ≤ scalar12711.lowerTail by norm_num [bm12711, scalar12711])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12711, bm12711, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12711 :
    agent12711.root+dsL+scalar12711.worldRadius < √(1/100/aL) ∧
    2*(agent12711.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12711, agent12711, scalar12711, tp12711, tm12711, ep12711, em12711, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12711, agent12711, scalar12711, tp12711, tm12711, ep12711, em12711, dsL]

noncomputable def master12711 : MasterCertificate 12711 world12711 agent12711 :=
  master scalar12711 dsL tp12711 tm12711 ep12711 em12711
    (by norm_num [dsL]) (by norm_num [tp12711]) (by norm_num [tm12711])
    (by norm_num [ep12711]) (by norm_num [em12711])
    positive12711 negative12711 tails12711.1 tails12711.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12711.1 tailGuards12711.2

theorem preserves12711 : master12711.toScalarCertificate = scalar12711 := rfl

noncomputable def tp12712 : ℝ := (92703687 / 400000000)
noncomputable def tm12712 : ℝ := (-((6065336767 / 10000000000)))
noncomputable def ep12712 : ℝ := (10291538274166259 / 20000000000000000000)
noncomputable def em12712 : ℝ := (50138320032297819 / 100000000000000000000)
noncomputable def bp12712 : ℝ := (2759139202319500451 / 6250000000000000000)
noncomputable def bm12712 : ℝ := (9016302866080619101 / 20000000000000000000)

theorem positive12712 :
    Eplus aL (agent12712.root+dsL) scalar12712.worldRadius world12712.frame
      agent12712.frame tp12712 ≤ -ep12712 := by
  apply positive_check (eT := (11559890451664142731 / 10000000000000000000)) (y := (18935051139270701737 / 50000000000000000000)) (u := (146038634822426418219 / 100000000000000000000))
  · norm_num [world12712, agent12712, scalar12712, tp12712, tm12712, ep12712, em12712, dsL]
  · norm_num [world12712, agent12712, scalar12712, tp12712, tm12712, ep12712, em12712, dsL]
  · norm_num [world12712, agent12712, scalar12712, tp12712, tm12712, ep12712, em12712, dsL]
  · norm_num [world12712, agent12712, scalar12712, tp12712, tm12712, ep12712, em12712, dsL]
  · norm_num [world12712, agent12712, scalar12712, tp12712, tm12712, ep12712, em12712, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12712, agent12712, tp12712, tm12712, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12712, agent12712, scalar12712, tp12712, tm12712, ep12712, em12712, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12712, agent12712, tp12712, tm12712, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12712, agent12712, scalar12712, tp12712, tm12712, ep12712, em12712, dsL]

theorem negative12712 :
    Eminus aL (agent12712.root+dsL) scalar12712.worldRadius world12712.frame
      agent12712.frame tm12712 ≤ -em12712 := by
  apply negative_check (lo := (8553714531581848319 / 12500000000000000000)) (hi := (68429716252654786553 / 100000000000000000000))
    (y := (-((17921627832492420419 / 25000000000000000000)))) (u := (48828056341726226781 / 100000000000000000000))
  · norm_num [world12712, agent12712, scalar12712, tp12712, tm12712, ep12712, em12712, dsL]
  · norm_num [world12712, agent12712, scalar12712, tp12712, tm12712, ep12712, em12712, dsL]
  · norm_num [world12712, agent12712, scalar12712, tp12712, tm12712, ep12712, em12712, dsL]
  · norm_num [world12712, agent12712, scalar12712, tp12712, tm12712, ep12712, em12712, dsL]
  · norm_num [world12712, agent12712, scalar12712, tp12712, tm12712, ep12712, em12712, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12712, agent12712, tp12712, tm12712, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12712, agent12712, tp12712, tm12712, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12712, agent12712, scalar12712, tp12712, tm12712, ep12712, em12712, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12712, agent12712, tp12712, tm12712, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12712, agent12712, scalar12712, tp12712, tm12712, ep12712, em12712, dsL]

theorem tails12712 :
    exp (-((12712:ℝ)*ep12712)) ≤ scalar12712.upperTail ∧
    exp (-((12712:ℝ)*em12712)) ≤ scalar12712.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12712:ℝ)) (by norm_num [ep12712]) ?_)
      (show bp12712^8 ≤ scalar12712.upperTail by norm_num [bp12712, scalar12712])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12712, bp12712, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12712:ℝ)) (by norm_num [em12712]) ?_)
      (show bm12712^8 ≤ scalar12712.lowerTail by norm_num [bm12712, scalar12712])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12712, bm12712, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12712 :
    agent12712.root+dsL+scalar12712.worldRadius < √(1/100/aL) ∧
    2*(agent12712.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12712, agent12712, scalar12712, tp12712, tm12712, ep12712, em12712, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12712, agent12712, scalar12712, tp12712, tm12712, ep12712, em12712, dsL]

noncomputable def master12712 : MasterCertificate 12712 world12712 agent12712 :=
  master scalar12712 dsL tp12712 tm12712 ep12712 em12712
    (by norm_num [dsL]) (by norm_num [tp12712]) (by norm_num [tm12712])
    (by norm_num [ep12712]) (by norm_num [em12712])
    positive12712 negative12712 tails12712.1 tails12712.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12712.1 tailGuards12712.2

theorem preserves12712 : master12712.toScalarCertificate = scalar12712 := rfl

noncomputable def tp12713 : ℝ := (1158838491 / 5000000000)
noncomputable def tm12713 : ℝ := (-((1516379659 / 2500000000)))
noncomputable def ep12713 : ℝ := (51460296981741159 / 100000000000000000000)
noncomputable def em12713 : ℝ := (50140554331386999 / 100000000000000000000)
noncomputable def bp12713 : ℝ := (8828311993639947423 / 20000000000000000000)
noncomputable def bm12713 : ℝ := (45077088502951362863 / 100000000000000000000)

theorem positive12713 :
    Eplus aL (agent12713.root+dsL) scalar12713.worldRadius world12713.frame
      agent12713.frame tp12713 ≤ -ep12713 := by
  apply positive_check (eT := (14449893443177815603 / 12500000000000000000)) (y := (7574178455615918433 / 20000000000000000000)) (u := (146039788531524234729 / 100000000000000000000))
  · norm_num [world12713, agent12713, scalar12713, tp12713, tm12713, ep12713, em12713, dsL]
  · norm_num [world12713, agent12713, scalar12713, tp12713, tm12713, ep12713, em12713, dsL]
  · norm_num [world12713, agent12713, scalar12713, tp12713, tm12713, ep12713, em12713, dsL]
  · norm_num [world12713, agent12713, scalar12713, tp12713, tm12713, ep12713, em12713, dsL]
  · norm_num [world12713, agent12713, scalar12713, tp12713, tm12713, ep12713, em12713, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12713, agent12713, tp12713, tm12713, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12713, agent12713, scalar12713, tp12713, tm12713, ep12713, em12713, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12713, agent12713, tp12713, tm12713, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12713, agent12713, scalar12713, tp12713, tm12713, ep12713, em12713, dsL]

theorem negative12713 :
    Eminus aL (agent12713.root+dsL) scalar12713.worldRadius world12713.frame
      agent12713.frame tm12713 ≤ -em12713 := by
  apply negative_check (lo := (68429511283093690669 / 100000000000000000000)) (hi := (6842951128309369067 / 10000000000000000000))
    (y := (-((71686580157171747599 / 100000000000000000000)))) (u := (48828022734752788969 / 100000000000000000000))
  · norm_num [world12713, agent12713, scalar12713, tp12713, tm12713, ep12713, em12713, dsL]
  · norm_num [world12713, agent12713, scalar12713, tp12713, tm12713, ep12713, em12713, dsL]
  · norm_num [world12713, agent12713, scalar12713, tp12713, tm12713, ep12713, em12713, dsL]
  · norm_num [world12713, agent12713, scalar12713, tp12713, tm12713, ep12713, em12713, dsL]
  · norm_num [world12713, agent12713, scalar12713, tp12713, tm12713, ep12713, em12713, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12713, agent12713, tp12713, tm12713, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12713, agent12713, tp12713, tm12713, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12713, agent12713, scalar12713, tp12713, tm12713, ep12713, em12713, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12713, agent12713, tp12713, tm12713, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12713, agent12713, scalar12713, tp12713, tm12713, ep12713, em12713, dsL]

theorem tails12713 :
    exp (-((12713:ℝ)*ep12713)) ≤ scalar12713.upperTail ∧
    exp (-((12713:ℝ)*em12713)) ≤ scalar12713.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12713:ℝ)) (by norm_num [ep12713]) ?_)
      (show bp12713^8 ≤ scalar12713.upperTail by norm_num [bp12713, scalar12713])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12713, bp12713, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12713:ℝ)) (by norm_num [em12713]) ?_)
      (show bm12713^8 ≤ scalar12713.lowerTail by norm_num [bm12713, scalar12713])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12713, bm12713, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12713 :
    agent12713.root+dsL+scalar12713.worldRadius < √(1/100/aL) ∧
    2*(agent12713.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12713, agent12713, scalar12713, tp12713, tm12713, ep12713, em12713, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12713, agent12713, scalar12713, tp12713, tm12713, ep12713, em12713, dsL]

noncomputable def master12713 : MasterCertificate 12713 world12713 agent12713 :=
  master scalar12713 dsL tp12713 tm12713 ep12713 em12713
    (by norm_num [dsL]) (by norm_num [tp12713]) (by norm_num [tm12713])
    (by norm_num [ep12713]) (by norm_num [em12713])
    positive12713 negative12713 tails12713.1 tails12713.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12713.1 tailGuards12713.2

theorem preserves12713 : master12713.toScalarCertificate = scalar12713 := rfl

noncomputable def tp12714 : ℝ := (289720219 / 1250000000)
noncomputable def tm12714 : ℝ := (-((3032850163 / 5000000000)))
noncomputable def ep12714 : ℝ := (51462902011766909 / 100000000000000000000)
noncomputable def em12714 : ℝ := (401142304535693 / 800000000000000000)
noncomputable def bp12714 : ℝ := (44136893312674521431 / 100000000000000000000)
noncomputable def bm12714 : ℝ := (45072663261891008127 / 100000000000000000000)

theorem positive12714 :
    Eplus aL (agent12714.root+dsL) scalar12714.worldRadius world12714.frame
      agent12714.frame tp12714 ≤ -ep12714 := by
  apply positive_check (eT := (57799695169732025919 / 50000000000000000000)) (y := (37871682149276891631 / 100000000000000000000)) (u := (14604094206230613999 / 10000000000000000000))
  · norm_num [world12714, agent12714, scalar12714, tp12714, tm12714, ep12714, em12714, dsL]
  · norm_num [world12714, agent12714, scalar12714, tp12714, tm12714, ep12714, em12714, dsL]
  · norm_num [world12714, agent12714, scalar12714, tp12714, tm12714, ep12714, em12714, dsL]
  · norm_num [world12714, agent12714, scalar12714, tp12714, tm12714, ep12714, em12714, dsL]
  · norm_num [world12714, agent12714, scalar12714, tp12714, tm12714, ep12714, em12714, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12714, agent12714, tp12714, tm12714, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12714, agent12714, scalar12714, tp12714, tm12714, ep12714, em12714, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12714, agent12714, tp12714, tm12714, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12714, agent12714, scalar12714, tp12714, tm12714, ep12714, em12714, dsL]

theorem negative12714 :
    Eminus aL (agent12714.root+dsL) scalar12714.worldRadius world12714.frame
      agent12714.frame tm12714 ≤ -em12714 := by
  apply negative_check (lo := (68429307022678974043 / 100000000000000000000)) (hi := (17107326755669743511 / 25000000000000000000))
    (y := (-((71686648633250138073 / 100000000000000000000)))) (u := (6103498662406139033 / 12500000000000000000))
  · norm_num [world12714, agent12714, scalar12714, tp12714, tm12714, ep12714, em12714, dsL]
  · norm_num [world12714, agent12714, scalar12714, tp12714, tm12714, ep12714, em12714, dsL]
  · norm_num [world12714, agent12714, scalar12714, tp12714, tm12714, ep12714, em12714, dsL]
  · norm_num [world12714, agent12714, scalar12714, tp12714, tm12714, ep12714, em12714, dsL]
  · norm_num [world12714, agent12714, scalar12714, tp12714, tm12714, ep12714, em12714, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12714, agent12714, tp12714, tm12714, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12714, agent12714, tp12714, tm12714, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12714, agent12714, scalar12714, tp12714, tm12714, ep12714, em12714, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12714, agent12714, tp12714, tm12714, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12714, agent12714, scalar12714, tp12714, tm12714, ep12714, em12714, dsL]

theorem tails12714 :
    exp (-((12714:ℝ)*ep12714)) ≤ scalar12714.upperTail ∧
    exp (-((12714:ℝ)*em12714)) ≤ scalar12714.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12714:ℝ)) (by norm_num [ep12714]) ?_)
      (show bp12714^8 ≤ scalar12714.upperTail by norm_num [bp12714, scalar12714])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12714, bp12714, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12714:ℝ)) (by norm_num [em12714]) ?_)
      (show bm12714^8 ≤ scalar12714.lowerTail by norm_num [bm12714, scalar12714])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12714, bm12714, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12714 :
    agent12714.root+dsL+scalar12714.worldRadius < √(1/100/aL) ∧
    2*(agent12714.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12714, agent12714, scalar12714, tp12714, tm12714, ep12714, em12714, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12714, agent12714, scalar12714, tp12714, tm12714, ep12714, em12714, dsL]

noncomputable def master12714 : MasterCertificate 12714 world12714 agent12714 :=
  master scalar12714 dsL tp12714 tm12714 ep12714 em12714
    (by norm_num [dsL]) (by norm_num [tp12714]) (by norm_num [tm12714])
    (by norm_num [ep12714]) (by norm_num [em12714])
    positive12714 negative12714 tails12714.1 tails12714.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12714.1 tailGuards12714.2

theorem preserves12714 : master12714.toScalarCertificate = scalar12714 := rfl

noncomputable def tp12715 : ℝ := (289730813 / 1250000000)
noncomputable def tm12715 : ℝ := (-((6065882047 / 10000000000)))
noncomputable def ep12715 : ℝ := (51465505792064209 / 100000000000000000000)
noncomputable def em12715 : ℝ := (12536255163661269 / 25000000000000000000)
noncomputable def bp12715 : ℝ := (44132227739687485559 / 100000000000000000000)
noncomputable def bm12715 : ℝ := (45068239025820792551 / 100000000000000000000)

theorem positive12715 :
    Eplus aL (agent12715.root+dsL) scalar12715.worldRadius world12715.frame
      agent12715.frame tp12715 ≤ -ep12715 := by
  apply positive_check (eT := (57799816518037520829 / 50000000000000000000)) (y := (1893623600991026823 / 5000000000000000000)) (u := (146042095601244877703 / 100000000000000000000))
  · norm_num [world12715, agent12715, scalar12715, tp12715, tm12715, ep12715, em12715, dsL]
  · norm_num [world12715, agent12715, scalar12715, tp12715, tm12715, ep12715, em12715, dsL]
  · norm_num [world12715, agent12715, scalar12715, tp12715, tm12715, ep12715, em12715, dsL]
  · norm_num [world12715, agent12715, scalar12715, tp12715, tm12715, ep12715, em12715, dsL]
  · norm_num [world12715, agent12715, scalar12715, tp12715, tm12715, ep12715, em12715, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12715, agent12715, tp12715, tm12715, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12715, agent12715, scalar12715, tp12715, tm12715, ep12715, em12715, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12715, agent12715, tp12715, tm12715, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12715, agent12715, scalar12715, tp12715, tm12715, ep12715, em12715, dsL]

theorem negative12715 :
    Eminus aL (agent12715.root+dsL) scalar12715.worldRadius world12715.frame
      agent12715.frame tm12715 ≤ -em12715 := by
  apply negative_check (lo := (8553637821591908203 / 12500000000000000000)) (hi := (4379462564655057 / 6400000000000000))
    (y := (-((35843358983869542417 / 50000000000000000000)))) (u := (48827955444624005117 / 100000000000000000000))
  · norm_num [world12715, agent12715, scalar12715, tp12715, tm12715, ep12715, em12715, dsL]
  · norm_num [world12715, agent12715, scalar12715, tp12715, tm12715, ep12715, em12715, dsL]
  · norm_num [world12715, agent12715, scalar12715, tp12715, tm12715, ep12715, em12715, dsL]
  · norm_num [world12715, agent12715, scalar12715, tp12715, tm12715, ep12715, em12715, dsL]
  · norm_num [world12715, agent12715, scalar12715, tp12715, tm12715, ep12715, em12715, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12715, agent12715, tp12715, tm12715, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12715, agent12715, tp12715, tm12715, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12715, agent12715, scalar12715, tp12715, tm12715, ep12715, em12715, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12715, agent12715, tp12715, tm12715, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12715, agent12715, scalar12715, tp12715, tm12715, ep12715, em12715, dsL]

theorem tails12715 :
    exp (-((12715:ℝ)*ep12715)) ≤ scalar12715.upperTail ∧
    exp (-((12715:ℝ)*em12715)) ≤ scalar12715.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12715:ℝ)) (by norm_num [ep12715]) ?_)
      (show bp12715^8 ≤ scalar12715.upperTail by norm_num [bp12715, scalar12715])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12715, bp12715, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12715:ℝ)) (by norm_num [em12715]) ?_)
      (show bm12715^8 ≤ scalar12715.lowerTail by norm_num [bm12715, scalar12715])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12715, bm12715, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12715 :
    agent12715.root+dsL+scalar12715.worldRadius < √(1/100/aL) ∧
    2*(agent12715.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12715, agent12715, scalar12715, tp12715, tm12715, ep12715, em12715, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12715, agent12715, scalar12715, tp12715, tm12715, ep12715, em12715, dsL]

noncomputable def master12715 : MasterCertificate 12715 world12715 agent12715 :=
  master scalar12715 dsL tp12715 tm12715 ep12715 em12715
    (by norm_num [dsL]) (by norm_num [tp12715]) (by norm_num [tm12715])
    (by norm_num [ep12715]) (by norm_num [em12715])
    positive12715 negative12715 tails12715.1 tails12715.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12715.1 tailGuards12715.2

theorem preserves12715 : master12715.toScalarCertificate = scalar12715 := rfl

noncomputable def tp12716 : ℝ := (1158965619 / 5000000000)
noncomputable def tm12716 : ℝ := (-((48528509 / 80000000)))
noncomputable def ep12716 : ℝ := (3216756770744701 / 6250000000000000000)
noncomputable def em12716 : ℝ := (25073626051196529 / 50000000000000000000)
noncomputable def bp12716 : ℝ := (44127563242695858179 / 100000000000000000000)
noncomputable def bm12716 : ℝ := (1126595394725636163 / 2500000000000000000)

theorem positive12716 :
    Eplus aL (agent12716.root+dsL) scalar12716.worldRadius world12716.frame
      agent12716.frame tp12716 ≤ -ep12716 := by
  apply positive_check (eT := (115599875635323591959 / 100000000000000000000)) (y := (3787326188960163291 / 10000000000000000000)) (u := (73021624574090732629 / 50000000000000000000))
  · norm_num [world12716, agent12716, scalar12716, tp12716, tm12716, ep12716, em12716, dsL]
  · norm_num [world12716, agent12716, scalar12716, tp12716, tm12716, ep12716, em12716, dsL]
  · norm_num [world12716, agent12716, scalar12716, tp12716, tm12716, ep12716, em12716, dsL]
  · norm_num [world12716, agent12716, scalar12716, tp12716, tm12716, ep12716, em12716, dsL]
  · norm_num [world12716, agent12716, scalar12716, tp12716, tm12716, ep12716, em12716, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12716, agent12716, tp12716, tm12716, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12716, agent12716, scalar12716, tp12716, tm12716, ep12716, em12716, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12716, agent12716, tp12716, tm12716, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12716, agent12716, scalar12716, tp12716, tm12716, ep12716, em12716, dsL]

theorem negative12716 :
    Eminus aL (agent12716.root+dsL) scalar12716.worldRadius world12716.frame
      agent12716.frame tm12716 ≤ -em12716 := by
  apply negative_check (lo := (34214449338914434507 / 50000000000000000000)) (hi := (13685779735565773803 / 20000000000000000000))
    (y := (-((2867471458779517553 / 4000000000000000000)))) (u := (48827921996632052133 / 100000000000000000000))
  · norm_num [world12716, agent12716, scalar12716, tp12716, tm12716, ep12716, em12716, dsL]
  · norm_num [world12716, agent12716, scalar12716, tp12716, tm12716, ep12716, em12716, dsL]
  · norm_num [world12716, agent12716, scalar12716, tp12716, tm12716, ep12716, em12716, dsL]
  · norm_num [world12716, agent12716, scalar12716, tp12716, tm12716, ep12716, em12716, dsL]
  · norm_num [world12716, agent12716, scalar12716, tp12716, tm12716, ep12716, em12716, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12716, agent12716, tp12716, tm12716, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12716, agent12716, tp12716, tm12716, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12716, agent12716, scalar12716, tp12716, tm12716, ep12716, em12716, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12716, agent12716, tp12716, tm12716, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12716, agent12716, scalar12716, tp12716, tm12716, ep12716, em12716, dsL]

theorem tails12716 :
    exp (-((12716:ℝ)*ep12716)) ≤ scalar12716.upperTail ∧
    exp (-((12716:ℝ)*em12716)) ≤ scalar12716.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12716:ℝ)) (by norm_num [ep12716]) ?_)
      (show bp12716^8 ≤ scalar12716.upperTail by norm_num [bp12716, scalar12716])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12716, bp12716, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12716:ℝ)) (by norm_num [em12716]) ?_)
      (show bm12716^8 ≤ scalar12716.lowerTail by norm_num [bm12716, scalar12716])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12716, bm12716, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12716 :
    agent12716.root+dsL+scalar12716.worldRadius < √(1/100/aL) ∧
    2*(agent12716.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12716, agent12716, scalar12716, tp12716, tm12716, ep12716, em12716, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12716, agent12716, scalar12716, tp12716, tm12716, ep12716, em12716, dsL]

noncomputable def master12716 : MasterCertificate 12716 world12716 agent12716 :=
  master scalar12716 dsL tp12716 tm12716 ep12716 em12716
    (by norm_num [dsL]) (by norm_num [tp12716]) (by norm_num [tm12716])
    (by norm_num [ep12716]) (by norm_num [em12716])
    positive12716 negative12716 tails12716.1 tails12716.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12716.1 tailGuards12716.2

theorem preserves12716 : master12716.toScalarCertificate = scalar12716 := rfl

noncomputable def tp12717 : ℝ := (1159007921 / 5000000000)
noncomputable def tm12717 : ℝ := (-((606624499 / 1000000000)))
noncomputable def ep12717 : ℝ := (25735354272723497 / 50000000000000000000)
noncomputable def em12717 : ℝ := (12537370347088891 / 25000000000000000000)
noncomputable def bp12717 : ℝ := (4412290058328690827 / 10000000000000000000)
noncomputable def bm12717 : ℝ := (1802375771336584673 / 4000000000000000000)

theorem positive12717 :
    Eplus aL (agent12717.root+dsL) scalar12717.worldRadius world12717.frame
      agent12717.frame tp12717 ≤ -ep12717 := by
  apply positive_check (eT := (115600117327435867393 / 100000000000000000000)) (y := (1893702502118131203 / 5000000000000000000)) (u := (36511100049154467973 / 25000000000000000000))
  · norm_num [world12717, agent12717, scalar12717, tp12717, tm12717, ep12717, em12717, dsL]
  · norm_num [world12717, agent12717, scalar12717, tp12717, tm12717, ep12717, em12717, dsL]
  · norm_num [world12717, agent12717, scalar12717, tp12717, tm12717, ep12717, em12717, dsL]
  · norm_num [world12717, agent12717, scalar12717, tp12717, tm12717, ep12717, em12717, dsL]
  · norm_num [world12717, agent12717, scalar12717, tp12717, tm12717, ep12717, em12717, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12717, agent12717, tp12717, tm12717, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12717, agent12717, scalar12717, tp12717, tm12717, ep12717, em12717, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12717, agent12717, tp12717, tm12717, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12717, agent12717, scalar12717, tp12717, tm12717, ep12717, em12717, dsL]

theorem negative12717 :
    Eminus aL (agent12717.root+dsL) scalar12717.worldRadius world12717.frame
      agent12717.frame tm12717 ≤ -em12717 := by
  apply negative_check (lo := (17107173909398432973 / 25000000000000000000)) (hi := (68428695637593731893 / 100000000000000000000))
    (y := (-((35843426744546167521 / 50000000000000000000)))) (u := (6103486159045357617 / 12500000000000000000))
  · norm_num [world12717, agent12717, scalar12717, tp12717, tm12717, ep12717, em12717, dsL]
  · norm_num [world12717, agent12717, scalar12717, tp12717, tm12717, ep12717, em12717, dsL]
  · norm_num [world12717, agent12717, scalar12717, tp12717, tm12717, ep12717, em12717, dsL]
  · norm_num [world12717, agent12717, scalar12717, tp12717, tm12717, ep12717, em12717, dsL]
  · norm_num [world12717, agent12717, scalar12717, tp12717, tm12717, ep12717, em12717, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12717, agent12717, tp12717, tm12717, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12717, agent12717, tp12717, tm12717, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12717, agent12717, scalar12717, tp12717, tm12717, ep12717, em12717, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12717, agent12717, tp12717, tm12717, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12717, agent12717, scalar12717, tp12717, tm12717, ep12717, em12717, dsL]

theorem tails12717 :
    exp (-((12717:ℝ)*ep12717)) ≤ scalar12717.upperTail ∧
    exp (-((12717:ℝ)*em12717)) ≤ scalar12717.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12717:ℝ)) (by norm_num [ep12717]) ?_)
      (show bp12717^8 ≤ scalar12717.upperTail by norm_num [bp12717, scalar12717])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12717, bp12717, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12717:ℝ)) (by norm_num [em12717]) ?_)
      (show bm12717^8 ≤ scalar12717.lowerTail by norm_num [bm12717, scalar12717])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12717, bm12717, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12717 :
    agent12717.root+dsL+scalar12717.worldRadius < √(1/100/aL) ∧
    2*(agent12717.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12717, agent12717, scalar12717, tp12717, tm12717, ep12717, em12717, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12717, agent12717, scalar12717, tp12717, tm12717, ep12717, em12717, dsL]

noncomputable def master12717 : MasterCertificate 12717 world12717 agent12717 :=
  master scalar12717 dsL tp12717 tm12717 ep12717 em12717
    (by norm_num [dsL]) (by norm_num [tp12717]) (by norm_num [tm12717])
    (by norm_num [ep12717]) (by norm_num [em12717])
    positive12717 negative12717 tails12717.1 tails12717.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12717.1 tailGuards12717.2

theorem preserves12717 : master12717.toScalarCertificate = scalar12717 := rfl

noncomputable def tp12718 : ℝ := (2318100421 / 10000000000)
noncomputable def tm12718 : ℝ := (-((1516606579 / 2500000000)))
noncomputable def ep12718 : ℝ := (51473308156289353 / 100000000000000000000)
noncomputable def em12718 : ℝ := (50151710085301263 / 100000000000000000000)
noncomputable def bp12718 : ℝ := (8823647710493090227 / 20000000000000000000)
noncomputable def bm12718 : ℝ := (45054973382415588437 / 100000000000000000000)

theorem positive12718 :
    Eplus aL (agent12718.root+dsL) scalar12718.worldRadius world12718.frame
      agent12718.frame tp12718 ≤ -ep12718 := by
  apply positive_check (eT := (115600358871587742099 / 100000000000000000000)) (y := (37874838174933691103 / 100000000000000000000)) (u := (4563923475769995261 / 3125000000000000000))
  · norm_num [world12718, agent12718, scalar12718, tp12718, tm12718, ep12718, em12718, dsL]
  · norm_num [world12718, agent12718, scalar12718, tp12718, tm12718, ep12718, em12718, dsL]
  · norm_num [world12718, agent12718, scalar12718, tp12718, tm12718, ep12718, em12718, dsL]
  · norm_num [world12718, agent12718, scalar12718, tp12718, tm12718, ep12718, em12718, dsL]
  · norm_num [world12718, agent12718, scalar12718, tp12718, tm12718, ep12718, em12718, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12718, agent12718, tp12718, tm12718, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12718, agent12718, scalar12718, tp12718, tm12718, ep12718, em12718, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12718, agent12718, tp12718, tm12718, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12718, agent12718, scalar12718, tp12718, tm12718, ep12718, em12718, dsL]

theorem negative12718 :
    Eminus aL (agent12718.root+dsL) scalar12718.worldRadius world12718.frame
      agent12718.frame tm12718 ≤ -em12718 := by
  apply negative_check (lo := (1368569854146046761 / 2000000000000000000)) (hi := (68428492707302338051 / 100000000000000000000))
    (y := (-((71686921104609380011 / 100000000000000000000)))) (u := (4882785625714422899 / 10000000000000000000))
  · norm_num [world12718, agent12718, scalar12718, tp12718, tm12718, ep12718, em12718, dsL]
  · norm_num [world12718, agent12718, scalar12718, tp12718, tm12718, ep12718, em12718, dsL]
  · norm_num [world12718, agent12718, scalar12718, tp12718, tm12718, ep12718, em12718, dsL]
  · norm_num [world12718, agent12718, scalar12718, tp12718, tm12718, ep12718, em12718, dsL]
  · norm_num [world12718, agent12718, scalar12718, tp12718, tm12718, ep12718, em12718, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12718, agent12718, tp12718, tm12718, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12718, agent12718, tp12718, tm12718, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12718, agent12718, scalar12718, tp12718, tm12718, ep12718, em12718, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12718, agent12718, tp12718, tm12718, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12718, agent12718, scalar12718, tp12718, tm12718, ep12718, em12718, dsL]

theorem tails12718 :
    exp (-((12718:ℝ)*ep12718)) ≤ scalar12718.upperTail ∧
    exp (-((12718:ℝ)*em12718)) ≤ scalar12718.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12718:ℝ)) (by norm_num [ep12718]) ?_)
      (show bp12718^8 ≤ scalar12718.upperTail by norm_num [bp12718, scalar12718])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12718, bp12718, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12718:ℝ)) (by norm_num [em12718]) ?_)
      (show bm12718^8 ≤ scalar12718.lowerTail by norm_num [bm12718, scalar12718])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12718, bm12718, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12718 :
    agent12718.root+dsL+scalar12718.worldRadius < √(1/100/aL) ∧
    2*(agent12718.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12718, agent12718, scalar12718, tp12718, tm12718, ep12718, em12718, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12718, agent12718, scalar12718, tp12718, tm12718, ep12718, em12718, dsL]

noncomputable def master12718 : MasterCertificate 12718 world12718 agent12718 :=
  master scalar12718 dsL tp12718 tm12718 ep12718 em12718
    (by norm_num [dsL]) (by norm_num [tp12718]) (by norm_num [tm12718])
    (by norm_num [ep12718]) (by norm_num [em12718])
    positive12718 negative12718 tails12718.1 tails12718.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12718.1 tailGuards12718.2

theorem preserves12718 : master12718.toScalarCertificate = scalar12718 := rfl

noncomputable def tp12719 : ℝ := (2318184991 / 10000000000)
noncomputable def tm12719 : ℝ := (-((3033303801 / 5000000000)))
noncomputable def ep12719 : ℝ := (25737952868848529 / 50000000000000000000)
noncomputable def em12719 : ℝ := (50153936935359431 / 100000000000000000000)
noncomputable def bp12719 : ℝ := (882271563017697549 / 2000000000000000000)
noncomputable def bm12719 : ℝ := (1802022159479271241 / 4000000000000000000)

theorem positive12719 :
    Eplus aL (agent12719.root+dsL) scalar12719.worldRadius world12719.frame
      agent12719.frame tp12719 ≤ -ep12719 := by
  apply positive_check (eT := (14450075047929735879 / 12500000000000000000)) (y := (9468906628059676033 / 25000000000000000000)) (u := (36511675640185166033 / 25000000000000000000))
  · norm_num [world12719, agent12719, scalar12719, tp12719, tm12719, ep12719, em12719, dsL]
  · norm_num [world12719, agent12719, scalar12719, tp12719, tm12719, ep12719, em12719, dsL]
  · norm_num [world12719, agent12719, scalar12719, tp12719, tm12719, ep12719, em12719, dsL]
  · norm_num [world12719, agent12719, scalar12719, tp12719, tm12719, ep12719, em12719, dsL]
  · norm_num [world12719, agent12719, scalar12719, tp12719, tm12719, ep12719, em12719, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12719, agent12719, tp12719, tm12719, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12719, agent12719, scalar12719, tp12719, tm12719, ep12719, em12719, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12719, agent12719, tp12719, tm12719, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12719, agent12719, scalar12719, tp12719, tm12719, ep12719, em12719, dsL]

theorem negative12719 :
    Eminus aL (agent12719.root+dsL) scalar12719.worldRadius world12719.frame
      agent12719.frame tm12719 ≤ -em12719 := by
  apply negative_check (lo := (34214144945627599653 / 50000000000000000000)) (hi := (68428289891255199307 / 100000000000000000000))
    (y := (-((71686988755957406963 / 100000000000000000000)))) (u := (48827823224452431901 / 100000000000000000000))
  · norm_num [world12719, agent12719, scalar12719, tp12719, tm12719, ep12719, em12719, dsL]
  · norm_num [world12719, agent12719, scalar12719, tp12719, tm12719, ep12719, em12719, dsL]
  · norm_num [world12719, agent12719, scalar12719, tp12719, tm12719, ep12719, em12719, dsL]
  · norm_num [world12719, agent12719, scalar12719, tp12719, tm12719, ep12719, em12719, dsL]
  · norm_num [world12719, agent12719, scalar12719, tp12719, tm12719, ep12719, em12719, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12719, agent12719, tp12719, tm12719, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12719, agent12719, tp12719, tm12719, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12719, agent12719, scalar12719, tp12719, tm12719, ep12719, em12719, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12719, agent12719, tp12719, tm12719, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12719, agent12719, scalar12719, tp12719, tm12719, ep12719, em12719, dsL]

theorem tails12719 :
    exp (-((12719:ℝ)*ep12719)) ≤ scalar12719.upperTail ∧
    exp (-((12719:ℝ)*em12719)) ≤ scalar12719.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12719:ℝ)) (by norm_num [ep12719]) ?_)
      (show bp12719^8 ≤ scalar12719.upperTail by norm_num [bp12719, scalar12719])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12719, bp12719, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12719:ℝ)) (by norm_num [em12719]) ?_)
      (show bm12719^8 ≤ scalar12719.lowerTail by norm_num [bm12719, scalar12719])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12719, bm12719, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12719 :
    agent12719.root+dsL+scalar12719.worldRadius < √(1/100/aL) ∧
    2*(agent12719.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12719, agent12719, scalar12719, tp12719, tm12719, ep12719, em12719, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12719, agent12719, scalar12719, tp12719, tm12719, ep12719, em12719, dsL]

noncomputable def master12719 : MasterCertificate 12719 world12719 agent12719 :=
  master scalar12719 dsL tp12719 tm12719 ep12719 em12719
    (by norm_num [dsL]) (by norm_num [tp12719]) (by norm_num [tm12719])
    (by norm_num [ep12719]) (by norm_num [em12719])
    positive12719 negative12719 tails12719.1 tails12719.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12719.1 tailGuards12719.2

theorem preserves12719 : master12719.toScalarCertificate = scalar12719 := rfl

noncomputable def tp12720 : ℝ := (289792973 / 1250000000)
noncomputable def tm12720 : ℝ := (-((3033506577 / 5000000000)))
noncomputable def ep12720 : ℝ := (10295984061309339 / 20000000000000000000)
noncomputable def em12720 : ℝ := (5015770761702717 / 10000000000000000000)
noncomputable def bp12720 : ℝ := (44107924188009591123 / 100000000000000000000)
noncomputable def bm12720 : ℝ := (22522514521926107367 / 50000000000000000000)

theorem positive12720 :
    Eplus aL (agent12720.root+dsL) scalar12720.worldRadius world12720.frame
      agent12720.frame tp12720 ≤ -ep12720 := by
  apply positive_check (eT := (115601378494938689563 / 100000000000000000000)) (y := (9468922690383679721 / 25000000000000000000)) (u := (18255849549343632001 / 12500000000000000000))
  · norm_num [world12720, agent12720, scalar12720, tp12720, tm12720, ep12720, em12720, dsL]
  · norm_num [world12720, agent12720, scalar12720, tp12720, tm12720, ep12720, em12720, dsL]
  · norm_num [world12720, agent12720, scalar12720, tp12720, tm12720, ep12720, em12720, dsL]
  · norm_num [world12720, agent12720, scalar12720, tp12720, tm12720, ep12720, em12720, dsL]
  · norm_num [world12720, agent12720, scalar12720, tp12720, tm12720, ep12720, em12720, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12720, agent12720, tp12720, tm12720, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12720, agent12720, scalar12720, tp12720, tm12720, ep12720, em12720, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12720, agent12720, tp12720, tm12720, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12720, agent12720, scalar12720, tp12720, tm12720, ep12720, em12720, dsL]

theorem negative12720 :
    Eminus aL (agent12720.root+dsL) scalar12720.worldRadius world12720.frame
      agent12720.frame tm12720 ≤ -em12720 := by
  apply negative_check (lo := (34213563678303707713 / 50000000000000000000)) (hi := (68427127356607415427 / 100000000000000000000))
    (y := (-((71685150921132231597 / 100000000000000000000)))) (u := (48828720607438209209 / 100000000000000000000))
  · norm_num [world12720, agent12720, scalar12720, tp12720, tm12720, ep12720, em12720, dsL]
  · norm_num [world12720, agent12720, scalar12720, tp12720, tm12720, ep12720, em12720, dsL]
  · norm_num [world12720, agent12720, scalar12720, tp12720, tm12720, ep12720, em12720, dsL]
  · norm_num [world12720, agent12720, scalar12720, tp12720, tm12720, ep12720, em12720, dsL]
  · norm_num [world12720, agent12720, scalar12720, tp12720, tm12720, ep12720, em12720, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12720, agent12720, tp12720, tm12720, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12720, agent12720, tp12720, tm12720, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12720, agent12720, scalar12720, tp12720, tm12720, ep12720, em12720, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12720, agent12720, tp12720, tm12720, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12720, agent12720, scalar12720, tp12720, tm12720, ep12720, em12720, dsL]

theorem tails12720 :
    exp (-((12720:ℝ)*ep12720)) ≤ scalar12720.upperTail ∧
    exp (-((12720:ℝ)*em12720)) ≤ scalar12720.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12720:ℝ)) (by norm_num [ep12720]) ?_)
      (show bp12720^8 ≤ scalar12720.upperTail by norm_num [bp12720, scalar12720])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12720, bp12720, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12720:ℝ)) (by norm_num [em12720]) ?_)
      (show bm12720^8 ≤ scalar12720.lowerTail by norm_num [bm12720, scalar12720])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12720, bm12720, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12720 :
    agent12720.root+dsL+scalar12720.worldRadius < √(1/100/aL) ∧
    2*(agent12720.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12720, agent12720, scalar12720, tp12720, tm12720, ep12720, em12720, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12720, agent12720, scalar12720, tp12720, tm12720, ep12720, em12720, dsL]

noncomputable def master12720 : MasterCertificate 12720 world12720 agent12720 :=
  master scalar12720 dsL tp12720 tm12720 ep12720 em12720
    (by norm_num [dsL]) (by norm_num [tp12720]) (by norm_num [tm12720])
    (by norm_num [ep12720]) (by norm_num [em12720])
    positive12720 negative12720 tails12720.1 tails12720.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12720.1 tailGuards12720.2

theorem preserves12720 : master12720.toScalarCertificate = scalar12720 := rfl

noncomputable def tp12721 : ℝ := (2318428279 / 10000000000)
noncomputable def tm12721 : ℝ := (-((6067194177 / 10000000000)))
noncomputable def ep12721 : ℝ := (6435314521266509 / 12500000000000000000)
noncomputable def em12721 : ℝ := (50159932863704511 / 100000000000000000000)
noncomputable def bp12721 : ℝ := (44103265429757630801 / 100000000000000000000)
noncomputable def bm12721 : ℝ := (22520305591890234203 / 50000000000000000000)

theorem positive12721 :
    Eplus aL (agent12721.root+dsL) scalar12721.worldRadius world12721.frame
      agent12721.frame tp12721 ≤ -ep12721 := by
  apply positive_check (eT := (115601619519391447387 / 100000000000000000000)) (y := (18938239267645691789 / 50000000000000000000)) (u := (36511986729403814003 / 25000000000000000000))
  · norm_num [world12721, agent12721, scalar12721, tp12721, tm12721, ep12721, em12721, dsL]
  · norm_num [world12721, agent12721, scalar12721, tp12721, tm12721, ep12721, em12721, dsL]
  · norm_num [world12721, agent12721, scalar12721, tp12721, tm12721, ep12721, em12721, dsL]
  · norm_num [world12721, agent12721, scalar12721, tp12721, tm12721, ep12721, em12721, dsL]
  · norm_num [world12721, agent12721, scalar12721, tp12721, tm12721, ep12721, em12721, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12721, agent12721, tp12721, tm12721, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12721, agent12721, scalar12721, tp12721, tm12721, ep12721, em12721, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12721, agent12721, tp12721, tm12721, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12721, agent12721, scalar12721, tp12721, tm12721, ep12721, em12721, dsL]

theorem negative12721 :
    Eminus aL (agent12721.root+dsL) scalar12721.worldRadius world12721.frame
      agent12721.frame tm12721 ≤ -em12721 := by
  apply negative_check (lo := (68426925576143842669 / 100000000000000000000)) (hi := (6842692557614384267 / 10000000000000000000))
    (y := (-((71685217850270502127 / 100000000000000000000)))) (u := (48828687926807214559 / 100000000000000000000))
  · norm_num [world12721, agent12721, scalar12721, tp12721, tm12721, ep12721, em12721, dsL]
  · norm_num [world12721, agent12721, scalar12721, tp12721, tm12721, ep12721, em12721, dsL]
  · norm_num [world12721, agent12721, scalar12721, tp12721, tm12721, ep12721, em12721, dsL]
  · norm_num [world12721, agent12721, scalar12721, tp12721, tm12721, ep12721, em12721, dsL]
  · norm_num [world12721, agent12721, scalar12721, tp12721, tm12721, ep12721, em12721, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12721, agent12721, tp12721, tm12721, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12721, agent12721, tp12721, tm12721, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12721, agent12721, scalar12721, tp12721, tm12721, ep12721, em12721, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12721, agent12721, tp12721, tm12721, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12721, agent12721, scalar12721, tp12721, tm12721, ep12721, em12721, dsL]

theorem tails12721 :
    exp (-((12721:ℝ)*ep12721)) ≤ scalar12721.upperTail ∧
    exp (-((12721:ℝ)*em12721)) ≤ scalar12721.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12721:ℝ)) (by norm_num [ep12721]) ?_)
      (show bp12721^8 ≤ scalar12721.upperTail by norm_num [bp12721, scalar12721])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12721, bp12721, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12721:ℝ)) (by norm_num [em12721]) ?_)
      (show bm12721^8 ≤ scalar12721.lowerTail by norm_num [bm12721, scalar12721])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12721, bm12721, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12721 :
    agent12721.root+dsL+scalar12721.worldRadius < √(1/100/aL) ∧
    2*(agent12721.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12721, agent12721, scalar12721, tp12721, tm12721, ep12721, em12721, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12721, agent12721, scalar12721, tp12721, tm12721, ep12721, em12721, dsL]

noncomputable def master12721 : MasterCertificate 12721 world12721 agent12721 :=
  master scalar12721 dsL tp12721 tm12721 ep12721 em12721
    (by norm_num [dsL]) (by norm_num [tp12721]) (by norm_num [tm12721])
    (by norm_num [ep12721]) (by norm_num [em12721])
    positive12721 negative12721 tails12721.1 tails12721.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12721.1 tailGuards12721.2

theorem preserves12721 : master12721.toScalarCertificate = scalar12721 := rfl

noncomputable def tp12722 : ℝ := (2318512741 / 10000000000)
noncomputable def tm12722 : ℝ := (-((1516843773 / 2500000000)))
noncomputable def ep12722 : ℝ := (51485109991489357 / 100000000000000000000)
noncomputable def em12722 : ℝ := (50162156245586639 / 100000000000000000000)
noncomputable def bp12722 : ℝ := (44098608309557023393 / 100000000000000000000)
noncomputable def bm12722 : ℝ := (45036194841999599609 / 100000000000000000000)

theorem positive12722 :
    Eplus aL (agent12722.root+dsL) scalar12722.worldRadius world12722.frame
      agent12722.frame tp12722 ≤ -ep12722 := by
  apply positive_check (eT := (115601860338046466411 / 100000000000000000000)) (y := (37877265990286334209 / 100000000000000000000)) (u := (73024548491998201629 / 50000000000000000000))
  · norm_num [world12722, agent12722, scalar12722, tp12722, tm12722, ep12722, em12722, dsL]
  · norm_num [world12722, agent12722, scalar12722, tp12722, tm12722, ep12722, em12722, dsL]
  · norm_num [world12722, agent12722, scalar12722, tp12722, tm12722, ep12722, em12722, dsL]
  · norm_num [world12722, agent12722, scalar12722, tp12722, tm12722, ep12722, em12722, dsL]
  · norm_num [world12722, agent12722, scalar12722, tp12722, tm12722, ep12722, em12722, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12722, agent12722, tp12722, tm12722, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12722, agent12722, scalar12722, tp12722, tm12722, ep12722, em12722, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12722, agent12722, tp12722, tm12722, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12722, agent12722, scalar12722, tp12722, tm12722, ep12722, em12722, dsL]

theorem negative12722 :
    Eminus aL (agent12722.root+dsL) scalar12722.worldRadius world12722.frame
      agent12722.frame tm12722 ≤ -em12722 := by
  apply negative_check (lo := (68426724200865286079 / 100000000000000000000)) (hi := (213833513127704019 / 312500000000000000))
    (y := (-((35842641870820421573 / 50000000000000000000)))) (u := (48828655752926219953 / 100000000000000000000))
  · norm_num [world12722, agent12722, scalar12722, tp12722, tm12722, ep12722, em12722, dsL]
  · norm_num [world12722, agent12722, scalar12722, tp12722, tm12722, ep12722, em12722, dsL]
  · norm_num [world12722, agent12722, scalar12722, tp12722, tm12722, ep12722, em12722, dsL]
  · norm_num [world12722, agent12722, scalar12722, tp12722, tm12722, ep12722, em12722, dsL]
  · norm_num [world12722, agent12722, scalar12722, tp12722, tm12722, ep12722, em12722, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12722, agent12722, tp12722, tm12722, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12722, agent12722, tp12722, tm12722, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12722, agent12722, scalar12722, tp12722, tm12722, ep12722, em12722, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12722, agent12722, tp12722, tm12722, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12722, agent12722, scalar12722, tp12722, tm12722, ep12722, em12722, dsL]

theorem tails12722 :
    exp (-((12722:ℝ)*ep12722)) ≤ scalar12722.upperTail ∧
    exp (-((12722:ℝ)*em12722)) ≤ scalar12722.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12722:ℝ)) (by norm_num [ep12722]) ?_)
      (show bp12722^8 ≤ scalar12722.upperTail by norm_num [bp12722, scalar12722])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12722, bp12722, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12722:ℝ)) (by norm_num [em12722]) ?_)
      (show bm12722^8 ≤ scalar12722.lowerTail by norm_num [bm12722, scalar12722])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12722, bm12722, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12722 :
    agent12722.root+dsL+scalar12722.worldRadius < √(1/100/aL) ∧
    2*(agent12722.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12722, agent12722, scalar12722, tp12722, tm12722, ep12722, em12722, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12722, agent12722, scalar12722, tp12722, tm12722, ep12722, em12722, dsL]

noncomputable def master12722 : MasterCertificate 12722 world12722 agent12722 :=
  master scalar12722 dsL tp12722 tm12722 ep12722 em12722
    (by norm_num [dsL]) (by norm_num [tp12722]) (by norm_num [tm12722])
    (by norm_num [ep12722]) (by norm_num [em12722])
    positive12722 negative12722 tails12722.1 tails12722.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12722.1 tailGuards12722.2

theorem preserves12722 : master12722.toScalarCertificate = scalar12722 := rfl

noncomputable def tp12723 : ℝ := (463719417 / 2000000000)
noncomputable def tm12723 : ℝ := (-((3033777999 / 5000000000)))
noncomputable def ep12723 : ℝ := (25743851300492767 / 50000000000000000000)
noncomputable def em12723 : ℝ := (50164378457594721 / 100000000000000000000)
noncomputable def bp12723 : ℝ := (44093952245027964531 / 100000000000000000000)
noncomputable def bm12723 : ℝ := (22515889760389134833 / 50000000000000000000)

theorem positive12723 :
    Eplus aL (agent12723.root+dsL) scalar12723.worldRadius world12723.frame
      agent12723.frame tp12723 ≤ -ep12723 := by
  apply positive_check (eT := (57801050168255915771 / 50000000000000000000)) (y := (7575610398581370907 / 20000000000000000000)) (u := (146050244938237413041 / 100000000000000000000))
  · norm_num [world12723, agent12723, scalar12723, tp12723, tm12723, ep12723, em12723, dsL]
  · norm_num [world12723, agent12723, scalar12723, tp12723, tm12723, ep12723, em12723, dsL]
  · norm_num [world12723, agent12723, scalar12723, tp12723, tm12723, ep12723, em12723, dsL]
  · norm_num [world12723, agent12723, scalar12723, tp12723, tm12723, ep12723, em12723, dsL]
  · norm_num [world12723, agent12723, scalar12723, tp12723, tm12723, ep12723, em12723, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12723, agent12723, tp12723, tm12723, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12723, agent12723, scalar12723, tp12723, tm12723, ep12723, em12723, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12723, agent12723, tp12723, tm12723, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12723, agent12723, scalar12723, tp12723, tm12723, ep12723, em12723, dsL]

theorem negative12723 :
    Eminus aL (agent12723.root+dsL) scalar12723.worldRadius world12723.frame
      agent12723.frame tm12723 ≤ -em12723 := by
  apply negative_check (lo := (34213261403544749083 / 50000000000000000000)) (hi := (68426522807089498167 / 100000000000000000000))
    (y := (-((71685350677786470639 / 100000000000000000000)))) (u := (1525894470903657373 / 3125000000000000000))
  · norm_num [world12723, agent12723, scalar12723, tp12723, tm12723, ep12723, em12723, dsL]
  · norm_num [world12723, agent12723, scalar12723, tp12723, tm12723, ep12723, em12723, dsL]
  · norm_num [world12723, agent12723, scalar12723, tp12723, tm12723, ep12723, em12723, dsL]
  · norm_num [world12723, agent12723, scalar12723, tp12723, tm12723, ep12723, em12723, dsL]
  · norm_num [world12723, agent12723, scalar12723, tp12723, tm12723, ep12723, em12723, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12723, agent12723, tp12723, tm12723, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12723, agent12723, tp12723, tm12723, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12723, agent12723, scalar12723, tp12723, tm12723, ep12723, em12723, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12723, agent12723, tp12723, tm12723, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12723, agent12723, scalar12723, tp12723, tm12723, ep12723, em12723, dsL]

theorem tails12723 :
    exp (-((12723:ℝ)*ep12723)) ≤ scalar12723.upperTail ∧
    exp (-((12723:ℝ)*em12723)) ≤ scalar12723.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12723:ℝ)) (by norm_num [ep12723]) ?_)
      (show bp12723^8 ≤ scalar12723.upperTail by norm_num [bp12723, scalar12723])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12723, bp12723, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12723:ℝ)) (by norm_num [em12723]) ?_)
      (show bm12723^8 ≤ scalar12723.lowerTail by norm_num [bm12723, scalar12723])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12723, bm12723, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12723 :
    agent12723.root+dsL+scalar12723.worldRadius < √(1/100/aL) ∧
    2*(agent12723.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12723, agent12723, scalar12723, tp12723, tm12723, ep12723, em12723, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12723, agent12723, scalar12723, tp12723, tm12723, ep12723, em12723, dsL]

noncomputable def master12723 : MasterCertificate 12723 world12723 agent12723 :=
  master scalar12723 dsL tp12723 tm12723 ep12723 em12723
    (by norm_num [dsL]) (by norm_num [tp12723]) (by norm_num [tm12723])
    (by norm_num [ep12723]) (by norm_num [em12723])
    positive12723 negative12723 tails12723.1 tails12723.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12723.1 tailGuards12723.2

theorem preserves12723 : master12723.toScalarCertificate = scalar12723 := rfl

noncomputable def tp12724 : ℝ := (2318681489 / 10000000000)
noncomputable def tm12724 : ℝ := (-((379233541 / 625000000)))
noncomputable def ep12724 : ℝ := (51490294134549267 / 100000000000000000000)
noncomputable def em12724 : ℝ := (50166599704687879 / 100000000000000000000)
noncomputable def bp12724 : ℝ := (22044648570410810089 / 50000000000000000000)
noncomputable def bm12724 : ℝ := (22513682536657589083 / 50000000000000000000)

theorem positive12724 :
    Eplus aL (agent12724.root+dsL) scalar12724.worldRadius world12724.frame
      agent12724.frame tp12724 ≤ -ep12724 := by
  apply positive_check (eT := (115602340801448214869 / 100000000000000000000)) (y := (1183713728512918509 / 3125000000000000000)) (u := (146051394824831792741 / 100000000000000000000))
  · norm_num [world12724, agent12724, scalar12724, tp12724, tm12724, ep12724, em12724, dsL]
  · norm_num [world12724, agent12724, scalar12724, tp12724, tm12724, ep12724, em12724, dsL]
  · norm_num [world12724, agent12724, scalar12724, tp12724, tm12724, ep12724, em12724, dsL]
  · norm_num [world12724, agent12724, scalar12724, tp12724, tm12724, ep12724, em12724, dsL]
  · norm_num [world12724, agent12724, scalar12724, tp12724, tm12724, ep12724, em12724, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12724, agent12724, tp12724, tm12724, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12724, agent12724, scalar12724, tp12724, tm12724, ep12724, em12724, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12724, agent12724, tp12724, tm12724, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12724, agent12724, scalar12724, tp12724, tm12724, ep12724, em12724, dsL]

theorem negative12724 :
    Eminus aL (agent12724.root+dsL) scalar12724.worldRadius world12724.frame
      agent12724.frame tm12724 ≤ -em12724 := by
  apply negative_check (lo := (68426322417531247933 / 100000000000000000000)) (hi := (34213161208765623967 / 50000000000000000000))
    (y := (-((71685415883947042979 / 100000000000000000000)))) (u := (6103573903707131617 / 12500000000000000000))
  · norm_num [world12724, agent12724, scalar12724, tp12724, tm12724, ep12724, em12724, dsL]
  · norm_num [world12724, agent12724, scalar12724, tp12724, tm12724, ep12724, em12724, dsL]
  · norm_num [world12724, agent12724, scalar12724, tp12724, tm12724, ep12724, em12724, dsL]
  · norm_num [world12724, agent12724, scalar12724, tp12724, tm12724, ep12724, em12724, dsL]
  · norm_num [world12724, agent12724, scalar12724, tp12724, tm12724, ep12724, em12724, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12724, agent12724, tp12724, tm12724, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12724, agent12724, tp12724, tm12724, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12724, agent12724, scalar12724, tp12724, tm12724, ep12724, em12724, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12724, agent12724, tp12724, tm12724, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12724, agent12724, scalar12724, tp12724, tm12724, ep12724, em12724, dsL]

theorem tails12724 :
    exp (-((12724:ℝ)*ep12724)) ≤ scalar12724.upperTail ∧
    exp (-((12724:ℝ)*em12724)) ≤ scalar12724.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12724:ℝ)) (by norm_num [ep12724]) ?_)
      (show bp12724^8 ≤ scalar12724.upperTail by norm_num [bp12724, scalar12724])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12724, bp12724, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12724:ℝ)) (by norm_num [em12724]) ?_)
      (show bm12724^8 ≤ scalar12724.lowerTail by norm_num [bm12724, scalar12724])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12724, bm12724, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12724 :
    agent12724.root+dsL+scalar12724.worldRadius < √(1/100/aL) ∧
    2*(agent12724.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12724, agent12724, scalar12724, tp12724, tm12724, ep12724, em12724, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12724, agent12724, scalar12724, tp12724, tm12724, ep12724, em12724, dsL]

noncomputable def master12724 : MasterCertificate 12724 world12724 agent12724 :=
  master scalar12724 dsL tp12724 tm12724 ep12724 em12724
    (by norm_num [dsL]) (by norm_num [tp12724]) (by norm_num [tm12724])
    (by norm_num [ep12724]) (by norm_num [em12724])
    positive12724 negative12724 tails12724.1 tails12724.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12724.1 tailGuards12724.2

theorem preserves12724 : master12724.toScalarCertificate = scalar12724 := rfl

end BstLean.Part268
