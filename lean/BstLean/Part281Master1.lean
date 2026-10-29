import BstLean.Part261Checker
import BstLean.Part281Scalar1
namespace BstLean.Part281
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp11884 : ℝ := (1206564601 / 5000000000)
noncomputable def tm11884 : ℝ := (-((1248224247 / 2000000000)))
noncomputable def ep11884 : ℝ := (5589837614958967 / 10000000000000000000)
noncomputable def em11884 : ℝ := (53848059194749409 / 100000000000000000000)
noncomputable def bp11884 : ℝ := (21794390664684604959 / 50000000000000000000)
noncomputable def bm11884 : ℝ := (22468404684228058511 / 50000000000000000000)

theorem positive11884 :
    Eplus aL (agent11884.root+dsL) scalar11884.worldRadius world11884.frame
      agent11884.frame tp11884 ≤ -ep11884 := by
  apply positive_check (eT := (29159051106443255521 / 25000000000000000000)) (y := (39717177110234502563 / 100000000000000000000)) (u := (74380571838134873411 / 50000000000000000000))
  · norm_num [world11884, agent11884, scalar11884, tp11884, tm11884, ep11884, em11884, dsL]
  · norm_num [world11884, agent11884, scalar11884, tp11884, tm11884, ep11884, em11884, dsL]
  · norm_num [world11884, agent11884, scalar11884, tp11884, tm11884, ep11884, em11884, dsL]
  · norm_num [world11884, agent11884, scalar11884, tp11884, tm11884, ep11884, em11884, dsL]
  · norm_num [world11884, agent11884, scalar11884, tp11884, tm11884, ep11884, em11884, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11884, agent11884, tp11884, tm11884, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11884, agent11884, scalar11884, tp11884, tm11884, ep11884, em11884, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11884, agent11884, tp11884, tm11884, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11884, agent11884, scalar11884, tp11884, tm11884, ep11884, em11884, dsL]

theorem negative11884 :
    Eminus aL (agent11884.root+dsL) scalar11884.worldRadius world11884.frame
      agent11884.frame tm11884 ≤ -em11884 := by
  apply negative_check (lo := (6716570569775649579 / 10000000000000000000)) (hi := (67165705697756495791 / 100000000000000000000))
    (y := (-((72890938840818406893 / 100000000000000000000)))) (u := (48243485232459618933 / 100000000000000000000))
  · norm_num [world11884, agent11884, scalar11884, tp11884, tm11884, ep11884, em11884, dsL]
  · norm_num [world11884, agent11884, scalar11884, tp11884, tm11884, ep11884, em11884, dsL]
  · norm_num [world11884, agent11884, scalar11884, tp11884, tm11884, ep11884, em11884, dsL]
  · norm_num [world11884, agent11884, scalar11884, tp11884, tm11884, ep11884, em11884, dsL]
  · norm_num [world11884, agent11884, scalar11884, tp11884, tm11884, ep11884, em11884, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11884, agent11884, tp11884, tm11884, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11884, agent11884, tp11884, tm11884, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11884, agent11884, scalar11884, tp11884, tm11884, ep11884, em11884, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11884, agent11884, tp11884, tm11884, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11884, agent11884, scalar11884, tp11884, tm11884, ep11884, em11884, dsL]

theorem tails11884 :
    exp (-((11884:ℝ)*ep11884)) ≤ scalar11884.upperTail ∧
    exp (-((11884:ℝ)*em11884)) ≤ scalar11884.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11884:ℝ)) (by norm_num [ep11884]) ?_)
      (show bp11884^8 ≤ scalar11884.upperTail by norm_num [bp11884, scalar11884])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11884, bp11884, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11884:ℝ)) (by norm_num [em11884]) ?_)
      (show bm11884^8 ≤ scalar11884.lowerTail by norm_num [bm11884, scalar11884])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11884, bm11884, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11884 :
    agent11884.root+dsL+scalar11884.worldRadius < √(1/100/aL) ∧
    2*(agent11884.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11884, agent11884, scalar11884, tp11884, tm11884, ep11884, em11884, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11884, agent11884, scalar11884, tp11884, tm11884, ep11884, em11884, dsL]

noncomputable def master11884 : MasterCertificate 11884 world11884 agent11884 :=
  master scalar11884 dsL tp11884 tm11884 ep11884 em11884
    (by norm_num [dsL]) (by norm_num [tp11884]) (by norm_num [tm11884])
    (by norm_num [ep11884]) (by norm_num [em11884])
    positive11884 negative11884 tails11884.1 tails11884.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11884.1 tailGuards11884.2

theorem preserves11884 : master11884.toScalarCertificate = scalar11884 := rfl

noncomputable def tp11885 : ℝ := (2413228101 / 10000000000)
noncomputable def tm11885 : ℝ := (-((6241341189 / 10000000000)))
noncomputable def ep11885 : ℝ := (55901300539780937 / 100000000000000000000)
noncomputable def em11885 : ℝ := (53850586612050039 / 100000000000000000000)
noncomputable def bp11885 : ℝ := (21791921098217239483 / 50000000000000000000)
noncomputable def bm11885 : ℝ := (44932097630759537621 / 100000000000000000000)

theorem positive11885 :
    Eplus aL (agent11885.root+dsL) scalar11885.worldRadius world11885.frame
      agent11885.frame tp11885 ≤ -ep11885 := by
  apply positive_check (eT := (29159123384063071851 / 25000000000000000000)) (y := (19858916995617768447 / 50000000000000000000)) (u := (148762120863168951651 / 100000000000000000000))
  · norm_num [world11885, agent11885, scalar11885, tp11885, tm11885, ep11885, em11885, dsL]
  · norm_num [world11885, agent11885, scalar11885, tp11885, tm11885, ep11885, em11885, dsL]
  · norm_num [world11885, agent11885, scalar11885, tp11885, tm11885, ep11885, em11885, dsL]
  · norm_num [world11885, agent11885, scalar11885, tp11885, tm11885, ep11885, em11885, dsL]
  · norm_num [world11885, agent11885, scalar11885, tp11885, tm11885, ep11885, em11885, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11885, agent11885, tp11885, tm11885, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11885, agent11885, scalar11885, tp11885, tm11885, ep11885, em11885, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11885, agent11885, tp11885, tm11885, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11885, agent11885, scalar11885, tp11885, tm11885, ep11885, em11885, dsL]

theorem negative11885 :
    Eminus aL (agent11885.root+dsL) scalar11885.worldRadius world11885.frame
      agent11885.frame tm11885 ≤ -em11885 := by
  apply negative_check (lo := (67165428580103112757 / 100000000000000000000)) (hi := (33582714290051556379 / 50000000000000000000))
    (y := (-((72890581385983790047 / 100000000000000000000)))) (u := (24121828840719091723 / 50000000000000000000))
  · norm_num [world11885, agent11885, scalar11885, tp11885, tm11885, ep11885, em11885, dsL]
  · norm_num [world11885, agent11885, scalar11885, tp11885, tm11885, ep11885, em11885, dsL]
  · norm_num [world11885, agent11885, scalar11885, tp11885, tm11885, ep11885, em11885, dsL]
  · norm_num [world11885, agent11885, scalar11885, tp11885, tm11885, ep11885, em11885, dsL]
  · norm_num [world11885, agent11885, scalar11885, tp11885, tm11885, ep11885, em11885, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11885, agent11885, tp11885, tm11885, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11885, agent11885, tp11885, tm11885, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11885, agent11885, scalar11885, tp11885, tm11885, ep11885, em11885, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11885, agent11885, tp11885, tm11885, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11885, agent11885, scalar11885, tp11885, tm11885, ep11885, em11885, dsL]

theorem tails11885 :
    exp (-((11885:ℝ)*ep11885)) ≤ scalar11885.upperTail ∧
    exp (-((11885:ℝ)*em11885)) ≤ scalar11885.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11885:ℝ)) (by norm_num [ep11885]) ?_)
      (show bp11885^8 ≤ scalar11885.upperTail by norm_num [bp11885, scalar11885])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11885, bp11885, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11885:ℝ)) (by norm_num [em11885]) ?_)
      (show bm11885^8 ≤ scalar11885.lowerTail by norm_num [bm11885, scalar11885])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11885, bm11885, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11885 :
    agent11885.root+dsL+scalar11885.worldRadius < √(1/100/aL) ∧
    2*(agent11885.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11885, agent11885, scalar11885, tp11885, tm11885, ep11885, em11885, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11885, agent11885, scalar11885, tp11885, tm11885, ep11885, em11885, dsL]

noncomputable def master11885 : MasterCertificate 11885 world11885 agent11885 :=
  master scalar11885 dsL tp11885 tm11885 ep11885 em11885
    (by norm_num [dsL]) (by norm_num [tp11885]) (by norm_num [tm11885])
    (by norm_num [ep11885]) (by norm_num [em11885])
    positive11885 negative11885 tails11885.1 tails11885.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11885.1 tailGuards11885.2

theorem preserves11885 : master11885.toScalarCertificate = scalar11885 := rfl

noncomputable def tp11886 : ℝ := (1206663459 / 5000000000)
noncomputable def tm11886 : ℝ := (-((3120780509 / 5000000000)))
noncomputable def ep11886 : ℝ := (27952111084818893 / 50000000000000000000)
noncomputable def em11886 : ℝ := (26926555747366277 / 50000000000000000000)
noncomputable def bp11886 : ℝ := (43578905091802169173 / 100000000000000000000)
noncomputable def bm11886 : ℝ := (8985477559020883139 / 20000000000000000000)

theorem positive11886 :
    Eplus aL (agent11886.root+dsL) scalar11886.worldRadius world11886.frame
      agent11886.frame tp11886 ≤ -ep11886 := by
  apply positive_check (eT := (14579597759830335799 / 12500000000000000000)) (y := (39718490212164298609 / 100000000000000000000)) (u := (148763097074543173733 / 100000000000000000000))
  · norm_num [world11886, agent11886, scalar11886, tp11886, tm11886, ep11886, em11886, dsL]
  · norm_num [world11886, agent11886, scalar11886, tp11886, tm11886, ep11886, em11886, dsL]
  · norm_num [world11886, agent11886, scalar11886, tp11886, tm11886, ep11886, em11886, dsL]
  · norm_num [world11886, agent11886, scalar11886, tp11886, tm11886, ep11886, em11886, dsL]
  · norm_num [world11886, agent11886, scalar11886, tp11886, tm11886, ep11886, em11886, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11886, agent11886, tp11886, tm11886, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11886, agent11886, scalar11886, tp11886, tm11886, ep11886, em11886, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11886, agent11886, tp11886, tm11886, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11886, agent11886, scalar11886, tp11886, tm11886, ep11886, em11886, dsL]

theorem negative11886 :
    Eminus aL (agent11886.root+dsL) scalar11886.worldRadius world11886.frame
      agent11886.frame tm11886 ≤ -em11886 := by
  apply negative_check (lo := (13433030386027859709 / 20000000000000000000)) (hi := (33582575965069649273 / 50000000000000000000))
    (y := (-((9111277992712278823 / 12500000000000000000)))) (u := (12060957531485976737 / 25000000000000000000))
  · norm_num [world11886, agent11886, scalar11886, tp11886, tm11886, ep11886, em11886, dsL]
  · norm_num [world11886, agent11886, scalar11886, tp11886, tm11886, ep11886, em11886, dsL]
  · norm_num [world11886, agent11886, scalar11886, tp11886, tm11886, ep11886, em11886, dsL]
  · norm_num [world11886, agent11886, scalar11886, tp11886, tm11886, ep11886, em11886, dsL]
  · norm_num [world11886, agent11886, scalar11886, tp11886, tm11886, ep11886, em11886, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11886, agent11886, tp11886, tm11886, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11886, agent11886, tp11886, tm11886, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11886, agent11886, scalar11886, tp11886, tm11886, ep11886, em11886, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11886, agent11886, tp11886, tm11886, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11886, agent11886, scalar11886, tp11886, tm11886, ep11886, em11886, dsL]

theorem tails11886 :
    exp (-((11886:ℝ)*ep11886)) ≤ scalar11886.upperTail ∧
    exp (-((11886:ℝ)*em11886)) ≤ scalar11886.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11886:ℝ)) (by norm_num [ep11886]) ?_)
      (show bp11886^8 ≤ scalar11886.upperTail by norm_num [bp11886, scalar11886])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11886, bp11886, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11886:ℝ)) (by norm_num [em11886]) ?_)
      (show bm11886^8 ≤ scalar11886.lowerTail by norm_num [bm11886, scalar11886])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11886, bm11886, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11886 :
    agent11886.root+dsL+scalar11886.worldRadius < √(1/100/aL) ∧
    2*(agent11886.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11886, agent11886, scalar11886, tp11886, tm11886, ep11886, em11886, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11886, agent11886, scalar11886, tp11886, tm11886, ep11886, em11886, dsL]

noncomputable def master11886 : MasterCertificate 11886 world11886 agent11886 :=
  master scalar11886 dsL tp11886 tm11886 ep11886 em11886
    (by norm_num [dsL]) (by norm_num [tp11886]) (by norm_num [tm11886])
    (by norm_num [ep11886]) (by norm_num [em11886])
    positive11886 negative11886 tails11886.1 tails11886.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11886.1 tailGuards11886.2

theorem preserves11886 : master11886.toScalarCertificate = scalar11886 := rfl

noncomputable def tp11887 : ℝ := (2413425597 / 10000000000)
noncomputable def tm11887 : ℝ := (-((6241780533 / 10000000000)))
noncomputable def ep11887 : ℝ := (13976785615884827 / 25000000000000000000)
noncomputable def em11887 : ℝ := (1346390877807443 / 2500000000000000000)
noncomputable def bp11887 : ℝ := (43573969093139848521 / 100000000000000000000)
noncomputable def bm11887 : ℝ := (898453580280758523 / 2000000000000000000)

theorem positive11887 :
    Eplus aL (agent11887.root+dsL) scalar11887.worldRadius world11887.frame
      agent11887.frame tp11887 ≤ -ep11887 := by
  apply positive_check (eT := (116637069636489541721 / 100000000000000000000)) (y := (77576454234913151 / 195312500000000000)) (u := (37191017629536258349 / 25000000000000000000))
  · norm_num [world11887, agent11887, scalar11887, tp11887, tm11887, ep11887, em11887, dsL]
  · norm_num [world11887, agent11887, scalar11887, tp11887, tm11887, ep11887, em11887, dsL]
  · norm_num [world11887, agent11887, scalar11887, tp11887, tm11887, ep11887, em11887, dsL]
  · norm_num [world11887, agent11887, scalar11887, tp11887, tm11887, ep11887, em11887, dsL]
  · norm_num [world11887, agent11887, scalar11887, tp11887, tm11887, ep11887, em11887, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11887, agent11887, tp11887, tm11887, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11887, agent11887, scalar11887, tp11887, tm11887, ep11887, em11887, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11887, agent11887, tp11887, tm11887, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11887, agent11887, scalar11887, tp11887, tm11887, ep11887, em11887, dsL]

theorem negative11887 :
    Eminus aL (agent11887.root+dsL) scalar11887.worldRadius world11887.frame
      agent11887.frame tm11887 ≤ -em11887 := by
  apply negative_check (lo := (16791219139318992183 / 25000000000000000000)) (hi := (67164876557275968733 / 100000000000000000000))
    (y := (-((3644493227581122789 / 5000000000000000000)))) (u := (48244003509793115233 / 100000000000000000000))
  · norm_num [world11887, agent11887, scalar11887, tp11887, tm11887, ep11887, em11887, dsL]
  · norm_num [world11887, agent11887, scalar11887, tp11887, tm11887, ep11887, em11887, dsL]
  · norm_num [world11887, agent11887, scalar11887, tp11887, tm11887, ep11887, em11887, dsL]
  · norm_num [world11887, agent11887, scalar11887, tp11887, tm11887, ep11887, em11887, dsL]
  · norm_num [world11887, agent11887, scalar11887, tp11887, tm11887, ep11887, em11887, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11887, agent11887, tp11887, tm11887, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11887, agent11887, tp11887, tm11887, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11887, agent11887, scalar11887, tp11887, tm11887, ep11887, em11887, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11887, agent11887, tp11887, tm11887, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11887, agent11887, scalar11887, tp11887, tm11887, ep11887, em11887, dsL]

theorem tails11887 :
    exp (-((11887:ℝ)*ep11887)) ≤ scalar11887.upperTail ∧
    exp (-((11887:ℝ)*em11887)) ≤ scalar11887.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11887:ℝ)) (by norm_num [ep11887]) ?_)
      (show bp11887^8 ≤ scalar11887.upperTail by norm_num [bp11887, scalar11887])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11887, bp11887, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11887:ℝ)) (by norm_num [em11887]) ?_)
      (show bm11887^8 ≤ scalar11887.lowerTail by norm_num [bm11887, scalar11887])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11887, bm11887, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11887 :
    agent11887.root+dsL+scalar11887.worldRadius < √(1/100/aL) ∧
    2*(agent11887.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11887, agent11887, scalar11887, tp11887, tm11887, ep11887, em11887, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11887, agent11887, scalar11887, tp11887, tm11887, ep11887, em11887, dsL]

noncomputable def master11887 : MasterCertificate 11887 world11887 agent11887 :=
  master scalar11887 dsL tp11887 tm11887 ep11887 em11887
    (by norm_num [dsL]) (by norm_num [tp11887]) (by norm_num [tm11887])
    (by norm_num [ep11887]) (by norm_num [em11887])
    positive11887 negative11887 tails11887.1 tails11887.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11887.1 tailGuards11887.2

theorem preserves11887 : master11887.toScalarCertificate = scalar11887 := rfl

noncomputable def tp11888 : ℝ := (2413524317 / 10000000000)
noncomputable def tm11888 : ℝ := (-((6242000263 / 10000000000)))
noncomputable def ep11888 : ℝ := (55910061783769159 / 100000000000000000000)
noncomputable def em11888 : ℝ := (53858157875102063 / 100000000000000000000)
noncomputable def bp11888 : ℝ := (43569033965861244021 / 100000000000000000000)
noncomputable def bm11888 : ℝ := (1796718840545594111 / 4000000000000000000)

theorem positive11888 :
    Eplus aL (agent11888.root+dsL) scalar11888.worldRadius world11888.frame
      agent11888.frame tp11888 ≤ -ep11888 := by
  apply positive_check (eT := (116637357541087506049 / 100000000000000000000)) (y := (310310937266474283 / 781250000000000000)) (u := (148765045523785413867 / 100000000000000000000))
  · norm_num [world11888, agent11888, scalar11888, tp11888, tm11888, ep11888, em11888, dsL]
  · norm_num [world11888, agent11888, scalar11888, tp11888, tm11888, ep11888, em11888, dsL]
  · norm_num [world11888, agent11888, scalar11888, tp11888, tm11888, ep11888, em11888, dsL]
  · norm_num [world11888, agent11888, scalar11888, tp11888, tm11888, ep11888, em11888, dsL]
  · norm_num [world11888, agent11888, scalar11888, tp11888, tm11888, ep11888, em11888, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11888, agent11888, tp11888, tm11888, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11888, agent11888, scalar11888, tp11888, tm11888, ep11888, em11888, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11888, agent11888, tp11888, tm11888, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11888, agent11888, scalar11888, tp11888, tm11888, ep11888, em11888, dsL]

theorem negative11888 :
    Eminus aL (agent11888.root+dsL) scalar11888.worldRadius world11888.frame
      agent11888.frame tm11888 ≤ -em11888 := by
  apply negative_check (lo := (33582300097960018833 / 50000000000000000000)) (hi := (67164600195920037667 / 100000000000000000000))
    (y := (-((72889508197382635241 / 100000000000000000000)))) (u := (2412208771482570161 / 5000000000000000000))
  · norm_num [world11888, agent11888, scalar11888, tp11888, tm11888, ep11888, em11888, dsL]
  · norm_num [world11888, agent11888, scalar11888, tp11888, tm11888, ep11888, em11888, dsL]
  · norm_num [world11888, agent11888, scalar11888, tp11888, tm11888, ep11888, em11888, dsL]
  · norm_num [world11888, agent11888, scalar11888, tp11888, tm11888, ep11888, em11888, dsL]
  · norm_num [world11888, agent11888, scalar11888, tp11888, tm11888, ep11888, em11888, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11888, agent11888, tp11888, tm11888, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11888, agent11888, tp11888, tm11888, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11888, agent11888, scalar11888, tp11888, tm11888, ep11888, em11888, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11888, agent11888, tp11888, tm11888, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11888, agent11888, scalar11888, tp11888, tm11888, ep11888, em11888, dsL]

theorem tails11888 :
    exp (-((11888:ℝ)*ep11888)) ≤ scalar11888.upperTail ∧
    exp (-((11888:ℝ)*em11888)) ≤ scalar11888.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11888:ℝ)) (by norm_num [ep11888]) ?_)
      (show bp11888^8 ≤ scalar11888.upperTail by norm_num [bp11888, scalar11888])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11888, bp11888, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11888:ℝ)) (by norm_num [em11888]) ?_)
      (show bm11888^8 ≤ scalar11888.lowerTail by norm_num [bm11888, scalar11888])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11888, bm11888, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11888 :
    agent11888.root+dsL+scalar11888.worldRadius < √(1/100/aL) ∧
    2*(agent11888.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11888, agent11888, scalar11888, tp11888, tm11888, ep11888, em11888, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11888, agent11888, scalar11888, tp11888, tm11888, ep11888, em11888, dsL]

noncomputable def master11888 : MasterCertificate 11888 world11888 agent11888 :=
  master scalar11888 dsL tp11888 tm11888 ep11888 em11888
    (by norm_num [dsL]) (by norm_num [tp11888]) (by norm_num [tm11888])
    (by norm_num [ep11888]) (by norm_num [em11888])
    positive11888 negative11888 tails11888.1 tails11888.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11888.1 tailGuards11888.2

theorem preserves11888 : master11888.toScalarCertificate = scalar11888 := rfl

noncomputable def tp11889 : ℝ := (37712859 / 156250000)
noncomputable def tm11889 : ℝ := (-((312110973 / 500000000)))
noncomputable def ep11889 : ℝ := (2795648931448049 / 5000000000000000000)
noncomputable def em11889 : ℝ := (53860678306879971 / 100000000000000000000)
noncomputable def bp11889 : ℝ := (43564100681966062041 / 100000000000000000000)
noncomputable def bm11889 : ℝ := (44913264779271098711 / 100000000000000000000)

theorem positive11889 :
    Eplus aL (agent11889.root+dsL) scalar11889.worldRadius world11889.frame
      agent11889.frame tp11889 ≤ -ep11889 := by
  apply positive_check (eT := (29159411258456216013 / 25000000000000000000)) (y := (39720455138806040659 / 100000000000000000000)) (u := (148766020188989105229 / 100000000000000000000))
  · norm_num [world11889, agent11889, scalar11889, tp11889, tm11889, ep11889, em11889, dsL]
  · norm_num [world11889, agent11889, scalar11889, tp11889, tm11889, ep11889, em11889, dsL]
  · norm_num [world11889, agent11889, scalar11889, tp11889, tm11889, ep11889, em11889, dsL]
  · norm_num [world11889, agent11889, scalar11889, tp11889, tm11889, ep11889, em11889, dsL]
  · norm_num [world11889, agent11889, scalar11889, tp11889, tm11889, ep11889, em11889, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11889, agent11889, tp11889, tm11889, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11889, agent11889, scalar11889, tp11889, tm11889, ep11889, em11889, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11889, agent11889, tp11889, tm11889, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11889, agent11889, scalar11889, tp11889, tm11889, ep11889, em11889, dsL]

theorem negative11889 :
    Eminus aL (agent11889.root+dsL) scalar11889.worldRadius world11889.frame
      agent11889.frame tm11889 ≤ -em11889 := by
  apply negative_check (lo := (33582163024783394273 / 50000000000000000000)) (hi := (67164326049566788547 / 100000000000000000000))
    (y := (-((583113182829346881 / 800000000000000000)))) (u := (24122174637409143853 / 50000000000000000000))
  · norm_num [world11889, agent11889, scalar11889, tp11889, tm11889, ep11889, em11889, dsL]
  · norm_num [world11889, agent11889, scalar11889, tp11889, tm11889, ep11889, em11889, dsL]
  · norm_num [world11889, agent11889, scalar11889, tp11889, tm11889, ep11889, em11889, dsL]
  · norm_num [world11889, agent11889, scalar11889, tp11889, tm11889, ep11889, em11889, dsL]
  · norm_num [world11889, agent11889, scalar11889, tp11889, tm11889, ep11889, em11889, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11889, agent11889, tp11889, tm11889, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11889, agent11889, tp11889, tm11889, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11889, agent11889, scalar11889, tp11889, tm11889, ep11889, em11889, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11889, agent11889, tp11889, tm11889, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11889, agent11889, scalar11889, tp11889, tm11889, ep11889, em11889, dsL]

theorem tails11889 :
    exp (-((11889:ℝ)*ep11889)) ≤ scalar11889.upperTail ∧
    exp (-((11889:ℝ)*em11889)) ≤ scalar11889.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11889:ℝ)) (by norm_num [ep11889]) ?_)
      (show bp11889^8 ≤ scalar11889.upperTail by norm_num [bp11889, scalar11889])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11889, bp11889, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11889:ℝ)) (by norm_num [em11889]) ?_)
      (show bm11889^8 ≤ scalar11889.lowerTail by norm_num [bm11889, scalar11889])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11889, bm11889, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11889 :
    agent11889.root+dsL+scalar11889.worldRadius < √(1/100/aL) ∧
    2*(agent11889.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11889, agent11889, scalar11889, tp11889, tm11889, ep11889, em11889, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11889, agent11889, scalar11889, tp11889, tm11889, ep11889, em11889, dsL]

noncomputable def master11889 : MasterCertificate 11889 world11889 agent11889 :=
  master scalar11889 dsL tp11889 tm11889 ep11889 em11889
    (by norm_num [dsL]) (by norm_num [tp11889]) (by norm_num [tm11889])
    (by norm_num [ep11889]) (by norm_num [em11889])
    positive11889 negative11889 tails11889.1 tails11889.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11889.1 tailGuards11889.2

theorem preserves11889 : master11889.toScalarCertificate = scalar11889 := rfl

noncomputable def tp11890 : ℝ := (2413721557 / 10000000000)
noncomputable def tm11890 : ℝ := (-((6242438583 / 10000000000)))
noncomputable def ep11890 : ℝ := (55915893863154419 / 100000000000000000000)
noncomputable def em11890 : ℝ := (53863197278975499 / 100000000000000000000)
noncomputable def bp11890 : ℝ := (43559168681981311093 / 100000000000000000000)
noncomputable def bm11890 : ℝ := (4490855972929088661 / 10000000000000000000)

theorem positive11890 :
    Eplus aL (agent11890.root+dsL) scalar11890.worldRadius world11890.frame
      agent11890.frame tp11890 ≤ -ep11890 := by
  apply positive_check (eT := (116637931988339396979 / 100000000000000000000)) (y := (39721109452679413921 / 100000000000000000000)) (u := (148766993588882608853 / 100000000000000000000))
  · norm_num [world11890, agent11890, scalar11890, tp11890, tm11890, ep11890, em11890, dsL]
  · norm_num [world11890, agent11890, scalar11890, tp11890, tm11890, ep11890, em11890, dsL]
  · norm_num [world11890, agent11890, scalar11890, tp11890, tm11890, ep11890, em11890, dsL]
  · norm_num [world11890, agent11890, scalar11890, tp11890, tm11890, ep11890, em11890, dsL]
  · norm_num [world11890, agent11890, scalar11890, tp11890, tm11890, ep11890, em11890, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11890, agent11890, tp11890, tm11890, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11890, agent11890, scalar11890, tp11890, tm11890, ep11890, em11890, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11890, agent11890, tp11890, tm11890, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11890, agent11890, scalar11890, tp11890, tm11890, ep11890, em11890, dsL]

theorem negative11890 :
    Eminus aL (agent11890.root+dsL) scalar11890.worldRadius world11890.frame
      agent11890.frame tm11890 ≤ -em11890 := by
  apply negative_check (lo := (33582026076141256791 / 50000000000000000000)) (hi := (67164052152282513583 / 100000000000000000000))
    (y := (-((72888787964557918487 / 100000000000000000000)))) (u := (24122261450645081201 / 50000000000000000000))
  · norm_num [world11890, agent11890, scalar11890, tp11890, tm11890, ep11890, em11890, dsL]
  · norm_num [world11890, agent11890, scalar11890, tp11890, tm11890, ep11890, em11890, dsL]
  · norm_num [world11890, agent11890, scalar11890, tp11890, tm11890, ep11890, em11890, dsL]
  · norm_num [world11890, agent11890, scalar11890, tp11890, tm11890, ep11890, em11890, dsL]
  · norm_num [world11890, agent11890, scalar11890, tp11890, tm11890, ep11890, em11890, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11890, agent11890, tp11890, tm11890, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11890, agent11890, tp11890, tm11890, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11890, agent11890, scalar11890, tp11890, tm11890, ep11890, em11890, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11890, agent11890, tp11890, tm11890, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11890, agent11890, scalar11890, tp11890, tm11890, ep11890, em11890, dsL]

theorem tails11890 :
    exp (-((11890:ℝ)*ep11890)) ≤ scalar11890.upperTail ∧
    exp (-((11890:ℝ)*em11890)) ≤ scalar11890.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11890:ℝ)) (by norm_num [ep11890]) ?_)
      (show bp11890^8 ≤ scalar11890.upperTail by norm_num [bp11890, scalar11890])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11890, bp11890, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11890:ℝ)) (by norm_num [em11890]) ?_)
      (show bm11890^8 ≤ scalar11890.lowerTail by norm_num [bm11890, scalar11890])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11890, bm11890, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11890 :
    agent11890.root+dsL+scalar11890.worldRadius < √(1/100/aL) ∧
    2*(agent11890.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11890, agent11890, scalar11890, tp11890, tm11890, ep11890, em11890, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11890, agent11890, scalar11890, tp11890, tm11890, ep11890, em11890, dsL]

noncomputable def master11890 : MasterCertificate 11890 world11890 agent11890 :=
  master scalar11890 dsL tp11890 tm11890 ep11890 em11890
    (by norm_num [dsL]) (by norm_num [tp11890]) (by norm_num [tm11890])
    (by norm_num [ep11890]) (by norm_num [em11890])
    positive11890 negative11890 tails11890.1 tails11890.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11890.1 tailGuards11890.2

theorem preserves11890 : master11890.toScalarCertificate = scalar11890 := rfl

noncomputable def tp11891 : ℝ := (2413820083 / 10000000000)
noncomputable def tm11891 : ℝ := (-((1248531579 / 2000000000)))
noncomputable def ep11891 : ℝ := (55918807424579993 / 100000000000000000000)
noncomputable def em11891 : ℝ := (53865714694076849 / 100000000000000000000)
noncomputable def bp11891 : ℝ := (5444279750731100451 / 12500000000000000000)
noncomputable def bm11891 : ℝ := (44903855928625846519 / 100000000000000000000)

theorem positive11891 :
    Eplus aL (agent11891.root+dsL) scalar11891.worldRadius world11891.frame
      agent11891.frame tp11891 ≤ -ep11891 := by
  apply positive_check (eT := (23327643715128975393 / 20000000000000000000)) (y := (794435265315088987 / 2000000000000000000)) (u := (148767966250117719787 / 100000000000000000000))
  · norm_num [world11891, agent11891, scalar11891, tp11891, tm11891, ep11891, em11891, dsL]
  · norm_num [world11891, agent11891, scalar11891, tp11891, tm11891, ep11891, em11891, dsL]
  · norm_num [world11891, agent11891, scalar11891, tp11891, tm11891, ep11891, em11891, dsL]
  · norm_num [world11891, agent11891, scalar11891, tp11891, tm11891, ep11891, em11891, dsL]
  · norm_num [world11891, agent11891, scalar11891, tp11891, tm11891, ep11891, em11891, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11891, agent11891, tp11891, tm11891, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11891, agent11891, scalar11891, tp11891, tm11891, ep11891, em11891, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11891, agent11891, tp11891, tm11891, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11891, agent11891, scalar11891, tp11891, tm11891, ep11891, em11891, dsL]

theorem negative11891 :
    Eminus aL (agent11891.root+dsL) scalar11891.worldRadius world11891.frame
      agent11891.frame tm11891 ≤ -em11891 := by
  apply negative_check (lo := (67163777377880809449 / 100000000000000000000)) (hi := (1343275547557616189 / 2000000000000000000))
    (y := (-((36444215243292108127 / 50000000000000000000)))) (u := (241223476825706561 / 500000000000000000))
  · norm_num [world11891, agent11891, scalar11891, tp11891, tm11891, ep11891, em11891, dsL]
  · norm_num [world11891, agent11891, scalar11891, tp11891, tm11891, ep11891, em11891, dsL]
  · norm_num [world11891, agent11891, scalar11891, tp11891, tm11891, ep11891, em11891, dsL]
  · norm_num [world11891, agent11891, scalar11891, tp11891, tm11891, ep11891, em11891, dsL]
  · norm_num [world11891, agent11891, scalar11891, tp11891, tm11891, ep11891, em11891, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11891, agent11891, tp11891, tm11891, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11891, agent11891, tp11891, tm11891, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11891, agent11891, scalar11891, tp11891, tm11891, ep11891, em11891, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11891, agent11891, tp11891, tm11891, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11891, agent11891, scalar11891, tp11891, tm11891, ep11891, em11891, dsL]

theorem tails11891 :
    exp (-((11891:ℝ)*ep11891)) ≤ scalar11891.upperTail ∧
    exp (-((11891:ℝ)*em11891)) ≤ scalar11891.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11891:ℝ)) (by norm_num [ep11891]) ?_)
      (show bp11891^8 ≤ scalar11891.upperTail by norm_num [bp11891, scalar11891])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11891, bp11891, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11891:ℝ)) (by norm_num [em11891]) ?_)
      (show bm11891^8 ≤ scalar11891.lowerTail by norm_num [bm11891, scalar11891])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11891, bm11891, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11891 :
    agent11891.root+dsL+scalar11891.worldRadius < √(1/100/aL) ∧
    2*(agent11891.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11891, agent11891, scalar11891, tp11891, tm11891, ep11891, em11891, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11891, agent11891, scalar11891, tp11891, tm11891, ep11891, em11891, dsL]

noncomputable def master11891 : MasterCertificate 11891 world11891 agent11891 :=
  master scalar11891 dsL tp11891 tm11891 ep11891 em11891
    (by norm_num [dsL]) (by norm_num [tp11891]) (by norm_num [tm11891])
    (by norm_num [ep11891]) (by norm_num [em11891])
    positive11891 negative11891 tails11891.1 tails11891.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11891.1 tailGuards11891.2

theorem preserves11891 : master11891.toScalarCertificate = scalar11891 := rfl

noncomputable def tp11892 : ℝ := (2413918577 / 10000000000)
noncomputable def tm11892 : ℝ := (-((6242876779 / 10000000000)))
noncomputable def ep11892 : ℝ := (27960859607747161 / 50000000000000000000)
noncomputable def em11892 : ℝ := (10773646097070179 / 20000000000000000000)
noncomputable def bp11892 : ℝ := (43549308716793758021 / 100000000000000000000)
noncomputable def bm11892 : ℝ := (22449576710927485637 / 50000000000000000000)

theorem positive11892 :
    Eplus aL (agent11892.root+dsL) scalar11892.worldRadius world11892.frame
      agent11892.frame tp11892 ≤ -ep11892 := by
  apply positive_check (eT := (58319252483412098819 / 50000000000000000000)) (y := (397224172010592473 / 1000000000000000000)) (u := (18596117387444019837 / 12500000000000000000))
  · norm_num [world11892, agent11892, scalar11892, tp11892, tm11892, ep11892, em11892, dsL]
  · norm_num [world11892, agent11892, scalar11892, tp11892, tm11892, ep11892, em11892, dsL]
  · norm_num [world11892, agent11892, scalar11892, tp11892, tm11892, ep11892, em11892, dsL]
  · norm_num [world11892, agent11892, scalar11892, tp11892, tm11892, ep11892, em11892, dsL]
  · norm_num [world11892, agent11892, scalar11892, tp11892, tm11892, ep11892, em11892, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11892, agent11892, tp11892, tm11892, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11892, agent11892, scalar11892, tp11892, tm11892, ep11892, em11892, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11892, agent11892, tp11892, tm11892, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11892, agent11892, scalar11892, tp11892, tm11892, ep11892, em11892, dsL]

theorem negative11892 :
    Eminus aL (agent11892.root+dsL) scalar11892.worldRadius world11892.frame
      agent11892.frame tm11892 ≤ -em11892 := by
  apply negative_check (lo := (6716350436858997201 / 10000000000000000000)) (hi := (67163504368589972011 / 100000000000000000000))
    (y := (-((36444035196035070663 / 50000000000000000000)))) (u := (48244869091955444411 / 100000000000000000000))
  · norm_num [world11892, agent11892, scalar11892, tp11892, tm11892, ep11892, em11892, dsL]
  · norm_num [world11892, agent11892, scalar11892, tp11892, tm11892, ep11892, em11892, dsL]
  · norm_num [world11892, agent11892, scalar11892, tp11892, tm11892, ep11892, em11892, dsL]
  · norm_num [world11892, agent11892, scalar11892, tp11892, tm11892, ep11892, em11892, dsL]
  · norm_num [world11892, agent11892, scalar11892, tp11892, tm11892, ep11892, em11892, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11892, agent11892, tp11892, tm11892, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11892, agent11892, tp11892, tm11892, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11892, agent11892, scalar11892, tp11892, tm11892, ep11892, em11892, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11892, agent11892, tp11892, tm11892, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11892, agent11892, scalar11892, tp11892, tm11892, ep11892, em11892, dsL]

theorem tails11892 :
    exp (-((11892:ℝ)*ep11892)) ≤ scalar11892.upperTail ∧
    exp (-((11892:ℝ)*em11892)) ≤ scalar11892.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11892:ℝ)) (by norm_num [ep11892]) ?_)
      (show bp11892^8 ≤ scalar11892.upperTail by norm_num [bp11892, scalar11892])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11892, bp11892, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11892:ℝ)) (by norm_num [em11892]) ?_)
      (show bm11892^8 ≤ scalar11892.lowerTail by norm_num [bm11892, scalar11892])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11892, bm11892, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11892 :
    agent11892.root+dsL+scalar11892.worldRadius < √(1/100/aL) ∧
    2*(agent11892.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11892, agent11892, scalar11892, tp11892, tm11892, ep11892, em11892, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11892, agent11892, scalar11892, tp11892, tm11892, ep11892, em11892, dsL]

noncomputable def master11892 : MasterCertificate 11892 world11892 agent11892 :=
  master scalar11892 dsL tp11892 tm11892 ep11892 em11892
    (by norm_num [dsL]) (by norm_num [tp11892]) (by norm_num [tm11892])
    (by norm_num [ep11892]) (by norm_num [em11892])
    positive11892 negative11892 tails11892.1 tails11892.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11892.1 tailGuards11892.2

theorem preserves11892 : master11892.toScalarCertificate = scalar11892 := rfl

noncomputable def tp11893 : ℝ := (150876063 / 625000000)
noncomputable def tm11893 : ℝ := (-((6243095687 / 10000000000)))
noncomputable def ep11893 : ℝ := (27962314669329657 / 50000000000000000000)
noncomputable def em11893 : ℝ := (10774148944795657 / 20000000000000000000)
noncomputable def bp11893 : ℝ := (8708876149647718371 / 20000000000000000000)
noncomputable def bm11893 : ℝ := (22447226080720743817 / 50000000000000000000)

theorem positive11893 :
    Eplus aL (agent11893.root+dsL) scalar11893.worldRadius world11893.frame
      agent11893.frame tp11893 ≤ -ep11893 := by
  apply positive_check (eT := (58319395465670210281 / 50000000000000000000)) (y := (9930767623270862511 / 25000000000000000000)) (u := (37192477749585113071 / 25000000000000000000))
  · norm_num [world11893, agent11893, scalar11893, tp11893, tm11893, ep11893, em11893, dsL]
  · norm_num [world11893, agent11893, scalar11893, tp11893, tm11893, ep11893, em11893, dsL]
  · norm_num [world11893, agent11893, scalar11893, tp11893, tm11893, ep11893, em11893, dsL]
  · norm_num [world11893, agent11893, scalar11893, tp11893, tm11893, ep11893, em11893, dsL]
  · norm_num [world11893, agent11893, scalar11893, tp11893, tm11893, ep11893, em11893, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11893, agent11893, tp11893, tm11893, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11893, agent11893, scalar11893, tp11893, tm11893, ep11893, em11893, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11893, agent11893, tp11893, tm11893, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11893, agent11893, scalar11893, tp11893, tm11893, ep11893, em11893, dsL]

theorem negative11893 :
    Eminus aL (agent11893.root+dsL) scalar11893.worldRadius world11893.frame
      agent11893.frame tm11893 ≤ -em11893 := by
  apply negative_check (lo := (33581615594372535789 / 50000000000000000000)) (hi := (67163231188745071579 / 100000000000000000000))
    (y := (-((911096389240600137 / 1250000000000000000)))) (u := (48245042413320521123 / 100000000000000000000))
  · norm_num [world11893, agent11893, scalar11893, tp11893, tm11893, ep11893, em11893, dsL]
  · norm_num [world11893, agent11893, scalar11893, tp11893, tm11893, ep11893, em11893, dsL]
  · norm_num [world11893, agent11893, scalar11893, tp11893, tm11893, ep11893, em11893, dsL]
  · norm_num [world11893, agent11893, scalar11893, tp11893, tm11893, ep11893, em11893, dsL]
  · norm_num [world11893, agent11893, scalar11893, tp11893, tm11893, ep11893, em11893, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11893, agent11893, tp11893, tm11893, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11893, agent11893, tp11893, tm11893, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11893, agent11893, scalar11893, tp11893, tm11893, ep11893, em11893, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11893, agent11893, tp11893, tm11893, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11893, agent11893, scalar11893, tp11893, tm11893, ep11893, em11893, dsL]

theorem tails11893 :
    exp (-((11893:ℝ)*ep11893)) ≤ scalar11893.upperTail ∧
    exp (-((11893:ℝ)*em11893)) ≤ scalar11893.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11893:ℝ)) (by norm_num [ep11893]) ?_)
      (show bp11893^8 ≤ scalar11893.upperTail by norm_num [bp11893, scalar11893])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11893, bp11893, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11893:ℝ)) (by norm_num [em11893]) ?_)
      (show bm11893^8 ≤ scalar11893.lowerTail by norm_num [bm11893, scalar11893])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11893, bm11893, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11893 :
    agent11893.root+dsL+scalar11893.worldRadius < √(1/100/aL) ∧
    2*(agent11893.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11893, agent11893, scalar11893, tp11893, tm11893, ep11893, em11893, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11893, agent11893, scalar11893, tp11893, tm11893, ep11893, em11893, dsL]

noncomputable def master11893 : MasterCertificate 11893 world11893 agent11893 :=
  master scalar11893 dsL tp11893 tm11893 ep11893 em11893
    (by norm_num [dsL]) (by norm_num [tp11893]) (by norm_num [tm11893])
    (by norm_num [ep11893]) (by norm_num [em11893])
    positive11893 negative11893 tails11893.1 tails11893.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11893.1 tailGuards11893.2

theorem preserves11893 : master11893.toScalarCertificate = scalar11893 := rfl

noncomputable def tp11894 : ℝ := (2414115409 / 10000000000)
noncomputable def tm11894 : ℝ := (-((6243314461 / 10000000000)))
noncomputable def ep11894 : ℝ := (11185507616046473 / 20000000000000000000)
noncomputable def em11894 : ℝ := (53873257667214551 / 100000000000000000000)
noncomputable def bp11894 : ℝ := (2721215869681084849 / 6250000000000000000)
noncomputable def bm11894 : ℝ := (11222437993916612173 / 25000000000000000000)

theorem positive11894 :
    Eplus aL (agent11894.root+dsL) scalar11894.worldRadius world11894.frame
      agent11894.frame tp11894 ≤ -ep11894 := by
  apply positive_check (eT := (116639076714665242011 / 100000000000000000000)) (y := (3972372394368596513 / 10000000000000000000)) (u := (18596360392424557429 / 12500000000000000000))
  · norm_num [world11894, agent11894, scalar11894, tp11894, tm11894, ep11894, em11894, dsL]
  · norm_num [world11894, agent11894, scalar11894, tp11894, tm11894, ep11894, em11894, dsL]
  · norm_num [world11894, agent11894, scalar11894, tp11894, tm11894, ep11894, em11894, dsL]
  · norm_num [world11894, agent11894, scalar11894, tp11894, tm11894, ep11894, em11894, dsL]
  · norm_num [world11894, agent11894, scalar11894, tp11894, tm11894, ep11894, em11894, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11894, agent11894, tp11894, tm11894, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11894, agent11894, scalar11894, tp11894, tm11894, ep11894, em11894, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11894, agent11894, tp11894, tm11894, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11894, agent11894, scalar11894, tp11894, tm11894, ep11894, em11894, dsL]

theorem negative11894 :
    Eminus aL (agent11894.root+dsL) scalar11894.worldRadius world11894.frame
      agent11894.frame tm11894 ≤ -em11894 := by
  apply negative_check (lo := (33581479257431787557 / 50000000000000000000)) (hi := (13432591702972715023 / 20000000000000000000))
    (y := (-((14577470413552429609 / 20000000000000000000)))) (u := (4824521564782218749 / 10000000000000000000))
  · norm_num [world11894, agent11894, scalar11894, tp11894, tm11894, ep11894, em11894, dsL]
  · norm_num [world11894, agent11894, scalar11894, tp11894, tm11894, ep11894, em11894, dsL]
  · norm_num [world11894, agent11894, scalar11894, tp11894, tm11894, ep11894, em11894, dsL]
  · norm_num [world11894, agent11894, scalar11894, tp11894, tm11894, ep11894, em11894, dsL]
  · norm_num [world11894, agent11894, scalar11894, tp11894, tm11894, ep11894, em11894, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11894, agent11894, tp11894, tm11894, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11894, agent11894, tp11894, tm11894, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11894, agent11894, scalar11894, tp11894, tm11894, ep11894, em11894, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11894, agent11894, tp11894, tm11894, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11894, agent11894, scalar11894, tp11894, tm11894, ep11894, em11894, dsL]

theorem tails11894 :
    exp (-((11894:ℝ)*ep11894)) ≤ scalar11894.upperTail ∧
    exp (-((11894:ℝ)*em11894)) ≤ scalar11894.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11894:ℝ)) (by norm_num [ep11894]) ?_)
      (show bp11894^8 ≤ scalar11894.upperTail by norm_num [bp11894, scalar11894])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11894, bp11894, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11894:ℝ)) (by norm_num [em11894]) ?_)
      (show bm11894^8 ≤ scalar11894.lowerTail by norm_num [bm11894, scalar11894])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11894, bm11894, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11894 :
    agent11894.root+dsL+scalar11894.worldRadius < √(1/100/aL) ∧
    2*(agent11894.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11894, agent11894, scalar11894, tp11894, tm11894, ep11894, em11894, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11894, agent11894, scalar11894, tp11894, tm11894, ep11894, em11894, dsL]

noncomputable def master11894 : MasterCertificate 11894 world11894 agent11894 :=
  master scalar11894 dsL tp11894 tm11894 ep11894 em11894
    (by norm_num [dsL]) (by norm_num [tp11894]) (by norm_num [tm11894])
    (by norm_num [ep11894]) (by norm_num [em11894])
    positive11894 negative11894 tails11894.1 tails11894.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11894.1 tailGuards11894.2

theorem preserves11894 : master11894.toScalarCertificate = scalar11894 := rfl

noncomputable def tp11895 : ℝ := (1207106881 / 5000000000)
noncomputable def tm11895 : ℝ := (-((6243532947 / 10000000000)))
noncomputable def ep11895 : ℝ := (55930445366435153 / 100000000000000000000)
noncomputable def em11895 : ℝ := (26937884656059119 / 50000000000000000000)
noncomputable def bp11895 : ℝ := (8706905652898692009 / 20000000000000000000)
noncomputable def bm11895 : ℝ := (22442526433238258133 / 50000000000000000000)

theorem positive11895 :
    Eplus aL (agent11895.root+dsL) scalar11895.worldRadius world11895.frame
      agent11895.frame tp11895 ≤ -ep11895 := by
  apply positive_check (eT := (29159840545714503689 / 25000000000000000000)) (y := (9931094227498194031 / 25000000000000000000)) (u := (29754370913261849323 / 20000000000000000000))
  · norm_num [world11895, agent11895, scalar11895, tp11895, tm11895, ep11895, em11895, dsL]
  · norm_num [world11895, agent11895, scalar11895, tp11895, tm11895, ep11895, em11895, dsL]
  · norm_num [world11895, agent11895, scalar11895, tp11895, tm11895, ep11895, em11895, dsL]
  · norm_num [world11895, agent11895, scalar11895, tp11895, tm11895, ep11895, em11895, dsL]
  · norm_num [world11895, agent11895, scalar11895, tp11895, tm11895, ep11895, em11895, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11895, agent11895, tp11895, tm11895, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11895, agent11895, scalar11895, tp11895, tm11895, ep11895, em11895, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11895, agent11895, tp11895, tm11895, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11895, agent11895, scalar11895, tp11895, tm11895, ep11895, em11895, dsL]

theorem negative11895 :
    Eminus aL (agent11895.root+dsL) scalar11895.worldRadius world11895.frame
      agent11895.frame tm11895 ≤ -em11895 := by
  apply negative_check (lo := (16790671751616689567 / 25000000000000000000)) (hi := (67162687006466758269 / 100000000000000000000))
    (y := (-((18221747779801673927 / 25000000000000000000)))) (u := (48245389788545422193 / 100000000000000000000))
  · norm_num [world11895, agent11895, scalar11895, tp11895, tm11895, ep11895, em11895, dsL]
  · norm_num [world11895, agent11895, scalar11895, tp11895, tm11895, ep11895, em11895, dsL]
  · norm_num [world11895, agent11895, scalar11895, tp11895, tm11895, ep11895, em11895, dsL]
  · norm_num [world11895, agent11895, scalar11895, tp11895, tm11895, ep11895, em11895, dsL]
  · norm_num [world11895, agent11895, scalar11895, tp11895, tm11895, ep11895, em11895, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11895, agent11895, tp11895, tm11895, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11895, agent11895, tp11895, tm11895, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11895, agent11895, scalar11895, tp11895, tm11895, ep11895, em11895, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11895, agent11895, tp11895, tm11895, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11895, agent11895, scalar11895, tp11895, tm11895, ep11895, em11895, dsL]

theorem tails11895 :
    exp (-((11895:ℝ)*ep11895)) ≤ scalar11895.upperTail ∧
    exp (-((11895:ℝ)*em11895)) ≤ scalar11895.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11895:ℝ)) (by norm_num [ep11895]) ?_)
      (show bp11895^8 ≤ scalar11895.upperTail by norm_num [bp11895, scalar11895])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11895, bp11895, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11895:ℝ)) (by norm_num [em11895]) ?_)
      (show bm11895^8 ≤ scalar11895.lowerTail by norm_num [bm11895, scalar11895])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11895, bm11895, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11895 :
    agent11895.root+dsL+scalar11895.worldRadius < √(1/100/aL) ∧
    2*(agent11895.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11895, agent11895, scalar11895, tp11895, tm11895, ep11895, em11895, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11895, agent11895, scalar11895, tp11895, tm11895, ep11895, em11895, dsL]

noncomputable def master11895 : MasterCertificate 11895 world11895 agent11895 :=
  master scalar11895 dsL tp11895 tm11895 ep11895 em11895
    (by norm_num [dsL]) (by norm_num [tp11895]) (by norm_num [tm11895])
    (by norm_num [ep11895]) (by norm_num [em11895])
    positive11895 negative11895 tails11895.1 tails11895.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11895.1 tailGuards11895.2

theorem preserves11895 : master11895.toScalarCertificate = scalar11895 := rfl

noncomputable def tp11896 : ℝ := (482862399 / 2000000000)
noncomputable def tm11896 : ℝ := (-((1560937873 / 2500000000)))
noncomputable def ep11896 : ℝ := (873958596683677 / 1562500000000000000)
noncomputable def em11896 : ℝ := (1077565572698807 / 2000000000000000000)
noncomputable def bp11896 : ℝ := (4352960445043152597 / 10000000000000000000)
noncomputable def bm11896 : ℝ := (1122008887926884847 / 2500000000000000000)

theorem positive11896 :
    Eplus aL (agent11896.root+dsL) scalar11896.worldRadius world11896.frame
      agent11896.frame tp11896 ≤ -ep11896 := by
  apply positive_check (eT := (116639646800609646403 / 100000000000000000000)) (y := (7945005718828468573 / 20000000000000000000)) (u := (148772824092063591139 / 100000000000000000000))
  · norm_num [world11896, agent11896, scalar11896, tp11896, tm11896, ep11896, em11896, dsL]
  · norm_num [world11896, agent11896, scalar11896, tp11896, tm11896, ep11896, em11896, dsL]
  · norm_num [world11896, agent11896, scalar11896, tp11896, tm11896, ep11896, em11896, dsL]
  · norm_num [world11896, agent11896, scalar11896, tp11896, tm11896, ep11896, em11896, dsL]
  · norm_num [world11896, agent11896, scalar11896, tp11896, tm11896, ep11896, em11896, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11896, agent11896, tp11896, tm11896, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11896, agent11896, scalar11896, tp11896, tm11896, ep11896, em11896, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11896, agent11896, tp11896, tm11896, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11896, agent11896, scalar11896, tp11896, tm11896, ep11896, em11896, dsL]

theorem negative11896 :
    Eminus aL (agent11896.root+dsL) scalar11896.worldRadius world11896.frame
      agent11896.frame tm11896 ≤ -em11896 := by
  apply negative_check (lo := (2686496607102867883 / 4000000000000000000)) (hi := (16790603794392924269 / 25000000000000000000))
    (y := (-((72886631805684380103 / 100000000000000000000)))) (u := (24122781570533132823 / 50000000000000000000))
  · norm_num [world11896, agent11896, scalar11896, tp11896, tm11896, ep11896, em11896, dsL]
  · norm_num [world11896, agent11896, scalar11896, tp11896, tm11896, ep11896, em11896, dsL]
  · norm_num [world11896, agent11896, scalar11896, tp11896, tm11896, ep11896, em11896, dsL]
  · norm_num [world11896, agent11896, scalar11896, tp11896, tm11896, ep11896, em11896, dsL]
  · norm_num [world11896, agent11896, scalar11896, tp11896, tm11896, ep11896, em11896, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11896, agent11896, tp11896, tm11896, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11896, agent11896, tp11896, tm11896, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11896, agent11896, scalar11896, tp11896, tm11896, ep11896, em11896, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11896, agent11896, tp11896, tm11896, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11896, agent11896, scalar11896, tp11896, tm11896, ep11896, em11896, dsL]

theorem tails11896 :
    exp (-((11896:ℝ)*ep11896)) ≤ scalar11896.upperTail ∧
    exp (-((11896:ℝ)*em11896)) ≤ scalar11896.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11896:ℝ)) (by norm_num [ep11896]) ?_)
      (show bp11896^8 ≤ scalar11896.upperTail by norm_num [bp11896, scalar11896])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11896, bp11896, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11896:ℝ)) (by norm_num [em11896]) ?_)
      (show bm11896^8 ≤ scalar11896.lowerTail by norm_num [bm11896, scalar11896])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11896, bm11896, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11896 :
    agent11896.root+dsL+scalar11896.worldRadius < √(1/100/aL) ∧
    2*(agent11896.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11896, agent11896, scalar11896, tp11896, tm11896, ep11896, em11896, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11896, agent11896, scalar11896, tp11896, tm11896, ep11896, em11896, dsL]

noncomputable def master11896 : MasterCertificate 11896 world11896 agent11896 :=
  master scalar11896 dsL tp11896 tm11896 ep11896 em11896
    (by norm_num [dsL]) (by norm_num [tp11896]) (by norm_num [tm11896])
    (by norm_num [ep11896]) (by norm_num [em11896])
    positive11896 negative11896 tails11896.1 tails11896.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11896.1 tailGuards11896.2

theorem preserves11896 : master11896.toScalarCertificate = scalar11896 := rfl

noncomputable def tp11897 : ℝ := (603602563 / 2500000000)
noncomputable def tm11897 : ℝ := (-((6243969871 / 10000000000)))
noncomputable def ep11897 : ℝ := (5593625354893 / 10000000000000000)
noncomputable def em11897 : ℝ := (26940393327762321 / 50000000000000000000)
noncomputable def bp11897 : ℝ := (43524681822284220917 / 100000000000000000000)
noncomputable def bm11897 : ℝ := (1121891481170106751 / 2500000000000000000)

theorem positive11897 :
    Eplus aL (agent11897.root+dsL) scalar11897.worldRadius world11897.frame
      agent11897.frame tp11897 ≤ -ep11897 := by
  apply positive_check (eT := (116639931638736036167 / 100000000000000000000)) (y := (19862840535872885329 / 50000000000000000000)) (u := (18596724350573452043 / 12500000000000000000))
  · norm_num [world11897, agent11897, scalar11897, tp11897, tm11897, ep11897, em11897, dsL]
  · norm_num [world11897, agent11897, scalar11897, tp11897, tm11897, ep11897, em11897, dsL]
  · norm_num [world11897, agent11897, scalar11897, tp11897, tm11897, ep11897, em11897, dsL]
  · norm_num [world11897, agent11897, scalar11897, tp11897, tm11897, ep11897, em11897, dsL]
  · norm_num [world11897, agent11897, scalar11897, tp11897, tm11897, ep11897, em11897, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11897, agent11897, tp11897, tm11897, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11897, agent11897, scalar11897, tp11897, tm11897, ep11897, em11897, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11897, agent11897, tp11897, tm11897, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11897, agent11897, scalar11897, tp11897, tm11897, ep11897, em11897, dsL]

theorem negative11897 :
    Eminus aL (agent11897.root+dsL) scalar11897.worldRadius world11897.frame
      agent11897.frame tm11897 ≤ -em11897 := by
  apply negative_check (lo := (6716214399160571483 / 10000000000000000000)) (hi := (67162143991605714831 / 100000000000000000000))
    (y := (-((36443135886819554383 / 50000000000000000000)))) (u := (24122868420433341193 / 50000000000000000000))
  · norm_num [world11897, agent11897, scalar11897, tp11897, tm11897, ep11897, em11897, dsL]
  · norm_num [world11897, agent11897, scalar11897, tp11897, tm11897, ep11897, em11897, dsL]
  · norm_num [world11897, agent11897, scalar11897, tp11897, tm11897, ep11897, em11897, dsL]
  · norm_num [world11897, agent11897, scalar11897, tp11897, tm11897, ep11897, em11897, dsL]
  · norm_num [world11897, agent11897, scalar11897, tp11897, tm11897, ep11897, em11897, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11897, agent11897, tp11897, tm11897, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11897, agent11897, tp11897, tm11897, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11897, agent11897, scalar11897, tp11897, tm11897, ep11897, em11897, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11897, agent11897, tp11897, tm11897, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11897, agent11897, scalar11897, tp11897, tm11897, ep11897, em11897, dsL]

theorem tails11897 :
    exp (-((11897:ℝ)*ep11897)) ≤ scalar11897.upperTail ∧
    exp (-((11897:ℝ)*em11897)) ≤ scalar11897.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11897:ℝ)) (by norm_num [ep11897]) ?_)
      (show bp11897^8 ≤ scalar11897.upperTail by norm_num [bp11897, scalar11897])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11897, bp11897, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11897:ℝ)) (by norm_num [em11897]) ?_)
      (show bm11897^8 ≤ scalar11897.lowerTail by norm_num [bm11897, scalar11897])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11897, bm11897, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11897 :
    agent11897.root+dsL+scalar11897.worldRadius < √(1/100/aL) ∧
    2*(agent11897.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11897, agent11897, scalar11897, tp11897, tm11897, ep11897, em11897, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11897, agent11897, scalar11897, tp11897, tm11897, ep11897, em11897, dsL]

noncomputable def master11897 : MasterCertificate 11897 world11897 agent11897 :=
  master scalar11897 dsL tp11897 tm11897 ep11897 em11897
    (by norm_num [dsL]) (by norm_num [tp11897]) (by norm_num [tm11897])
    (by norm_num [ep11897]) (by norm_num [em11897])
    positive11897 negative11897 tails11897.1 tails11897.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11897.1 tailGuards11897.2

theorem preserves11897 : master11897.toScalarCertificate = scalar11897 := rfl

noncomputable def tp11898 : ℝ := (1207254207 / 5000000000)
noncomputable def tm11898 : ℝ := (-((1561047019 / 2500000000)))
noncomputable def ep11898 : ℝ := (55939155435156741 / 100000000000000000000)
noncomputable def em11898 : ℝ := (26941646632352497 / 50000000000000000000)
noncomputable def bp11898 : ℝ := (10879940097398571877 / 25000000000000000000)
noncomputable def bm11898 : ℝ := (11217741032124418041 / 25000000000000000000)

theorem positive11898 :
    Eplus aL (agent11898.root+dsL) scalar11898.worldRadius world11898.frame
      agent11898.frame tp11898 ≤ -ep11898 := by
  apply positive_check (eT := (116640215812294260579 / 100000000000000000000)) (y := (19863166303219601161 / 50000000000000000000)) (u := (148774764120633214801 / 100000000000000000000))
  · norm_num [world11898, agent11898, scalar11898, tp11898, tm11898, ep11898, em11898, dsL]
  · norm_num [world11898, agent11898, scalar11898, tp11898, tm11898, ep11898, em11898, dsL]
  · norm_num [world11898, agent11898, scalar11898, tp11898, tm11898, ep11898, em11898, dsL]
  · norm_num [world11898, agent11898, scalar11898, tp11898, tm11898, ep11898, em11898, dsL]
  · norm_num [world11898, agent11898, scalar11898, tp11898, tm11898, ep11898, em11898, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11898, agent11898, tp11898, tm11898, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11898, agent11898, scalar11898, tp11898, tm11898, ep11898, em11898, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11898, agent11898, tp11898, tm11898, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11898, agent11898, scalar11898, tp11898, tm11898, ep11898, em11898, dsL]

theorem negative11898 :
    Eminus aL (agent11898.root+dsL) scalar11898.worldRadius world11898.frame
      agent11898.frame tm11898 ≤ -em11898 := by
  apply negative_check (lo := (33580936741437062539 / 50000000000000000000)) (hi := (67161873482874125079 / 100000000000000000000))
    (y := (-((14577182283447931133 / 20000000000000000000)))) (u := (2412295534889005191 / 5000000000000000000))
  · norm_num [world11898, agent11898, scalar11898, tp11898, tm11898, ep11898, em11898, dsL]
  · norm_num [world11898, agent11898, scalar11898, tp11898, tm11898, ep11898, em11898, dsL]
  · norm_num [world11898, agent11898, scalar11898, tp11898, tm11898, ep11898, em11898, dsL]
  · norm_num [world11898, agent11898, scalar11898, tp11898, tm11898, ep11898, em11898, dsL]
  · norm_num [world11898, agent11898, scalar11898, tp11898, tm11898, ep11898, em11898, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11898, agent11898, tp11898, tm11898, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11898, agent11898, tp11898, tm11898, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11898, agent11898, scalar11898, tp11898, tm11898, ep11898, em11898, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11898, agent11898, tp11898, tm11898, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11898, agent11898, scalar11898, tp11898, tm11898, ep11898, em11898, dsL]

theorem tails11898 :
    exp (-((11898:ℝ)*ep11898)) ≤ scalar11898.upperTail ∧
    exp (-((11898:ℝ)*em11898)) ≤ scalar11898.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11898:ℝ)) (by norm_num [ep11898]) ?_)
      (show bp11898^8 ≤ scalar11898.upperTail by norm_num [bp11898, scalar11898])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11898, bp11898, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11898:ℝ)) (by norm_num [em11898]) ?_)
      (show bm11898^8 ≤ scalar11898.lowerTail by norm_num [bm11898, scalar11898])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11898, bm11898, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11898 :
    agent11898.root+dsL+scalar11898.worldRadius < √(1/100/aL) ∧
    2*(agent11898.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11898, agent11898, scalar11898, tp11898, tm11898, ep11898, em11898, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11898, agent11898, scalar11898, tp11898, tm11898, ep11898, em11898, dsL]

noncomputable def master11898 : MasterCertificate 11898 world11898 agent11898 :=
  master scalar11898 dsL tp11898 tm11898 ep11898 em11898
    (by norm_num [dsL]) (by norm_num [tp11898]) (by norm_num [tm11898])
    (by norm_num [ep11898]) (by norm_num [em11898])
    positive11898 negative11898 tails11898.1 tails11898.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11898.1 tailGuards11898.2

theorem preserves11898 : master11898.toScalarCertificate = scalar11898 := rfl

noncomputable def tp11899 : ℝ := (2414606563 / 10000000000)
noncomputable def tm11899 : ℝ := (-((6244406319 / 10000000000)))
noncomputable def ep11899 : ℝ := (55942055757832653 / 100000000000000000000)
noncomputable def em11899 : ℝ := (53885798447017629 / 100000000000000000000)
noncomputable def bp11899 : ℝ := (1740593608386764991 / 4000000000000000000)
noncomputable def bm11899 : ℝ := (44866270172453753017 / 100000000000000000000)

theorem positive11899 :
    Eplus aL (agent11899.root+dsL) scalar11899.worldRadius world11899.frame
      agent11899.frame tp11899 ≤ -ep11899 := by
  apply positive_check (eT := (58320249965558521681 / 50000000000000000000)) (y := (39726984330636500913 / 100000000000000000000)) (u := (37193933431232508087 / 25000000000000000000))
  · norm_num [world11899, agent11899, scalar11899, tp11899, tm11899, ep11899, em11899, dsL]
  · norm_num [world11899, agent11899, scalar11899, tp11899, tm11899, ep11899, em11899, dsL]
  · norm_num [world11899, agent11899, scalar11899, tp11899, tm11899, ep11899, em11899, dsL]
  · norm_num [world11899, agent11899, scalar11899, tp11899, tm11899, ep11899, em11899, dsL]
  · norm_num [world11899, agent11899, scalar11899, tp11899, tm11899, ep11899, em11899, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11899, agent11899, tp11899, tm11899, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11899, agent11899, scalar11899, tp11899, tm11899, ep11899, em11899, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11899, agent11899, tp11899, tm11899, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11899, agent11899, scalar11899, tp11899, tm11899, ep11899, em11899, dsL]

theorem negative11899 :
    Eminus aL (agent11899.root+dsL) scalar11899.worldRadius world11899.frame
      agent11899.frame tm11899 ≤ -em11899 := by
  apply negative_check (lo := (33580801371778269267 / 50000000000000000000)) (hi := (13432320548711307707 / 20000000000000000000))
    (y := (-((36442776078109826033 / 50000000000000000000)))) (u := (24123042013421169191 / 50000000000000000000))
  · norm_num [world11899, agent11899, scalar11899, tp11899, tm11899, ep11899, em11899, dsL]
  · norm_num [world11899, agent11899, scalar11899, tp11899, tm11899, ep11899, em11899, dsL]
  · norm_num [world11899, agent11899, scalar11899, tp11899, tm11899, ep11899, em11899, dsL]
  · norm_num [world11899, agent11899, scalar11899, tp11899, tm11899, ep11899, em11899, dsL]
  · norm_num [world11899, agent11899, scalar11899, tp11899, tm11899, ep11899, em11899, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11899, agent11899, tp11899, tm11899, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11899, agent11899, tp11899, tm11899, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11899, agent11899, scalar11899, tp11899, tm11899, ep11899, em11899, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11899, agent11899, tp11899, tm11899, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11899, agent11899, scalar11899, tp11899, tm11899, ep11899, em11899, dsL]

theorem tails11899 :
    exp (-((11899:ℝ)*ep11899)) ≤ scalar11899.upperTail ∧
    exp (-((11899:ℝ)*em11899)) ≤ scalar11899.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11899:ℝ)) (by norm_num [ep11899]) ?_)
      (show bp11899^8 ≤ scalar11899.upperTail by norm_num [bp11899, scalar11899])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11899, bp11899, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11899:ℝ)) (by norm_num [em11899]) ?_)
      (show bm11899^8 ≤ scalar11899.lowerTail by norm_num [bm11899, scalar11899])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11899, bm11899, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11899 :
    agent11899.root+dsL+scalar11899.worldRadius < √(1/100/aL) ∧
    2*(agent11899.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11899, agent11899, scalar11899, tp11899, tm11899, ep11899, em11899, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11899, agent11899, scalar11899, tp11899, tm11899, ep11899, em11899, dsL]

noncomputable def master11899 : MasterCertificate 11899 world11899 agent11899 :=
  master scalar11899 dsL tp11899 tm11899 ep11899 em11899
    (by norm_num [dsL]) (by norm_num [tp11899]) (by norm_num [tm11899])
    (by norm_num [ep11899]) (by norm_num [em11899])
    positive11899 negative11899 tails11899.1 tails11899.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11899.1 tailGuards11899.2

theorem preserves11899 : master11899.toScalarCertificate = scalar11899 := rfl

noncomputable def tp11900 : ℝ := (2414704659 / 10000000000)
noncomputable def tm11900 : ℝ := (-((6244624211 / 10000000000)))
noncomputable def ep11900 : ℝ := (55944953490593857 / 100000000000000000000)
noncomputable def em11900 : ℝ := (26944150634519591 / 50000000000000000000)
noncomputable def bp11900 : ℝ := (21754960973368908229 / 50000000000000000000)
noncomputable def bm11900 : ℝ := (22430789000769443191 / 50000000000000000000)

theorem positive11900 :
    Eplus aL (agent11900.root+dsL) scalar11900.worldRadius world11900.frame
      agent11900.frame tp11900 ≤ -ep11900 := by
  apply positive_check (eT := (116640783697718790299 / 100000000000000000000)) (y := (9931908936378719347 / 25000000000000000000)) (u := (74388351437675760951 / 50000000000000000000))
  · norm_num [world11900, agent11900, scalar11900, tp11900, tm11900, ep11900, em11900, dsL]
  · norm_num [world11900, agent11900, scalar11900, tp11900, tm11900, ep11900, em11900, dsL]
  · norm_num [world11900, agent11900, scalar11900, tp11900, tm11900, ep11900, em11900, dsL]
  · norm_num [world11900, agent11900, scalar11900, tp11900, tm11900, ep11900, em11900, dsL]
  · norm_num [world11900, agent11900, scalar11900, tp11900, tm11900, ep11900, em11900, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11900, agent11900, tp11900, tm11900, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11900, agent11900, scalar11900, tp11900, tm11900, ep11900, em11900, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11900, agent11900, tp11900, tm11900, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11900, agent11900, scalar11900, tp11900, tm11900, ep11900, em11900, dsL]

theorem negative11900 :
    Eminus aL (agent11900.root+dsL) scalar11900.worldRadius world11900.frame
      agent11900.frame tm11900 ≤ -em11900 := by
  apply negative_check (lo := (67161333439205415683 / 100000000000000000000)) (hi := (16790333359801353921 / 25000000000000000000))
    (y := (-((72885190456549237899 / 100000000000000000000)))) (u := (1929850341323393811 / 4000000000000000000))
  · norm_num [world11900, agent11900, scalar11900, tp11900, tm11900, ep11900, em11900, dsL]
  · norm_num [world11900, agent11900, scalar11900, tp11900, tm11900, ep11900, em11900, dsL]
  · norm_num [world11900, agent11900, scalar11900, tp11900, tm11900, ep11900, em11900, dsL]
  · norm_num [world11900, agent11900, scalar11900, tp11900, tm11900, ep11900, em11900, dsL]
  · norm_num [world11900, agent11900, scalar11900, tp11900, tm11900, ep11900, em11900, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11900, agent11900, tp11900, tm11900, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11900, agent11900, tp11900, tm11900, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11900, agent11900, scalar11900, tp11900, tm11900, ep11900, em11900, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11900, agent11900, tp11900, tm11900, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11900, agent11900, scalar11900, tp11900, tm11900, ep11900, em11900, dsL]

theorem tails11900 :
    exp (-((11900:ℝ)*ep11900)) ≤ scalar11900.upperTail ∧
    exp (-((11900:ℝ)*em11900)) ≤ scalar11900.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11900:ℝ)) (by norm_num [ep11900]) ?_)
      (show bp11900^8 ≤ scalar11900.upperTail by norm_num [bp11900, scalar11900])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11900, bp11900, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11900:ℝ)) (by norm_num [em11900]) ?_)
      (show bm11900^8 ≤ scalar11900.lowerTail by norm_num [bm11900, scalar11900])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11900, bm11900, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11900 :
    agent11900.root+dsL+scalar11900.worldRadius < √(1/100/aL) ∧
    2*(agent11900.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11900, agent11900, scalar11900, tp11900, tm11900, ep11900, em11900, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11900, agent11900, scalar11900, tp11900, tm11900, ep11900, em11900, dsL]

noncomputable def master11900 : MasterCertificate 11900 world11900 agent11900 :=
  master scalar11900 dsL tp11900 tm11900 ep11900 em11900
    (by norm_num [dsL]) (by norm_num [tp11900]) (by norm_num [tm11900])
    (by norm_num [ep11900]) (by norm_num [em11900])
    positive11900 negative11900 tails11900.1 tails11900.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11900.1 tailGuards11900.2

theorem preserves11900 : master11900.toScalarCertificate = scalar11900 := rfl

noncomputable def tp11901 : ℝ := (2414802677 / 10000000000)
noncomputable def tm11901 : ℝ := (-((6244842033 / 10000000000)))
noncomputable def ep11901 : ℝ := (55947850391238279 / 100000000000000000000)
noncomputable def em11901 : ℝ := (53890803289581207 / 100000000000000000000)
noncomputable def bp11901 : ℝ := (21752502231533515737 / 50000000000000000000)
noncomputable def bm11901 : ℝ := (22428443287747120141 / 50000000000000000000)

theorem positive11901 :
    Eplus aL (agent11901.root+dsL) scalar11901.worldRadius world11901.frame
      agent11901.frame tp11901 ≤ -ep11901 := by
  apply positive_check (eT := (29160266731570548367 / 25000000000000000000)) (y := (19864143152846992931 / 50000000000000000000)) (u := (29755534152096910737 / 20000000000000000000))
  · norm_num [world11901, agent11901, scalar11901, tp11901, tm11901, ep11901, em11901, dsL]
  · norm_num [world11901, agent11901, scalar11901, tp11901, tm11901, ep11901, em11901, dsL]
  · norm_num [world11901, agent11901, scalar11901, tp11901, tm11901, ep11901, em11901, dsL]
  · norm_num [world11901, agent11901, scalar11901, tp11901, tm11901, ep11901, em11901, dsL]
  · norm_num [world11901, agent11901, scalar11901, tp11901, tm11901, ep11901, em11901, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11901, agent11901, tp11901, tm11901, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11901, agent11901, scalar11901, tp11901, tm11901, ep11901, em11901, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11901, agent11901, tp11901, tm11901, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11901, agent11901, scalar11901, tp11901, tm11901, ep11901, em11901, dsL]

theorem negative11901 :
    Eminus aL (agent11901.root+dsL) scalar11901.worldRadius world11901.frame
      agent11901.frame tm11901 ≤ -em11901 := by
  apply negative_check (lo := (67161064366628306469 / 100000000000000000000)) (hi := (6716106436662830647 / 10000000000000000000))
    (y := (-((36442414626143683019 / 50000000000000000000)))) (u := (48246432800941591767 / 100000000000000000000))
  · norm_num [world11901, agent11901, scalar11901, tp11901, tm11901, ep11901, em11901, dsL]
  · norm_num [world11901, agent11901, scalar11901, tp11901, tm11901, ep11901, em11901, dsL]
  · norm_num [world11901, agent11901, scalar11901, tp11901, tm11901, ep11901, em11901, dsL]
  · norm_num [world11901, agent11901, scalar11901, tp11901, tm11901, ep11901, em11901, dsL]
  · norm_num [world11901, agent11901, scalar11901, tp11901, tm11901, ep11901, em11901, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11901, agent11901, tp11901, tm11901, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11901, agent11901, tp11901, tm11901, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11901, agent11901, scalar11901, tp11901, tm11901, ep11901, em11901, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11901, agent11901, tp11901, tm11901, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11901, agent11901, scalar11901, tp11901, tm11901, ep11901, em11901, dsL]

theorem tails11901 :
    exp (-((11901:ℝ)*ep11901)) ≤ scalar11901.upperTail ∧
    exp (-((11901:ℝ)*em11901)) ≤ scalar11901.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11901:ℝ)) (by norm_num [ep11901]) ?_)
      (show bp11901^8 ≤ scalar11901.upperTail by norm_num [bp11901, scalar11901])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11901, bp11901, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11901:ℝ)) (by norm_num [em11901]) ?_)
      (show bm11901^8 ≤ scalar11901.lowerTail by norm_num [bm11901, scalar11901])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11901, bm11901, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11901 :
    agent11901.root+dsL+scalar11901.worldRadius < √(1/100/aL) ∧
    2*(agent11901.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11901, agent11901, scalar11901, tp11901, tm11901, ep11901, em11901, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11901, agent11901, scalar11901, tp11901, tm11901, ep11901, em11901, dsL]

noncomputable def master11901 : MasterCertificate 11901 world11901 agent11901 :=
  master scalar11901 dsL tp11901 tm11901 ep11901 em11901
    (by norm_num [dsL]) (by norm_num [tp11901]) (by norm_num [tm11901])
    (by norm_num [ep11901]) (by norm_num [em11901])
    positive11901 negative11901 tails11901.1 tails11901.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11901.1 tailGuards11901.2

theorem preserves11901 : master11901.toScalarCertificate = scalar11901 := rfl

noncomputable def tp11902 : ℝ := (2414900637 / 10000000000)
noncomputable def tm11902 : ℝ := (-((6245059827 / 10000000000)))
noncomputable def ep11902 : ℝ := (5595074558344887 / 10000000000000000000)
noncomputable def em11902 : ℝ := (53893303731505961 / 100000000000000000000)
noncomputable def bp11902 : ℝ := (43500088325782290849 / 100000000000000000000)
noncomputable def bm11902 : ℝ := (44852196412898681211 / 100000000000000000000)

theorem positive11902 :
    Eplus aL (agent11902.root+dsL) scalar11902.worldRadius world11902.frame
      agent11902.frame tp11902 ≤ -ep11902 := by
  apply positive_check (eT := (116641349765501613351 / 100000000000000000000)) (y := (19864468208344230731 / 50000000000000000000)) (u := (74389318991811750441 / 50000000000000000000))
  · norm_num [world11902, agent11902, scalar11902, tp11902, tm11902, ep11902, em11902, dsL]
  · norm_num [world11902, agent11902, scalar11902, tp11902, tm11902, ep11902, em11902, dsL]
  · norm_num [world11902, agent11902, scalar11902, tp11902, tm11902, ep11902, em11902, dsL]
  · norm_num [world11902, agent11902, scalar11902, tp11902, tm11902, ep11902, em11902, dsL]
  · norm_num [world11902, agent11902, scalar11902, tp11902, tm11902, ep11902, em11902, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11902, agent11902, tp11902, tm11902, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11902, agent11902, scalar11902, tp11902, tm11902, ep11902, em11902, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11902, agent11902, tp11902, tm11902, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11902, agent11902, scalar11902, tp11902, tm11902, ep11902, em11902, dsL]

theorem negative11902 :
    Eminus aL (agent11902.root+dsL) scalar11902.worldRadius world11902.frame
      agent11902.frame tm11902 ≤ -em11902 := by
  apply negative_check (lo := (16790198836516976729 / 25000000000000000000)) (hi := (67160795346067906917 / 100000000000000000000))
    (y := (-((3644223440496606409 / 5000000000000000000)))) (u := (48246606701833703779 / 100000000000000000000))
  · norm_num [world11902, agent11902, scalar11902, tp11902, tm11902, ep11902, em11902, dsL]
  · norm_num [world11902, agent11902, scalar11902, tp11902, tm11902, ep11902, em11902, dsL]
  · norm_num [world11902, agent11902, scalar11902, tp11902, tm11902, ep11902, em11902, dsL]
  · norm_num [world11902, agent11902, scalar11902, tp11902, tm11902, ep11902, em11902, dsL]
  · norm_num [world11902, agent11902, scalar11902, tp11902, tm11902, ep11902, em11902, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11902, agent11902, tp11902, tm11902, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11902, agent11902, tp11902, tm11902, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11902, agent11902, scalar11902, tp11902, tm11902, ep11902, em11902, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11902, agent11902, tp11902, tm11902, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11902, agent11902, scalar11902, tp11902, tm11902, ep11902, em11902, dsL]

theorem tails11902 :
    exp (-((11902:ℝ)*ep11902)) ≤ scalar11902.upperTail ∧
    exp (-((11902:ℝ)*em11902)) ≤ scalar11902.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11902:ℝ)) (by norm_num [ep11902]) ?_)
      (show bp11902^8 ≤ scalar11902.upperTail by norm_num [bp11902, scalar11902])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11902, bp11902, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11902:ℝ)) (by norm_num [em11902]) ?_)
      (show bm11902^8 ≤ scalar11902.lowerTail by norm_num [bm11902, scalar11902])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11902, bm11902, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11902 :
    agent11902.root+dsL+scalar11902.worldRadius < √(1/100/aL) ∧
    2*(agent11902.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11902, agent11902, scalar11902, tp11902, tm11902, ep11902, em11902, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11902, agent11902, scalar11902, tp11902, tm11902, ep11902, em11902, dsL]

noncomputable def master11902 : MasterCertificate 11902 world11902 agent11902 :=
  master scalar11902 dsL tp11902 tm11902 ep11902 em11902
    (by norm_num [dsL]) (by norm_num [tp11902]) (by norm_num [tm11902])
    (by norm_num [ep11902]) (by norm_num [em11902])
    positive11902 negative11902 tails11902.1 tails11902.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11902.1 tailGuards11902.2

theorem preserves11902 : master11902.toScalarCertificate = scalar11902 := rfl

noncomputable def tp11903 : ℝ := (603749647 / 2500000000)
noncomputable def tm11903 : ℝ := (-((6245277383 / 10000000000)))
noncomputable def ep11903 : ℝ := (55953638678429629 / 100000000000000000000)
noncomputable def em11903 : ℝ := (3368487641668531 / 6250000000000000000)
noncomputable def bp11903 : ℝ := (8699034757288446441 / 20000000000000000000)
noncomputable def bm11903 : ℝ := (8969501546533632043 / 20000000000000000000)

theorem positive11903 :
    Eplus aL (agent11903.root+dsL) scalar11903.worldRadius world11903.frame
      agent11903.frame tp11903 ≤ -ep11903 := by
  apply positive_check (eT := (116641632579727506153 / 100000000000000000000)) (y := (39729586946627556243 / 100000000000000000000)) (u := (148779605836354644271 / 100000000000000000000))
  · norm_num [world11903, agent11903, scalar11903, tp11903, tm11903, ep11903, em11903, dsL]
  · norm_num [world11903, agent11903, scalar11903, tp11903, tm11903, ep11903, em11903, dsL]
  · norm_num [world11903, agent11903, scalar11903, tp11903, tm11903, ep11903, em11903, dsL]
  · norm_num [world11903, agent11903, scalar11903, tp11903, tm11903, ep11903, em11903, dsL]
  · norm_num [world11903, agent11903, scalar11903, tp11903, tm11903, ep11903, em11903, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11903, agent11903, tp11903, tm11903, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11903, agent11903, scalar11903, tp11903, tm11903, ep11903, em11903, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11903, agent11903, tp11903, tm11903, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11903, agent11903, scalar11903, tp11903, tm11903, ep11903, em11903, dsL]

theorem negative11903 :
    Eminus aL (agent11903.root+dsL) scalar11903.worldRadius world11903.frame
      agent11903.frame tm11903 ≤ -em11903 := by
  apply negative_check (lo := (33580263638248450911 / 50000000000000000000)) (hi := (67160527276496901823 / 100000000000000000000))
    (y := (-((14576821425891636231 / 20000000000000000000)))) (u := (4824678120070505031 / 10000000000000000000))
  · norm_num [world11903, agent11903, scalar11903, tp11903, tm11903, ep11903, em11903, dsL]
  · norm_num [world11903, agent11903, scalar11903, tp11903, tm11903, ep11903, em11903, dsL]
  · norm_num [world11903, agent11903, scalar11903, tp11903, tm11903, ep11903, em11903, dsL]
  · norm_num [world11903, agent11903, scalar11903, tp11903, tm11903, ep11903, em11903, dsL]
  · norm_num [world11903, agent11903, scalar11903, tp11903, tm11903, ep11903, em11903, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11903, agent11903, tp11903, tm11903, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11903, agent11903, tp11903, tm11903, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11903, agent11903, scalar11903, tp11903, tm11903, ep11903, em11903, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11903, agent11903, tp11903, tm11903, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11903, agent11903, scalar11903, tp11903, tm11903, ep11903, em11903, dsL]

theorem tails11903 :
    exp (-((11903:ℝ)*ep11903)) ≤ scalar11903.upperTail ∧
    exp (-((11903:ℝ)*em11903)) ≤ scalar11903.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11903:ℝ)) (by norm_num [ep11903]) ?_)
      (show bp11903^8 ≤ scalar11903.upperTail by norm_num [bp11903, scalar11903])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11903, bp11903, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11903:ℝ)) (by norm_num [em11903]) ?_)
      (show bm11903^8 ≤ scalar11903.lowerTail by norm_num [bm11903, scalar11903])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11903, bm11903, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11903 :
    agent11903.root+dsL+scalar11903.worldRadius < √(1/100/aL) ∧
    2*(agent11903.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11903, agent11903, scalar11903, tp11903, tm11903, ep11903, em11903, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11903, agent11903, scalar11903, tp11903, tm11903, ep11903, em11903, dsL]

noncomputable def master11903 : MasterCertificate 11903 world11903 agent11903 :=
  master scalar11903 dsL tp11903 tm11903 ep11903 em11903
    (by norm_num [dsL]) (by norm_num [tp11903]) (by norm_num [tm11903])
    (by norm_num [ep11903]) (by norm_num [em11903])
    positive11903 negative11903 tails11903.1 tails11903.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11903.1 tailGuards11903.2

theorem preserves11903 : master11903.toScalarCertificate = scalar11903 := rfl

noncomputable def tp11904 : ℝ := (2415096411 / 10000000000)
noncomputable def tm11904 : ℝ := (-((1249098969 / 2000000000)))
noncomputable def ep11904 : ℝ := (55956529956611597 / 100000000000000000000)
noncomputable def em11904 : ℝ := (13474574773603951 / 25000000000000000000)
noncomputable def bp11904 : ℝ := (2718141291468502573 / 6250000000000000000)
noncomputable def bm11904 : ℝ := (44842820401800492707 / 100000000000000000000)

theorem positive11904 :
    Eplus aL (agent11904.root+dsL) scalar11904.worldRadius world11904.frame
      agent11904.frame tp11904 ≤ -ep11904 := by
  apply positive_check (eT := (116641914484208549403 / 100000000000000000000)) (y := (39730235837819949389 / 100000000000000000000)) (u := (9298785703577828487 / 6250000000000000000))
  · norm_num [world11904, agent11904, scalar11904, tp11904, tm11904, ep11904, em11904, dsL]
  · norm_num [world11904, agent11904, scalar11904, tp11904, tm11904, ep11904, em11904, dsL]
  · norm_num [world11904, agent11904, scalar11904, tp11904, tm11904, ep11904, em11904, dsL]
  · norm_num [world11904, agent11904, scalar11904, tp11904, tm11904, ep11904, em11904, dsL]
  · norm_num [world11904, agent11904, scalar11904, tp11904, tm11904, ep11904, em11904, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11904, agent11904, tp11904, tm11904, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11904, agent11904, scalar11904, tp11904, tm11904, ep11904, em11904, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11904, agent11904, tp11904, tm11904, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11904, agent11904, scalar11904, tp11904, tm11904, ep11904, em11904, dsL]

theorem negative11904 :
    Eminus aL (agent11904.root+dsL) scalar11904.worldRadius world11904.frame
      agent11904.frame tm11904 ≤ -em11904 := by
  apply negative_check (lo := (33580129770711253253 / 50000000000000000000)) (hi := (67160259541422506507 / 100000000000000000000))
    (y := (-((72883745458952058643 / 100000000000000000000)))) (u := (48246955695398354451 / 100000000000000000000))
  · norm_num [world11904, agent11904, scalar11904, tp11904, tm11904, ep11904, em11904, dsL]
  · norm_num [world11904, agent11904, scalar11904, tp11904, tm11904, ep11904, em11904, dsL]
  · norm_num [world11904, agent11904, scalar11904, tp11904, tm11904, ep11904, em11904, dsL]
  · norm_num [world11904, agent11904, scalar11904, tp11904, tm11904, ep11904, em11904, dsL]
  · norm_num [world11904, agent11904, scalar11904, tp11904, tm11904, ep11904, em11904, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11904, agent11904, tp11904, tm11904, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11904, agent11904, tp11904, tm11904, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11904, agent11904, scalar11904, tp11904, tm11904, ep11904, em11904, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11904, agent11904, tp11904, tm11904, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11904, agent11904, scalar11904, tp11904, tm11904, ep11904, em11904, dsL]

theorem tails11904 :
    exp (-((11904:ℝ)*ep11904)) ≤ scalar11904.upperTail ∧
    exp (-((11904:ℝ)*em11904)) ≤ scalar11904.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11904:ℝ)) (by norm_num [ep11904]) ?_)
      (show bp11904^8 ≤ scalar11904.upperTail by norm_num [bp11904, scalar11904])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11904, bp11904, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11904:ℝ)) (by norm_num [em11904]) ?_)
      (show bm11904^8 ≤ scalar11904.lowerTail by norm_num [bm11904, scalar11904])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11904, bm11904, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11904 :
    agent11904.root+dsL+scalar11904.worldRadius < √(1/100/aL) ∧
    2*(agent11904.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11904, agent11904, scalar11904, tp11904, tm11904, ep11904, em11904, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11904, agent11904, scalar11904, tp11904, tm11904, ep11904, em11904, dsL]

noncomputable def master11904 : MasterCertificate 11904 world11904 agent11904 :=
  master scalar11904 dsL tp11904 tm11904 ep11904 em11904
    (by norm_num [dsL]) (by norm_num [tp11904]) (by norm_num [tm11904])
    (by norm_num [ep11904]) (by norm_num [em11904])
    positive11904 negative11904 tails11904.1 tails11904.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11904.1 tailGuards11904.2

theorem preserves11904 : master11904.toScalarCertificate = scalar11904 := rfl

noncomputable def tp11905 : ℝ := (2415194223 / 10000000000)
noncomputable def tm11905 : ℝ := (-((6245712271 / 10000000000)))
noncomputable def ep11905 : ℝ := (13989854908788581 / 25000000000000000000)
noncomputable def em11905 : ℝ := (26950397236524041 / 50000000000000000000)
noncomputable def bp11905 : ℝ := (21742674408178967327 / 50000000000000000000)
noncomputable def bm11905 : ℝ := (44838134247855923587 / 100000000000000000000)

theorem positive11905 :
    Eplus aL (agent11905.root+dsL) scalar11905.worldRadius world11905.frame
      agent11905.frame tp11905 ≤ -ep11905 := by
  apply positive_check (eT := (58321098174419270249 / 50000000000000000000)) (y := (19865442529960214447 / 50000000000000000000)) (u := (148781537176730555479 / 100000000000000000000))
  · norm_num [world11905, agent11905, scalar11905, tp11905, tm11905, ep11905, em11905, dsL]
  · norm_num [world11905, agent11905, scalar11905, tp11905, tm11905, ep11905, em11905, dsL]
  · norm_num [world11905, agent11905, scalar11905, tp11905, tm11905, ep11905, em11905, dsL]
  · norm_num [world11905, agent11905, scalar11905, tp11905, tm11905, ep11905, em11905, dsL]
  · norm_num [world11905, agent11905, scalar11905, tp11905, tm11905, ep11905, em11905, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11905, agent11905, tp11905, tm11905, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11905, agent11905, scalar11905, tp11905, tm11905, ep11905, em11905, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11905, agent11905, tp11905, tm11905, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11905, agent11905, scalar11905, tp11905, tm11905, ep11905, em11905, dsL]

theorem negative11905 :
    Eminus aL (agent11905.root+dsL) scalar11905.worldRadius world11905.frame
      agent11905.frame tm11905 ≤ -em11905 := by
  apply negative_check (lo := (13431998378512266987 / 20000000000000000000)) (hi := (8394998986570166867 / 12500000000000000000))
    (y := (-((14576676919328977897 / 20000000000000000000)))) (u := (1929885192031598237 / 4000000000000000000))
  · norm_num [world11905, agent11905, scalar11905, tp11905, tm11905, ep11905, em11905, dsL]
  · norm_num [world11905, agent11905, scalar11905, tp11905, tm11905, ep11905, em11905, dsL]
  · norm_num [world11905, agent11905, scalar11905, tp11905, tm11905, ep11905, em11905, dsL]
  · norm_num [world11905, agent11905, scalar11905, tp11905, tm11905, ep11905, em11905, dsL]
  · norm_num [world11905, agent11905, scalar11905, tp11905, tm11905, ep11905, em11905, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11905, agent11905, tp11905, tm11905, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11905, agent11905, tp11905, tm11905, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11905, agent11905, scalar11905, tp11905, tm11905, ep11905, em11905, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11905, agent11905, tp11905, tm11905, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11905, agent11905, scalar11905, tp11905, tm11905, ep11905, em11905, dsL]

theorem tails11905 :
    exp (-((11905:ℝ)*ep11905)) ≤ scalar11905.upperTail ∧
    exp (-((11905:ℝ)*em11905)) ≤ scalar11905.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11905:ℝ)) (by norm_num [ep11905]) ?_)
      (show bp11905^8 ≤ scalar11905.upperTail by norm_num [bp11905, scalar11905])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11905, bp11905, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11905:ℝ)) (by norm_num [em11905]) ?_)
      (show bm11905^8 ≤ scalar11905.lowerTail by norm_num [bm11905, scalar11905])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11905, bm11905, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11905 :
    agent11905.root+dsL+scalar11905.worldRadius < √(1/100/aL) ∧
    2*(agent11905.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11905, agent11905, scalar11905, tp11905, tm11905, ep11905, em11905, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11905, agent11905, scalar11905, tp11905, tm11905, ep11905, em11905, dsL]

noncomputable def master11905 : MasterCertificate 11905 world11905 agent11905 :=
  master scalar11905 dsL tp11905 tm11905 ep11905 em11905
    (by norm_num [dsL]) (by norm_num [tp11905]) (by norm_num [tm11905])
    (by norm_num [ep11905]) (by norm_num [em11905])
    positive11905 negative11905 tails11905.1 tails11905.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11905.1 tailGuards11905.2

theorem preserves11905 : master11905.toScalarCertificate = scalar11905 := rfl

noncomputable def tp11906 : ℝ := (301911503 / 1250000000)
noncomputable def tm11906 : ℝ := (-((1249185899 / 2000000000)))
noncomputable def ep11906 : ℝ := (13990576999851751 / 25000000000000000000)
noncomputable def em11906 : ℝ := (53903288606007321 / 100000000000000000000)
noncomputable def bp11906 : ℝ := (869608761206660557 / 2000000000000000000)
noncomputable def bm11906 : ℝ := (22416724567543401231 / 50000000000000000000)

theorem positive11906 :
    Eplus aL (agent11906.root+dsL) scalar11906.worldRadius world11906.frame
      agent11906.frame tp11906 ≤ -ep11906 := by
  apply positive_check (eT := (58321239086816333793 / 50000000000000000000)) (y := (19865767333723997881 / 50000000000000000000)) (u := (148782503675934907613 / 100000000000000000000))
  · norm_num [world11906, agent11906, scalar11906, tp11906, tm11906, ep11906, em11906, dsL]
  · norm_num [world11906, agent11906, scalar11906, tp11906, tm11906, ep11906, em11906, dsL]
  · norm_num [world11906, agent11906, scalar11906, tp11906, tm11906, ep11906, em11906, dsL]
  · norm_num [world11906, agent11906, scalar11906, tp11906, tm11906, ep11906, em11906, dsL]
  · norm_num [world11906, agent11906, scalar11906, tp11906, tm11906, ep11906, em11906, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11906, agent11906, tp11906, tm11906, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11906, agent11906, scalar11906, tp11906, tm11906, ep11906, em11906, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11906, agent11906, tp11906, tm11906, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11906, agent11906, scalar11906, tp11906, tm11906, ep11906, em11906, dsL]

theorem negative11906 :
    Eminus aL (agent11906.root+dsL) scalar11906.worldRadius world11906.frame
      agent11906.frame tm11906 ≤ -em11906 := by
  apply negative_check (lo := (67159725040461086239 / 100000000000000000000)) (hi := (419748281502881789 / 625000000000000000))
    (y := (-((72883022845324880653 / 100000000000000000000)))) (u := (48247304335734567699 / 100000000000000000000))
  · norm_num [world11906, agent11906, scalar11906, tp11906, tm11906, ep11906, em11906, dsL]
  · norm_num [world11906, agent11906, scalar11906, tp11906, tm11906, ep11906, em11906, dsL]
  · norm_num [world11906, agent11906, scalar11906, tp11906, tm11906, ep11906, em11906, dsL]
  · norm_num [world11906, agent11906, scalar11906, tp11906, tm11906, ep11906, em11906, dsL]
  · norm_num [world11906, agent11906, scalar11906, tp11906, tm11906, ep11906, em11906, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11906, agent11906, tp11906, tm11906, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11906, agent11906, tp11906, tm11906, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11906, agent11906, scalar11906, tp11906, tm11906, ep11906, em11906, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11906, agent11906, tp11906, tm11906, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11906, agent11906, scalar11906, tp11906, tm11906, ep11906, em11906, dsL]

theorem tails11906 :
    exp (-((11906:ℝ)*ep11906)) ≤ scalar11906.upperTail ∧
    exp (-((11906:ℝ)*em11906)) ≤ scalar11906.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11906:ℝ)) (by norm_num [ep11906]) ?_)
      (show bp11906^8 ≤ scalar11906.upperTail by norm_num [bp11906, scalar11906])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11906, bp11906, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11906:ℝ)) (by norm_num [em11906]) ?_)
      (show bm11906^8 ≤ scalar11906.lowerTail by norm_num [bm11906, scalar11906])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11906, bm11906, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11906 :
    agent11906.root+dsL+scalar11906.worldRadius < √(1/100/aL) ∧
    2*(agent11906.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11906, agent11906, scalar11906, tp11906, tm11906, ep11906, em11906, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11906, agent11906, scalar11906, tp11906, tm11906, ep11906, em11906, dsL]

noncomputable def master11906 : MasterCertificate 11906 world11906 agent11906 :=
  master scalar11906 dsL tp11906 tm11906 ep11906 em11906
    (by norm_num [dsL]) (by norm_num [tp11906]) (by norm_num [tm11906])
    (by norm_num [ep11906]) (by norm_num [em11906])
    positive11906 negative11906 tails11906.1 tails11906.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11906.1 tailGuards11906.2

theorem preserves11906 : master11906.toScalarCertificate = scalar11906 := rfl

noncomputable def tp11907 : ℝ := (2415389757 / 10000000000)
noncomputable def tm11907 : ℝ := (-((6246146699 / 10000000000)))
noncomputable def ep11907 : ℝ := (27982597571763127 / 50000000000000000000)
noncomputable def em11907 : ℝ := (26952890805178707 / 50000000000000000000)
noncomputable def bp11907 : ℝ := (21737764167232233531 / 50000000000000000000)
noncomputable def bm11907 : ℝ := (4482876498537110843 / 10000000000000000000)

theorem positive11907 :
    Eplus aL (agent11907.root+dsL) scalar11907.worldRadius world11907.frame
      agent11907.frame tp11907 ≤ -ep11907 := by
  apply positive_check (eT := (116642759534796463811 / 100000000000000000000)) (y := (39732183594964376621 / 100000000000000000000)) (u := (148783469169673494999 / 100000000000000000000))
  · norm_num [world11907, agent11907, scalar11907, tp11907, tm11907, ep11907, em11907, dsL]
  · norm_num [world11907, agent11907, scalar11907, tp11907, tm11907, ep11907, em11907, dsL]
  · norm_num [world11907, agent11907, scalar11907, tp11907, tm11907, ep11907, em11907, dsL]
  · norm_num [world11907, agent11907, scalar11907, tp11907, tm11907, ep11907, em11907, dsL]
  · norm_num [world11907, agent11907, scalar11907, tp11907, tm11907, ep11907, em11907, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11907, agent11907, tp11907, tm11907, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11907, agent11907, scalar11907, tp11907, tm11907, ep11907, em11907, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11907, agent11907, tp11907, tm11907, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11907, agent11907, scalar11907, tp11907, tm11907, ep11907, em11907, dsL]

theorem negative11907 :
    Eminus aL (agent11907.root+dsL) scalar11907.worldRadius world11907.frame
      agent11907.frame tm11907 ≤ -em11907 := by
  apply negative_check (lo := (33579729103040565071 / 50000000000000000000)) (hi := (67159458206081130143 / 100000000000000000000))
    (y := (-((72882662057216670473 / 100000000000000000000)))) (u := (1206186960164628907 / 2500000000000000000))
  · norm_num [world11907, agent11907, scalar11907, tp11907, tm11907, ep11907, em11907, dsL]
  · norm_num [world11907, agent11907, scalar11907, tp11907, tm11907, ep11907, em11907, dsL]
  · norm_num [world11907, agent11907, scalar11907, tp11907, tm11907, ep11907, em11907, dsL]
  · norm_num [world11907, agent11907, scalar11907, tp11907, tm11907, ep11907, em11907, dsL]
  · norm_num [world11907, agent11907, scalar11907, tp11907, tm11907, ep11907, em11907, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11907, agent11907, tp11907, tm11907, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11907, agent11907, tp11907, tm11907, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11907, agent11907, scalar11907, tp11907, tm11907, ep11907, em11907, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11907, agent11907, tp11907, tm11907, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11907, agent11907, scalar11907, tp11907, tm11907, ep11907, em11907, dsL]

theorem tails11907 :
    exp (-((11907:ℝ)*ep11907)) ≤ scalar11907.upperTail ∧
    exp (-((11907:ℝ)*em11907)) ≤ scalar11907.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11907:ℝ)) (by norm_num [ep11907]) ?_)
      (show bp11907^8 ≤ scalar11907.upperTail by norm_num [bp11907, scalar11907])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11907, bp11907, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11907:ℝ)) (by norm_num [em11907]) ?_)
      (show bm11907^8 ≤ scalar11907.lowerTail by norm_num [bm11907, scalar11907])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11907, bm11907, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11907 :
    agent11907.root+dsL+scalar11907.worldRadius < √(1/100/aL) ∧
    2*(agent11907.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11907, agent11907, scalar11907, tp11907, tm11907, ep11907, em11907, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11907, agent11907, scalar11907, tp11907, tm11907, ep11907, em11907, dsL]

noncomputable def master11907 : MasterCertificate 11907 world11907 agent11907 :=
  master scalar11907 dsL tp11907 tm11907 ep11907 em11907
    (by norm_num [dsL]) (by norm_num [tp11907]) (by norm_num [tm11907])
    (by norm_num [ep11907]) (by norm_num [em11907])
    positive11907 negative11907 tails11907.1 tails11907.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11907.1 tailGuards11907.2

theorem preserves11907 : master11907.toScalarCertificate = scalar11907 := rfl

noncomputable def tp11908 : ℝ := (2415487389 / 10000000000)
noncomputable def tm11908 : ℝ := (-((390397733 / 625000000)))
noncomputable def ep11908 : ℝ := (5596807975437681 / 10000000000000000000)
noncomputable def em11908 : ℝ := (13477068073703647 / 25000000000000000000)
noncomputable def bp11908 : ℝ := (43470620488404957337 / 100000000000000000000)
noncomputable def bm11908 : ℝ := (11206020648382803927 / 25000000000000000000)

theorem positive11908 :
    Eplus aL (agent11908.root+dsL) scalar11908.worldRadius world11908.frame
      agent11908.frame tp11908 ≤ -ep11908 := by
  apply positive_check (eT := (116643040187048185951 / 100000000000000000000)) (y := (39732831252029978017 / 100000000000000000000)) (u := (148784432779444459279 / 100000000000000000000))
  · norm_num [world11908, agent11908, scalar11908, tp11908, tm11908, ep11908, em11908, dsL]
  · norm_num [world11908, agent11908, scalar11908, tp11908, tm11908, ep11908, em11908, dsL]
  · norm_num [world11908, agent11908, scalar11908, tp11908, tm11908, ep11908, em11908, dsL]
  · norm_num [world11908, agent11908, scalar11908, tp11908, tm11908, ep11908, em11908, dsL]
  · norm_num [world11908, agent11908, scalar11908, tp11908, tm11908, ep11908, em11908, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11908, agent11908, tp11908, tm11908, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11908, agent11908, scalar11908, tp11908, tm11908, ep11908, em11908, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11908, agent11908, tp11908, tm11908, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11908, agent11908, scalar11908, tp11908, tm11908, ep11908, em11908, dsL]

theorem negative11908 :
    Eminus aL (agent11908.root+dsL) scalar11908.worldRadius world11908.frame
      agent11908.frame tm11908 ≤ -em11908 := by
  apply negative_check (lo := (67159192052850831041 / 100000000000000000000)) (hi := (33579596026425415521 / 50000000000000000000))
    (y := (-((72882300080628380639 / 100000000000000000000)))) (u := (12061913262869378733 / 25000000000000000000))
  · norm_num [world11908, agent11908, scalar11908, tp11908, tm11908, ep11908, em11908, dsL]
  · norm_num [world11908, agent11908, scalar11908, tp11908, tm11908, ep11908, em11908, dsL]
  · norm_num [world11908, agent11908, scalar11908, tp11908, tm11908, ep11908, em11908, dsL]
  · norm_num [world11908, agent11908, scalar11908, tp11908, tm11908, ep11908, em11908, dsL]
  · norm_num [world11908, agent11908, scalar11908, tp11908, tm11908, ep11908, em11908, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11908, agent11908, tp11908, tm11908, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11908, agent11908, tp11908, tm11908, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11908, agent11908, scalar11908, tp11908, tm11908, ep11908, em11908, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11908, agent11908, tp11908, tm11908, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11908, agent11908, scalar11908, tp11908, tm11908, ep11908, em11908, dsL]

theorem tails11908 :
    exp (-((11908:ℝ)*ep11908)) ≤ scalar11908.upperTail ∧
    exp (-((11908:ℝ)*em11908)) ≤ scalar11908.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11908:ℝ)) (by norm_num [ep11908]) ?_)
      (show bp11908^8 ≤ scalar11908.upperTail by norm_num [bp11908, scalar11908])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11908, bp11908, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11908:ℝ)) (by norm_num [em11908]) ?_)
      (show bm11908^8 ≤ scalar11908.lowerTail by norm_num [bm11908, scalar11908])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11908, bm11908, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11908 :
    agent11908.root+dsL+scalar11908.worldRadius < √(1/100/aL) ∧
    2*(agent11908.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11908, agent11908, scalar11908, tp11908, tm11908, ep11908, em11908, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11908, agent11908, scalar11908, tp11908, tm11908, ep11908, em11908, dsL]

noncomputable def master11908 : MasterCertificate 11908 world11908 agent11908 :=
  master scalar11908 dsL tp11908 tm11908 ep11908 em11908
    (by norm_num [dsL]) (by norm_num [tp11908]) (by norm_num [tm11908])
    (by norm_num [ep11908]) (by norm_num [em11908])
    positive11908 negative11908 tails11908.1 tails11908.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11908.1 tailGuards11908.2

theorem preserves11908 : master11908.toScalarCertificate = scalar11908 := rfl

end BstLean.Part281
