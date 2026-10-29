import BstLean.Part261Checker
import BstLean.Part281Scalar12
namespace BstLean.Part281
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12159 : ℝ := (94955833 / 400000000)
noncomputable def tm12159 : ℝ := (-((3070600553 / 5000000000)))
noncomputable def ep12159 : ℝ := (27312539101113471 / 50000000000000000000)
noncomputable def em12159 : ℝ := (26332388673489551 / 50000000000000000000)
noncomputable def bp12159 : ℝ := (1089869347685550049 / 2500000000000000000)
noncomputable def bm12159 : ℝ := (22456592434510095529 / 50000000000000000000)

theorem positive12159 :
    Eplus aL (agent12159.root+dsL) scalar12159.worldRadius world12159.frame
      agent12159.frame tp12159 ≤ -ep12159 := by
  apply positive_check (eT := (29056780186928958817 / 25000000000000000000)) (y := (19816459989237784777 / 50000000000000000000)) (u := (148635854593342346573 / 100000000000000000000))
  · norm_num [world12159, agent12159, scalar12159, tp12159, tm12159, ep12159, em12159, dsL]
  · norm_num [world12159, agent12159, scalar12159, tp12159, tm12159, ep12159, em12159, dsL]
  · norm_num [world12159, agent12159, scalar12159, tp12159, tm12159, ep12159, em12159, dsL]
  · norm_num [world12159, agent12159, scalar12159, tp12159, tm12159, ep12159, em12159, dsL]
  · norm_num [world12159, agent12159, scalar12159, tp12159, tm12159, ep12159, em12159, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12159, agent12159, tp12159, tm12159, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12159, agent12159, scalar12159, tp12159, tm12159, ep12159, em12159, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12159, agent12159, tp12159, tm12159, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12159, agent12159, scalar12159, tp12159, tm12159, ep12159, em12159, dsL]

theorem negative12159 :
    Eminus aL (agent12159.root+dsL) scalar12159.worldRadius world12159.frame
      agent12159.frame tm12159 ≤ -em12159 := by
  apply negative_check (lo := (67772172104237456281 / 100000000000000000000)) (hi := (33886086052118728141 / 50000000000000000000))
    (y := (-((73300000995641951353 / 100000000000000000000)))) (u := (24023271237985344161 / 50000000000000000000))
  · norm_num [world12159, agent12159, scalar12159, tp12159, tm12159, ep12159, em12159, dsL]
  · norm_num [world12159, agent12159, scalar12159, tp12159, tm12159, ep12159, em12159, dsL]
  · norm_num [world12159, agent12159, scalar12159, tp12159, tm12159, ep12159, em12159, dsL]
  · norm_num [world12159, agent12159, scalar12159, tp12159, tm12159, ep12159, em12159, dsL]
  · norm_num [world12159, agent12159, scalar12159, tp12159, tm12159, ep12159, em12159, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12159, agent12159, tp12159, tm12159, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12159, agent12159, tp12159, tm12159, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12159, agent12159, scalar12159, tp12159, tm12159, ep12159, em12159, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12159, agent12159, tp12159, tm12159, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12159, agent12159, scalar12159, tp12159, tm12159, ep12159, em12159, dsL]

theorem tails12159 :
    exp (-((12159:ℝ)*ep12159)) ≤ scalar12159.upperTail ∧
    exp (-((12159:ℝ)*em12159)) ≤ scalar12159.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12159:ℝ)) (by norm_num [ep12159]) ?_)
      (show bp12159^8 ≤ scalar12159.upperTail by norm_num [bp12159, scalar12159])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12159, bp12159, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12159:ℝ)) (by norm_num [em12159]) ?_)
      (show bm12159^8 ≤ scalar12159.lowerTail by norm_num [bm12159, scalar12159])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12159, bm12159, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12159 :
    agent12159.root+dsL+scalar12159.worldRadius < √(1/100/aL) ∧
    2*(agent12159.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12159, agent12159, scalar12159, tp12159, tm12159, ep12159, em12159, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12159, agent12159, scalar12159, tp12159, tm12159, ep12159, em12159, dsL]

noncomputable def master12159 : MasterCertificate 12159 world12159 agent12159 :=
  master scalar12159 dsL tp12159 tm12159 ep12159 em12159
    (by norm_num [dsL]) (by norm_num [tp12159]) (by norm_num [tm12159])
    (by norm_num [ep12159]) (by norm_num [em12159])
    positive12159 negative12159 tails12159.1 tails12159.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12159.1 tailGuards12159.2

theorem preserves12159 : master12159.toScalarCertificate = scalar12159 := rfl

noncomputable def tp12160 : ℝ := (593498481 / 2500000000)
noncomputable def tm12160 : ℝ := (-((6141421113 / 10000000000)))
noncomputable def ep12160 : ℝ := (10925590540320287 / 20000000000000000000)
noncomputable def em12160 : ℝ := (52667274769588551 / 100000000000000000000)
noncomputable def bp12160 : ℝ := (43589892710907649459 / 100000000000000000000)
noncomputable def bm12160 : ℝ := (8981704698167691573 / 20000000000000000000)

theorem positive12160 :
    Eplus aL (agent12160.root+dsL) scalar12160.worldRadius world12160.frame
      agent12160.frame tp12160 ≤ -ep12160 := by
  apply positive_check (eT := (58113712730814934721 / 50000000000000000000)) (y := (198167725033527391 / 500000000000000000)) (u := (37159195903074158317 / 25000000000000000000))
  · norm_num [world12160, agent12160, scalar12160, tp12160, tm12160, ep12160, em12160, dsL]
  · norm_num [world12160, agent12160, scalar12160, tp12160, tm12160, ep12160, em12160, dsL]
  · norm_num [world12160, agent12160, scalar12160, tp12160, tm12160, ep12160, em12160, dsL]
  · norm_num [world12160, agent12160, scalar12160, tp12160, tm12160, ep12160, em12160, dsL]
  · norm_num [world12160, agent12160, scalar12160, tp12160, tm12160, ep12160, em12160, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12160, agent12160, tp12160, tm12160, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12160, agent12160, scalar12160, tp12160, tm12160, ep12160, em12160, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12160, agent12160, tp12160, tm12160, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12160, agent12160, scalar12160, tp12160, tm12160, ep12160, em12160, dsL]

theorem negative12160 :
    Eminus aL (agent12160.root+dsL) scalar12160.worldRadius world12160.frame
      agent12160.frame tm12160 ≤ -em12160 := by
  apply negative_check (lo := (67771857438559667371 / 100000000000000000000)) (hi := (16942964359639916843 / 25000000000000000000))
    (y := (-((36649801395996904747 / 50000000000000000000)))) (u := (24023366899718280961 / 50000000000000000000))
  · norm_num [world12160, agent12160, scalar12160, tp12160, tm12160, ep12160, em12160, dsL]
  · norm_num [world12160, agent12160, scalar12160, tp12160, tm12160, ep12160, em12160, dsL]
  · norm_num [world12160, agent12160, scalar12160, tp12160, tm12160, ep12160, em12160, dsL]
  · norm_num [world12160, agent12160, scalar12160, tp12160, tm12160, ep12160, em12160, dsL]
  · norm_num [world12160, agent12160, scalar12160, tp12160, tm12160, ep12160, em12160, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12160, agent12160, tp12160, tm12160, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12160, agent12160, tp12160, tm12160, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12160, agent12160, scalar12160, tp12160, tm12160, ep12160, em12160, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12160, agent12160, tp12160, tm12160, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12160, agent12160, scalar12160, tp12160, tm12160, ep12160, em12160, dsL]

theorem tails12160 :
    exp (-((12160:ℝ)*ep12160)) ≤ scalar12160.upperTail ∧
    exp (-((12160:ℝ)*em12160)) ≤ scalar12160.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12160:ℝ)) (by norm_num [ep12160]) ?_)
      (show bp12160^8 ≤ scalar12160.upperTail by norm_num [bp12160, scalar12160])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12160, bp12160, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12160:ℝ)) (by norm_num [em12160]) ?_)
      (show bm12160^8 ≤ scalar12160.lowerTail by norm_num [bm12160, scalar12160])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12160, bm12160, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12160 :
    agent12160.root+dsL+scalar12160.worldRadius < √(1/100/aL) ∧
    2*(agent12160.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12160, agent12160, scalar12160, tp12160, tm12160, ep12160, em12160, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12160, agent12160, scalar12160, tp12160, tm12160, ep12160, em12160, dsL]

noncomputable def master12160 : MasterCertificate 12160 world12160 agent12160 :=
  master scalar12160 dsL tp12160 tm12160 ep12160 em12160
    (by norm_num [dsL]) (by norm_num [tp12160]) (by norm_num [tm12160])
    (by norm_num [ep12160]) (by norm_num [em12160])
    positive12160 negative12160 tails12160.1 tails12160.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12160.1 tailGuards12160.2

theorem preserves12160 : master12160.toScalarCertificate = scalar12160 := rfl

noncomputable def tp12161 : ℝ := (474818391 / 2000000000)
noncomputable def tm12161 : ℝ := (-((1228328223 / 2000000000)))
noncomputable def ep12161 : ℝ := (27315412290562233 / 50000000000000000000)
noncomputable def em12161 : ℝ := (52669769764702241 / 100000000000000000000)
noncomputable def bp12161 : ℝ := (21792506741744832367 / 50000000000000000000)
noncomputable def bm12161 : ℝ := (11225965993270181781 / 25000000000000000000)

theorem positive12161 :
    Eplus aL (agent12161.root+dsL) scalar12161.worldRadius world12161.frame
      agent12161.frame tp12161 ≤ -ep12161 := by
  apply positive_check (eT := (23245545942369392907 / 20000000000000000000)) (y := (39634169690904249257 / 100000000000000000000)) (u := (148637712125697556043 / 100000000000000000000))
  · norm_num [world12161, agent12161, scalar12161, tp12161, tm12161, ep12161, em12161, dsL]
  · norm_num [world12161, agent12161, scalar12161, tp12161, tm12161, ep12161, em12161, dsL]
  · norm_num [world12161, agent12161, scalar12161, tp12161, tm12161, ep12161, em12161, dsL]
  · norm_num [world12161, agent12161, scalar12161, tp12161, tm12161, ep12161, em12161, dsL]
  · norm_num [world12161, agent12161, scalar12161, tp12161, tm12161, ep12161, em12161, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12161, agent12161, tp12161, tm12161, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12161, agent12161, scalar12161, tp12161, tm12161, ep12161, em12161, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12161, agent12161, tp12161, tm12161, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12161, agent12161, scalar12161, tp12161, tm12161, ep12161, em12161, dsL]

theorem negative12161 :
    Eminus aL (agent12161.root+dsL) scalar12161.worldRadius world12161.frame
      agent12161.frame tm12161 ≤ -em12161 := by
  apply negative_check (lo := (6777154273437819741 / 10000000000000000000)) (hi := (67771542734378197411 / 100000000000000000000))
    (y := (-((4581200369296126561 / 6250000000000000000)))) (u := (48046924489256370979 / 100000000000000000000))
  · norm_num [world12161, agent12161, scalar12161, tp12161, tm12161, ep12161, em12161, dsL]
  · norm_num [world12161, agent12161, scalar12161, tp12161, tm12161, ep12161, em12161, dsL]
  · norm_num [world12161, agent12161, scalar12161, tp12161, tm12161, ep12161, em12161, dsL]
  · norm_num [world12161, agent12161, scalar12161, tp12161, tm12161, ep12161, em12161, dsL]
  · norm_num [world12161, agent12161, scalar12161, tp12161, tm12161, ep12161, em12161, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12161, agent12161, tp12161, tm12161, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12161, agent12161, tp12161, tm12161, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12161, agent12161, scalar12161, tp12161, tm12161, ep12161, em12161, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12161, agent12161, tp12161, tm12161, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12161, agent12161, scalar12161, tp12161, tm12161, ep12161, em12161, dsL]

theorem tails12161 :
    exp (-((12161:ℝ)*ep12161)) ≤ scalar12161.upperTail ∧
    exp (-((12161:ℝ)*em12161)) ≤ scalar12161.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12161:ℝ)) (by norm_num [ep12161]) ?_)
      (show bp12161^8 ≤ scalar12161.upperTail by norm_num [bp12161, scalar12161])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12161, bp12161, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12161:ℝ)) (by norm_num [em12161]) ?_)
      (show bm12161^8 ≤ scalar12161.lowerTail by norm_num [bm12161, scalar12161])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12161, bm12161, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12161 :
    agent12161.root+dsL+scalar12161.worldRadius < √(1/100/aL) ∧
    2*(agent12161.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12161, agent12161, scalar12161, tp12161, tm12161, ep12161, em12161, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12161, agent12161, scalar12161, tp12161, tm12161, ep12161, em12161, dsL]

noncomputable def master12161 : MasterCertificate 12161 world12161 agent12161 :=
  master scalar12161 dsL tp12161 tm12161 ep12161 em12161
    (by norm_num [dsL]) (by norm_num [tp12161]) (by norm_num [tm12161])
    (by norm_num [ep12161]) (by norm_num [em12161])
    positive12161 negative12161 tails12161.1 tails12161.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12161.1 tailGuards12161.2

theorem preserves12161 : master12161.toScalarCertificate = scalar12161 := rfl

noncomputable def tp12162 : ℝ := (1187095001 / 5000000000)
noncomputable def tm12162 : ℝ := (-((6141860773 / 10000000000)))
noncomputable def ep12162 : ℝ := (27316847919723957 / 50000000000000000000)
noncomputable def em12162 : ℝ := (13168066037857833 / 25000000000000000000)
noncomputable def bp12162 : ℝ := (680939607826506977 / 1562500000000000000)
noncomputable def bm12162 : ℝ := (1122480126849694891 / 2500000000000000000)

theorem positive12162 :
    Eplus aL (agent12162.root+dsL) scalar12162.worldRadius world12162.frame
      agent12162.frame tp12162 ≤ -ep12162 := by
  apply positive_check (eT := (58114017058394901191 / 50000000000000000000)) (y := (63415672192135293 / 160000000000000000)) (u := (4644957554757162763 / 3125000000000000000))
  · norm_num [world12162, agent12162, scalar12162, tp12162, tm12162, ep12162, em12162, dsL]
  · norm_num [world12162, agent12162, scalar12162, tp12162, tm12162, ep12162, em12162, dsL]
  · norm_num [world12162, agent12162, scalar12162, tp12162, tm12162, ep12162, em12162, dsL]
  · norm_num [world12162, agent12162, scalar12162, tp12162, tm12162, ep12162, em12162, dsL]
  · norm_num [world12162, agent12162, scalar12162, tp12162, tm12162, ep12162, em12162, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12162, agent12162, tp12162, tm12162, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12162, agent12162, scalar12162, tp12162, tm12162, ep12162, em12162, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12162, agent12162, tp12162, tm12162, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12162, agent12162, scalar12162, tp12162, tm12162, ep12162, em12162, dsL]

theorem negative12162 :
    Eminus aL (agent12162.root+dsL) scalar12162.worldRadius world12162.frame
      agent12162.frame tm12162 ≤ -em12162 := by
  apply negative_check (lo := (67771229446949725731 / 100000000000000000000)) (hi := (16942807361737431433 / 25000000000000000000))
    (y := (-((73298806709698307359 / 100000000000000000000)))) (u := (48047116292500384039 / 100000000000000000000))
  · norm_num [world12162, agent12162, scalar12162, tp12162, tm12162, ep12162, em12162, dsL]
  · norm_num [world12162, agent12162, scalar12162, tp12162, tm12162, ep12162, em12162, dsL]
  · norm_num [world12162, agent12162, scalar12162, tp12162, tm12162, ep12162, em12162, dsL]
  · norm_num [world12162, agent12162, scalar12162, tp12162, tm12162, ep12162, em12162, dsL]
  · norm_num [world12162, agent12162, scalar12162, tp12162, tm12162, ep12162, em12162, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12162, agent12162, tp12162, tm12162, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12162, agent12162, tp12162, tm12162, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12162, agent12162, scalar12162, tp12162, tm12162, ep12162, em12162, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12162, agent12162, tp12162, tm12162, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12162, agent12162, scalar12162, tp12162, tm12162, ep12162, em12162, dsL]

theorem tails12162 :
    exp (-((12162:ℝ)*ep12162)) ≤ scalar12162.upperTail ∧
    exp (-((12162:ℝ)*em12162)) ≤ scalar12162.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12162:ℝ)) (by norm_num [ep12162]) ?_)
      (show bp12162^8 ≤ scalar12162.upperTail by norm_num [bp12162, scalar12162])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12162, bp12162, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12162:ℝ)) (by norm_num [em12162]) ?_)
      (show bm12162^8 ≤ scalar12162.lowerTail by norm_num [bm12162, scalar12162])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12162, bm12162, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12162 :
    agent12162.root+dsL+scalar12162.worldRadius < √(1/100/aL) ∧
    2*(agent12162.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12162, agent12162, scalar12162, tp12162, tm12162, ep12162, em12162, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12162, agent12162, scalar12162, tp12162, tm12162, ep12162, em12162, dsL]

noncomputable def master12162 : MasterCertificate 12162 world12162 agent12162 :=
  master scalar12162 dsL tp12162 tm12162 ep12162 em12162
    (by norm_num [dsL]) (by norm_num [tp12162]) (by norm_num [tm12162])
    (by norm_num [ep12162]) (by norm_num [em12162])
    positive12162 negative12162 tails12162.1 tails12162.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12162.1 tailGuards12162.2

theorem preserves12162 : master12162.toScalarCertificate = scalar12162 := rfl

noncomputable def tp12163 : ℝ := (1187143977 / 5000000000)
noncomputable def tm12163 : ℝ := (-((6142080221 / 10000000000)))
noncomputable def ep12163 : ℝ := (54636564786878939 / 100000000000000000000)
noncomputable def em12163 : ℝ := (13168689107505779 / 25000000000000000000)
noncomputable def bp12163 : ℝ := (4357525808256911429 / 10000000000000000000)
noncomputable def bm12163 : ℝ := (44894547817249258071 / 100000000000000000000)

theorem positive12163 :
    Eplus aL (agent12163.root+dsL) scalar12163.worldRadius world12163.frame
      agent12163.frame tp12163 ≤ -ep12163 := by
  apply positive_check (eT := (116228337859265965001 / 100000000000000000000)) (y := (19817709699583493453 / 50000000000000000000)) (u := (74319784837537242467 / 50000000000000000000))
  · norm_num [world12163, agent12163, scalar12163, tp12163, tm12163, ep12163, em12163, dsL]
  · norm_num [world12163, agent12163, scalar12163, tp12163, tm12163, ep12163, em12163, dsL]
  · norm_num [world12163, agent12163, scalar12163, tp12163, tm12163, ep12163, em12163, dsL]
  · norm_num [world12163, agent12163, scalar12163, tp12163, tm12163, ep12163, em12163, dsL]
  · norm_num [world12163, agent12163, scalar12163, tp12163, tm12163, ep12163, em12163, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12163, agent12163, tp12163, tm12163, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12163, agent12163, scalar12163, tp12163, tm12163, ep12163, em12163, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12163, agent12163, tp12163, tm12163, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12163, agent12163, scalar12163, tp12163, tm12163, ep12163, em12163, dsL]

theorem negative12163 :
    Eminus aL (agent12163.root+dsL) scalar12163.worldRadius world12163.frame
      agent12163.frame tm12163 ≤ -em12163 := by
  apply negative_check (lo := (33885458500486363281 / 50000000000000000000)) (hi := (67770917000972726563 / 100000000000000000000))
    (y := (-((18324601559205634263 / 25000000000000000000)))) (u := (48047308708554012113 / 100000000000000000000))
  · norm_num [world12163, agent12163, scalar12163, tp12163, tm12163, ep12163, em12163, dsL]
  · norm_num [world12163, agent12163, scalar12163, tp12163, tm12163, ep12163, em12163, dsL]
  · norm_num [world12163, agent12163, scalar12163, tp12163, tm12163, ep12163, em12163, dsL]
  · norm_num [world12163, agent12163, scalar12163, tp12163, tm12163, ep12163, em12163, dsL]
  · norm_num [world12163, agent12163, scalar12163, tp12163, tm12163, ep12163, em12163, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12163, agent12163, tp12163, tm12163, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12163, agent12163, tp12163, tm12163, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12163, agent12163, scalar12163, tp12163, tm12163, ep12163, em12163, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12163, agent12163, tp12163, tm12163, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12163, agent12163, scalar12163, tp12163, tm12163, ep12163, em12163, dsL]

theorem tails12163 :
    exp (-((12163:ℝ)*ep12163)) ≤ scalar12163.upperTail ∧
    exp (-((12163:ℝ)*em12163)) ≤ scalar12163.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12163:ℝ)) (by norm_num [ep12163]) ?_)
      (show bp12163^8 ≤ scalar12163.upperTail by norm_num [bp12163, scalar12163])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12163, bp12163, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12163:ℝ)) (by norm_num [em12163]) ?_)
      (show bm12163^8 ≤ scalar12163.lowerTail by norm_num [bm12163, scalar12163])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12163, bm12163, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12163 :
    agent12163.root+dsL+scalar12163.worldRadius < √(1/100/aL) ∧
    2*(agent12163.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12163, agent12163, scalar12163, tp12163, tm12163, ep12163, em12163, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12163, agent12163, scalar12163, tp12163, tm12163, ep12163, em12163, dsL]

noncomputable def master12163 : MasterCertificate 12163 world12163 agent12163 :=
  master scalar12163 dsL tp12163 tm12163 ep12163 em12163
    (by norm_num [dsL]) (by norm_num [tp12163]) (by norm_num [tm12163])
    (by norm_num [ep12163]) (by norm_num [em12163])
    positive12163 negative12163 tails12163.1 tails12163.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12163.1 tailGuards12163.2

theorem preserves12163 : master12163.toScalarCertificate = scalar12163 := rfl

noncomputable def tp12164 : ℝ := (296798229 / 1250000000)
noncomputable def tm12164 : ℝ := (-((767787487 / 1250000000)))
noncomputable def ep12164 : ℝ := (13659858111634719 / 25000000000000000000)
noncomputable def em12164 : ℝ := (3292327967453889 / 6250000000000000000)
noncomputable def bp12164 : ℝ := (21785191175304943209 / 50000000000000000000)
noncomputable def bm12164 : ℝ := (22444945801497014847 / 50000000000000000000)

theorem positive12164 :
    Eplus aL (agent12164.root+dsL) scalar12164.worldRadius world12164.frame
      agent12164.frame tp12164 ≤ -ep12164 := by
  apply positive_check (eT := (23245728218784968359 / 20000000000000000000)) (y := (9909010780729258517 / 25000000000000000000)) (u := (148640496778263794657 / 100000000000000000000))
  · norm_num [world12164, agent12164, scalar12164, tp12164, tm12164, ep12164, em12164, dsL]
  · norm_num [world12164, agent12164, scalar12164, tp12164, tm12164, ep12164, em12164, dsL]
  · norm_num [world12164, agent12164, scalar12164, tp12164, tm12164, ep12164, em12164, dsL]
  · norm_num [world12164, agent12164, scalar12164, tp12164, tm12164, ep12164, em12164, dsL]
  · norm_num [world12164, agent12164, scalar12164, tp12164, tm12164, ep12164, em12164, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12164, agent12164, tp12164, tm12164, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12164, agent12164, scalar12164, tp12164, tm12164, ep12164, em12164, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12164, agent12164, tp12164, tm12164, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12164, agent12164, scalar12164, tp12164, tm12164, ep12164, em12164, dsL]

theorem negative12164 :
    Eminus aL (agent12164.root+dsL) scalar12164.worldRadius world12164.frame
      agent12164.frame tm12164 ≤ -em12164 := by
  apply negative_check (lo := (13554120704110743293 / 20000000000000000000)) (hi := (33885301760276858233 / 50000000000000000000))
    (y := (-((73298009609171302149 / 100000000000000000000)))) (u := (48047499277843949433 / 100000000000000000000))
  · norm_num [world12164, agent12164, scalar12164, tp12164, tm12164, ep12164, em12164, dsL]
  · norm_num [world12164, agent12164, scalar12164, tp12164, tm12164, ep12164, em12164, dsL]
  · norm_num [world12164, agent12164, scalar12164, tp12164, tm12164, ep12164, em12164, dsL]
  · norm_num [world12164, agent12164, scalar12164, tp12164, tm12164, ep12164, em12164, dsL]
  · norm_num [world12164, agent12164, scalar12164, tp12164, tm12164, ep12164, em12164, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12164, agent12164, tp12164, tm12164, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12164, agent12164, tp12164, tm12164, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12164, agent12164, scalar12164, tp12164, tm12164, ep12164, em12164, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12164, agent12164, tp12164, tm12164, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12164, agent12164, scalar12164, tp12164, tm12164, ep12164, em12164, dsL]

theorem tails12164 :
    exp (-((12164:ℝ)*ep12164)) ≤ scalar12164.upperTail ∧
    exp (-((12164:ℝ)*em12164)) ≤ scalar12164.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12164:ℝ)) (by norm_num [ep12164]) ?_)
      (show bp12164^8 ≤ scalar12164.upperTail by norm_num [bp12164, scalar12164])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12164, bp12164, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12164:ℝ)) (by norm_num [em12164]) ?_)
      (show bm12164^8 ≤ scalar12164.lowerTail by norm_num [bm12164, scalar12164])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12164, bm12164, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12164 :
    agent12164.root+dsL+scalar12164.worldRadius < √(1/100/aL) ∧
    2*(agent12164.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12164, agent12164, scalar12164, tp12164, tm12164, ep12164, em12164, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12164, agent12164, scalar12164, tp12164, tm12164, ep12164, em12164, dsL]

noncomputable def master12164 : MasterCertificate 12164 world12164 agent12164 :=
  master scalar12164 dsL tp12164 tm12164 ep12164 em12164
    (by norm_num [dsL]) (by norm_num [tp12164]) (by norm_num [tm12164])
    (by norm_num [ep12164]) (by norm_num [em12164])
    positive12164 negative12164 tails12164.1 tails12164.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12164.1 tailGuards12164.2

theorem preserves12164 : master12164.toScalarCertificate = scalar12164 := rfl

noncomputable def tp12165 : ℝ := (2374483641 / 10000000000)
noncomputable def tm12165 : ℝ := (-((6142519061 / 10000000000)))
noncomputable def ep12165 : ℝ := (27321149185107181 / 50000000000000000000)
noncomputable def em12165 : ℝ := (52679736876717577 / 100000000000000000000)
noncomputable def bp12165 : ℝ := (340355531264950089 / 781250000000000000)
noncomputable def bm12165 : ℝ := (44885236719529345549 / 100000000000000000000)

theorem positive12165 :
    Eplus aL (agent12165.root+dsL) scalar12165.worldRadius world12165.frame
      agent12165.frame tp12165 ≤ -ep12165 := by
  apply positive_check (eT := (58114471928795167211 / 50000000000000000000)) (y := (19818333162921981211 / 50000000000000000000)) (u := (74320711556538393739 / 50000000000000000000))
  · norm_num [world12165, agent12165, scalar12165, tp12165, tm12165, ep12165, em12165, dsL]
  · norm_num [world12165, agent12165, scalar12165, tp12165, tm12165, ep12165, em12165, dsL]
  · norm_num [world12165, agent12165, scalar12165, tp12165, tm12165, ep12165, em12165, dsL]
  · norm_num [world12165, agent12165, scalar12165, tp12165, tm12165, ep12165, em12165, dsL]
  · norm_num [world12165, agent12165, scalar12165, tp12165, tm12165, ep12165, em12165, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12165, agent12165, tp12165, tm12165, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12165, agent12165, scalar12165, tp12165, tm12165, ep12165, em12165, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12165, agent12165, tp12165, tm12165, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12165, agent12165, scalar12165, tp12165, tm12165, ep12165, em12165, dsL]

theorem negative12165 :
    Eminus aL (agent12165.root+dsL) scalar12165.worldRadius world12165.frame
      agent12165.frame tm12165 ≤ -em12165 := by
  apply negative_check (lo := (8471286521157667783 / 12500000000000000000)) (hi := (13554058433852268453 / 20000000000000000000))
    (y := (-((73297609081139093657 / 100000000000000000000)))) (u := (384381533775461827 / 800000000000000000))
  · norm_num [world12165, agent12165, scalar12165, tp12165, tm12165, ep12165, em12165, dsL]
  · norm_num [world12165, agent12165, scalar12165, tp12165, tm12165, ep12165, em12165, dsL]
  · norm_num [world12165, agent12165, scalar12165, tp12165, tm12165, ep12165, em12165, dsL]
  · norm_num [world12165, agent12165, scalar12165, tp12165, tm12165, ep12165, em12165, dsL]
  · norm_num [world12165, agent12165, scalar12165, tp12165, tm12165, ep12165, em12165, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12165, agent12165, tp12165, tm12165, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12165, agent12165, tp12165, tm12165, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12165, agent12165, scalar12165, tp12165, tm12165, ep12165, em12165, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12165, agent12165, tp12165, tm12165, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12165, agent12165, scalar12165, tp12165, tm12165, ep12165, em12165, dsL]

theorem tails12165 :
    exp (-((12165:ℝ)*ep12165)) ≤ scalar12165.upperTail ∧
    exp (-((12165:ℝ)*em12165)) ≤ scalar12165.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12165:ℝ)) (by norm_num [ep12165]) ?_)
      (show bp12165^8 ≤ scalar12165.upperTail by norm_num [bp12165, scalar12165])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12165, bp12165, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12165:ℝ)) (by norm_num [em12165]) ?_)
      (show bm12165^8 ≤ scalar12165.lowerTail by norm_num [bm12165, scalar12165])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12165, bm12165, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12165 :
    agent12165.root+dsL+scalar12165.worldRadius < √(1/100/aL) ∧
    2*(agent12165.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12165, agent12165, scalar12165, tp12165, tm12165, ep12165, em12165, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12165, agent12165, scalar12165, tp12165, tm12165, ep12165, em12165, dsL]

noncomputable def master12165 : MasterCertificate 12165 world12165 agent12165 :=
  master scalar12165 dsL tp12165 tm12165 ep12165 em12165
    (by norm_num [dsL]) (by norm_num [tp12165]) (by norm_num [tm12165])
    (by norm_num [ep12165]) (by norm_num [em12165])
    positive12165 negative12165 tails12165.1 tails12165.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12165.1 tailGuards12165.2

theorem preserves12165 : master12165.toScalarCertificate = scalar12165 := rfl

noncomputable def tp12166 : ℝ := (1187290727 / 5000000000)
noncomputable def tm12166 : ℝ := (-((1535684579 / 2500000000)))
noncomputable def ep12166 : ℝ := (54645162462916507 / 100000000000000000000)
noncomputable def em12166 : ℝ := (26341112304040421 / 50000000000000000000)
noncomputable def bp12166 : ℝ := (21780317549673453447 / 50000000000000000000)
noncomputable def bm12166 : ℝ := (1122014579414627529 / 2500000000000000000)

theorem positive12166 :
    Eplus aL (agent12166.root+dsL) scalar12166.worldRadius world12166.frame
      agent12166.frame tp12166 ≤ -ep12166 := by
  apply positive_check (eT := (116229246687657672217 / 100000000000000000000)) (y := (1585491604235368673 / 4000000000000000000)) (u := (148642350311497553281 / 100000000000000000000))
  · norm_num [world12166, agent12166, scalar12166, tp12166, tm12166, ep12166, em12166, dsL]
  · norm_num [world12166, agent12166, scalar12166, tp12166, tm12166, ep12166, em12166, dsL]
  · norm_num [world12166, agent12166, scalar12166, tp12166, tm12166, ep12166, em12166, dsL]
  · norm_num [world12166, agent12166, scalar12166, tp12166, tm12166, ep12166, em12166, dsL]
  · norm_num [world12166, agent12166, scalar12166, tp12166, tm12166, ep12166, em12166, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12166, agent12166, tp12166, tm12166, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12166, agent12166, scalar12166, tp12166, tm12166, ep12166, em12166, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12166, agent12166, tp12166, tm12166, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12166, agent12166, scalar12166, tp12166, tm12166, ep12166, em12166, dsL]

theorem negative12166 :
    Eminus aL (agent12166.root+dsL) scalar12166.worldRadius world12166.frame
      agent12166.frame tm12166 ≤ -em12166 := by
  apply negative_check (lo := (4235623773225574079 / 6250000000000000000)) (hi := (13553996074321837053 / 20000000000000000000))
    (y := (-((18324302583741256907 / 25000000000000000000)))) (u := (24023941655323586351 / 50000000000000000000))
  · norm_num [world12166, agent12166, scalar12166, tp12166, tm12166, ep12166, em12166, dsL]
  · norm_num [world12166, agent12166, scalar12166, tp12166, tm12166, ep12166, em12166, dsL]
  · norm_num [world12166, agent12166, scalar12166, tp12166, tm12166, ep12166, em12166, dsL]
  · norm_num [world12166, agent12166, scalar12166, tp12166, tm12166, ep12166, em12166, dsL]
  · norm_num [world12166, agent12166, scalar12166, tp12166, tm12166, ep12166, em12166, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12166, agent12166, tp12166, tm12166, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12166, agent12166, tp12166, tm12166, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12166, agent12166, scalar12166, tp12166, tm12166, ep12166, em12166, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12166, agent12166, tp12166, tm12166, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12166, agent12166, scalar12166, tp12166, tm12166, ep12166, em12166, dsL]

theorem tails12166 :
    exp (-((12166:ℝ)*ep12166)) ≤ scalar12166.upperTail ∧
    exp (-((12166:ℝ)*em12166)) ≤ scalar12166.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12166:ℝ)) (by norm_num [ep12166]) ?_)
      (show bp12166^8 ≤ scalar12166.upperTail by norm_num [bp12166, scalar12166])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12166, bp12166, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12166:ℝ)) (by norm_num [em12166]) ?_)
      (show bm12166^8 ≤ scalar12166.lowerTail by norm_num [bm12166, scalar12166])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12166, bm12166, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12166 :
    agent12166.root+dsL+scalar12166.worldRadius < √(1/100/aL) ∧
    2*(agent12166.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12166, agent12166, scalar12166, tp12166, tm12166, ep12166, em12166, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12166, agent12166, scalar12166, tp12166, tm12166, ep12166, em12166, dsL]

noncomputable def master12166 : MasterCertificate 12166 world12166 agent12166 :=
  master scalar12166 dsL tp12166 tm12166 ep12166 em12166
    (by norm_num [dsL]) (by norm_num [tp12166]) (by norm_num [tm12166])
    (by norm_num [ep12166]) (by norm_num [em12166])
    positive12166 negative12166 tails12166.1 tails12166.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12166.1 tailGuards12166.2

theorem preserves12166 : master12166.toScalarCertificate = scalar12166 := rfl

noncomputable def tp12167 : ℝ := (148417449 / 625000000)
noncomputable def tm12167 : ℝ := (-((76786969 / 125000000)))
noncomputable def ep12167 : ℝ := (13662006327260497 / 25000000000000000000)
noncomputable def em12167 : ℝ := (13171177784411569 / 25000000000000000000)
noncomputable def bp12167 : ℝ := (21777881627862204999 / 50000000000000000000)
noncomputable def bm12167 : ℝ := (44875930657240817717 / 100000000000000000000)

theorem positive12167 :
    Eplus aL (agent12167.root+dsL) scalar12167.worldRadius world12167.frame
      agent12167.frame tp12167 ≤ -ep12167 := by
  apply positive_check (eT := (7264346808981670541 / 6250000000000000000)) (y := (19818956530444888247 / 50000000000000000000)) (u := (148643276289343409969 / 100000000000000000000))
  · norm_num [world12167, agent12167, scalar12167, tp12167, tm12167, ep12167, em12167, dsL]
  · norm_num [world12167, agent12167, scalar12167, tp12167, tm12167, ep12167, em12167, dsL]
  · norm_num [world12167, agent12167, scalar12167, tp12167, tm12167, ep12167, em12167, dsL]
  · norm_num [world12167, agent12167, scalar12167, tp12167, tm12167, ep12167, em12167, dsL]
  · norm_num [world12167, agent12167, scalar12167, tp12167, tm12167, ep12167, em12167, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12167, agent12167, tp12167, tm12167, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12167, agent12167, scalar12167, tp12167, tm12167, ep12167, em12167, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12167, agent12167, tp12167, tm12167, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12167, agent12167, scalar12167, tp12167, tm12167, ep12167, em12167, dsL]

theorem negative12167 :
    Eminus aL (agent12167.root+dsL) scalar12167.worldRadius world12167.frame
      agent12167.frame tm12167 ≤ -em12167 := by
  apply negative_check (lo := (67769668732805125971 / 100000000000000000000)) (hi := (16942417183201281493 / 25000000000000000000))
    (y := (-((73296812296923151259 / 100000000000000000000)))) (u := (48048074559881687547 / 100000000000000000000))
  · norm_num [world12167, agent12167, scalar12167, tp12167, tm12167, ep12167, em12167, dsL]
  · norm_num [world12167, agent12167, scalar12167, tp12167, tm12167, ep12167, em12167, dsL]
  · norm_num [world12167, agent12167, scalar12167, tp12167, tm12167, ep12167, em12167, dsL]
  · norm_num [world12167, agent12167, scalar12167, tp12167, tm12167, ep12167, em12167, dsL]
  · norm_num [world12167, agent12167, scalar12167, tp12167, tm12167, ep12167, em12167, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12167, agent12167, tp12167, tm12167, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12167, agent12167, tp12167, tm12167, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12167, agent12167, scalar12167, tp12167, tm12167, ep12167, em12167, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12167, agent12167, tp12167, tm12167, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12167, agent12167, scalar12167, tp12167, tm12167, ep12167, em12167, dsL]

theorem tails12167 :
    exp (-((12167:ℝ)*ep12167)) ≤ scalar12167.upperTail ∧
    exp (-((12167:ℝ)*em12167)) ≤ scalar12167.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12167:ℝ)) (by norm_num [ep12167]) ?_)
      (show bp12167^8 ≤ scalar12167.upperTail by norm_num [bp12167, scalar12167])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12167, bp12167, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12167:ℝ)) (by norm_num [em12167]) ?_)
      (show bm12167^8 ≤ scalar12167.lowerTail by norm_num [bm12167, scalar12167])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12167, bm12167, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12167 :
    agent12167.root+dsL+scalar12167.worldRadius < √(1/100/aL) ∧
    2*(agent12167.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12167, agent12167, scalar12167, tp12167, tm12167, ep12167, em12167, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12167, agent12167, scalar12167, tp12167, tm12167, ep12167, em12167, dsL]

noncomputable def master12167 : MasterCertificate 12167 world12167 agent12167 :=
  master scalar12167 dsL tp12167 tm12167 ep12167 em12167
    (by norm_num [dsL]) (by norm_num [tp12167]) (by norm_num [tm12167])
    (by norm_num [ep12167]) (by norm_num [em12167])
    positive12167 negative12167 tails12167.1 tails12167.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12167.1 tailGuards12167.2

theorem preserves12167 : master12167.toScalarCertificate = scalar12167 := rfl

noncomputable def tp12168 : ℝ := (296847111 / 1250000000)
noncomputable def tm12168 : ℝ := (-((3071588247 / 5000000000)))
noncomputable def ep12168 : ℝ := (10930177332348429 / 20000000000000000000)
noncomputable def em12168 : ℝ := (13171799073434919 / 25000000000000000000)
noncomputable def bp12168 : ℝ := (43550892634531110443 / 100000000000000000000)
noncomputable def bm12168 : ℝ := (11217819819661676393 / 25000000000000000000)

theorem positive12168 :
    Eplus aL (agent12168.root+dsL) scalar12168.worldRadius world12168.frame
      agent12168.frame tp12168 ≤ -ep12168 := by
  apply positive_check (eT := (14528731380667402179 / 12500000000000000000)) (y := (39638536161008621359 / 100000000000000000000)) (u := (74322101244330097647 / 50000000000000000000))
  · norm_num [world12168, agent12168, scalar12168, tp12168, tm12168, ep12168, em12168, dsL]
  · norm_num [world12168, agent12168, scalar12168, tp12168, tm12168, ep12168, em12168, dsL]
  · norm_num [world12168, agent12168, scalar12168, tp12168, tm12168, ep12168, em12168, dsL]
  · norm_num [world12168, agent12168, scalar12168, tp12168, tm12168, ep12168, em12168, dsL]
  · norm_num [world12168, agent12168, scalar12168, tp12168, tm12168, ep12168, em12168, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12168, agent12168, tp12168, tm12168, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12168, agent12168, scalar12168, tp12168, tm12168, ep12168, em12168, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12168, agent12168, tp12168, tm12168, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12168, agent12168, scalar12168, tp12168, tm12168, ep12168, em12168, dsL]

theorem negative12168 :
    Eminus aL (agent12168.root+dsL) scalar12168.worldRadius world12168.frame
      agent12168.frame tm12168 ≤ -em12168 := by
  apply negative_check (lo := (67769358021124761021 / 100000000000000000000)) (hi := (33884679010562380511 / 50000000000000000000))
    (y := (-((73296413340451430273 / 100000000000000000000)))) (u := (48048266251167063659 / 100000000000000000000))
  · norm_num [world12168, agent12168, scalar12168, tp12168, tm12168, ep12168, em12168, dsL]
  · norm_num [world12168, agent12168, scalar12168, tp12168, tm12168, ep12168, em12168, dsL]
  · norm_num [world12168, agent12168, scalar12168, tp12168, tm12168, ep12168, em12168, dsL]
  · norm_num [world12168, agent12168, scalar12168, tp12168, tm12168, ep12168, em12168, dsL]
  · norm_num [world12168, agent12168, scalar12168, tp12168, tm12168, ep12168, em12168, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12168, agent12168, tp12168, tm12168, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12168, agent12168, tp12168, tm12168, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12168, agent12168, scalar12168, tp12168, tm12168, ep12168, em12168, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12168, agent12168, tp12168, tm12168, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12168, agent12168, scalar12168, tp12168, tm12168, ep12168, em12168, dsL]

theorem tails12168 :
    exp (-((12168:ℝ)*ep12168)) ≤ scalar12168.upperTail ∧
    exp (-((12168:ℝ)*em12168)) ≤ scalar12168.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12168:ℝ)) (by norm_num [ep12168]) ?_)
      (show bp12168^8 ≤ scalar12168.upperTail by norm_num [bp12168, scalar12168])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12168, bp12168, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12168:ℝ)) (by norm_num [em12168]) ?_)
      (show bm12168^8 ≤ scalar12168.lowerTail by norm_num [bm12168, scalar12168])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12168, bm12168, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12168 :
    agent12168.root+dsL+scalar12168.worldRadius < √(1/100/aL) ∧
    2*(agent12168.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12168, agent12168, scalar12168, tp12168, tm12168, ep12168, em12168, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12168, agent12168, scalar12168, tp12168, tm12168, ep12168, em12168, dsL]

noncomputable def master12168 : MasterCertificate 12168 world12168 agent12168 :=
  master scalar12168 dsL tp12168 tm12168 ep12168 em12168
    (by norm_num [dsL]) (by norm_num [tp12168]) (by norm_num [tm12168])
    (by norm_num [ep12168]) (by norm_num [em12168])
    positive12168 negative12168 tails12168.1 tails12168.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12168.1 tailGuards12168.2

theorem preserves12168 : master12168.toScalarCertificate = scalar12168 := rfl

noncomputable def tp12169 : ℝ := (148429661 / 625000000)
noncomputable def tm12169 : ℝ := (-((3071697649 / 5000000000)))
noncomputable def ep12169 : ℝ := (54653745942050659 / 100000000000000000000)
noncomputable def em12169 : ℝ := (52689679506831347 / 100000000000000000000)
noncomputable def bp12169 : ℝ := (21773011809611909599 / 50000000000000000000)
noncomputable def bm12169 : ℝ := (44866629429470319793 / 100000000000000000000)

theorem positive12169 :
    Eplus aL (agent12169.root+dsL) scalar12169.worldRadius world12169.frame
      agent12169.frame tp12169 ≤ -ep12169 := by
  apply positive_check (eT := (14528769133269741193 / 12500000000000000000)) (y := (39639159583703897459 / 100000000000000000000)) (u := (148645129173242299761 / 100000000000000000000))
  · norm_num [world12169, agent12169, scalar12169, tp12169, tm12169, ep12169, em12169, dsL]
  · norm_num [world12169, agent12169, scalar12169, tp12169, tm12169, ep12169, em12169, dsL]
  · norm_num [world12169, agent12169, scalar12169, tp12169, tm12169, ep12169, em12169, dsL]
  · norm_num [world12169, agent12169, scalar12169, tp12169, tm12169, ep12169, em12169, dsL]
  · norm_num [world12169, agent12169, scalar12169, tp12169, tm12169, ep12169, em12169, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12169, agent12169, tp12169, tm12169, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12169, agent12169, scalar12169, tp12169, tm12169, ep12169, em12169, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12169, agent12169, tp12169, tm12169, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12169, agent12169, scalar12169, tp12169, tm12169, ep12169, em12169, dsL]

theorem negative12169 :
    Eminus aL (agent12169.root+dsL) scalar12169.worldRadius world12169.frame
      agent12169.frame tm12169 ≤ -em12169 := by
  apply negative_check (lo := (33884523989501936103 / 50000000000000000000)) (hi := (67769047979003872207 / 100000000000000000000))
    (y := (-((73296013375462766789 / 100000000000000000000)))) (u := (6006057303474255937 / 12500000000000000000))
  · norm_num [world12169, agent12169, scalar12169, tp12169, tm12169, ep12169, em12169, dsL]
  · norm_num [world12169, agent12169, scalar12169, tp12169, tm12169, ep12169, em12169, dsL]
  · norm_num [world12169, agent12169, scalar12169, tp12169, tm12169, ep12169, em12169, dsL]
  · norm_num [world12169, agent12169, scalar12169, tp12169, tm12169, ep12169, em12169, dsL]
  · norm_num [world12169, agent12169, scalar12169, tp12169, tm12169, ep12169, em12169, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12169, agent12169, tp12169, tm12169, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12169, agent12169, tp12169, tm12169, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12169, agent12169, scalar12169, tp12169, tm12169, ep12169, em12169, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12169, agent12169, tp12169, tm12169, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12169, agent12169, scalar12169, tp12169, tm12169, ep12169, em12169, dsL]

theorem tails12169 :
    exp (-((12169:ℝ)*ep12169)) ≤ scalar12169.upperTail ∧
    exp (-((12169:ℝ)*em12169)) ≤ scalar12169.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12169:ℝ)) (by norm_num [ep12169]) ?_)
      (show bp12169^8 ≤ scalar12169.upperTail by norm_num [bp12169, scalar12169])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12169, bp12169, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12169:ℝ)) (by norm_num [em12169]) ?_)
      (show bm12169^8 ≤ scalar12169.lowerTail by norm_num [bm12169, scalar12169])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12169, bm12169, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12169 :
    agent12169.root+dsL+scalar12169.worldRadius < √(1/100/aL) ∧
    2*(agent12169.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12169, agent12169, scalar12169, tp12169, tm12169, ep12169, em12169, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12169, agent12169, scalar12169, tp12169, tm12169, ep12169, em12169, dsL]

noncomputable def master12169 : MasterCertificate 12169 world12169 agent12169 :=
  master scalar12169 dsL tp12169 tm12169 ep12169 em12169
    (by norm_num [dsL]) (by norm_num [tp12169]) (by norm_num [tm12169])
    (by norm_num [ep12169]) (by norm_num [em12169])
    positive12169 negative12169 tails12169.1 tails12169.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12169.1 tailGuards12169.2

theorem preserves12169 : master12169.toScalarCertificate = scalar12169 := rfl

noncomputable def tp12170 : ℝ := (474994431 / 2000000000)
noncomputable def tm12170 : ℝ := (-((1228722813 / 2000000000)))
noncomputable def ep12170 : ℝ := (6832075527906997 / 12500000000000000000)
noncomputable def em12170 : ℝ := (52692161800624941 / 100000000000000000000)
noncomputable def bp12170 : ℝ := (43541155498810181473 / 100000000000000000000)
noncomputable def bm12170 : ℝ := (44861980411023235399 / 100000000000000000000)

theorem positive12170 :
    Eplus aL (agent12170.root+dsL) scalar12170.worldRadius world12170.frame
      agent12170.frame tp12170 ≤ -ep12170 := by
  apply positive_check (eT := (4649218172865135109 / 4000000000000000000)) (y := (7927956321357120023 / 20000000000000000000)) (u := (74323026891565612269 / 50000000000000000000))
  · norm_num [world12170, agent12170, scalar12170, tp12170, tm12170, ep12170, em12170, dsL]
  · norm_num [world12170, agent12170, scalar12170, tp12170, tm12170, ep12170, em12170, dsL]
  · norm_num [world12170, agent12170, scalar12170, tp12170, tm12170, ep12170, em12170, dsL]
  · norm_num [world12170, agent12170, scalar12170, tp12170, tm12170, ep12170, em12170, dsL]
  · norm_num [world12170, agent12170, scalar12170, tp12170, tm12170, ep12170, em12170, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12170, agent12170, tp12170, tm12170, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12170, agent12170, scalar12170, tp12170, tm12170, ep12170, em12170, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12170, agent12170, tp12170, tm12170, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12170, agent12170, scalar12170, tp12170, tm12170, ep12170, em12170, dsL]

theorem negative12170 :
    Eminus aL (agent12170.root+dsL) scalar12170.worldRadius world12170.frame
      agent12170.frame tm12170 ≤ -em12170 := by
  apply negative_check (lo := (8471092254446214219 / 12500000000000000000)) (hi := (67768738035569713753 / 100000000000000000000))
    (y := (-((73295614503597843851 / 100000000000000000000)))) (u := (12012162519989617047 / 25000000000000000000))
  · norm_num [world12170, agent12170, scalar12170, tp12170, tm12170, ep12170, em12170, dsL]
  · norm_num [world12170, agent12170, scalar12170, tp12170, tm12170, ep12170, em12170, dsL]
  · norm_num [world12170, agent12170, scalar12170, tp12170, tm12170, ep12170, em12170, dsL]
  · norm_num [world12170, agent12170, scalar12170, tp12170, tm12170, ep12170, em12170, dsL]
  · norm_num [world12170, agent12170, scalar12170, tp12170, tm12170, ep12170, em12170, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12170, agent12170, tp12170, tm12170, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12170, agent12170, tp12170, tm12170, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12170, agent12170, scalar12170, tp12170, tm12170, ep12170, em12170, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12170, agent12170, tp12170, tm12170, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12170, agent12170, scalar12170, tp12170, tm12170, ep12170, em12170, dsL]

theorem tails12170 :
    exp (-((12170:ℝ)*ep12170)) ≤ scalar12170.upperTail ∧
    exp (-((12170:ℝ)*em12170)) ≤ scalar12170.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12170:ℝ)) (by norm_num [ep12170]) ?_)
      (show bp12170^8 ≤ scalar12170.upperTail by norm_num [bp12170, scalar12170])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12170, bp12170, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12170:ℝ)) (by norm_num [em12170]) ?_)
      (show bm12170^8 ≤ scalar12170.lowerTail by norm_num [bm12170, scalar12170])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12170, bm12170, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12170 :
    agent12170.root+dsL+scalar12170.worldRadius < √(1/100/aL) ∧
    2*(agent12170.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12170, agent12170, scalar12170, tp12170, tm12170, ep12170, em12170, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12170, agent12170, scalar12170, tp12170, tm12170, ep12170, em12170, dsL]

noncomputable def master12170 : MasterCertificate 12170 world12170 agent12170 :=
  master scalar12170 dsL tp12170 tm12170 ep12170 em12170
    (by norm_num [dsL]) (by norm_num [tp12170]) (by norm_num [tm12170])
    (by norm_num [ep12170]) (by norm_num [em12170])
    positive12170 negative12170 tails12170.1 tails12170.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12170.1 tailGuards12170.2

theorem preserves12170 : master12170.toScalarCertificate = scalar12170 := rfl

noncomputable def tp12171 : ℝ := (2375069689 / 10000000000)
noncomputable def tm12171 : ℝ := (-((153595817 / 250000000)))
noncomputable def ep12171 : ℝ := (27329730382446859 / 50000000000000000000)
noncomputable def em12171 : ℝ := (52694642440038851 / 100000000000000000000)
noncomputable def bp12171 : ℝ := (43536288763721626609 / 100000000000000000000)
noncomputable def bm12171 : ℝ := (44857332724956858327 / 100000000000000000000)

theorem positive12171 :
    Eplus aL (agent12171.root+dsL) scalar12171.worldRadius world12171.frame
      agent12171.frame tp12171 ≤ -ep12171 := by
  apply positive_check (eT := (58115377641417166497 / 50000000000000000000)) (y := (7928080707698663543 / 20000000000000000000)) (u := (3716174456573669659 / 2500000000000000000))
  · norm_num [world12171, agent12171, scalar12171, tp12171, tm12171, ep12171, em12171, dsL]
  · norm_num [world12171, agent12171, scalar12171, tp12171, tm12171, ep12171, em12171, dsL]
  · norm_num [world12171, agent12171, scalar12171, tp12171, tm12171, ep12171, em12171, dsL]
  · norm_num [world12171, agent12171, scalar12171, tp12171, tm12171, ep12171, em12171, dsL]
  · norm_num [world12171, agent12171, scalar12171, tp12171, tm12171, ep12171, em12171, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12171, agent12171, tp12171, tm12171, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12171, agent12171, scalar12171, tp12171, tm12171, ep12171, em12171, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12171, agent12171, tp12171, tm12171, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12171, agent12171, scalar12171, tp12171, tm12171, ep12171, em12171, dsL]

theorem negative12171 :
    Eminus aL (agent12171.root+dsL) scalar12171.worldRadius world12171.frame
      agent12171.frame tm12171 ≤ -em12171 := by
  apply negative_check (lo := (33884214342208162659 / 50000000000000000000)) (hi := (67768428684416325319 / 100000000000000000000))
    (y := (-((73295215222321627901 / 100000000000000000000)))) (u := (9609768385920944317 / 20000000000000000000))
  · norm_num [world12171, agent12171, scalar12171, tp12171, tm12171, ep12171, em12171, dsL]
  · norm_num [world12171, agent12171, scalar12171, tp12171, tm12171, ep12171, em12171, dsL]
  · norm_num [world12171, agent12171, scalar12171, tp12171, tm12171, ep12171, em12171, dsL]
  · norm_num [world12171, agent12171, scalar12171, tp12171, tm12171, ep12171, em12171, dsL]
  · norm_num [world12171, agent12171, scalar12171, tp12171, tm12171, ep12171, em12171, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12171, agent12171, tp12171, tm12171, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12171, agent12171, tp12171, tm12171, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12171, agent12171, scalar12171, tp12171, tm12171, ep12171, em12171, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12171, agent12171, tp12171, tm12171, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12171, agent12171, scalar12171, tp12171, tm12171, ep12171, em12171, dsL]

theorem tails12171 :
    exp (-((12171:ℝ)*ep12171)) ≤ scalar12171.upperTail ∧
    exp (-((12171:ℝ)*em12171)) ≤ scalar12171.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12171:ℝ)) (by norm_num [ep12171]) ?_)
      (show bp12171^8 ≤ scalar12171.upperTail by norm_num [bp12171, scalar12171])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12171, bp12171, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12171:ℝ)) (by norm_num [em12171]) ?_)
      (show bm12171^8 ≤ scalar12171.lowerTail by norm_num [bm12171, scalar12171])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12171, bm12171, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12171 :
    agent12171.root+dsL+scalar12171.worldRadius < √(1/100/aL) ∧
    2*(agent12171.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12171, agent12171, scalar12171, tp12171, tm12171, ep12171, em12171, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12171, agent12171, scalar12171, tp12171, tm12171, ep12171, em12171, dsL]

noncomputable def master12171 : MasterCertificate 12171 world12171 agent12171 :=
  master scalar12171 dsL tp12171 tm12171 ep12171 em12171
    (by norm_num [dsL]) (by norm_num [tp12171]) (by norm_num [tm12171])
    (by norm_num [ep12171]) (by norm_num [em12171])
    positive12171 negative12171 tails12171.1 tails12171.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12171.1 tailGuards12171.2

theorem preserves12171 : master12171.toScalarCertificate = scalar12171 := rfl

noncomputable def tp12172 : ℝ := (37111987 / 156250000)
noncomputable def tm12172 : ℝ := (-((1228810207 / 2000000000)))
noncomputable def ep12172 : ℝ := (54662315334329363 / 100000000000000000000)
noncomputable def em12172 : ℝ := (26348560632709547 / 50000000000000000000)
noncomputable def bp12172 : ℝ := (43531423567980212143 / 100000000000000000000)
noncomputable def bm12172 : ℝ := (11213171620047099697 / 25000000000000000000)

theorem positive12172 :
    Eplus aL (agent12172.root+dsL) scalar12172.worldRadius world12172.frame
      agent12172.frame tp12172 ≤ -ep12172 := by
  apply positive_check (eT := (29057763969057247401 / 25000000000000000000)) (y := (9910256286109253859 / 25000000000000000000)) (u := (9290493891516913531 / 6250000000000000000))
  · norm_num [world12172, agent12172, scalar12172, tp12172, tm12172, ep12172, em12172, dsL]
  · norm_num [world12172, agent12172, scalar12172, tp12172, tm12172, ep12172, em12172, dsL]
  · norm_num [world12172, agent12172, scalar12172, tp12172, tm12172, ep12172, em12172, dsL]
  · norm_num [world12172, agent12172, scalar12172, tp12172, tm12172, ep12172, em12172, dsL]
  · norm_num [world12172, agent12172, scalar12172, tp12172, tm12172, ep12172, em12172, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12172, agent12172, tp12172, tm12172, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12172, agent12172, scalar12172, tp12172, tm12172, ep12172, em12172, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12172, agent12172, tp12172, tm12172, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12172, agent12172, scalar12172, tp12172, tm12172, ep12172, em12172, dsL]

theorem negative12172 :
    Eminus aL (agent12172.root+dsL) scalar12172.worldRadius world12172.frame
      agent12172.frame tm12172 ≤ -em12172 := by
  apply negative_check (lo := (33884060194458186867 / 50000000000000000000)) (hi := (13553624077783274747 / 20000000000000000000))
    (y := (-((7329481459843240781 / 10000000000000000000)))) (u := (48049034425129576453 / 100000000000000000000))
  · norm_num [world12172, agent12172, scalar12172, tp12172, tm12172, ep12172, em12172, dsL]
  · norm_num [world12172, agent12172, scalar12172, tp12172, tm12172, ep12172, em12172, dsL]
  · norm_num [world12172, agent12172, scalar12172, tp12172, tm12172, ep12172, em12172, dsL]
  · norm_num [world12172, agent12172, scalar12172, tp12172, tm12172, ep12172, em12172, dsL]
  · norm_num [world12172, agent12172, scalar12172, tp12172, tm12172, ep12172, em12172, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12172, agent12172, tp12172, tm12172, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12172, agent12172, tp12172, tm12172, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12172, agent12172, scalar12172, tp12172, tm12172, ep12172, em12172, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12172, agent12172, tp12172, tm12172, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12172, agent12172, scalar12172, tp12172, tm12172, ep12172, em12172, dsL]

theorem tails12172 :
    exp (-((12172:ℝ)*ep12172)) ≤ scalar12172.upperTail ∧
    exp (-((12172:ℝ)*em12172)) ≤ scalar12172.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12172:ℝ)) (by norm_num [ep12172]) ?_)
      (show bp12172^8 ≤ scalar12172.upperTail by norm_num [bp12172, scalar12172])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12172, bp12172, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12172:ℝ)) (by norm_num [em12172]) ?_)
      (show bm12172^8 ≤ scalar12172.lowerTail by norm_num [bm12172, scalar12172])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12172, bm12172, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12172 :
    agent12172.root+dsL+scalar12172.worldRadius < √(1/100/aL) ∧
    2*(agent12172.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12172, agent12172, scalar12172, tp12172, tm12172, ep12172, em12172, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12172, agent12172, scalar12172, tp12172, tm12172, ep12172, em12172, dsL]

noncomputable def master12172 : MasterCertificate 12172 world12172 agent12172 :=
  master scalar12172 dsL tp12172 tm12172 ep12172 em12172
    (by norm_num [dsL]) (by norm_num [tp12172]) (by norm_num [tm12172])
    (by norm_num [ep12172]) (by norm_num [em12172])
    positive12172 negative12172 tails12172.1 tails12172.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12172.1 tailGuards12172.2

theorem preserves12172 : master12172.toScalarCertificate = scalar12172 := rfl

noncomputable def tp12173 : ℝ := (593816153 / 2500000000)
noncomputable def tm12173 : ℝ := (-((153606739 / 250000000)))
noncomputable def ep12173 : ℝ := (27332584571456391 / 50000000000000000000)
noncomputable def em12173 : ℝ := (52699599336212799 / 100000000000000000000)
noncomputable def bp12173 : ℝ := (21763279554611494837 / 50000000000000000000)
noncomputable def bm12173 : ℝ := (44848040953687955629 / 100000000000000000000)

theorem positive12173 :
    Eplus aL (agent12173.root+dsL) scalar12173.worldRadius world12173.frame
      agent12173.frame tp12173 ≤ -ep12173 := by
  apply positive_check (eT := (116231356248997789121 / 100000000000000000000)) (y := (39641646734415952581 / 100000000000000000000)) (u := (148648826247606682421 / 100000000000000000000))
  · norm_num [world12173, agent12173, scalar12173, tp12173, tm12173, ep12173, em12173, dsL]
  · norm_num [world12173, agent12173, scalar12173, tp12173, tm12173, ep12173, em12173, dsL]
  · norm_num [world12173, agent12173, scalar12173, tp12173, tm12173, ep12173, em12173, dsL]
  · norm_num [world12173, agent12173, scalar12173, tp12173, tm12173, ep12173, em12173, dsL]
  · norm_num [world12173, agent12173, scalar12173, tp12173, tm12173, ep12173, em12173, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12173, agent12173, tp12173, tm12173, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12173, agent12173, scalar12173, tp12173, tm12173, ep12173, em12173, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12173, agent12173, tp12173, tm12173, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12173, agent12173, scalar12173, tp12173, tm12173, ep12173, em12173, dsL]

theorem negative12173 :
    Eminus aL (agent12173.root+dsL) scalar12173.worldRadius world12173.frame
      agent12173.frame tm12173 ≤ -em12173 := by
  apply negative_check (lo := (16941952825940313917 / 25000000000000000000)) (hi := (67767811303761255669 / 100000000000000000000))
    (y := (-((36647208482160135971 / 50000000000000000000)))) (u := (12012306371215215439 / 25000000000000000000))
  · norm_num [world12173, agent12173, scalar12173, tp12173, tm12173, ep12173, em12173, dsL]
  · norm_num [world12173, agent12173, scalar12173, tp12173, tm12173, ep12173, em12173, dsL]
  · norm_num [world12173, agent12173, scalar12173, tp12173, tm12173, ep12173, em12173, dsL]
  · norm_num [world12173, agent12173, scalar12173, tp12173, tm12173, ep12173, em12173, dsL]
  · norm_num [world12173, agent12173, scalar12173, tp12173, tm12173, ep12173, em12173, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12173, agent12173, tp12173, tm12173, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12173, agent12173, tp12173, tm12173, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12173, agent12173, scalar12173, tp12173, tm12173, ep12173, em12173, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12173, agent12173, tp12173, tm12173, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12173, agent12173, scalar12173, tp12173, tm12173, ep12173, em12173, dsL]

theorem tails12173 :
    exp (-((12173:ℝ)*ep12173)) ≤ scalar12173.upperTail ∧
    exp (-((12173:ℝ)*em12173)) ≤ scalar12173.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12173:ℝ)) (by norm_num [ep12173]) ?_)
      (show bp12173^8 ≤ scalar12173.upperTail by norm_num [bp12173, scalar12173])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12173, bp12173, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12173:ℝ)) (by norm_num [em12173]) ?_)
      (show bm12173^8 ≤ scalar12173.lowerTail by norm_num [bm12173, scalar12173])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12173, bm12173, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12173 :
    agent12173.root+dsL+scalar12173.worldRadius < √(1/100/aL) ∧
    2*(agent12173.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12173, agent12173, scalar12173, tp12173, tm12173, ep12173, em12173, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12173, agent12173, scalar12173, tp12173, tm12173, ep12173, em12173, dsL]

noncomputable def master12173 : MasterCertificate 12173 world12173 agent12173 :=
  master scalar12173 dsL tp12173 tm12173 ep12173 em12173
    (by norm_num [dsL]) (by norm_num [tp12173]) (by norm_num [tm12173])
    (by norm_num [ep12173]) (by norm_num [em12173])
    positive12173 negative12173 tails12173.1 tails12173.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12173.1 tailGuards12173.2

theorem preserves12173 : master12173.toScalarCertificate = scalar12173 := rfl

noncomputable def tp12174 : ℝ := (296920251 / 1250000000)
noncomputable def tm12174 : ℝ := (-((384030483 / 625000000)))
noncomputable def ep12174 : ℝ := (27334010081434977 / 50000000000000000000)
noncomputable def em12174 : ℝ := (52702074859680803 / 100000000000000000000)
noncomputable def bp12174 : ℝ := (43521696730425892547 / 100000000000000000000)
noncomputable def bm12174 : ℝ := (22421698684416002189 / 50000000000000000000)

theorem positive12174 :
    Eplus aL (agent12174.root+dsL) scalar12174.worldRadius world12174.frame
      agent12174.frame tp12174 ≤ -ep12174 := by
  apply positive_check (eT := (116231656305484327727 / 100000000000000000000)) (y := (39642268067499556767 / 100000000000000000000)) (u := (148649749854811883697 / 100000000000000000000))
  · norm_num [world12174, agent12174, scalar12174, tp12174, tm12174, ep12174, em12174, dsL]
  · norm_num [world12174, agent12174, scalar12174, tp12174, tm12174, ep12174, em12174, dsL]
  · norm_num [world12174, agent12174, scalar12174, tp12174, tm12174, ep12174, em12174, dsL]
  · norm_num [world12174, agent12174, scalar12174, tp12174, tm12174, ep12174, em12174, dsL]
  · norm_num [world12174, agent12174, scalar12174, tp12174, tm12174, ep12174, em12174, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12174, agent12174, tp12174, tm12174, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12174, agent12174, scalar12174, tp12174, tm12174, ep12174, em12174, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12174, agent12174, tp12174, tm12174, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12174, agent12174, scalar12174, tp12174, tm12174, ep12174, em12174, dsL]

theorem negative12174 :
    Eminus aL (agent12174.root+dsL) scalar12174.worldRadius world12174.frame
      agent12174.frame tm12174 ≤ -em12174 := by
  apply negative_check (lo := (8470937961310872593 / 12500000000000000000)) (hi := (13553500738097396149 / 20000000000000000000))
    (y := (-((7329401648590942753 / 10000000000000000000)))) (u := (24024708956010410467 / 50000000000000000000))
  · norm_num [world12174, agent12174, scalar12174, tp12174, tm12174, ep12174, em12174, dsL]
  · norm_num [world12174, agent12174, scalar12174, tp12174, tm12174, ep12174, em12174, dsL]
  · norm_num [world12174, agent12174, scalar12174, tp12174, tm12174, ep12174, em12174, dsL]
  · norm_num [world12174, agent12174, scalar12174, tp12174, tm12174, ep12174, em12174, dsL]
  · norm_num [world12174, agent12174, scalar12174, tp12174, tm12174, ep12174, em12174, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12174, agent12174, tp12174, tm12174, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12174, agent12174, tp12174, tm12174, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12174, agent12174, scalar12174, tp12174, tm12174, ep12174, em12174, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12174, agent12174, tp12174, tm12174, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12174, agent12174, scalar12174, tp12174, tm12174, ep12174, em12174, dsL]

theorem tails12174 :
    exp (-((12174:ℝ)*ep12174)) ≤ scalar12174.upperTail ∧
    exp (-((12174:ℝ)*em12174)) ≤ scalar12174.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12174:ℝ)) (by norm_num [ep12174]) ?_)
      (show bp12174^8 ≤ scalar12174.upperTail by norm_num [bp12174, scalar12174])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12174, bp12174, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12174:ℝ)) (by norm_num [em12174]) ?_)
      (show bm12174^8 ≤ scalar12174.lowerTail by norm_num [bm12174, scalar12174])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12174, bm12174, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12174 :
    agent12174.root+dsL+scalar12174.worldRadius < √(1/100/aL) ∧
    2*(agent12174.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12174, agent12174, scalar12174, tp12174, tm12174, ep12174, em12174, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12174, agent12174, scalar12174, tp12174, tm12174, ep12174, em12174, dsL]

noncomputable def master12174 : MasterCertificate 12174 world12174 agent12174 :=
  master scalar12174 dsL tp12174 tm12174 ep12174 em12174
    (by norm_num [dsL]) (by norm_num [tp12174]) (by norm_num [tm12174])
    (by norm_num [ep12174]) (by norm_num [em12174])
    positive12174 negative12174 tails12174.1 tails12174.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12174.1 tailGuards12174.2

theorem preserves12174 : master12174.toScalarCertificate = scalar12174 := rfl

noncomputable def tp12175 : ℝ := (2375459361 / 10000000000)
noncomputable def tm12175 : ℝ := (-((6144705797 / 10000000000)))
noncomputable def ep12175 : ℝ := (54670870422357297 / 100000000000000000000)
noncomputable def em12175 : ℝ := (13176137407258427 / 25000000000000000000)
noncomputable def bp12175 : ℝ := (10879208772069367041 / 25000000000000000000)
noncomputable def bm12175 : ℝ := (44838754501876739493 / 100000000000000000000)

theorem positive12175 :
    Eplus aL (agent12175.root+dsL) scalar12175.worldRadius world12175.frame
      agent12175.frame tp12175 ≤ -ep12175 := by
  apply positive_check (eT := (116231956082519987613 / 100000000000000000000)) (y := (9910722310034888607 / 25000000000000000000)) (u := (74325336614627639243 / 50000000000000000000))
  · norm_num [world12175, agent12175, scalar12175, tp12175, tm12175, ep12175, em12175, dsL]
  · norm_num [world12175, agent12175, scalar12175, tp12175, tm12175, ep12175, em12175, dsL]
  · norm_num [world12175, agent12175, scalar12175, tp12175, tm12175, ep12175, em12175, dsL]
  · norm_num [world12175, agent12175, scalar12175, tp12175, tm12175, ep12175, em12175, dsL]
  · norm_num [world12175, agent12175, scalar12175, tp12175, tm12175, ep12175, em12175, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12175, agent12175, tp12175, tm12175, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12175, agent12175, scalar12175, tp12175, tm12175, ep12175, em12175, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12175, agent12175, tp12175, tm12175, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12175, agent12175, scalar12175, tp12175, tm12175, ep12175, em12175, dsL]

theorem negative12175 :
    Eminus aL (agent12175.root+dsL) scalar12175.worldRadius world12175.frame
      agent12175.frame tm12175 ≤ -em12175 := by
  apply negative_check (lo := (33883598220921837557 / 50000000000000000000)) (hi := (13553439288368735023 / 20000000000000000000))
    (y := (-((73293616370910764897 / 100000000000000000000)))) (u := (12012402541333318483 / 25000000000000000000))
  · norm_num [world12175, agent12175, scalar12175, tp12175, tm12175, ep12175, em12175, dsL]
  · norm_num [world12175, agent12175, scalar12175, tp12175, tm12175, ep12175, em12175, dsL]
  · norm_num [world12175, agent12175, scalar12175, tp12175, tm12175, ep12175, em12175, dsL]
  · norm_num [world12175, agent12175, scalar12175, tp12175, tm12175, ep12175, em12175, dsL]
  · norm_num [world12175, agent12175, scalar12175, tp12175, tm12175, ep12175, em12175, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12175, agent12175, tp12175, tm12175, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12175, agent12175, tp12175, tm12175, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12175, agent12175, scalar12175, tp12175, tm12175, ep12175, em12175, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12175, agent12175, tp12175, tm12175, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12175, agent12175, scalar12175, tp12175, tm12175, ep12175, em12175, dsL]

theorem tails12175 :
    exp (-((12175:ℝ)*ep12175)) ≤ scalar12175.upperTail ∧
    exp (-((12175:ℝ)*em12175)) ≤ scalar12175.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12175:ℝ)) (by norm_num [ep12175]) ?_)
      (show bp12175^8 ≤ scalar12175.upperTail by norm_num [bp12175, scalar12175])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12175, bp12175, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12175:ℝ)) (by norm_num [em12175]) ?_)
      (show bm12175^8 ≤ scalar12175.lowerTail by norm_num [bm12175, scalar12175])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12175, bm12175, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12175 :
    agent12175.root+dsL+scalar12175.worldRadius < √(1/100/aL) ∧
    2*(agent12175.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12175, agent12175, scalar12175, tp12175, tm12175, ep12175, em12175, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12175, agent12175, scalar12175, tp12175, tm12175, ep12175, em12175, dsL]

noncomputable def master12175 : MasterCertificate 12175 world12175 agent12175 :=
  master scalar12175 dsL tp12175 tm12175 ep12175 em12175
    (by norm_num [dsL]) (by norm_num [tp12175]) (by norm_num [tm12175])
    (by norm_num [ep12175]) (by norm_num [em12175])
    positive12175 negative12175 tails12175.1 tails12175.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12175.1 tailGuards12175.2

theorem preserves12175 : master12175.toScalarCertificate = scalar12175 := rfl

noncomputable def tp12176 : ℝ := (2375556637 / 10000000000)
noncomputable def tm12176 : ℝ := (-((6144923773 / 10000000000)))
noncomputable def ep12176 : ℝ := (54673719194931961 / 100000000000000000000)
noncomputable def em12176 : ℝ := (6588377878884193 / 12500000000000000000)
noncomputable def bp12176 : ℝ := (4351197466386470069 / 10000000000000000000)
noncomputable def bm12176 : ℝ := (44834112771256604773 / 100000000000000000000)

theorem positive12176 :
    Eplus aL (agent12176.root+dsL) scalar12176.worldRadius world12176.frame
      agent12176.frame tp12176 ≤ -ep12176 := by
  apply positive_check (eT := (58116127664922321267 / 50000000000000000000)) (y := (39643509638304381087 / 100000000000000000000)) (u := (37162898864541184479 / 25000000000000000000))
  · norm_num [world12176, agent12176, scalar12176, tp12176, tm12176, ep12176, em12176, dsL]
  · norm_num [world12176, agent12176, scalar12176, tp12176, tm12176, ep12176, em12176, dsL]
  · norm_num [world12176, agent12176, scalar12176, tp12176, tm12176, ep12176, em12176, dsL]
  · norm_num [world12176, agent12176, scalar12176, tp12176, tm12176, ep12176, em12176, dsL]
  · norm_num [world12176, agent12176, scalar12176, tp12176, tm12176, ep12176, em12176, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12176, agent12176, tp12176, tm12176, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12176, agent12176, scalar12176, tp12176, tm12176, ep12176, em12176, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12176, agent12176, tp12176, tm12176, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12176, agent12176, scalar12176, tp12176, tm12176, ep12176, em12176, dsL]

theorem negative12176 :
    Eminus aL (agent12176.root+dsL) scalar12176.worldRadius world12176.frame
      agent12176.frame tm12176 ≤ -em12176 := by
  apply negative_check (lo := (67766889532121997681 / 100000000000000000000)) (hi := (33883444766060998841 / 50000000000000000000))
    (y := (-((73293216669351126009 / 100000000000000000000)))) (u := (1501556319398697787 / 3125000000000000000))
  · norm_num [world12176, agent12176, scalar12176, tp12176, tm12176, ep12176, em12176, dsL]
  · norm_num [world12176, agent12176, scalar12176, tp12176, tm12176, ep12176, em12176, dsL]
  · norm_num [world12176, agent12176, scalar12176, tp12176, tm12176, ep12176, em12176, dsL]
  · norm_num [world12176, agent12176, scalar12176, tp12176, tm12176, ep12176, em12176, dsL]
  · norm_num [world12176, agent12176, scalar12176, tp12176, tm12176, ep12176, em12176, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12176, agent12176, tp12176, tm12176, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12176, agent12176, tp12176, tm12176, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12176, agent12176, scalar12176, tp12176, tm12176, ep12176, em12176, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12176, agent12176, tp12176, tm12176, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12176, agent12176, scalar12176, tp12176, tm12176, ep12176, em12176, dsL]

theorem tails12176 :
    exp (-((12176:ℝ)*ep12176)) ≤ scalar12176.upperTail ∧
    exp (-((12176:ℝ)*em12176)) ≤ scalar12176.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12176:ℝ)) (by norm_num [ep12176]) ?_)
      (show bp12176^8 ≤ scalar12176.upperTail by norm_num [bp12176, scalar12176])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12176, bp12176, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12176:ℝ)) (by norm_num [em12176]) ?_)
      (show bm12176^8 ≤ scalar12176.lowerTail by norm_num [bm12176, scalar12176])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12176, bm12176, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12176 :
    agent12176.root+dsL+scalar12176.worldRadius < √(1/100/aL) ∧
    2*(agent12176.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12176, agent12176, scalar12176, tp12176, tm12176, ep12176, em12176, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12176, agent12176, scalar12176, tp12176, tm12176, ep12176, em12176, dsL]

noncomputable def master12176 : MasterCertificate 12176 world12176 agent12176 :=
  master scalar12176 dsL tp12176 tm12176 ep12176 em12176
    (by norm_num [dsL]) (by norm_num [tp12176]) (by norm_num [tm12176])
    (by norm_num [ep12176]) (by norm_num [em12176])
    positive12176 negative12176 tails12176.1 tails12176.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12176.1 tailGuards12176.2

theorem preserves12176 : master12176.toScalarCertificate = scalar12176 := rfl

noncomputable def tp12177 : ℝ := (1187826969 / 5000000000)
noncomputable def tm12177 : ℝ := (-((6145141721 / 10000000000)))
noncomputable def ep12177 : ℝ := (2187062649738657 / 4000000000000000000)
noncomputable def em12177 : ℝ := (52709494792274963 / 100000000000000000000)
noncomputable def bp12177 : ℝ := (4350711561417705209 / 10000000000000000000)
noncomputable def bm12177 : ℝ := (44829472363590997401 / 100000000000000000000)

theorem positive12177 :
    Eplus aL (agent12177.root+dsL) scalar12177.worldRadius world12177.frame
      agent12177.frame tp12177 ≤ -ep12177 := by
  apply positive_check (eT := (116232554798161878827 / 100000000000000000000)) (y := (9911032800322523273 / 25000000000000000000)) (u := (148652519424331289087 / 100000000000000000000))
  · norm_num [world12177, agent12177, scalar12177, tp12177, tm12177, ep12177, em12177, dsL]
  · norm_num [world12177, agent12177, scalar12177, tp12177, tm12177, ep12177, em12177, dsL]
  · norm_num [world12177, agent12177, scalar12177, tp12177, tm12177, ep12177, em12177, dsL]
  · norm_num [world12177, agent12177, scalar12177, tp12177, tm12177, ep12177, em12177, dsL]
  · norm_num [world12177, agent12177, scalar12177, tp12177, tm12177, ep12177, em12177, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12177, agent12177, tp12177, tm12177, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12177, agent12177, scalar12177, tp12177, tm12177, ep12177, em12177, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12177, agent12177, tp12177, tm12177, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12177, agent12177, scalar12177, tp12177, tm12177, ep12177, em12177, dsL]

theorem negative12177 :
    Eminus aL (agent12177.root+dsL) scalar12177.worldRadius world12177.frame
      agent12177.frame tm12177 ≤ -em12177 := by
  apply negative_check (lo := (33883291341206096411 / 50000000000000000000)) (hi := (67766582682412192823 / 100000000000000000000))
    (y := (-((36646408882255316601 / 50000000000000000000)))) (u := (48049993894127531929 / 100000000000000000000))
  · norm_num [world12177, agent12177, scalar12177, tp12177, tm12177, ep12177, em12177, dsL]
  · norm_num [world12177, agent12177, scalar12177, tp12177, tm12177, ep12177, em12177, dsL]
  · norm_num [world12177, agent12177, scalar12177, tp12177, tm12177, ep12177, em12177, dsL]
  · norm_num [world12177, agent12177, scalar12177, tp12177, tm12177, ep12177, em12177, dsL]
  · norm_num [world12177, agent12177, scalar12177, tp12177, tm12177, ep12177, em12177, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12177, agent12177, tp12177, tm12177, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12177, agent12177, tp12177, tm12177, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12177, agent12177, scalar12177, tp12177, tm12177, ep12177, em12177, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12177, agent12177, tp12177, tm12177, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12177, agent12177, scalar12177, tp12177, tm12177, ep12177, em12177, dsL]

theorem tails12177 :
    exp (-((12177:ℝ)*ep12177)) ≤ scalar12177.upperTail ∧
    exp (-((12177:ℝ)*em12177)) ≤ scalar12177.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12177:ℝ)) (by norm_num [ep12177]) ?_)
      (show bp12177^8 ≤ scalar12177.upperTail by norm_num [bp12177, scalar12177])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12177, bp12177, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12177:ℝ)) (by norm_num [em12177]) ?_)
      (show bm12177^8 ≤ scalar12177.lowerTail by norm_num [bm12177, scalar12177])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12177, bm12177, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12177 :
    agent12177.root+dsL+scalar12177.worldRadius < √(1/100/aL) ∧
    2*(agent12177.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12177, agent12177, scalar12177, tp12177, tm12177, ep12177, em12177, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12177, agent12177, scalar12177, tp12177, tm12177, ep12177, em12177, dsL]

noncomputable def master12177 : MasterCertificate 12177 world12177 agent12177 :=
  master scalar12177 dsL tp12177 tm12177 ep12177 em12177
    (by norm_num [dsL]) (by norm_num [tp12177]) (by norm_num [tm12177])
    (by norm_num [ep12177]) (by norm_num [em12177])
    positive12177 negative12177 tails12177.1 tails12177.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12177.1 tailGuards12177.2

theorem preserves12177 : master12177.toScalarCertificate = scalar12177 := rfl

noncomputable def tp12178 : ℝ := (2375751139 / 10000000000)
noncomputable def tm12178 : ℝ := (-((6145359473 / 10000000000)))
noncomputable def ep12178 : ℝ := (27339705734060431 / 50000000000000000000)
noncomputable def em12178 : ℝ := (52711964894319329 / 100000000000000000000)
noncomputable def bp12178 : ℝ := (43502258005271696061 / 100000000000000000000)
noncomputable def bm12178 : ℝ := (22412416645672027187 / 50000000000000000000)

theorem positive12178 :
    Eplus aL (agent12178.root+dsL) scalar12178.worldRadius world12178.frame
      agent12178.frame tp12178 ≤ -ep12178 := by
  apply positive_check (eT := (14529106695944695501 / 12500000000000000000)) (y := (39644751467654219817 / 100000000000000000000)) (u := (148653441468768267957 / 100000000000000000000))
  · norm_num [world12178, agent12178, scalar12178, tp12178, tm12178, ep12178, em12178, dsL]
  · norm_num [world12178, agent12178, scalar12178, tp12178, tm12178, ep12178, em12178, dsL]
  · norm_num [world12178, agent12178, scalar12178, tp12178, tm12178, ep12178, em12178, dsL]
  · norm_num [world12178, agent12178, scalar12178, tp12178, tm12178, ep12178, em12178, dsL]
  · norm_num [world12178, agent12178, scalar12178, tp12178, tm12178, ep12178, em12178, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12178, agent12178, tp12178, tm12178, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12178, agent12178, scalar12178, tp12178, tm12178, ep12178, em12178, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12178, agent12178, tp12178, tm12178, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12178, agent12178, scalar12178, tp12178, tm12178, ep12178, em12178, dsL]

theorem negative12178 :
    Eminus aL (agent12178.root+dsL) scalar12178.worldRadius world12178.frame
      agent12178.frame tm12178 ≤ -em12178 := by
  apply negative_check (lo := (33883138306749381381 / 50000000000000000000)) (hi := (67766276613498762763 / 100000000000000000000))
    (y := (-((73292417842050329143 / 100000000000000000000)))) (u := (600627325715369259 / 1250000000000000000))
  · norm_num [world12178, agent12178, scalar12178, tp12178, tm12178, ep12178, em12178, dsL]
  · norm_num [world12178, agent12178, scalar12178, tp12178, tm12178, ep12178, em12178, dsL]
  · norm_num [world12178, agent12178, scalar12178, tp12178, tm12178, ep12178, em12178, dsL]
  · norm_num [world12178, agent12178, scalar12178, tp12178, tm12178, ep12178, em12178, dsL]
  · norm_num [world12178, agent12178, scalar12178, tp12178, tm12178, ep12178, em12178, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12178, agent12178, tp12178, tm12178, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12178, agent12178, tp12178, tm12178, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12178, agent12178, scalar12178, tp12178, tm12178, ep12178, em12178, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12178, agent12178, tp12178, tm12178, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12178, agent12178, scalar12178, tp12178, tm12178, ep12178, em12178, dsL]

theorem tails12178 :
    exp (-((12178:ℝ)*ep12178)) ≤ scalar12178.upperTail ∧
    exp (-((12178:ℝ)*em12178)) ≤ scalar12178.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12178:ℝ)) (by norm_num [ep12178]) ?_)
      (show bp12178^8 ≤ scalar12178.upperTail by norm_num [bp12178, scalar12178])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12178, bp12178, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12178:ℝ)) (by norm_num [em12178]) ?_)
      (show bm12178^8 ≤ scalar12178.lowerTail by norm_num [bm12178, scalar12178])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12178, bm12178, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12178 :
    agent12178.root+dsL+scalar12178.worldRadius < √(1/100/aL) ∧
    2*(agent12178.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12178, agent12178, scalar12178, tp12178, tm12178, ep12178, em12178, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12178, agent12178, scalar12178, tp12178, tm12178, ep12178, em12178, dsL]

noncomputable def master12178 : MasterCertificate 12178 world12178 agent12178 :=
  master scalar12178 dsL tp12178 tm12178 ep12178 em12178
    (by norm_num [dsL]) (by norm_num [tp12178]) (by norm_num [tm12178])
    (by norm_num [ep12178]) (by norm_num [em12178])
    positive12178 negative12178 tails12178.1 tails12178.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12178.1 tailGuards12178.2

theorem preserves12178 : master12178.toScalarCertificate = scalar12178 := rfl

noncomputable def tp12179 : ℝ := (2375848273 / 10000000000)
noncomputable def tm12179 : ℝ := (-((1229115403 / 2000000000)))
noncomputable def ep12179 : ℝ := (54682255458445653 / 100000000000000000000)
noncomputable def em12179 : ℝ := (2635721690290963 / 5000000000000000000)
noncomputable def bp12179 : ℝ := (21748700723344113577 / 50000000000000000000)
noncomputable def bm12179 : ℝ := (44820195234730329043 / 100000000000000000000)

theorem positive12179 :
    Eplus aL (agent12179.root+dsL) scalar12179.worldRadius world12179.frame
      agent12179.frame tp12179 ≤ -ep12179 := by
  apply positive_check (eT := (116233151880891037159 / 100000000000000000000)) (y := (39645371192636439053 / 100000000000000000000)) (u := (74327181357068284731 / 50000000000000000000))
  · norm_num [world12179, agent12179, scalar12179, tp12179, tm12179, ep12179, em12179, dsL]
  · norm_num [world12179, agent12179, scalar12179, tp12179, tm12179, ep12179, em12179, dsL]
  · norm_num [world12179, agent12179, scalar12179, tp12179, tm12179, ep12179, em12179, dsL]
  · norm_num [world12179, agent12179, scalar12179, tp12179, tm12179, ep12179, em12179, dsL]
  · norm_num [world12179, agent12179, scalar12179, tp12179, tm12179, ep12179, em12179, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12179, agent12179, tp12179, tm12179, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12179, agent12179, scalar12179, tp12179, tm12179, ep12179, em12179, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12179, agent12179, tp12179, tm12179, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12179, agent12179, scalar12179, tp12179, tm12179, ep12179, em12179, dsL]

theorem negative12179 :
    Eminus aL (agent12179.root+dsL) scalar12179.worldRadius world12179.frame
      agent12179.frame tm12179 ≤ -em12179 := by
  apply negative_check (lo := (33882985692725951111 / 50000000000000000000)) (hi := (67765971385451902223 / 100000000000000000000))
    (y := (-((36646008534158687457 / 50000000000000000000)))) (u := (24025189315069892147 / 50000000000000000000))
  · norm_num [world12179, agent12179, scalar12179, tp12179, tm12179, ep12179, em12179, dsL]
  · norm_num [world12179, agent12179, scalar12179, tp12179, tm12179, ep12179, em12179, dsL]
  · norm_num [world12179, agent12179, scalar12179, tp12179, tm12179, ep12179, em12179, dsL]
  · norm_num [world12179, agent12179, scalar12179, tp12179, tm12179, ep12179, em12179, dsL]
  · norm_num [world12179, agent12179, scalar12179, tp12179, tm12179, ep12179, em12179, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12179, agent12179, tp12179, tm12179, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12179, agent12179, tp12179, tm12179, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12179, agent12179, scalar12179, tp12179, tm12179, ep12179, em12179, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12179, agent12179, tp12179, tm12179, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12179, agent12179, scalar12179, tp12179, tm12179, ep12179, em12179, dsL]

theorem tails12179 :
    exp (-((12179:ℝ)*ep12179)) ≤ scalar12179.upperTail ∧
    exp (-((12179:ℝ)*em12179)) ≤ scalar12179.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12179:ℝ)) (by norm_num [ep12179]) ?_)
      (show bp12179^8 ≤ scalar12179.upperTail by norm_num [bp12179, scalar12179])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12179, bp12179, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12179:ℝ)) (by norm_num [em12179]) ?_)
      (show bm12179^8 ≤ scalar12179.lowerTail by norm_num [bm12179, scalar12179])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12179, bm12179, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12179 :
    agent12179.root+dsL+scalar12179.worldRadius < √(1/100/aL) ∧
    2*(agent12179.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12179, agent12179, scalar12179, tp12179, tm12179, ep12179, em12179, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12179, agent12179, scalar12179, tp12179, tm12179, ep12179, em12179, dsL]

noncomputable def master12179 : MasterCertificate 12179 world12179 agent12179 :=
  master scalar12179 dsL tp12179 tm12179 ep12179 em12179
    (by norm_num [dsL]) (by norm_num [tp12179]) (by norm_num [tm12179])
    (by norm_num [ep12179]) (by norm_num [em12179])
    positive12179 negative12179 tails12179.1 tails12179.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12179.1 tailGuards12179.2

theorem preserves12179 : master12179.toScalarCertificate = scalar12179 := rfl

noncomputable def tp12180 : ℝ := (18562073 / 78125000)
noncomputable def tm12180 : ℝ := (-((1229158919 / 2000000000)))
noncomputable def ep12180 : ℝ := (6835637184762923 / 12500000000000000000)
noncomputable def em12180 : ℝ := (52716900905199149 / 100000000000000000000)
noncomputable def bp12180 : ℝ := (43492546425980781969 / 100000000000000000000)
noncomputable def bm12180 : ℝ := (44815558617845503593 / 100000000000000000000)

theorem positive12180 :
    Eplus aL (agent12180.root+dsL) scalar12180.worldRadius world12180.frame
      agent12180.frame tp12180 ≤ -ep12180 := by
  apply positive_check (eT := (116233449767611828351 / 100000000000000000000)) (y := (9911497611342743119 / 25000000000000000000)) (u := (74327641631596469823 / 50000000000000000000))
  · norm_num [world12180, agent12180, scalar12180, tp12180, tm12180, ep12180, em12180, dsL]
  · norm_num [world12180, agent12180, scalar12180, tp12180, tm12180, ep12180, em12180, dsL]
  · norm_num [world12180, agent12180, scalar12180, tp12180, tm12180, ep12180, em12180, dsL]
  · norm_num [world12180, agent12180, scalar12180, tp12180, tm12180, ep12180, em12180, dsL]
  · norm_num [world12180, agent12180, scalar12180, tp12180, tm12180, ep12180, em12180, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12180, agent12180, tp12180, tm12180, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12180, agent12180, scalar12180, tp12180, tm12180, ep12180, em12180, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12180, agent12180, tp12180, tm12180, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12180, agent12180, scalar12180, tp12180, tm12180, ep12180, em12180, dsL]

theorem negative12180 :
    Eminus aL (agent12180.root+dsL) scalar12180.worldRadius world12180.frame
      agent12180.frame tm12180 ≤ -em12180 := by
  apply negative_check (lo := (16941416483544823779 / 25000000000000000000)) (hi := (67765665934179295117 / 100000000000000000000))
    (y := (-((73291617854393326267 / 100000000000000000000)))) (u := (48050570454324728081 / 100000000000000000000))
  · norm_num [world12180, agent12180, scalar12180, tp12180, tm12180, ep12180, em12180, dsL]
  · norm_num [world12180, agent12180, scalar12180, tp12180, tm12180, ep12180, em12180, dsL]
  · norm_num [world12180, agent12180, scalar12180, tp12180, tm12180, ep12180, em12180, dsL]
  · norm_num [world12180, agent12180, scalar12180, tp12180, tm12180, ep12180, em12180, dsL]
  · norm_num [world12180, agent12180, scalar12180, tp12180, tm12180, ep12180, em12180, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12180, agent12180, tp12180, tm12180, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12180, agent12180, tp12180, tm12180, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12180, agent12180, scalar12180, tp12180, tm12180, ep12180, em12180, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12180, agent12180, tp12180, tm12180, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12180, agent12180, scalar12180, tp12180, tm12180, ep12180, em12180, dsL]

theorem tails12180 :
    exp (-((12180:ℝ)*ep12180)) ≤ scalar12180.upperTail ∧
    exp (-((12180:ℝ)*em12180)) ≤ scalar12180.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12180:ℝ)) (by norm_num [ep12180]) ?_)
      (show bp12180^8 ≤ scalar12180.upperTail by norm_num [bp12180, scalar12180])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12180, bp12180, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12180:ℝ)) (by norm_num [em12180]) ?_)
      (show bm12180^8 ≤ scalar12180.lowerTail by norm_num [bm12180, scalar12180])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12180, bm12180, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12180 :
    agent12180.root+dsL+scalar12180.worldRadius < √(1/100/aL) ∧
    2*(agent12180.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12180, agent12180, scalar12180, tp12180, tm12180, ep12180, em12180, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12180, agent12180, scalar12180, tp12180, tm12180, ep12180, em12180, dsL]

noncomputable def master12180 : MasterCertificate 12180 world12180 agent12180 :=
  master scalar12180 dsL tp12180 tm12180 ep12180 em12180
    (by norm_num [dsL]) (by norm_num [tp12180]) (by norm_num [tm12180])
    (by norm_num [ep12180]) (by norm_num [em12180])
    positive12180 negative12180 tails12180.1 tails12180.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12180.1 tailGuards12180.2

theorem preserves12180 : master12180.toScalarCertificate = scalar12180 := rfl

noncomputable def tp12181 : ℝ := (475208477 / 2000000000)
noncomputable def tm12181 : ℝ := (-((768251483 / 1250000000)))
noncomputable def ep12181 : ℝ := (54687938406216283 / 100000000000000000000)
noncomputable def em12181 : ℝ := (26359683481957561 / 50000000000000000000)
noncomputable def bp12181 : ℝ := (43487692360962076827 / 100000000000000000000)
noncomputable def bm12181 : ℝ := (44810922914280248819 / 100000000000000000000)

theorem positive12181 :
    Eplus aL (agent12181.root+dsL) scalar12181.worldRadius world12181.frame
      agent12181.frame tp12181 ≤ -ep12181 := by
  apply positive_check (eT := (14529218433829301639 / 12500000000000000000)) (y := (39646609661154541791 / 100000000000000000000)) (u := (148656203763019952179 / 100000000000000000000))
  · norm_num [world12181, agent12181, scalar12181, tp12181, tm12181, ep12181, em12181, dsL]
  · norm_num [world12181, agent12181, scalar12181, tp12181, tm12181, ep12181, em12181, dsL]
  · norm_num [world12181, agent12181, scalar12181, tp12181, tm12181, ep12181, em12181, dsL]
  · norm_num [world12181, agent12181, scalar12181, tp12181, tm12181, ep12181, em12181, dsL]
  · norm_num [world12181, agent12181, scalar12181, tp12181, tm12181, ep12181, em12181, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12181, agent12181, tp12181, tm12181, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12181, agent12181, scalar12181, tp12181, tm12181, ep12181, em12181, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12181, agent12181, tp12181, tm12181, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12181, agent12181, scalar12181, tp12181, tm12181, ep12181, em12181, dsL]

theorem negative12181 :
    Eminus aL (agent12181.root+dsL) scalar12181.worldRadius world12181.frame
      agent12181.frame tm12181 ≤ -em12181 := by
  apply negative_check (lo := (33882680878494478229 / 50000000000000000000)) (hi := (67765361756988956459 / 100000000000000000000))
    (y := (-((18322804126733436159 / 25000000000000000000)))) (u := (48050763304455560287 / 100000000000000000000))
  · norm_num [world12181, agent12181, scalar12181, tp12181, tm12181, ep12181, em12181, dsL]
  · norm_num [world12181, agent12181, scalar12181, tp12181, tm12181, ep12181, em12181, dsL]
  · norm_num [world12181, agent12181, scalar12181, tp12181, tm12181, ep12181, em12181, dsL]
  · norm_num [world12181, agent12181, scalar12181, tp12181, tm12181, ep12181, em12181, dsL]
  · norm_num [world12181, agent12181, scalar12181, tp12181, tm12181, ep12181, em12181, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12181, agent12181, tp12181, tm12181, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12181, agent12181, tp12181, tm12181, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12181, agent12181, scalar12181, tp12181, tm12181, ep12181, em12181, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12181, agent12181, tp12181, tm12181, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12181, agent12181, scalar12181, tp12181, tm12181, ep12181, em12181, dsL]

theorem tails12181 :
    exp (-((12181:ℝ)*ep12181)) ≤ scalar12181.upperTail ∧
    exp (-((12181:ℝ)*em12181)) ≤ scalar12181.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12181:ℝ)) (by norm_num [ep12181]) ?_)
      (show bp12181^8 ≤ scalar12181.upperTail by norm_num [bp12181, scalar12181])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12181, bp12181, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12181:ℝ)) (by norm_num [em12181]) ?_)
      (show bm12181^8 ≤ scalar12181.lowerTail by norm_num [bm12181, scalar12181])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12181, bm12181, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12181 :
    agent12181.root+dsL+scalar12181.worldRadius < √(1/100/aL) ∧
    2*(agent12181.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12181, agent12181, scalar12181, tp12181, tm12181, ep12181, em12181, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12181, agent12181, scalar12181, tp12181, tm12181, ep12181, em12181, dsL]

noncomputable def master12181 : MasterCertificate 12181 world12181 agent12181 :=
  master scalar12181 dsL tp12181 tm12181 ep12181 em12181
    (by norm_num [dsL]) (by norm_num [tp12181]) (by norm_num [tm12181])
    (by norm_num [ep12181]) (by norm_num [em12181])
    positive12181 negative12181 tails12181.1 tails12181.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12181.1 tailGuards12181.2

theorem preserves12181 : master12181.toScalarCertificate = scalar12181 := rfl

noncomputable def tp12182 : ℝ := (475227887 / 2000000000)
noncomputable def tm12182 : ℝ := (-((6146229143 / 10000000000)))
noncomputable def ep12182 : ℝ := (27345388686828519 / 50000000000000000000)
noncomputable def em12182 : ℝ := (52721831219116021 / 100000000000000000000)
noncomputable def bp12182 : ℝ := (8696567965418125921 / 20000000000000000000)
noncomputable def bm12182 : ℝ := (4480628864450923153 / 10000000000000000000)

theorem positive12182 :
    Eplus aL (agent12182.root+dsL) scalar12182.worldRadius world12182.frame
      agent12182.frame tp12182 ≤ -ep12182 := by
  apply positive_check (eT := (11623404527692307819 / 10000000000000000000)) (y := (39647229697979468341 / 100000000000000000000)) (u := (74328562744541669153 / 50000000000000000000))
  · norm_num [world12182, agent12182, scalar12182, tp12182, tm12182, ep12182, em12182, dsL]
  · norm_num [world12182, agent12182, scalar12182, tp12182, tm12182, ep12182, em12182, dsL]
  · norm_num [world12182, agent12182, scalar12182, tp12182, tm12182, ep12182, em12182, dsL]
  · norm_num [world12182, agent12182, scalar12182, tp12182, tm12182, ep12182, em12182, dsL]
  · norm_num [world12182, agent12182, scalar12182, tp12182, tm12182, ep12182, em12182, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12182, agent12182, tp12182, tm12182, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12182, agent12182, scalar12182, tp12182, tm12182, ep12182, em12182, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12182, agent12182, tp12182, tm12182, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12182, agent12182, scalar12182, tp12182, tm12182, ep12182, em12182, dsL]

theorem negative12182 :
    Eminus aL (agent12182.root+dsL) scalar12182.worldRadius world12182.frame
      agent12182.frame tm12182 ≤ -em12182 := by
  apply negative_check (lo := (33882528738332046259 / 50000000000000000000)) (hi := (67765057476664092519 / 100000000000000000000))
    (y := (-((36645408222357467383 / 50000000000000000000)))) (u := (9610191107557983477 / 20000000000000000000))
  · norm_num [world12182, agent12182, scalar12182, tp12182, tm12182, ep12182, em12182, dsL]
  · norm_num [world12182, agent12182, scalar12182, tp12182, tm12182, ep12182, em12182, dsL]
  · norm_num [world12182, agent12182, scalar12182, tp12182, tm12182, ep12182, em12182, dsL]
  · norm_num [world12182, agent12182, scalar12182, tp12182, tm12182, ep12182, em12182, dsL]
  · norm_num [world12182, agent12182, scalar12182, tp12182, tm12182, ep12182, em12182, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12182, agent12182, tp12182, tm12182, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12182, agent12182, tp12182, tm12182, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12182, agent12182, scalar12182, tp12182, tm12182, ep12182, em12182, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12182, agent12182, tp12182, tm12182, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12182, agent12182, scalar12182, tp12182, tm12182, ep12182, em12182, dsL]

theorem tails12182 :
    exp (-((12182:ℝ)*ep12182)) ≤ scalar12182.upperTail ∧
    exp (-((12182:ℝ)*em12182)) ≤ scalar12182.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12182:ℝ)) (by norm_num [ep12182]) ?_)
      (show bp12182^8 ≤ scalar12182.upperTail by norm_num [bp12182, scalar12182])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12182, bp12182, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12182:ℝ)) (by norm_num [em12182]) ?_)
      (show bm12182^8 ≤ scalar12182.lowerTail by norm_num [bm12182, scalar12182])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12182, bm12182, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12182 :
    agent12182.root+dsL+scalar12182.worldRadius < √(1/100/aL) ∧
    2*(agent12182.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12182, agent12182, scalar12182, tp12182, tm12182, ep12182, em12182, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12182, agent12182, scalar12182, tp12182, tm12182, ep12182, em12182, dsL]

noncomputable def master12182 : MasterCertificate 12182 world12182 agent12182 :=
  master scalar12182 dsL tp12182 tm12182 ep12182 em12182
    (by norm_num [dsL]) (by norm_num [tp12182]) (by norm_num [tm12182])
    (by norm_num [ep12182]) (by norm_num [em12182])
    positive12182 negative12182 tails12182.1 tails12182.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12182.1 tailGuards12182.2

theorem preserves12182 : master12182.toScalarCertificate = scalar12182 := rfl

noncomputable def tp12183 : ℝ := (2376236347 / 10000000000)
noncomputable def tm12183 : ℝ := (-((6146446389 / 10000000000)))
noncomputable def ep12183 : ℝ := (54693615102764371 / 100000000000000000000)
noncomputable def em12183 : ℝ := (5272429428067971 / 10000000000000000000)
noncomputable def bp12183 : ℝ := (4347798834602284113 / 10000000000000000000)
noncomputable def bm12183 : ℝ := (1400051731012076663 / 3125000000000000000)

theorem positive12183 :
    Eplus aL (agent12183.root+dsL) scalar12183.worldRadius world12183.frame
      agent12183.frame tp12183 ≤ -ep12183 := by
  apply positive_check (eT := (116234342104749265647 / 100000000000000000000)) (y := (19823923958066452021 / 50000000000000000000)) (u := (29731608903452056819 / 20000000000000000000))
  · norm_num [world12183, agent12183, scalar12183, tp12183, tm12183, ep12183, em12183, dsL]
  · norm_num [world12183, agent12183, scalar12183, tp12183, tm12183, ep12183, em12183, dsL]
  · norm_num [world12183, agent12183, scalar12183, tp12183, tm12183, ep12183, em12183, dsL]
  · norm_num [world12183, agent12183, scalar12183, tp12183, tm12183, ep12183, em12183, dsL]
  · norm_num [world12183, agent12183, scalar12183, tp12183, tm12183, ep12183, em12183, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12183, agent12183, tp12183, tm12183, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12183, agent12183, scalar12183, tp12183, tm12183, ep12183, em12183, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12183, agent12183, tp12183, tm12183, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12183, agent12183, scalar12183, tp12183, tm12183, ep12183, em12183, dsL]

theorem negative12183 :
    Eminus aL (agent12183.root+dsL) scalar12183.worldRadius world12183.frame
      agent12183.frame tm12183 ≤ -em12183 := by
  apply negative_check (lo := (67764753277674274441 / 100000000000000000000)) (hi := (33882376638837137221 / 50000000000000000000))
    (y := (-((18322604313821650263 / 25000000000000000000)))) (u := (24025573676253744679 / 50000000000000000000))
  · norm_num [world12183, agent12183, scalar12183, tp12183, tm12183, ep12183, em12183, dsL]
  · norm_num [world12183, agent12183, scalar12183, tp12183, tm12183, ep12183, em12183, dsL]
  · norm_num [world12183, agent12183, scalar12183, tp12183, tm12183, ep12183, em12183, dsL]
  · norm_num [world12183, agent12183, scalar12183, tp12183, tm12183, ep12183, em12183, dsL]
  · norm_num [world12183, agent12183, scalar12183, tp12183, tm12183, ep12183, em12183, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12183, agent12183, tp12183, tm12183, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12183, agent12183, tp12183, tm12183, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12183, agent12183, scalar12183, tp12183, tm12183, ep12183, em12183, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12183, agent12183, tp12183, tm12183, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12183, agent12183, scalar12183, tp12183, tm12183, ep12183, em12183, dsL]

theorem tails12183 :
    exp (-((12183:ℝ)*ep12183)) ≤ scalar12183.upperTail ∧
    exp (-((12183:ℝ)*em12183)) ≤ scalar12183.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12183:ℝ)) (by norm_num [ep12183]) ?_)
      (show bp12183^8 ≤ scalar12183.upperTail by norm_num [bp12183, scalar12183])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12183, bp12183, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12183:ℝ)) (by norm_num [em12183]) ?_)
      (show bm12183^8 ≤ scalar12183.lowerTail by norm_num [bm12183, scalar12183])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12183, bm12183, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12183 :
    agent12183.root+dsL+scalar12183.worldRadius < √(1/100/aL) ∧
    2*(agent12183.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12183, agent12183, scalar12183, tp12183, tm12183, ep12183, em12183, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12183, agent12183, scalar12183, tp12183, tm12183, ep12183, em12183, dsL]

noncomputable def master12183 : MasterCertificate 12183 world12183 agent12183 :=
  master scalar12183 dsL tp12183 tm12183 ep12183 em12183
    (by norm_num [dsL]) (by norm_num [tp12183]) (by norm_num [tm12183])
    (by norm_num [ep12183]) (by norm_num [em12183])
    positive12183 negative12183 tails12183.1 tails12183.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12183.1 tailGuards12183.2

theorem preserves12183 : master12183.toScalarCertificate = scalar12183 := rfl

end BstLean.Part281
