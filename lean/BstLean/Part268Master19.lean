import BstLean.Part261Checker
import BstLean.Part268Scalar19
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12825 : ℝ := (1163884543 / 5000000000)
noncomputable def tm12825 : ℝ := (-((760979293 / 1250000000)))
noncomputable def ep12825 : ℝ := (51760020915370529 / 100000000000000000000)
noncomputable def em12825 : ℝ := (25200376612755173 / 50000000000000000000)
noncomputable def bp12825 : ℝ := (27259135740155787 / 62500000000000000)
noncomputable def bm12825 : ℝ := (44575443393850059499 / 100000000000000000000)

theorem positive12825 :
    Eplus aL (agent12825.root+dsL) scalar12825.worldRadius world12825.frame
      agent12825.frame tp12825 ≤ -ep12825 := by
  apply positive_check (eT := (23126171041237255327 / 20000000000000000000)) (y := (37949055335983081217 / 100000000000000000000)) (u := (36538495579715116341 / 25000000000000000000))
  · norm_num [world12825, agent12825, scalar12825, tp12825, tm12825, ep12825, em12825, dsL]
  · norm_num [world12825, agent12825, scalar12825, tp12825, tm12825, ep12825, em12825, dsL]
  · norm_num [world12825, agent12825, scalar12825, tp12825, tm12825, ep12825, em12825, dsL]
  · norm_num [world12825, agent12825, scalar12825, tp12825, tm12825, ep12825, em12825, dsL]
  · norm_num [world12825, agent12825, scalar12825, tp12825, tm12825, ep12825, em12825, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12825, agent12825, tp12825, tm12825, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12825, agent12825, scalar12825, tp12825, tm12825, ep12825, em12825, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12825, agent12825, tp12825, tm12825, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12825, agent12825, scalar12825, tp12825, tm12825, ep12825, em12825, dsL]

theorem negative12825 :
    Eminus aL (agent12825.root+dsL) scalar12825.worldRadius world12825.frame
      agent12825.frame tm12825 ≤ -em12825 := by
  apply negative_check (lo := (34198945899949319187 / 50000000000000000000)) (hi := (547183134399189107 / 800000000000000000))
    (y := (-((35835406584951016399 / 50000000000000000000)))) (u := (48835722049840495479 / 100000000000000000000))
  · norm_num [world12825, agent12825, scalar12825, tp12825, tm12825, ep12825, em12825, dsL]
  · norm_num [world12825, agent12825, scalar12825, tp12825, tm12825, ep12825, em12825, dsL]
  · norm_num [world12825, agent12825, scalar12825, tp12825, tm12825, ep12825, em12825, dsL]
  · norm_num [world12825, agent12825, scalar12825, tp12825, tm12825, ep12825, em12825, dsL]
  · norm_num [world12825, agent12825, scalar12825, tp12825, tm12825, ep12825, em12825, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12825, agent12825, tp12825, tm12825, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12825, agent12825, tp12825, tm12825, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12825, agent12825, scalar12825, tp12825, tm12825, ep12825, em12825, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12825, agent12825, tp12825, tm12825, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12825, agent12825, scalar12825, tp12825, tm12825, ep12825, em12825, dsL]

theorem tails12825 :
    exp (-((12825:ℝ)*ep12825)) ≤ scalar12825.upperTail ∧
    exp (-((12825:ℝ)*em12825)) ≤ scalar12825.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12825:ℝ)) (by norm_num [ep12825]) ?_)
      (show bp12825^8 ≤ scalar12825.upperTail by norm_num [bp12825, scalar12825])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12825, bp12825, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12825:ℝ)) (by norm_num [em12825]) ?_)
      (show bm12825^8 ≤ scalar12825.lowerTail by norm_num [bm12825, scalar12825])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12825, bm12825, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12825 :
    agent12825.root+dsL+scalar12825.worldRadius < √(1/100/aL) ∧
    2*(agent12825.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12825, agent12825, scalar12825, tp12825, tm12825, ep12825, em12825, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12825, agent12825, scalar12825, tp12825, tm12825, ep12825, em12825, dsL]

noncomputable def master12825 : MasterCertificate 12825 world12825 agent12825 :=
  master scalar12825 dsL tp12825 tm12825 ep12825 em12825
    (by norm_num [dsL]) (by norm_num [tp12825]) (by norm_num [tm12825])
    (by norm_num [ep12825]) (by norm_num [em12825])
    positive12825 negative12825 tails12825.1 tails12825.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12825.1 tailGuards12825.2

theorem preserves12825 : master12825.toScalarCertificate = scalar12825 := rfl

noncomputable def tp12826 : ℝ := (290981249 / 1250000000)
noncomputable def tm12826 : ℝ := (-((608800703 / 1000000000)))
noncomputable def ep12826 : ℝ := (25881245543668669 / 50000000000000000000)
noncomputable def em12826 : ℝ := (50402863885865221 / 100000000000000000000)
noncomputable def bp12826 : ℝ := (43610068283530881277 / 100000000000000000000)
noncomputable def bm12826 : ℝ := (5571390864037279163 / 12500000000000000000)

theorem positive12826 :
    Eplus aL (agent12826.root+dsL) scalar12826.worldRadius world12826.frame
      agent12826.frame tp12826 ≤ -ep12826 := by
  apply positive_check (eT := (4625242946193348263 / 4000000000000000000)) (y := (37949804266304406041 / 100000000000000000000)) (u := (36538769228612187261 / 25000000000000000000))
  · norm_num [world12826, agent12826, scalar12826, tp12826, tm12826, ep12826, em12826, dsL]
  · norm_num [world12826, agent12826, scalar12826, tp12826, tm12826, ep12826, em12826, dsL]
  · norm_num [world12826, agent12826, scalar12826, tp12826, tm12826, ep12826, em12826, dsL]
  · norm_num [world12826, agent12826, scalar12826, tp12826, tm12826, ep12826, em12826, dsL]
  · norm_num [world12826, agent12826, scalar12826, tp12826, tm12826, ep12826, em12826, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12826, agent12826, tp12826, tm12826, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12826, agent12826, scalar12826, tp12826, tm12826, ep12826, em12826, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12826, agent12826, tp12826, tm12826, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12826, agent12826, scalar12826, tp12826, tm12826, ep12826, em12826, dsL]

theorem negative12826 :
    Eminus aL (agent12826.root+dsL) scalar12826.worldRadius world12826.frame
      agent12826.frame tm12826 ≤ -em12826 := by
  apply negative_check (lo := (34198859946797544353 / 50000000000000000000)) (hi := (68397719893595088707 / 100000000000000000000))
    (y := (-((35835418678319649951 / 50000000000000000000)))) (u := (48835710238074139231 / 100000000000000000000))
  · norm_num [world12826, agent12826, scalar12826, tp12826, tm12826, ep12826, em12826, dsL]
  · norm_num [world12826, agent12826, scalar12826, tp12826, tm12826, ep12826, em12826, dsL]
  · norm_num [world12826, agent12826, scalar12826, tp12826, tm12826, ep12826, em12826, dsL]
  · norm_num [world12826, agent12826, scalar12826, tp12826, tm12826, ep12826, em12826, dsL]
  · norm_num [world12826, agent12826, scalar12826, tp12826, tm12826, ep12826, em12826, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12826, agent12826, tp12826, tm12826, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12826, agent12826, tp12826, tm12826, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12826, agent12826, scalar12826, tp12826, tm12826, ep12826, em12826, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12826, agent12826, tp12826, tm12826, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12826, agent12826, scalar12826, tp12826, tm12826, ep12826, em12826, dsL]

theorem tails12826 :
    exp (-((12826:ℝ)*ep12826)) ≤ scalar12826.upperTail ∧
    exp (-((12826:ℝ)*em12826)) ≤ scalar12826.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12826:ℝ)) (by norm_num [ep12826]) ?_)
      (show bp12826^8 ≤ scalar12826.upperTail by norm_num [bp12826, scalar12826])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12826, bp12826, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12826:ℝ)) (by norm_num [em12826]) ?_)
      (show bm12826^8 ≤ scalar12826.lowerTail by norm_num [bm12826, scalar12826])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12826, bm12826, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12826 :
    agent12826.root+dsL+scalar12826.worldRadius < √(1/100/aL) ∧
    2*(agent12826.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12826, agent12826, scalar12826, tp12826, tm12826, ep12826, em12826, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12826, agent12826, scalar12826, tp12826, tm12826, ep12826, em12826, dsL]

noncomputable def master12826 : MasterCertificate 12826 world12826 agent12826 :=
  master scalar12826 dsL tp12826 tm12826 ep12826 em12826
    (by norm_num [dsL]) (by norm_num [tp12826]) (by norm_num [tm12826])
    (by norm_num [ep12826]) (by norm_num [em12826])
    positive12826 negative12826 tails12826.1 tails12826.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12826.1 tailGuards12826.2

theorem preserves12826 : master12826.toScalarCertificate = scalar12826 := rfl

noncomputable def tp12827 : ℝ := (581982711 / 2500000000)
noncomputable def tm12827 : ℝ := (-((6088179619 / 10000000000)))
noncomputable def ep12827 : ℝ := (12941239749584987 / 25000000000000000000)
noncomputable def em12827 : ℝ := (25202486221984023 / 50000000000000000000)
noncomputable def bp12827 : ℝ := (43605521168744942853 / 100000000000000000000)
noncomputable def bm12827 : ℝ := (5570851514472997043 / 12500000000000000000)

theorem positive12827 :
    Eplus aL (agent12827.root+dsL) scalar12827.worldRadius world12827.frame
      agent12827.frame tp12827 ≤ -ep12827 := by
  apply positive_check (eT := (57815645873409723791 / 50000000000000000000)) (y := (1897527639905782333 / 5000000000000000000)) (u := (146156170935787740651 / 100000000000000000000))
  · norm_num [world12827, agent12827, scalar12827, tp12827, tm12827, ep12827, em12827, dsL]
  · norm_num [world12827, agent12827, scalar12827, tp12827, tm12827, ep12827, em12827, dsL]
  · norm_num [world12827, agent12827, scalar12827, tp12827, tm12827, ep12827, em12827, dsL]
  · norm_num [world12827, agent12827, scalar12827, tp12827, tm12827, ep12827, em12827, dsL]
  · norm_num [world12827, agent12827, scalar12827, tp12827, tm12827, ep12827, em12827, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12827, agent12827, tp12827, tm12827, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12827, agent12827, scalar12827, tp12827, tm12827, ep12827, em12827, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12827, agent12827, tp12827, tm12827, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12827, agent12827, scalar12827, tp12827, tm12827, ep12827, em12827, dsL]

theorem negative12827 :
    Eminus aL (agent12827.root+dsL) scalar12827.worldRadius world12827.frame
      agent12827.frame tm12827 ≤ -em12827 := by
  apply negative_check (lo := (68397548344168666147 / 100000000000000000000)) (hi := (17099387086042166537 / 25000000000000000000))
    (y := (-((14334172231532058791 / 20000000000000000000)))) (u := (12208924653669469029 / 25000000000000000000))
  · norm_num [world12827, agent12827, scalar12827, tp12827, tm12827, ep12827, em12827, dsL]
  · norm_num [world12827, agent12827, scalar12827, tp12827, tm12827, ep12827, em12827, dsL]
  · norm_num [world12827, agent12827, scalar12827, tp12827, tm12827, ep12827, em12827, dsL]
  · norm_num [world12827, agent12827, scalar12827, tp12827, tm12827, ep12827, em12827, dsL]
  · norm_num [world12827, agent12827, scalar12827, tp12827, tm12827, ep12827, em12827, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12827, agent12827, tp12827, tm12827, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12827, agent12827, tp12827, tm12827, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12827, agent12827, scalar12827, tp12827, tm12827, ep12827, em12827, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12827, agent12827, tp12827, tm12827, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12827, agent12827, scalar12827, tp12827, tm12827, ep12827, em12827, dsL]

theorem tails12827 :
    exp (-((12827:ℝ)*ep12827)) ≤ scalar12827.upperTail ∧
    exp (-((12827:ℝ)*em12827)) ≤ scalar12827.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12827:ℝ)) (by norm_num [ep12827]) ?_)
      (show bp12827^8 ≤ scalar12827.upperTail by norm_num [bp12827, scalar12827])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12827, bp12827, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12827:ℝ)) (by norm_num [em12827]) ?_)
      (show bm12827^8 ≤ scalar12827.lowerTail by norm_num [bm12827, scalar12827])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12827, bm12827, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12827 :
    agent12827.root+dsL+scalar12827.worldRadius < √(1/100/aL) ∧
    2*(agent12827.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12827, agent12827, scalar12827, tp12827, tm12827, ep12827, em12827, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12827, agent12827, scalar12827, tp12827, tm12827, ep12827, em12827, dsL]

noncomputable def master12827 : MasterCertificate 12827 world12827 agent12827 :=
  master scalar12827 dsL tp12827 tm12827 ep12827 em12827
    (by norm_num [dsL]) (by norm_num [tp12827]) (by norm_num [tm12827])
    (by norm_num [ep12827]) (by norm_num [em12827])
    positive12827 negative12827 tails12827.1 tails12827.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12827.1 tailGuards12827.2

theorem preserves12827 : master12827.toScalarCertificate = scalar12827 := rfl

noncomputable def tp12828 : ℝ := (1164005827 / 5000000000)
noncomputable def tm12828 : ℝ := (-((60883521 / 100000000)))
noncomputable def ep12828 : ℝ := (10353485215002337 / 20000000000000000000)
noncomputable def em12828 : ℝ := (50407080220324821 / 100000000000000000000)
noncomputable def bp12828 : ℝ := (43600974842382635851 / 100000000000000000000)
noncomputable def bm12828 : ℝ := (11140624515167454317 / 25000000000000000000)

theorem positive12828 :
    Eplus aL (agent12828.root+dsL) scalar12828.worldRadius world12828.frame
      agent12828.frame tp12828 ≤ -ep12828 := by
  apply positive_check (eT := (57815754784383531387 / 50000000000000000000)) (y := (7590260198834383543 / 20000000000000000000)) (u := (5846290578983423239 / 4000000000000000000))
  · norm_num [world12828, agent12828, scalar12828, tp12828, tm12828, ep12828, em12828, dsL]
  · norm_num [world12828, agent12828, scalar12828, tp12828, tm12828, ep12828, em12828, dsL]
  · norm_num [world12828, agent12828, scalar12828, tp12828, tm12828, ep12828, em12828, dsL]
  · norm_num [world12828, agent12828, scalar12828, tp12828, tm12828, ep12828, em12828, dsL]
  · norm_num [world12828, agent12828, scalar12828, tp12828, tm12828, ep12828, em12828, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12828, agent12828, tp12828, tm12828, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12828, agent12828, scalar12828, tp12828, tm12828, ep12828, em12828, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12828, agent12828, tp12828, tm12828, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12828, agent12828, scalar12828, tp12828, tm12828, ep12828, em12828, dsL]

theorem negative12828 :
    Eminus aL (agent12828.root+dsL) scalar12828.worldRadius world12828.frame
      agent12828.frame tm12828 ≤ -em12828 := by
  apply negative_check (lo := (68397377198478815079 / 100000000000000000000)) (hi := (1709934429961970377 / 2500000000000000000))
    (y := (-((17917721212585311623 / 25000000000000000000)))) (u := (48835687044192983077 / 100000000000000000000))
  · norm_num [world12828, agent12828, scalar12828, tp12828, tm12828, ep12828, em12828, dsL]
  · norm_num [world12828, agent12828, scalar12828, tp12828, tm12828, ep12828, em12828, dsL]
  · norm_num [world12828, agent12828, scalar12828, tp12828, tm12828, ep12828, em12828, dsL]
  · norm_num [world12828, agent12828, scalar12828, tp12828, tm12828, ep12828, em12828, dsL]
  · norm_num [world12828, agent12828, scalar12828, tp12828, tm12828, ep12828, em12828, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12828, agent12828, tp12828, tm12828, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12828, agent12828, tp12828, tm12828, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12828, agent12828, scalar12828, tp12828, tm12828, ep12828, em12828, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12828, agent12828, tp12828, tm12828, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12828, agent12828, scalar12828, tp12828, tm12828, ep12828, em12828, dsL]

theorem tails12828 :
    exp (-((12828:ℝ)*ep12828)) ≤ scalar12828.upperTail ∧
    exp (-((12828:ℝ)*em12828)) ≤ scalar12828.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12828:ℝ)) (by norm_num [ep12828]) ?_)
      (show bp12828^8 ≤ scalar12828.upperTail by norm_num [bp12828, scalar12828])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12828, bp12828, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12828:ℝ)) (by norm_num [em12828]) ?_)
      (show bm12828^8 ≤ scalar12828.lowerTail by norm_num [bm12828, scalar12828])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12828, bm12828, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12828 :
    agent12828.root+dsL+scalar12828.worldRadius < √(1/100/aL) ∧
    2*(agent12828.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12828, agent12828, scalar12828, tp12828, tm12828, ep12828, em12828, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12828, agent12828, scalar12828, tp12828, tm12828, ep12828, em12828, dsL]

noncomputable def master12828 : MasterCertificate 12828 world12828 agent12828 :=
  master scalar12828 dsL tp12828 tm12828 ep12828 em12828
    (by norm_num [dsL]) (by norm_num [tp12828]) (by norm_num [tm12828])
    (by norm_num [ep12828]) (by norm_num [em12828])
    positive12828 negative12828 tails12828.1 tails12828.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12828.1 tailGuards12828.2

theorem preserves12828 : master12828.toScalarCertificate = scalar12828 := rfl

noncomputable def tp12829 : ℝ := (465618479 / 2000000000)
noncomputable def tm12829 : ℝ := (-((1217704903 / 2000000000)))
noncomputable def ep12829 : ℝ := (51769891672209441 / 100000000000000000000)
noncomputable def em12829 : ℝ := (5040918665769919 / 10000000000000000000)
noncomputable def bp12829 : ℝ := (21798214877733579913 / 50000000000000000000)
noncomputable def bm12829 : ℝ := (44558185145123059447 / 100000000000000000000)

theorem positive12829 :
    Eplus aL (agent12829.root+dsL) scalar12829.worldRadius world12829.frame
      agent12829.frame tp12829 ≤ -ep12829 := by
  apply positive_check (eT := (11563172692592844093 / 10000000000000000000)) (y := (37952048277725998651 / 100000000000000000000)) (u := (73079178343933527081 / 50000000000000000000))
  · norm_num [world12829, agent12829, scalar12829, tp12829, tm12829, ep12829, em12829, dsL]
  · norm_num [world12829, agent12829, scalar12829, tp12829, tm12829, ep12829, em12829, dsL]
  · norm_num [world12829, agent12829, scalar12829, tp12829, tm12829, ep12829, em12829, dsL]
  · norm_num [world12829, agent12829, scalar12829, tp12829, tm12829, ep12829, em12829, dsL]
  · norm_num [world12829, agent12829, scalar12829, tp12829, tm12829, ep12829, em12829, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12829, agent12829, tp12829, tm12829, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12829, agent12829, scalar12829, tp12829, tm12829, ep12829, em12829, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12829, agent12829, tp12829, tm12829, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12829, agent12829, scalar12829, tp12829, tm12829, ep12829, em12829, dsL]

theorem negative12829 :
    Eminus aL (agent12829.root+dsL) scalar12829.worldRadius world12829.frame
      agent12829.frame tm12829 ≤ -em12829 := by
  apply negative_check (lo := (68397206277269881619 / 100000000000000000000)) (hi := (3419860313863494081 / 5000000000000000000))
    (y := (-((35835454211378668817 / 50000000000000000000)))) (u := (976713510648859777 / 2000000000000000000))
  · norm_num [world12829, agent12829, scalar12829, tp12829, tm12829, ep12829, em12829, dsL]
  · norm_num [world12829, agent12829, scalar12829, tp12829, tm12829, ep12829, em12829, dsL]
  · norm_num [world12829, agent12829, scalar12829, tp12829, tm12829, ep12829, em12829, dsL]
  · norm_num [world12829, agent12829, scalar12829, tp12829, tm12829, ep12829, em12829, dsL]
  · norm_num [world12829, agent12829, scalar12829, tp12829, tm12829, ep12829, em12829, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12829, agent12829, tp12829, tm12829, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12829, agent12829, tp12829, tm12829, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12829, agent12829, scalar12829, tp12829, tm12829, ep12829, em12829, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12829, agent12829, tp12829, tm12829, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12829, agent12829, scalar12829, tp12829, tm12829, ep12829, em12829, dsL]

theorem tails12829 :
    exp (-((12829:ℝ)*ep12829)) ≤ scalar12829.upperTail ∧
    exp (-((12829:ℝ)*em12829)) ≤ scalar12829.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12829:ℝ)) (by norm_num [ep12829]) ?_)
      (show bp12829^8 ≤ scalar12829.upperTail by norm_num [bp12829, scalar12829])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12829, bp12829, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12829:ℝ)) (by norm_num [em12829]) ?_)
      (show bm12829^8 ≤ scalar12829.lowerTail by norm_num [bm12829, scalar12829])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12829, bm12829, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12829 :
    agent12829.root+dsL+scalar12829.worldRadius < √(1/100/aL) ∧
    2*(agent12829.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12829, agent12829, scalar12829, tp12829, tm12829, ep12829, em12829, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12829, agent12829, scalar12829, tp12829, tm12829, ep12829, em12829, dsL]

noncomputable def master12829 : MasterCertificate 12829 world12829 agent12829 :=
  master scalar12829 dsL tp12829 tm12829 ep12829 em12829
    (by norm_num [dsL]) (by norm_num [tp12829]) (by norm_num [tm12829])
    (by norm_num [ep12829]) (by norm_num [em12829])
    positive12829 negative12829 tails12829.1 tails12829.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12829.1 tailGuards12829.2

theorem preserves12829 : master12829.toScalarCertificate = scalar12829 := rfl

noncomputable def tp12830 : ℝ := (2328246421 / 10000000000)
noncomputable def tm12830 : ℝ := (-((3044459247 / 5000000000)))
noncomputable def ep12830 : ℝ := (51773751472963093 / 100000000000000000000)
noncomputable def em12830 : ℝ := (3150800816628749 / 6250000000000000000)
noncomputable def bp12830 : ℝ := (43590910190067974669 / 100000000000000000000)
noncomputable def bm12830 : ℝ := (44552786356591150607 / 100000000000000000000)

theorem positive12830 :
    Eplus aL (agent12830.root+dsL) scalar12830.worldRadius world12830.frame
      agent12830.frame tp12830 ≤ -ep12830 := by
  apply positive_check (eT := (115632472969437710933 / 100000000000000000000)) (y := (37952075567661209597 / 100000000000000000000)) (u := (18269799571799167771 / 12500000000000000000))
  · norm_num [world12830, agent12830, scalar12830, tp12830, tm12830, ep12830, em12830, dsL]
  · norm_num [world12830, agent12830, scalar12830, tp12830, tm12830, ep12830, em12830, dsL]
  · norm_num [world12830, agent12830, scalar12830, tp12830, tm12830, ep12830, em12830, dsL]
  · norm_num [world12830, agent12830, scalar12830, tp12830, tm12830, ep12830, em12830, dsL]
  · norm_num [world12830, agent12830, scalar12830, tp12830, tm12830, ep12830, em12830, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12830, agent12830, tp12830, tm12830, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12830, agent12830, scalar12830, tp12830, tm12830, ep12830, em12830, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12830, agent12830, tp12830, tm12830, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12830, agent12830, scalar12830, tp12830, tm12830, ep12830, em12830, dsL]

theorem negative12830 :
    Eminus aL (agent12830.root+dsL) scalar12830.worldRadius world12830.frame
      agent12830.frame tm12830 ≤ -em12830 := by
  apply negative_check (lo := (17099022477464587827 / 25000000000000000000)) (hi := (68396089909858351309 / 100000000000000000000))
    (y := (-((2239657533008173293 / 3125000000000000000)))) (u := (6104573435250071157 / 12500000000000000000))
  · norm_num [world12830, agent12830, scalar12830, tp12830, tm12830, ep12830, em12830, dsL]
  · norm_num [world12830, agent12830, scalar12830, tp12830, tm12830, ep12830, em12830, dsL]
  · norm_num [world12830, agent12830, scalar12830, tp12830, tm12830, ep12830, em12830, dsL]
  · norm_num [world12830, agent12830, scalar12830, tp12830, tm12830, ep12830, em12830, dsL]
  · norm_num [world12830, agent12830, scalar12830, tp12830, tm12830, ep12830, em12830, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12830, agent12830, tp12830, tm12830, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12830, agent12830, tp12830, tm12830, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12830, agent12830, scalar12830, tp12830, tm12830, ep12830, em12830, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12830, agent12830, tp12830, tm12830, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12830, agent12830, scalar12830, tp12830, tm12830, ep12830, em12830, dsL]

theorem tails12830 :
    exp (-((12830:ℝ)*ep12830)) ≤ scalar12830.upperTail ∧
    exp (-((12830:ℝ)*em12830)) ≤ scalar12830.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12830:ℝ)) (by norm_num [ep12830]) ?_)
      (show bp12830^8 ≤ scalar12830.upperTail by norm_num [bp12830, scalar12830])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12830, bp12830, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12830:ℝ)) (by norm_num [em12830]) ?_)
      (show bm12830^8 ≤ scalar12830.lowerTail by norm_num [bm12830, scalar12830])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12830, bm12830, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12830 :
    agent12830.root+dsL+scalar12830.worldRadius < √(1/100/aL) ∧
    2*(agent12830.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12830, agent12830, scalar12830, tp12830, tm12830, ep12830, em12830, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12830, agent12830, scalar12830, tp12830, tm12830, ep12830, em12830, dsL]

noncomputable def master12830 : MasterCertificate 12830 world12830 agent12830 :=
  master scalar12830 dsL tp12830 tm12830 ep12830 em12830
    (by norm_num [dsL]) (by norm_num [tp12830]) (by norm_num [tm12830])
    (by norm_num [ep12830]) (by norm_num [em12830])
    positive12830 negative12830 tails12830.1 tails12830.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12830.1 tailGuards12830.2

theorem preserves12830 : master12830.toScalarCertificate = scalar12830 := rfl

noncomputable def tp12831 : ℝ := (2328327419 / 10000000000)
noncomputable def tm12831 : ℝ := (-((3044545831 / 5000000000)))
noncomputable def ep12831 : ℝ := (51776219740263919 / 100000000000000000000)
noncomputable def em12831 : ℝ := (25207461427139533 / 50000000000000000000)
noncomputable def bp12831 : ℝ := (10896590918109078023 / 25000000000000000000)
noncomputable def bm12831 : ℝ := (8909694286591871203 / 20000000000000000000)

theorem positive12831 :
    Eplus aL (agent12831.root+dsL) scalar12831.worldRadius world12831.frame
      agent12831.frame tp12831 ≤ -ep12831 := by
  apply positive_check (eT := (115632692235864319291 / 100000000000000000000)) (y := (7590564047049548351 / 20000000000000000000)) (u := (146159484972650096289 / 100000000000000000000))
  · norm_num [world12831, agent12831, scalar12831, tp12831, tm12831, ep12831, em12831, dsL]
  · norm_num [world12831, agent12831, scalar12831, tp12831, tm12831, ep12831, em12831, dsL]
  · norm_num [world12831, agent12831, scalar12831, tp12831, tm12831, ep12831, em12831, dsL]
  · norm_num [world12831, agent12831, scalar12831, tp12831, tm12831, ep12831, em12831, dsL]
  · norm_num [world12831, agent12831, scalar12831, tp12831, tm12831, ep12831, em12831, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12831, agent12831, tp12831, tm12831, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12831, agent12831, scalar12831, tp12831, tm12831, ep12831, em12831, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12831, agent12831, tp12831, tm12831, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12831, agent12831, scalar12831, tp12831, tm12831, ep12831, em12831, dsL]

theorem negative12831 :
    Eminus aL (agent12831.root+dsL) scalar12831.worldRadius world12831.frame
      agent12831.frame tm12831 ≤ -em12831 := by
  apply negative_check (lo := (68395915684524398527 / 100000000000000000000)) (hi := (1068686182570693727 / 1562500000000000000))
    (y := (-((4479316069927055513 / 6250000000000000000)))) (u := (24418289818794746781 / 50000000000000000000))
  · norm_num [world12831, agent12831, scalar12831, tp12831, tm12831, ep12831, em12831, dsL]
  · norm_num [world12831, agent12831, scalar12831, tp12831, tm12831, ep12831, em12831, dsL]
  · norm_num [world12831, agent12831, scalar12831, tp12831, tm12831, ep12831, em12831, dsL]
  · norm_num [world12831, agent12831, scalar12831, tp12831, tm12831, ep12831, em12831, dsL]
  · norm_num [world12831, agent12831, scalar12831, tp12831, tm12831, ep12831, em12831, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12831, agent12831, tp12831, tm12831, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12831, agent12831, tp12831, tm12831, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12831, agent12831, scalar12831, tp12831, tm12831, ep12831, em12831, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12831, agent12831, tp12831, tm12831, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12831, agent12831, scalar12831, tp12831, tm12831, ep12831, em12831, dsL]

theorem tails12831 :
    exp (-((12831:ℝ)*ep12831)) ≤ scalar12831.upperTail ∧
    exp (-((12831:ℝ)*em12831)) ≤ scalar12831.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12831:ℝ)) (by norm_num [ep12831]) ?_)
      (show bp12831^8 ≤ scalar12831.upperTail by norm_num [bp12831, scalar12831])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12831, bp12831, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12831:ℝ)) (by norm_num [em12831]) ?_)
      (show bm12831^8 ≤ scalar12831.lowerTail by norm_num [bm12831, scalar12831])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12831, bm12831, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12831 :
    agent12831.root+dsL+scalar12831.worldRadius < √(1/100/aL) ∧
    2*(agent12831.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12831, agent12831, scalar12831, tp12831, tm12831, ep12831, em12831, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12831, agent12831, scalar12831, tp12831, tm12831, ep12831, em12831, dsL]

noncomputable def master12831 : MasterCertificate 12831 world12831 agent12831 :=
  master scalar12831 dsL tp12831 tm12831 ep12831 em12831
    (by norm_num [dsL]) (by norm_num [tp12831]) (by norm_num [tm12831])
    (by norm_num [ep12831]) (by norm_num [em12831])
    positive12831 negative12831 tails12831.1 tails12831.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12831.1 tailGuards12831.2

theorem preserves12831 : master12831.toScalarCertificate = scalar12831 := rfl

noncomputable def tp12832 : ℝ := (145525523 / 625000000)
noncomputable def tm12832 : ℝ := (-((6089264737 / 10000000000)))
noncomputable def ep12832 : ℝ := (12944672055306397 / 25000000000000000000)
noncomputable def em12832 : ℝ := (25208516478051417 / 50000000000000000000)
noncomputable def bp12832 : ℝ := (43581817210715895067 / 100000000000000000000)
noncomputable def bm12832 : ℝ := (44544156468212872507 / 100000000000000000000)

theorem positive12832 :
    Eplus aL (agent12832.root+dsL) scalar12832.worldRadius world12832.frame
      agent12832.frame tp12832 ≤ -ep12832 := by
  apply positive_check (eT := (11563291118168593129 / 10000000000000000000)) (y := (4744195415484131867 / 12500000000000000000)) (u := (36540142767798269187 / 25000000000000000000))
  · norm_num [world12832, agent12832, scalar12832, tp12832, tm12832, ep12832, em12832, dsL]
  · norm_num [world12832, agent12832, scalar12832, tp12832, tm12832, ep12832, em12832, dsL]
  · norm_num [world12832, agent12832, scalar12832, tp12832, tm12832, ep12832, em12832, dsL]
  · norm_num [world12832, agent12832, scalar12832, tp12832, tm12832, ep12832, em12832, dsL]
  · norm_num [world12832, agent12832, scalar12832, tp12832, tm12832, ep12832, em12832, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12832, agent12832, tp12832, tm12832, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12832, agent12832, scalar12832, tp12832, tm12832, ep12832, em12832, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12832, agent12832, tp12832, tm12832, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12832, agent12832, scalar12832, tp12832, tm12832, ep12832, em12832, dsL]

theorem negative12832 :
    Eminus aL (agent12832.root+dsL) scalar12832.worldRadius world12832.frame
      agent12832.frame tm12832 ≤ -em12832 := by
  apply negative_check (lo := (68395741799089650469 / 100000000000000000000)) (hi := (6839574179908965047 / 10000000000000000000))
    (y := (-((71669071102380232953 / 100000000000000000000)))) (u := (2441828640425186793 / 5000000000000000000))
  · norm_num [world12832, agent12832, scalar12832, tp12832, tm12832, ep12832, em12832, dsL]
  · norm_num [world12832, agent12832, scalar12832, tp12832, tm12832, ep12832, em12832, dsL]
  · norm_num [world12832, agent12832, scalar12832, tp12832, tm12832, ep12832, em12832, dsL]
  · norm_num [world12832, agent12832, scalar12832, tp12832, tm12832, ep12832, em12832, dsL]
  · norm_num [world12832, agent12832, scalar12832, tp12832, tm12832, ep12832, em12832, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12832, agent12832, tp12832, tm12832, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12832, agent12832, tp12832, tm12832, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12832, agent12832, scalar12832, tp12832, tm12832, ep12832, em12832, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12832, agent12832, tp12832, tm12832, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12832, agent12832, scalar12832, tp12832, tm12832, ep12832, em12832, dsL]

theorem tails12832 :
    exp (-((12832:ℝ)*ep12832)) ≤ scalar12832.upperTail ∧
    exp (-((12832:ℝ)*em12832)) ≤ scalar12832.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12832:ℝ)) (by norm_num [ep12832]) ?_)
      (show bp12832^8 ≤ scalar12832.upperTail by norm_num [bp12832, scalar12832])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12832, bp12832, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12832:ℝ)) (by norm_num [em12832]) ?_)
      (show bm12832^8 ≤ scalar12832.lowerTail by norm_num [bm12832, scalar12832])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12832, bm12832, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12832 :
    agent12832.root+dsL+scalar12832.worldRadius < √(1/100/aL) ∧
    2*(agent12832.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12832, agent12832, scalar12832, tp12832, tm12832, ep12832, em12832, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12832, agent12832, scalar12832, tp12832, tm12832, ep12832, em12832, dsL]

noncomputable def master12832 : MasterCertificate 12832 world12832 agent12832 :=
  master scalar12832 dsL tp12832 tm12832 ep12832 em12832
    (by norm_num [dsL]) (by norm_num [tp12832]) (by norm_num [tm12832])
    (by norm_num [ep12832]) (by norm_num [em12832])
    positive12832 negative12832 tails12832.1 tails12832.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12832.1 tailGuards12832.2

theorem preserves12832 : master12832.toScalarCertificate = scalar12832 := rfl

noncomputable def tp12833 : ℝ := (2328489303 / 10000000000)
noncomputable def tm12833 : ℝ := (-((1217887571 / 2000000000)))
noncomputable def ep12833 : ℝ := (51781155398635367 / 100000000000000000000)
noncomputable def em12833 : ℝ := (50419141841524921 / 100000000000000000000)
noncomputable def bp12833 : ℝ := (43577271865536383251 / 100000000000000000000)
noncomputable def bm12833 : ℝ := (44539842555543129473 / 100000000000000000000)

theorem positive12833 :
    Eplus aL (agent12833.root+dsL) scalar12833.worldRadius world12833.frame
      agent12833.frame tp12833 ≤ -ep12833 := by
  apply positive_check (eT := (5781656502969681259 / 5000000000000000000)) (y := (37954306615819205699 / 100000000000000000000)) (u := (146161657474983867827 / 100000000000000000000))
  · norm_num [world12833, agent12833, scalar12833, tp12833, tm12833, ep12833, em12833, dsL]
  · norm_num [world12833, agent12833, scalar12833, tp12833, tm12833, ep12833, em12833, dsL]
  · norm_num [world12833, agent12833, scalar12833, tp12833, tm12833, ep12833, em12833, dsL]
  · norm_num [world12833, agent12833, scalar12833, tp12833, tm12833, ep12833, em12833, dsL]
  · norm_num [world12833, agent12833, scalar12833, tp12833, tm12833, ep12833, em12833, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12833, agent12833, tp12833, tm12833, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12833, agent12833, scalar12833, tp12833, tm12833, ep12833, em12833, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12833, agent12833, tp12833, tm12833, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12833, agent12833, scalar12833, tp12833, tm12833, ep12833, em12833, dsL]

theorem negative12833 :
    Eminus aL (agent12833.root+dsL) scalar12833.worldRadius world12833.frame
      agent12833.frame tm12833 ≤ -em12833 := by
  apply negative_check (lo := (17098891918316820007 / 25000000000000000000)) (hi := (68395567673267280029 / 100000000000000000000))
    (y := (-((35834543155087631973 / 50000000000000000000)))) (u := (1220914134538460193 / 2500000000000000000))
  · norm_num [world12833, agent12833, scalar12833, tp12833, tm12833, ep12833, em12833, dsL]
  · norm_num [world12833, agent12833, scalar12833, tp12833, tm12833, ep12833, em12833, dsL]
  · norm_num [world12833, agent12833, scalar12833, tp12833, tm12833, ep12833, em12833, dsL]
  · norm_num [world12833, agent12833, scalar12833, tp12833, tm12833, ep12833, em12833, dsL]
  · norm_num [world12833, agent12833, scalar12833, tp12833, tm12833, ep12833, em12833, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12833, agent12833, tp12833, tm12833, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12833, agent12833, tp12833, tm12833, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12833, agent12833, scalar12833, tp12833, tm12833, ep12833, em12833, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12833, agent12833, tp12833, tm12833, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12833, agent12833, scalar12833, tp12833, tm12833, ep12833, em12833, dsL]

theorem tails12833 :
    exp (-((12833:ℝ)*ep12833)) ≤ scalar12833.upperTail ∧
    exp (-((12833:ℝ)*em12833)) ≤ scalar12833.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12833:ℝ)) (by norm_num [ep12833]) ?_)
      (show bp12833^8 ≤ scalar12833.upperTail by norm_num [bp12833, scalar12833])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12833, bp12833, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12833:ℝ)) (by norm_num [em12833]) ?_)
      (show bm12833^8 ≤ scalar12833.lowerTail by norm_num [bm12833, scalar12833])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12833, bm12833, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12833 :
    agent12833.root+dsL+scalar12833.worldRadius < √(1/100/aL) ∧
    2*(agent12833.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12833, agent12833, scalar12833, tp12833, tm12833, ep12833, em12833, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12833, agent12833, scalar12833, tp12833, tm12833, ep12833, em12833, dsL]

noncomputable def master12833 : MasterCertificate 12833 world12833 agent12833 :=
  master scalar12833 dsL tp12833 tm12833 ep12833 em12833
    (by norm_num [dsL]) (by norm_num [tp12833]) (by norm_num [tm12833])
    (by norm_num [ep12833]) (by norm_num [em12833])
    positive12833 negative12833 tails12833.1 tails12833.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12833.1 tailGuards12833.2

theorem preserves12833 : master12833.toScalarCertificate = scalar12833 := rfl

noncomputable def tp12834 : ℝ := (582142551 / 2500000000)
noncomputable def tm12834 : ℝ := (-((6089610727 / 10000000000)))
noncomputable def ep12834 : ℝ := (3236476328948323 / 6250000000000000000)
noncomputable def em12834 : ℝ := (5042124950264287 / 10000000000000000000)
noncomputable def bp12834 : ℝ := (43572727643375226439 / 100000000000000000000)
noncomputable def bm12834 : ℝ := (22267764850287277309 / 50000000000000000000)

theorem positive12834 :
    Eplus aL (agent12834.root+dsL) scalar12834.worldRadius world12834.frame
      agent12834.frame tp12834 ≤ -ep12834 := by
  apply positive_check (eT := (115633348724710517253 / 100000000000000000000)) (y := (37955049760646182021 / 100000000000000000000)) (u := (146162743671816418807 / 100000000000000000000))
  · norm_num [world12834, agent12834, scalar12834, tp12834, tm12834, ep12834, em12834, dsL]
  · norm_num [world12834, agent12834, scalar12834, tp12834, tm12834, ep12834, em12834, dsL]
  · norm_num [world12834, agent12834, scalar12834, tp12834, tm12834, ep12834, em12834, dsL]
  · norm_num [world12834, agent12834, scalar12834, tp12834, tm12834, ep12834, em12834, dsL]
  · norm_num [world12834, agent12834, scalar12834, tp12834, tm12834, ep12834, em12834, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12834, agent12834, tp12834, tm12834, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12834, agent12834, scalar12834, tp12834, tm12834, ep12834, em12834, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12834, agent12834, tp12834, tm12834, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12834, agent12834, scalar12834, tp12834, tm12834, ep12834, em12834, dsL]

theorem negative12834 :
    Eminus aL (agent12834.root+dsL) scalar12834.worldRadius world12834.frame
      agent12834.frame tm12834 ≤ -em12834 := by
  apply negative_check (lo := (17098848635027000949 / 25000000000000000000)) (hi := (68395394540108003797 / 100000000000000000000))
    (y := (-((8958637493207918371 / 12500000000000000000)))) (u := (12209139680608702241 / 25000000000000000000))
  · norm_num [world12834, agent12834, scalar12834, tp12834, tm12834, ep12834, em12834, dsL]
  · norm_num [world12834, agent12834, scalar12834, tp12834, tm12834, ep12834, em12834, dsL]
  · norm_num [world12834, agent12834, scalar12834, tp12834, tm12834, ep12834, em12834, dsL]
  · norm_num [world12834, agent12834, scalar12834, tp12834, tm12834, ep12834, em12834, dsL]
  · norm_num [world12834, agent12834, scalar12834, tp12834, tm12834, ep12834, em12834, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12834, agent12834, tp12834, tm12834, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12834, agent12834, tp12834, tm12834, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12834, agent12834, scalar12834, tp12834, tm12834, ep12834, em12834, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12834, agent12834, tp12834, tm12834, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12834, agent12834, scalar12834, tp12834, tm12834, ep12834, em12834, dsL]

theorem tails12834 :
    exp (-((12834:ℝ)*ep12834)) ≤ scalar12834.upperTail ∧
    exp (-((12834:ℝ)*em12834)) ≤ scalar12834.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12834:ℝ)) (by norm_num [ep12834]) ?_)
      (show bp12834^8 ≤ scalar12834.upperTail by norm_num [bp12834, scalar12834])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12834, bp12834, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12834:ℝ)) (by norm_num [em12834]) ?_)
      (show bm12834^8 ≤ scalar12834.lowerTail by norm_num [bm12834, scalar12834])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12834, bm12834, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12834 :
    agent12834.root+dsL+scalar12834.worldRadius < √(1/100/aL) ∧
    2*(agent12834.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12834, agent12834, scalar12834, tp12834, tm12834, ep12834, em12834, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12834, agent12834, scalar12834, tp12834, tm12834, ep12834, em12834, dsL]

noncomputable def master12834 : MasterCertificate 12834 world12834 agent12834 :=
  master scalar12834 dsL tp12834 tm12834 ep12834 em12834
    (by norm_num [dsL]) (by norm_num [tp12834]) (by norm_num [tm12834])
    (by norm_num [ep12834]) (by norm_num [em12834])
    positive12834 negative12834 tails12834.1 tails12834.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12834.1 tailGuards12834.2

theorem preserves12834 : master12834.toScalarCertificate = scalar12834 := rfl

noncomputable def tp12835 : ℝ := (582162759 / 2500000000)
noncomputable def tm12835 : ℝ := (-((761222939 / 1250000000)))
noncomputable def ep12835 : ℝ := (10357217098603687 / 20000000000000000000)
noncomputable def em12835 : ℝ := (12605838914441133 / 25000000000000000000)
noncomputable def bp12835 : ℝ := (43568184769146083477 / 100000000000000000000)
noncomputable def bm12835 : ℝ := (22265609052269780159 / 50000000000000000000)

theorem positive12835 :
    Eplus aL (agent12835.root+dsL) scalar12835.worldRadius world12835.frame
      agent12835.frame tp12835 ≤ -ep12835 := by
  apply positive_check (eT := (28908391731294167699 / 25000000000000000000)) (y := (7591158408465896453 / 20000000000000000000)) (u := (146163828615117166503 / 100000000000000000000))
  · norm_num [world12835, agent12835, scalar12835, tp12835, tm12835, ep12835, em12835, dsL]
  · norm_num [world12835, agent12835, scalar12835, tp12835, tm12835, ep12835, em12835, dsL]
  · norm_num [world12835, agent12835, scalar12835, tp12835, tm12835, ep12835, em12835, dsL]
  · norm_num [world12835, agent12835, scalar12835, tp12835, tm12835, ep12835, em12835, dsL]
  · norm_num [world12835, agent12835, scalar12835, tp12835, tm12835, ep12835, em12835, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12835, agent12835, tp12835, tm12835, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12835, agent12835, scalar12835, tp12835, tm12835, ep12835, em12835, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12835, agent12835, tp12835, tm12835, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12835, agent12835, scalar12835, tp12835, tm12835, ep12835, em12835, dsL]

theorem negative12835 :
    Eminus aL (agent12835.root+dsL) scalar12835.worldRadius world12835.frame
      agent12835.frame tm12835 ≤ -em12835 := by
  apply negative_check (lo := (68395221721221440399 / 100000000000000000000)) (hi := (170988054303053601 / 250000000000000000))
    (y := (-((17917278282960650203 / 25000000000000000000)))) (u := (12209138070689764747 / 25000000000000000000))
  · norm_num [world12835, agent12835, scalar12835, tp12835, tm12835, ep12835, em12835, dsL]
  · norm_num [world12835, agent12835, scalar12835, tp12835, tm12835, ep12835, em12835, dsL]
  · norm_num [world12835, agent12835, scalar12835, tp12835, tm12835, ep12835, em12835, dsL]
  · norm_num [world12835, agent12835, scalar12835, tp12835, tm12835, ep12835, em12835, dsL]
  · norm_num [world12835, agent12835, scalar12835, tp12835, tm12835, ep12835, em12835, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12835, agent12835, tp12835, tm12835, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12835, agent12835, tp12835, tm12835, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12835, agent12835, scalar12835, tp12835, tm12835, ep12835, em12835, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12835, agent12835, tp12835, tm12835, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12835, agent12835, scalar12835, tp12835, tm12835, ep12835, em12835, dsL]

theorem tails12835 :
    exp (-((12835:ℝ)*ep12835)) ≤ scalar12835.upperTail ∧
    exp (-((12835:ℝ)*em12835)) ≤ scalar12835.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12835:ℝ)) (by norm_num [ep12835]) ?_)
      (show bp12835^8 ≤ scalar12835.upperTail by norm_num [bp12835, scalar12835])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12835, bp12835, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12835:ℝ)) (by norm_num [em12835]) ?_)
      (show bm12835^8 ≤ scalar12835.lowerTail by norm_num [bm12835, scalar12835])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12835, bm12835, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12835 :
    agent12835.root+dsL+scalar12835.worldRadius < √(1/100/aL) ∧
    2*(agent12835.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12835, agent12835, scalar12835, tp12835, tm12835, ep12835, em12835, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12835, agent12835, scalar12835, tp12835, tm12835, ep12835, em12835, dsL]

noncomputable def master12835 : MasterCertificate 12835 world12835 agent12835 :=
  master scalar12835 dsL tp12835 tm12835 ep12835 em12835
    (by norm_num [dsL]) (by norm_num [tp12835]) (by norm_num [tm12835])
    (by norm_num [ep12835]) (by norm_num [em12835])
    positive12835 negative12835 tails12835.1 tails12835.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12835.1 tailGuards12835.2

theorem preserves12835 : master12835.toScalarCertificate = scalar12835 := rfl

noncomputable def tp12836 : ℝ := (465746369 / 2000000000)
noncomputable def tm12836 : ℝ := (-((6089956261 / 10000000000)))
noncomputable def ep12836 : ℝ := (25894274207330987 / 50000000000000000000)
noncomputable def em12836 : ℝ := (50425460592631281 / 100000000000000000000)
noncomputable def bp12836 : ℝ := (10890910753645774141 / 25000000000000000000)
noncomputable def bm12836 : ℝ := (44526907563261404363 / 100000000000000000000)

theorem positive12836 :
    Eplus aL (agent12836.root+dsL) scalar12836.worldRadius world12836.frame
      agent12836.frame tp12836 ≤ -ep12836 := by
  apply positive_check (eT := (115633784992644688883 / 100000000000000000000)) (y := (7591306873859914227 / 20000000000000000000)) (u := (146164913632664674951 / 100000000000000000000))
  · norm_num [world12836, agent12836, scalar12836, tp12836, tm12836, ep12836, em12836, dsL]
  · norm_num [world12836, agent12836, scalar12836, tp12836, tm12836, ep12836, em12836, dsL]
  · norm_num [world12836, agent12836, scalar12836, tp12836, tm12836, ep12836, em12836, dsL]
  · norm_num [world12836, agent12836, scalar12836, tp12836, tm12836, ep12836, em12836, dsL]
  · norm_num [world12836, agent12836, scalar12836, tp12836, tm12836, ep12836, em12836, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12836, agent12836, tp12836, tm12836, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12836, agent12836, scalar12836, tp12836, tm12836, ep12836, em12836, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12836, agent12836, tp12836, tm12836, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12836, agent12836, scalar12836, tp12836, tm12836, ep12836, em12836, dsL]

theorem negative12836 :
    Eminus aL (agent12836.root+dsL) scalar12836.worldRadius world12836.frame
      agent12836.frame tm12836 ≤ -em12836 := by
  apply negative_check (lo := (17098762249738390897 / 25000000000000000000)) (hi := (68395048998953563589 / 100000000000000000000))
    (y := (-((71669126777025427409 / 100000000000000000000)))) (u := (24418272809461334223 / 50000000000000000000))
  · norm_num [world12836, agent12836, scalar12836, tp12836, tm12836, ep12836, em12836, dsL]
  · norm_num [world12836, agent12836, scalar12836, tp12836, tm12836, ep12836, em12836, dsL]
  · norm_num [world12836, agent12836, scalar12836, tp12836, tm12836, ep12836, em12836, dsL]
  · norm_num [world12836, agent12836, scalar12836, tp12836, tm12836, ep12836, em12836, dsL]
  · norm_num [world12836, agent12836, scalar12836, tp12836, tm12836, ep12836, em12836, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12836, agent12836, tp12836, tm12836, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12836, agent12836, tp12836, tm12836, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12836, agent12836, scalar12836, tp12836, tm12836, ep12836, em12836, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12836, agent12836, tp12836, tm12836, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12836, agent12836, scalar12836, tp12836, tm12836, ep12836, em12836, dsL]

theorem tails12836 :
    exp (-((12836:ℝ)*ep12836)) ≤ scalar12836.upperTail ∧
    exp (-((12836:ℝ)*em12836)) ≤ scalar12836.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12836:ℝ)) (by norm_num [ep12836]) ?_)
      (show bp12836^8 ≤ scalar12836.upperTail by norm_num [bp12836, scalar12836])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12836, bp12836, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12836:ℝ)) (by norm_num [em12836]) ?_)
      (show bm12836^8 ≤ scalar12836.lowerTail by norm_num [bm12836, scalar12836])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12836, bm12836, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12836 :
    agent12836.root+dsL+scalar12836.worldRadius < √(1/100/aL) ∧
    2*(agent12836.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12836, agent12836, scalar12836, tp12836, tm12836, ep12836, em12836, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12836, agent12836, scalar12836, tp12836, tm12836, ep12836, em12836, dsL]

noncomputable def master12836 : MasterCertificate 12836 world12836 agent12836 :=
  master scalar12836 dsL tp12836 tm12836 ep12836 em12836
    (by norm_num [dsL]) (by norm_num [tp12836]) (by norm_num [tm12836])
    (by norm_num [ep12836]) (by norm_num [em12836])
    positive12836 negative12836 tails12836.1 tails12836.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12836.1 tailGuards12836.2

theorem preserves12836 : master12836.toScalarCertificate = scalar12836 := rfl

noncomputable def tp12837 : ℝ := (2328812633 / 10000000000)
noncomputable def tm12837 : ℝ := (-((380633069 / 625000000)))
noncomputable def ep12837 : ℝ := (12947752661314287 / 25000000000000000000)
noncomputable def em12837 : ℝ := (50427564895596499 / 100000000000000000000)
noncomputable def bp12837 : ℝ := (43559101948282875021 / 100000000000000000000)
noncomputable def bm12837 : ℝ := (44522597656386472667 / 100000000000000000000)

theorem positive12837 :
    Eplus aL (agent12837.root+dsL) scalar12837.worldRadius world12837.frame
      agent12837.frame tp12837 ≤ -ep12837 := by
  apply positive_check (eT := (115634002941529076293 / 100000000000000000000)) (y := (9489319143801677127 / 25000000000000000000)) (u := (73082999240656859613 / 50000000000000000000))
  · norm_num [world12837, agent12837, scalar12837, tp12837, tm12837, ep12837, em12837, dsL]
  · norm_num [world12837, agent12837, scalar12837, tp12837, tm12837, ep12837, em12837, dsL]
  · norm_num [world12837, agent12837, scalar12837, tp12837, tm12837, ep12837, em12837, dsL]
  · norm_num [world12837, agent12837, scalar12837, tp12837, tm12837, ep12837, em12837, dsL]
  · norm_num [world12837, agent12837, scalar12837, tp12837, tm12837, ep12837, em12837, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12837, agent12837, tp12837, tm12837, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12837, agent12837, scalar12837, tp12837, tm12837, ep12837, em12837, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12837, agent12837, tp12837, tm12837, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12837, agent12837, scalar12837, tp12837, tm12837, ep12837, em12837, dsL]

theorem negative12837 :
    Eminus aL (agent12837.root+dsL) scalar12837.worldRadius world12837.frame
      agent12837.frame tm12837 ≤ -em12837 := by
  apply negative_check (lo := (17098718954682508237 / 25000000000000000000)) (hi := (68394875818730032949 / 100000000000000000000))
    (y := (-((71669141979345265973 / 100000000000000000000)))) (u := (48836538194635369683 / 100000000000000000000))
  · norm_num [world12837, agent12837, scalar12837, tp12837, tm12837, ep12837, em12837, dsL]
  · norm_num [world12837, agent12837, scalar12837, tp12837, tm12837, ep12837, em12837, dsL]
  · norm_num [world12837, agent12837, scalar12837, tp12837, tm12837, ep12837, em12837, dsL]
  · norm_num [world12837, agent12837, scalar12837, tp12837, tm12837, ep12837, em12837, dsL]
  · norm_num [world12837, agent12837, scalar12837, tp12837, tm12837, ep12837, em12837, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12837, agent12837, tp12837, tm12837, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12837, agent12837, tp12837, tm12837, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12837, agent12837, scalar12837, tp12837, tm12837, ep12837, em12837, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12837, agent12837, tp12837, tm12837, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12837, agent12837, scalar12837, tp12837, tm12837, ep12837, em12837, dsL]

theorem tails12837 :
    exp (-((12837:ℝ)*ep12837)) ≤ scalar12837.upperTail ∧
    exp (-((12837:ℝ)*em12837)) ≤ scalar12837.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12837:ℝ)) (by norm_num [ep12837]) ?_)
      (show bp12837^8 ≤ scalar12837.upperTail by norm_num [bp12837, scalar12837])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12837, bp12837, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12837:ℝ)) (by norm_num [em12837]) ?_)
      (show bm12837^8 ≤ scalar12837.lowerTail by norm_num [bm12837, scalar12837])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12837, bm12837, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12837 :
    agent12837.root+dsL+scalar12837.worldRadius < √(1/100/aL) ∧
    2*(agent12837.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12837, agent12837, scalar12837, tp12837, tm12837, ep12837, em12837, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12837, agent12837, scalar12837, tp12837, tm12837, ep12837, em12837, dsL]

noncomputable def master12837 : MasterCertificate 12837 world12837 agent12837 :=
  master scalar12837 dsL tp12837 tm12837 ep12837 em12837
    (by norm_num [dsL]) (by norm_num [tp12837]) (by norm_num [tm12837])
    (by norm_num [ep12837]) (by norm_num [em12837])
    positive12837 negative12837 tails12837.1 tails12837.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12837.1 tailGuards12837.2

theorem preserves12837 : master12837.toScalarCertificate = scalar12837 := rfl

noncomputable def tp12838 : ℝ := (1164446671 / 5000000000)
noncomputable def tm12838 : ℝ := (-((6090301613 / 10000000000)))
noncomputable def ep12838 : ℝ := (12948367774564353 / 25000000000000000000)
noncomputable def em12838 : ℝ := (49247722210391 / 97656250000000000)
noncomputable def bp12838 : ℝ := (43554562329674591227 / 100000000000000000000)
noncomputable def bm12838 : ℝ := (11129572278728111247 / 25000000000000000000)

theorem positive12838 :
    Eplus aL (agent12838.root+dsL) scalar12838.worldRadius world12838.frame
      agent12838.frame tp12838 ≤ -ep12838 := by
  apply positive_check (eT := (115634220353490970171 / 100000000000000000000)) (y := (37958017894600618771 / 100000000000000000000)) (u := (14616708204222408241 / 10000000000000000000))
  · norm_num [world12838, agent12838, scalar12838, tp12838, tm12838, ep12838, em12838, dsL]
  · norm_num [world12838, agent12838, scalar12838, tp12838, tm12838, ep12838, em12838, dsL]
  · norm_num [world12838, agent12838, scalar12838, tp12838, tm12838, ep12838, em12838, dsL]
  · norm_num [world12838, agent12838, scalar12838, tp12838, tm12838, ep12838, em12838, dsL]
  · norm_num [world12838, agent12838, scalar12838, tp12838, tm12838, ep12838, em12838, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12838, agent12838, tp12838, tm12838, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12838, agent12838, scalar12838, tp12838, tm12838, ep12838, em12838, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12838, agent12838, tp12838, tm12838, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12838, agent12838, scalar12838, tp12838, tm12838, ep12838, em12838, dsL]

theorem negative12838 :
    Eminus aL (agent12838.root+dsL) scalar12838.worldRadius world12838.frame
      agent12838.frame tm12838 ≤ -em12838 := by
  apply negative_check (lo := (34197352003238166893 / 50000000000000000000)) (hi := (68394704006476333787 / 100000000000000000000))
    (y := (-((71669154629214311811 / 100000000000000000000)))) (u := (1220913300421940807 / 2500000000000000000))
  · norm_num [world12838, agent12838, scalar12838, tp12838, tm12838, ep12838, em12838, dsL]
  · norm_num [world12838, agent12838, scalar12838, tp12838, tm12838, ep12838, em12838, dsL]
  · norm_num [world12838, agent12838, scalar12838, tp12838, tm12838, ep12838, em12838, dsL]
  · norm_num [world12838, agent12838, scalar12838, tp12838, tm12838, ep12838, em12838, dsL]
  · norm_num [world12838, agent12838, scalar12838, tp12838, tm12838, ep12838, em12838, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12838, agent12838, tp12838, tm12838, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12838, agent12838, tp12838, tm12838, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12838, agent12838, scalar12838, tp12838, tm12838, ep12838, em12838, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12838, agent12838, tp12838, tm12838, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12838, agent12838, scalar12838, tp12838, tm12838, ep12838, em12838, dsL]

theorem tails12838 :
    exp (-((12838:ℝ)*ep12838)) ≤ scalar12838.upperTail ∧
    exp (-((12838:ℝ)*em12838)) ≤ scalar12838.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12838:ℝ)) (by norm_num [ep12838]) ?_)
      (show bp12838^8 ≤ scalar12838.upperTail by norm_num [bp12838, scalar12838])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12838, bp12838, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12838:ℝ)) (by norm_num [em12838]) ?_)
      (show bm12838^8 ≤ scalar12838.lowerTail by norm_num [bm12838, scalar12838])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12838, bm12838, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12838 :
    agent12838.root+dsL+scalar12838.worldRadius < √(1/100/aL) ∧
    2*(agent12838.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12838, agent12838, scalar12838, tp12838, tm12838, ep12838, em12838, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12838, agent12838, scalar12838, tp12838, tm12838, ep12838, em12838, dsL]

noncomputable def master12838 : MasterCertificate 12838 world12838 agent12838 :=
  master scalar12838 dsL tp12838 tm12838 ep12838 em12838
    (by norm_num [dsL]) (by norm_num [tp12838]) (by norm_num [tm12838])
    (by norm_num [ep12838]) (by norm_num [em12838])
    positive12838 negative12838 tails12838.1 tails12838.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12838.1 tailGuards12838.2

theorem preserves12838 : master12838.toScalarCertificate = scalar12838 := rfl

noncomputable def tp12839 : ℝ := (2328974099 / 10000000000)
noncomputable def tm12839 : ℝ := (-((3045237021 / 5000000000)))
noncomputable def ep12839 : ℝ := (25897965430179097 / 50000000000000000000)
noncomputable def em12839 : ℝ := (25215884779797463 / 50000000000000000000)
noncomputable def bp12839 : ℝ := (21775011699588833707 / 50000000000000000000)
noncomputable def bm12839 : ℝ := (8902796241533302269 / 20000000000000000000)

theorem positive12839 :
    Eplus aL (agent12839.root+dsL) scalar12839.worldRadius world12839.frame
      agent12839.frame tp12839 ≤ -ep12839 := by
  apply positive_check (eT := (57817219072258778391 / 50000000000000000000)) (y := (18979380150444204593 / 50000000000000000000)) (u := (36542041799964994483 / 25000000000000000000))
  · norm_num [world12839, agent12839, scalar12839, tp12839, tm12839, ep12839, em12839, dsL]
  · norm_num [world12839, agent12839, scalar12839, tp12839, tm12839, ep12839, em12839, dsL]
  · norm_num [world12839, agent12839, scalar12839, tp12839, tm12839, ep12839, em12839, dsL]
  · norm_num [world12839, agent12839, scalar12839, tp12839, tm12839, ep12839, em12839, dsL]
  · norm_num [world12839, agent12839, scalar12839, tp12839, tm12839, ep12839, em12839, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12839, agent12839, tp12839, tm12839, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12839, agent12839, scalar12839, tp12839, tm12839, ep12839, em12839, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12839, agent12839, tp12839, tm12839, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12839, agent12839, scalar12839, tp12839, tm12839, ep12839, em12839, dsL]

theorem negative12839 :
    Eminus aL (agent12839.root+dsL) scalar12839.worldRadius world12839.frame
      agent12839.frame tm12839 ≤ -em12839 := by
  apply negative_check (lo := (34197266239288708229 / 50000000000000000000)) (hi := (68394532478577416459 / 100000000000000000000))
    (y := (-((71669167152406538411 / 100000000000000000000)))) (u := (24418262950492616977 / 50000000000000000000))
  · norm_num [world12839, agent12839, scalar12839, tp12839, tm12839, ep12839, em12839, dsL]
  · norm_num [world12839, agent12839, scalar12839, tp12839, tm12839, ep12839, em12839, dsL]
  · norm_num [world12839, agent12839, scalar12839, tp12839, tm12839, ep12839, em12839, dsL]
  · norm_num [world12839, agent12839, scalar12839, tp12839, tm12839, ep12839, em12839, dsL]
  · norm_num [world12839, agent12839, scalar12839, tp12839, tm12839, ep12839, em12839, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12839, agent12839, tp12839, tm12839, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12839, agent12839, tp12839, tm12839, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12839, agent12839, scalar12839, tp12839, tm12839, ep12839, em12839, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12839, agent12839, tp12839, tm12839, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12839, agent12839, scalar12839, tp12839, tm12839, ep12839, em12839, dsL]

theorem tails12839 :
    exp (-((12839:ℝ)*ep12839)) ≤ scalar12839.upperTail ∧
    exp (-((12839:ℝ)*em12839)) ≤ scalar12839.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12839:ℝ)) (by norm_num [ep12839]) ?_)
      (show bp12839^8 ≤ scalar12839.upperTail by norm_num [bp12839, scalar12839])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12839, bp12839, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12839:ℝ)) (by norm_num [em12839]) ?_)
      (show bm12839^8 ≤ scalar12839.lowerTail by norm_num [bm12839, scalar12839])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12839, bm12839, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12839 :
    agent12839.root+dsL+scalar12839.worldRadius < √(1/100/aL) ∧
    2*(agent12839.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12839, agent12839, scalar12839, tp12839, tm12839, ep12839, em12839, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12839, agent12839, scalar12839, tp12839, tm12839, ep12839, em12839, dsL]

noncomputable def master12839 : MasterCertificate 12839 world12839 agent12839 :=
  master scalar12839 dsL tp12839 tm12839 ep12839 em12839
    (by norm_num [dsL]) (by norm_num [tp12839]) (by norm_num [tm12839])
    (by norm_num [ep12839]) (by norm_num [em12839])
    positive12839 negative12839 tails12839.1 tails12839.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12839.1 tailGuards12839.2

theorem preserves12839 : master12839.toScalarCertificate = scalar12839 := rfl

noncomputable def tp12840 : ℝ := (2329127981 / 10000000000)
noncomputable def tm12840 : ℝ := (-((6090867977 / 10000000000)))
noncomputable def ep12840 : ℝ := (51799781816319069 / 100000000000000000000)
noncomputable def em12840 : ℝ := (50435388673334949 / 100000000000000000000)
noncomputable def bp12840 : ℝ := (8708902474477051093 / 20000000000000000000)
noncomputable def bm12840 : ℝ := (44508589712012272877 / 100000000000000000000)

theorem positive12840 :
    Eplus aL (agent12840.root+dsL) scalar12840.worldRadius world12840.frame
      agent12840.frame tp12840 ≤ -ep12840 := by
  apply positive_check (eT := (23127036673092180299 / 20000000000000000000)) (y := (18979390350934053093 / 50000000000000000000)) (u := (36542049254900283403 / 25000000000000000000))
  · norm_num [world12840, agent12840, scalar12840, tp12840, tm12840, ep12840, em12840, dsL]
  · norm_num [world12840, agent12840, scalar12840, tp12840, tm12840, ep12840, em12840, dsL]
  · norm_num [world12840, agent12840, scalar12840, tp12840, tm12840, ep12840, em12840, dsL]
  · norm_num [world12840, agent12840, scalar12840, tp12840, tm12840, ep12840, em12840, dsL]
  · norm_num [world12840, agent12840, scalar12840, tp12840, tm12840, ep12840, em12840, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12840, agent12840, tp12840, tm12840, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12840, agent12840, scalar12840, tp12840, tm12840, ep12840, em12840, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12840, agent12840, tp12840, tm12840, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12840, agent12840, scalar12840, tp12840, tm12840, ep12840, em12840, dsL]

theorem negative12840 :
    Eminus aL (agent12840.root+dsL) scalar12840.worldRadius world12840.frame
      agent12840.frame tm12840 ≤ -em12840 := by
  apply negative_check (lo := (68393415994259386603 / 100000000000000000000)) (hi := (17098353998564846651 / 25000000000000000000))
    (y := (-((7166728901129226647 / 10000000000000000000)))) (u := (12209360782117587179 / 25000000000000000000))
  · norm_num [world12840, agent12840, scalar12840, tp12840, tm12840, ep12840, em12840, dsL]
  · norm_num [world12840, agent12840, scalar12840, tp12840, tm12840, ep12840, em12840, dsL]
  · norm_num [world12840, agent12840, scalar12840, tp12840, tm12840, ep12840, em12840, dsL]
  · norm_num [world12840, agent12840, scalar12840, tp12840, tm12840, ep12840, em12840, dsL]
  · norm_num [world12840, agent12840, scalar12840, tp12840, tm12840, ep12840, em12840, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12840, agent12840, tp12840, tm12840, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12840, agent12840, tp12840, tm12840, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12840, agent12840, scalar12840, tp12840, tm12840, ep12840, em12840, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12840, agent12840, tp12840, tm12840, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12840, agent12840, scalar12840, tp12840, tm12840, ep12840, em12840, dsL]

theorem tails12840 :
    exp (-((12840:ℝ)*ep12840)) ≤ scalar12840.upperTail ∧
    exp (-((12840:ℝ)*em12840)) ≤ scalar12840.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12840:ℝ)) (by norm_num [ep12840]) ?_)
      (show bp12840^8 ≤ scalar12840.upperTail by norm_num [bp12840, scalar12840])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12840, bp12840, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12840:ℝ)) (by norm_num [em12840]) ?_)
      (show bm12840^8 ≤ scalar12840.lowerTail by norm_num [bm12840, scalar12840])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12840, bm12840, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12840 :
    agent12840.root+dsL+scalar12840.worldRadius < √(1/100/aL) ∧
    2*(agent12840.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12840, agent12840, scalar12840, tp12840, tm12840, ep12840, em12840, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12840, agent12840, scalar12840, tp12840, tm12840, ep12840, em12840, dsL]

noncomputable def master12840 : MasterCertificate 12840 world12840 agent12840 :=
  master scalar12840 dsL tp12840 tm12840 ep12840 em12840
    (by norm_num [dsL]) (by norm_num [tp12840]) (by norm_num [tm12840])
    (by norm_num [ep12840]) (by norm_num [em12840])
    positive12840 negative12840 tails12840.1 tails12840.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12840.1 tailGuards12840.2

theorem preserves12840 : master12840.toScalarCertificate = scalar12840 := rfl

noncomputable def tp12841 : ℝ := (2329208537 / 10000000000)
noncomputable def tm12841 : ℝ := (-((380690023 / 625000000)))
noncomputable def ep12841 : ℝ := (25901119294413183 / 50000000000000000000)
noncomputable def em12841 : ℝ := (504374879065737 / 1000000000000000000)
noncomputable def bp12841 : ℝ := (43539975967354343183 / 100000000000000000000)
noncomputable def bm12841 : ℝ := (5563035522397954799 / 12500000000000000000)

theorem positive12841 :
    Eplus aL (agent12841.root+dsL) scalar12841.worldRadius world12841.frame
      agent12841.frame tp12841 ≤ -ep12841 := by
  apply positive_check (eT := (115635399762125031689 / 100000000000000000000)) (y := (1518380818243597829 / 4000000000000000000)) (u := (73084639154504504969 / 50000000000000000000))
  · norm_num [world12841, agent12841, scalar12841, tp12841, tm12841, ep12841, em12841, dsL]
  · norm_num [world12841, agent12841, scalar12841, tp12841, tm12841, ep12841, em12841, dsL]
  · norm_num [world12841, agent12841, scalar12841, tp12841, tm12841, ep12841, em12841, dsL]
  · norm_num [world12841, agent12841, scalar12841, tp12841, tm12841, ep12841, em12841, dsL]
  · norm_num [world12841, agent12841, scalar12841, tp12841, tm12841, ep12841, em12841, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12841, agent12841, tp12841, tm12841, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12841, agent12841, scalar12841, tp12841, tm12841, ep12841, em12841, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12841, agent12841, tp12841, tm12841, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12841, agent12841, scalar12841, tp12841, tm12841, ep12841, em12841, dsL]

theorem negative12841 :
    Eminus aL (agent12841.root+dsL) scalar12841.worldRadius world12841.frame
      agent12841.frame tm12841 ≤ -em12841 := by
  apply negative_check (lo := (68393244537440871727 / 100000000000000000000)) (hi := (4274577783590054483 / 6250000000000000000))
    (y := (-((17916825637816835557 / 25000000000000000000)))) (u := (24418718257946584577 / 50000000000000000000))
  · norm_num [world12841, agent12841, scalar12841, tp12841, tm12841, ep12841, em12841, dsL]
  · norm_num [world12841, agent12841, scalar12841, tp12841, tm12841, ep12841, em12841, dsL]
  · norm_num [world12841, agent12841, scalar12841, tp12841, tm12841, ep12841, em12841, dsL]
  · norm_num [world12841, agent12841, scalar12841, tp12841, tm12841, ep12841, em12841, dsL]
  · norm_num [world12841, agent12841, scalar12841, tp12841, tm12841, ep12841, em12841, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12841, agent12841, tp12841, tm12841, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12841, agent12841, tp12841, tm12841, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12841, agent12841, scalar12841, tp12841, tm12841, ep12841, em12841, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12841, agent12841, tp12841, tm12841, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12841, agent12841, scalar12841, tp12841, tm12841, ep12841, em12841, dsL]

theorem tails12841 :
    exp (-((12841:ℝ)*ep12841)) ≤ scalar12841.upperTail ∧
    exp (-((12841:ℝ)*em12841)) ≤ scalar12841.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12841:ℝ)) (by norm_num [ep12841]) ?_)
      (show bp12841^8 ≤ scalar12841.upperTail by norm_num [bp12841, scalar12841])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12841, bp12841, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12841:ℝ)) (by norm_num [em12841]) ?_)
      (show bm12841^8 ≤ scalar12841.lowerTail by norm_num [bm12841, scalar12841])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12841, bm12841, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12841 :
    agent12841.root+dsL+scalar12841.worldRadius < √(1/100/aL) ∧
    2*(agent12841.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12841, agent12841, scalar12841, tp12841, tm12841, ep12841, em12841, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12841, agent12841, scalar12841, tp12841, tm12841, ep12841, em12841, dsL]

noncomputable def master12841 : MasterCertificate 12841 world12841 agent12841 :=
  master scalar12841 dsL tp12841 tm12841 ep12841 em12841
    (by norm_num [dsL]) (by norm_num [tp12841]) (by norm_num [tm12841])
    (by norm_num [ep12841]) (by norm_num [em12841])
    positive12841 negative12841 tails12841.1 tails12841.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12841.1 tailGuards12841.2

theorem preserves12841 : master12841.toScalarCertificate = scalar12841 := rfl

noncomputable def tp12842 : ℝ := (1164644579 / 5000000000)
noncomputable def tm12842 : ℝ := (-((304560621 / 500000000)))
noncomputable def ep12842 : ℝ := (51804693721952893 / 100000000000000000000)
noncomputable def em12842 : ℝ := (25219792815023201 / 50000000000000000000)
noncomputable def bp12842 : ℝ := (43535440913213545833 / 100000000000000000000)
noncomputable def bm12842 : ℝ := (44499979907790711133 / 100000000000000000000)

theorem positive12842 :
    Eplus aL (agent12842.root+dsL) scalar12842.worldRadius world12842.frame
      agent12842.frame tp12842 ≤ -ep12842 := by
  apply positive_check (eT := (115635616660449168491 / 100000000000000000000)) (y := (37960261692669431151 / 100000000000000000000)) (u := (146170361773183317601 / 100000000000000000000))
  · norm_num [world12842, agent12842, scalar12842, tp12842, tm12842, ep12842, em12842, dsL]
  · norm_num [world12842, agent12842, scalar12842, tp12842, tm12842, ep12842, em12842, dsL]
  · norm_num [world12842, agent12842, scalar12842, tp12842, tm12842, ep12842, em12842, dsL]
  · norm_num [world12842, agent12842, scalar12842, tp12842, tm12842, ep12842, em12842, dsL]
  · norm_num [world12842, agent12842, scalar12842, tp12842, tm12842, ep12842, em12842, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12842, agent12842, tp12842, tm12842, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12842, agent12842, scalar12842, tp12842, tm12842, ep12842, em12842, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12842, agent12842, tp12842, tm12842, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12842, agent12842, scalar12842, tp12842, tm12842, ep12842, em12842, dsL]

theorem negative12842 :
    Eminus aL (agent12842.root+dsL) scalar12842.worldRadius world12842.frame
      agent12842.frame tm12842 ≤ -em12842 := by
  apply negative_check (lo := (6839307446976267963 / 10000000000000000000)) (hi := (68393074469762679631 / 100000000000000000000))
    (y := (-((71667313202777156489 / 100000000000000000000)))) (u := (3052339457123068917 / 6250000000000000000))
  · norm_num [world12842, agent12842, scalar12842, tp12842, tm12842, ep12842, em12842, dsL]
  · norm_num [world12842, agent12842, scalar12842, tp12842, tm12842, ep12842, em12842, dsL]
  · norm_num [world12842, agent12842, scalar12842, tp12842, tm12842, ep12842, em12842, dsL]
  · norm_num [world12842, agent12842, scalar12842, tp12842, tm12842, ep12842, em12842, dsL]
  · norm_num [world12842, agent12842, scalar12842, tp12842, tm12842, ep12842, em12842, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12842, agent12842, tp12842, tm12842, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12842, agent12842, tp12842, tm12842, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12842, agent12842, scalar12842, tp12842, tm12842, ep12842, em12842, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12842, agent12842, tp12842, tm12842, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12842, agent12842, scalar12842, tp12842, tm12842, ep12842, em12842, dsL]

theorem tails12842 :
    exp (-((12842:ℝ)*ep12842)) ≤ scalar12842.upperTail ∧
    exp (-((12842:ℝ)*em12842)) ≤ scalar12842.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12842:ℝ)) (by norm_num [ep12842]) ?_)
      (show bp12842^8 ≤ scalar12842.upperTail by norm_num [bp12842, scalar12842])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12842, bp12842, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12842:ℝ)) (by norm_num [em12842]) ?_)
      (show bm12842^8 ≤ scalar12842.lowerTail by norm_num [bm12842, scalar12842])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12842, bm12842, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12842 :
    agent12842.root+dsL+scalar12842.worldRadius < √(1/100/aL) ∧
    2*(agent12842.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12842, agent12842, scalar12842, tp12842, tm12842, ep12842, em12842, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12842, agent12842, scalar12842, tp12842, tm12842, ep12842, em12842, dsL]

noncomputable def master12842 : MasterCertificate 12842 world12842 agent12842 :=
  master scalar12842 dsL tp12842 tm12842 ep12842 em12842
    (by norm_num [dsL]) (by norm_num [tp12842]) (by norm_num [tm12842])
    (by norm_num [ep12842]) (by norm_num [em12842])
    positive12842 negative12842 tails12842.1 tails12842.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12842.1 tailGuards12842.2

theorem preserves12842 : master12842.toScalarCertificate = scalar12842 := rfl

noncomputable def tp12843 : ℝ := (2329369713 / 10000000000)
noncomputable def tm12843 : ℝ := (-((1522846117 / 2500000000)))
noncomputable def ep12843 : ℝ := (25903574015363459 / 50000000000000000000)
noncomputable def em12843 : ℝ := (2017667303232519 / 4000000000000000000)
noncomputable def bp12843 : ℝ := (4353090664033709121 / 10000000000000000000)
noncomputable def bm12843 : ℝ := (22247838185650750007 / 50000000000000000000)

theorem positive12843 :
    Eplus aL (agent12843.root+dsL) scalar12843.worldRadius world12843.frame
      agent12843.frame tp12843 ≤ -ep12843 := by
  apply positive_check (eT := (57817916557856243067 / 50000000000000000000)) (y := (37961002171515789363 / 100000000000000000000)) (u := (146171444137799228859 / 100000000000000000000))
  · norm_num [world12843, agent12843, scalar12843, tp12843, tm12843, ep12843, em12843, dsL]
  · norm_num [world12843, agent12843, scalar12843, tp12843, tm12843, ep12843, em12843, dsL]
  · norm_num [world12843, agent12843, scalar12843, tp12843, tm12843, ep12843, em12843, dsL]
  · norm_num [world12843, agent12843, scalar12843, tp12843, tm12843, ep12843, em12843, dsL]
  · norm_num [world12843, agent12843, scalar12843, tp12843, tm12843, ep12843, em12843, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12843, agent12843, tp12843, tm12843, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12843, agent12843, scalar12843, tp12843, tm12843, ep12843, em12843, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12843, agent12843, tp12843, tm12843, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12843, agent12843, scalar12843, tp12843, tm12843, ep12843, em12843, dsL]

theorem negative12843 :
    Eminus aL (agent12843.root+dsL) scalar12843.worldRadius world12843.frame
      agent12843.frame tm12843 ≤ -em12843 := by
  apply negative_check (lo := (34196452181050620529 / 50000000000000000000)) (hi := (68392904362101241059 / 100000000000000000000))
    (y := (-((17916831187212077847 / 25000000000000000000)))) (u := (24418712837582429233 / 50000000000000000000))
  · norm_num [world12843, agent12843, scalar12843, tp12843, tm12843, ep12843, em12843, dsL]
  · norm_num [world12843, agent12843, scalar12843, tp12843, tm12843, ep12843, em12843, dsL]
  · norm_num [world12843, agent12843, scalar12843, tp12843, tm12843, ep12843, em12843, dsL]
  · norm_num [world12843, agent12843, scalar12843, tp12843, tm12843, ep12843, em12843, dsL]
  · norm_num [world12843, agent12843, scalar12843, tp12843, tm12843, ep12843, em12843, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12843, agent12843, tp12843, tm12843, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12843, agent12843, tp12843, tm12843, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12843, agent12843, scalar12843, tp12843, tm12843, ep12843, em12843, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12843, agent12843, tp12843, tm12843, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12843, agent12843, scalar12843, tp12843, tm12843, ep12843, em12843, dsL]

theorem tails12843 :
    exp (-((12843:ℝ)*ep12843)) ≤ scalar12843.upperTail ∧
    exp (-((12843:ℝ)*em12843)) ≤ scalar12843.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12843:ℝ)) (by norm_num [ep12843]) ?_)
      (show bp12843^8 ≤ scalar12843.upperTail by norm_num [bp12843, scalar12843])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12843, bp12843, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12843:ℝ)) (by norm_num [em12843]) ?_)
      (show bm12843^8 ≤ scalar12843.lowerTail by norm_num [bm12843, scalar12843])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12843, bm12843, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12843 :
    agent12843.root+dsL+scalar12843.worldRadius < √(1/100/aL) ∧
    2*(agent12843.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12843, agent12843, scalar12843, tp12843, tm12843, ep12843, em12843, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12843, agent12843, scalar12843, tp12843, tm12843, ep12843, em12843, dsL]

noncomputable def master12843 : MasterCertificate 12843 world12843 agent12843 :=
  master scalar12843 dsL tp12843 tm12843 ep12843 em12843
    (by norm_num [dsL]) (by norm_num [tp12843]) (by norm_num [tm12843])
    (by norm_num [ep12843]) (by norm_num [em12843])
    positive12843 negative12843 tails12843.1 tails12843.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12843.1 tailGuards12843.2

theorem preserves12843 : master12843.toScalarCertificate = scalar12843 := rfl

noncomputable def tp12844 : ℝ := (1164725103 / 5000000000)
noncomputable def tm12844 : ℝ := (-((6091556551 / 10000000000)))
noncomputable def ep12844 : ℝ := (6476200206688827 / 12500000000000000000)
noncomputable def em12844 : ℝ := (50443778904264903 / 100000000000000000000)
noncomputable def bp12844 : ℝ := (43526373052024124907 / 100000000000000000000)
noncomputable def bm12844 : ℝ := (44491373465857779801 / 100000000000000000000)

theorem positive12844 :
    Eplus aL (agent12844.root+dsL) scalar12844.worldRadius world12844.frame
      agent12844.frame tp12844 ≤ -ep12844 := by
  apply positive_check (eT := (115636049156688570417 / 100000000000000000000)) (y := (18980870905247068843 / 50000000000000000000)) (u := (913578283017334791 / 625000000000000000))
  · norm_num [world12844, agent12844, scalar12844, tp12844, tm12844, ep12844, em12844, dsL]
  · norm_num [world12844, agent12844, scalar12844, tp12844, tm12844, ep12844, em12844, dsL]
  · norm_num [world12844, agent12844, scalar12844, tp12844, tm12844, ep12844, em12844, dsL]
  · norm_num [world12844, agent12844, scalar12844, tp12844, tm12844, ep12844, em12844, dsL]
  · norm_num [world12844, agent12844, scalar12844, tp12844, tm12844, ep12844, em12844, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12844, agent12844, tp12844, tm12844, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12844, agent12844, scalar12844, tp12844, tm12844, ep12844, em12844, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12844, agent12844, tp12844, tm12844, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12844, agent12844, scalar12844, tp12844, tm12844, ep12844, em12844, dsL]

theorem negative12844 :
    Eminus aL (agent12844.root+dsL) scalar12844.worldRadius world12844.frame
      agent12844.frame tm12844 ≤ -em12844 := by
  apply negative_check (lo := (2137272939008312999 / 3125000000000000000)) (hi := (68392734048266015969 / 100000000000000000000))
    (y := (-((35833668639668869817 / 50000000000000000000)))) (u := (24418709777798390309 / 50000000000000000000))
  · norm_num [world12844, agent12844, scalar12844, tp12844, tm12844, ep12844, em12844, dsL]
  · norm_num [world12844, agent12844, scalar12844, tp12844, tm12844, ep12844, em12844, dsL]
  · norm_num [world12844, agent12844, scalar12844, tp12844, tm12844, ep12844, em12844, dsL]
  · norm_num [world12844, agent12844, scalar12844, tp12844, tm12844, ep12844, em12844, dsL]
  · norm_num [world12844, agent12844, scalar12844, tp12844, tm12844, ep12844, em12844, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12844, agent12844, tp12844, tm12844, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12844, agent12844, tp12844, tm12844, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12844, agent12844, scalar12844, tp12844, tm12844, ep12844, em12844, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12844, agent12844, tp12844, tm12844, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12844, agent12844, scalar12844, tp12844, tm12844, ep12844, em12844, dsL]

theorem tails12844 :
    exp (-((12844:ℝ)*ep12844)) ≤ scalar12844.upperTail ∧
    exp (-((12844:ℝ)*em12844)) ≤ scalar12844.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12844:ℝ)) (by norm_num [ep12844]) ?_)
      (show bp12844^8 ≤ scalar12844.upperTail by norm_num [bp12844, scalar12844])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12844, bp12844, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12844:ℝ)) (by norm_num [em12844]) ?_)
      (show bm12844^8 ≤ scalar12844.lowerTail by norm_num [bm12844, scalar12844])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12844, bm12844, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12844 :
    agent12844.root+dsL+scalar12844.worldRadius < √(1/100/aL) ∧
    2*(agent12844.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12844, agent12844, scalar12844, tp12844, tm12844, ep12844, em12844, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12844, agent12844, scalar12844, tp12844, tm12844, ep12844, em12844, dsL]

noncomputable def master12844 : MasterCertificate 12844 world12844 agent12844 :=
  master scalar12844 dsL tp12844 tm12844 ep12844 em12844
    (by norm_num [dsL]) (by norm_num [tp12844]) (by norm_num [tm12844])
    (by norm_num [ep12844]) (by norm_num [em12844])
    positive12844 negative12844 tails12844.1 tails12844.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12844.1 tailGuards12844.2

theorem preserves12844 : master12844.toScalarCertificate = scalar12844 := rfl

noncomputable def tp12845 : ℝ := (2329530661 / 10000000000)
noncomputable def tm12845 : ℝ := (-((6091728297 / 10000000000)))
noncomputable def ep12845 : ℝ := (3238253314317141 / 6250000000000000000)
noncomputable def em12845 : ℝ := (50445873137671321 / 100000000000000000000)
noncomputable def bp12845 : ℝ := (43521841239254603097 / 100000000000000000000)
noncomputable def bm12845 : ℝ := (44487072236283762531 / 100000000000000000000)

theorem positive12845 :
    Eplus aL (agent12845.root+dsL) scalar12845.worldRadius world12845.frame
      agent12845.frame tp12845 ≤ -ep12845 := by
  apply positive_check (eT := (14454533119571080229 / 12500000000000000000)) (y := (37962481329146200951 / 100000000000000000000)) (u := (73086803129929616611 / 50000000000000000000))
  · norm_num [world12845, agent12845, scalar12845, tp12845, tm12845, ep12845, em12845, dsL]
  · norm_num [world12845, agent12845, scalar12845, tp12845, tm12845, ep12845, em12845, dsL]
  · norm_num [world12845, agent12845, scalar12845, tp12845, tm12845, ep12845, em12845, dsL]
  · norm_num [world12845, agent12845, scalar12845, tp12845, tm12845, ep12845, em12845, dsL]
  · norm_num [world12845, agent12845, scalar12845, tp12845, tm12845, ep12845, em12845, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12845, agent12845, tp12845, tm12845, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12845, agent12845, scalar12845, tp12845, tm12845, ep12845, em12845, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12845, agent12845, tp12845, tm12845, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12845, agent12845, scalar12845, tp12845, tm12845, ep12845, em12845, dsL]

theorem negative12845 :
    Eminus aL (agent12845.root+dsL) scalar12845.worldRadius world12845.frame
      agent12845.frame tm12845 ≤ -em12845 := by
  apply negative_check (lo := (8549070639351134317 / 12500000000000000000)) (hi := (68392565114809074537 / 100000000000000000000))
    (y := (-((71667347099223487463 / 100000000000000000000)))) (u := (48837414759818213541 / 100000000000000000000))
  · norm_num [world12845, agent12845, scalar12845, tp12845, tm12845, ep12845, em12845, dsL]
  · norm_num [world12845, agent12845, scalar12845, tp12845, tm12845, ep12845, em12845, dsL]
  · norm_num [world12845, agent12845, scalar12845, tp12845, tm12845, ep12845, em12845, dsL]
  · norm_num [world12845, agent12845, scalar12845, tp12845, tm12845, ep12845, em12845, dsL]
  · norm_num [world12845, agent12845, scalar12845, tp12845, tm12845, ep12845, em12845, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12845, agent12845, tp12845, tm12845, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12845, agent12845, tp12845, tm12845, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12845, agent12845, scalar12845, tp12845, tm12845, ep12845, em12845, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12845, agent12845, tp12845, tm12845, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12845, agent12845, scalar12845, tp12845, tm12845, ep12845, em12845, dsL]

theorem tails12845 :
    exp (-((12845:ℝ)*ep12845)) ≤ scalar12845.upperTail ∧
    exp (-((12845:ℝ)*em12845)) ≤ scalar12845.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12845:ℝ)) (by norm_num [ep12845]) ?_)
      (show bp12845^8 ≤ scalar12845.upperTail by norm_num [bp12845, scalar12845])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12845, bp12845, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12845:ℝ)) (by norm_num [em12845]) ?_)
      (show bm12845^8 ≤ scalar12845.lowerTail by norm_num [bm12845, scalar12845])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12845, bm12845, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12845 :
    agent12845.root+dsL+scalar12845.worldRadius < √(1/100/aL) ∧
    2*(agent12845.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12845, agent12845, scalar12845, tp12845, tm12845, ep12845, em12845, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12845, agent12845, scalar12845, tp12845, tm12845, ep12845, em12845, dsL]

noncomputable def master12845 : MasterCertificate 12845 world12845 agent12845 :=
  master scalar12845 dsL tp12845 tm12845 ep12845 em12845
    (by norm_num [dsL]) (by norm_num [tp12845]) (by norm_num [tm12845])
    (by norm_num [ep12845]) (by norm_num [em12845])
    positive12845 negative12845 tails12845.1 tails12845.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12845.1 tailGuards12845.2

theorem preserves12845 : master12845.toScalarCertificate = scalar12845 := rfl

noncomputable def tp12846 : ℝ := (465922231 / 2000000000)
noncomputable def tm12846 : ℝ := (-((6091900189 / 10000000000)))
noncomputable def ep12846 : ℝ := (51814504050107593 / 100000000000000000000)
noncomputable def em12846 : ℝ := (12611991758455277 / 25000000000000000000)
noncomputable def bp12846 : ℝ := (10879327469841676147 / 25000000000000000000)
noncomputable def bm12846 : ℝ := (8896554286107348541 / 20000000000000000000)

theorem positive12846 :
    Eplus aL (agent12846.root+dsL) scalar12846.worldRadius world12846.frame
      agent12846.frame tp12846 ≤ -ep12846 := by
  apply positive_check (eT := (28909120267643536383 / 25000000000000000000)) (y := (18981610939487352533 / 50000000000000000000)) (u := (9135918047016118859 / 6250000000000000000))
  · norm_num [world12846, agent12846, scalar12846, tp12846, tm12846, ep12846, em12846, dsL]
  · norm_num [world12846, agent12846, scalar12846, tp12846, tm12846, ep12846, em12846, dsL]
  · norm_num [world12846, agent12846, scalar12846, tp12846, tm12846, ep12846, em12846, dsL]
  · norm_num [world12846, agent12846, scalar12846, tp12846, tm12846, ep12846, em12846, dsL]
  · norm_num [world12846, agent12846, scalar12846, tp12846, tm12846, ep12846, em12846, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12846, agent12846, tp12846, tm12846, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12846, agent12846, scalar12846, tp12846, tm12846, ep12846, em12846, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12846, agent12846, tp12846, tm12846, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12846, agent12846, scalar12846, tp12846, tm12846, ep12846, em12846, dsL]

theorem negative12846 :
    Eminus aL (agent12846.root+dsL) scalar12846.worldRadius world12846.frame
      agent12846.frame tm12846 ≤ -em12846 := by
  apply negative_check (lo := (68392395501677613521 / 100000000000000000000)) (hi := (34196197750838806761 / 50000000000000000000))
    (y := (-((14333471878305195363 / 20000000000000000000)))) (u := (48837408756575832253 / 100000000000000000000))
  · norm_num [world12846, agent12846, scalar12846, tp12846, tm12846, ep12846, em12846, dsL]
  · norm_num [world12846, agent12846, scalar12846, tp12846, tm12846, ep12846, em12846, dsL]
  · norm_num [world12846, agent12846, scalar12846, tp12846, tm12846, ep12846, em12846, dsL]
  · norm_num [world12846, agent12846, scalar12846, tp12846, tm12846, ep12846, em12846, dsL]
  · norm_num [world12846, agent12846, scalar12846, tp12846, tm12846, ep12846, em12846, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12846, agent12846, tp12846, tm12846, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12846, agent12846, tp12846, tm12846, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12846, agent12846, scalar12846, tp12846, tm12846, ep12846, em12846, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12846, agent12846, tp12846, tm12846, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12846, agent12846, scalar12846, tp12846, tm12846, ep12846, em12846, dsL]

theorem tails12846 :
    exp (-((12846:ℝ)*ep12846)) ≤ scalar12846.upperTail ∧
    exp (-((12846:ℝ)*em12846)) ≤ scalar12846.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12846:ℝ)) (by norm_num [ep12846]) ?_)
      (show bp12846^8 ≤ scalar12846.upperTail by norm_num [bp12846, scalar12846])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12846, bp12846, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12846:ℝ)) (by norm_num [em12846]) ?_)
      (show bm12846^8 ≤ scalar12846.lowerTail by norm_num [bm12846, scalar12846])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12846, bm12846, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12846 :
    agent12846.root+dsL+scalar12846.worldRadius < √(1/100/aL) ∧
    2*(agent12846.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12846, agent12846, scalar12846, tp12846, tm12846, ep12846, em12846, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12846, agent12846, scalar12846, tp12846, tm12846, ep12846, em12846, dsL]

noncomputable def master12846 : MasterCertificate 12846 world12846 agent12846 :=
  master scalar12846 dsL tp12846 tm12846 ep12846 em12846
    (by norm_num [dsL]) (by norm_num [tp12846]) (by norm_num [tm12846])
    (by norm_num [ep12846]) (by norm_num [em12846])
    positive12846 negative12846 tails12846.1 tails12846.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12846.1 tailGuards12846.2

theorem preserves12846 : master12846.toScalarCertificate = scalar12846 := rfl

noncomputable def tp12847 : ℝ := (1164845757 / 5000000000)
noncomputable def tm12847 : ℝ := (-((609207201 / 1000000000)))
noncomputable def ep12847 : ℝ := (10363390592444023 / 20000000000000000000)
noncomputable def em12847 : ℝ := (10090011797059041 / 20000000000000000000)
noncomputable def bp12847 : ℝ := (10878195049568619413 / 25000000000000000000)
noncomputable def bm12847 : ℝ := (1111961804918987571 / 2500000000000000000)

theorem positive12847 :
    Eplus aL (agent12847.root+dsL) scalar12847.worldRadius world12847.frame
      agent12847.frame tp12847 ≤ -ep12847 := by
  apply positive_check (eT := (115636696243931268337 / 100000000000000000000)) (y := (37963960457784092437 / 100000000000000000000)) (u := (73087884185760314253 / 50000000000000000000))
  · norm_num [world12847, agent12847, scalar12847, tp12847, tm12847, ep12847, em12847, dsL]
  · norm_num [world12847, agent12847, scalar12847, tp12847, tm12847, ep12847, em12847, dsL]
  · norm_num [world12847, agent12847, scalar12847, tp12847, tm12847, ep12847, em12847, dsL]
  · norm_num [world12847, agent12847, scalar12847, tp12847, tm12847, ep12847, em12847, dsL]
  · norm_num [world12847, agent12847, scalar12847, tp12847, tm12847, ep12847, em12847, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12847, agent12847, tp12847, tm12847, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12847, agent12847, scalar12847, tp12847, tm12847, ep12847, em12847, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12847, agent12847, tp12847, tm12847, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12847, agent12847, scalar12847, tp12847, tm12847, ep12847, em12847, dsL]

theorem negative12847 :
    Eminus aL (agent12847.root+dsL) scalar12847.worldRadius world12847.frame
      agent12847.frame tm12847 ≤ -em12847 := by
  apply negative_check (lo := (68392226134424392217 / 100000000000000000000)) (hi := (34196113067212196109 / 50000000000000000000))
    (y := (-((71667371258090458317 / 100000000000000000000)))) (u := (190771105317396777 / 390625000000000000))
  · norm_num [world12847, agent12847, scalar12847, tp12847, tm12847, ep12847, em12847, dsL]
  · norm_num [world12847, agent12847, scalar12847, tp12847, tm12847, ep12847, em12847, dsL]
  · norm_num [world12847, agent12847, scalar12847, tp12847, tm12847, ep12847, em12847, dsL]
  · norm_num [world12847, agent12847, scalar12847, tp12847, tm12847, ep12847, em12847, dsL]
  · norm_num [world12847, agent12847, scalar12847, tp12847, tm12847, ep12847, em12847, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12847, agent12847, tp12847, tm12847, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12847, agent12847, tp12847, tm12847, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12847, agent12847, scalar12847, tp12847, tm12847, ep12847, em12847, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12847, agent12847, tp12847, tm12847, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12847, agent12847, scalar12847, tp12847, tm12847, ep12847, em12847, dsL]

theorem tails12847 :
    exp (-((12847:ℝ)*ep12847)) ≤ scalar12847.upperTail ∧
    exp (-((12847:ℝ)*em12847)) ≤ scalar12847.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12847:ℝ)) (by norm_num [ep12847]) ?_)
      (show bp12847^8 ≤ scalar12847.upperTail by norm_num [bp12847, scalar12847])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12847, bp12847, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12847:ℝ)) (by norm_num [em12847]) ?_)
      (show bm12847^8 ≤ scalar12847.lowerTail by norm_num [bm12847, scalar12847])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12847, bm12847, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12847 :
    agent12847.root+dsL+scalar12847.worldRadius < √(1/100/aL) ∧
    2*(agent12847.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12847, agent12847, scalar12847, tp12847, tm12847, ep12847, em12847, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12847, agent12847, scalar12847, tp12847, tm12847, ep12847, em12847, dsL]

noncomputable def master12847 : MasterCertificate 12847 world12847 agent12847 :=
  master scalar12847 dsL tp12847 tm12847 ep12847 em12847
    (by norm_num [dsL]) (by norm_num [tp12847]) (by norm_num [tm12847])
    (by norm_num [ep12847]) (by norm_num [em12847])
    positive12847 negative12847 tails12847.1 tails12847.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12847.1 tailGuards12847.2

theorem preserves12847 : master12847.toScalarCertificate = scalar12847 := rfl

noncomputable def tp12848 : ℝ := (465954371 / 2000000000)
noncomputable def tm12848 : ℝ := (-((3046121751 / 5000000000)))
noncomputable def ep12848 : ℝ := (5181940071878347 / 10000000000000000000)
noncomputable def em12848 : ℝ := (50452149874499157 / 100000000000000000000)
noncomputable def bp12848 : ℝ := (43508251529734662993 / 100000000000000000000)
noncomputable def bm12848 : ℝ := (44474173904638159351 / 100000000000000000000)

theorem positive12848 :
    Eplus aL (agent12848.root+dsL) scalar12848.worldRadius world12848.frame
      agent12848.frame tp12848 ≤ -ep12848 := by
  apply positive_check (eT := (115636911320407442649 / 100000000000000000000)) (y := (9491174753926772861 / 25000000000000000000)) (u := (146176847968226159643 / 100000000000000000000))
  · norm_num [world12848, agent12848, scalar12848, tp12848, tm12848, ep12848, em12848, dsL]
  · norm_num [world12848, agent12848, scalar12848, tp12848, tm12848, ep12848, em12848, dsL]
  · norm_num [world12848, agent12848, scalar12848, tp12848, tm12848, ep12848, em12848, dsL]
  · norm_num [world12848, agent12848, scalar12848, tp12848, tm12848, ep12848, em12848, dsL]
  · norm_num [world12848, agent12848, scalar12848, tp12848, tm12848, ep12848, em12848, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12848, agent12848, tp12848, tm12848, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12848, agent12848, scalar12848, tp12848, tm12848, ep12848, em12848, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12848, agent12848, tp12848, tm12848, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12848, agent12848, scalar12848, tp12848, tm12848, ep12848, em12848, dsL]

theorem negative12848 :
    Eminus aL (agent12848.root+dsL) scalar12848.worldRadius world12848.frame
      agent12848.frame tm12848 ≤ -em12848 := by
  apply negative_check (lo := (13678411622675068929 / 20000000000000000000)) (hi := (34196029056687672323 / 50000000000000000000))
    (y := (-((71667380459788545651 / 100000000000000000000)))) (u := (48837398467383407479 / 100000000000000000000))
  · norm_num [world12848, agent12848, scalar12848, tp12848, tm12848, ep12848, em12848, dsL]
  · norm_num [world12848, agent12848, scalar12848, tp12848, tm12848, ep12848, em12848, dsL]
  · norm_num [world12848, agent12848, scalar12848, tp12848, tm12848, ep12848, em12848, dsL]
  · norm_num [world12848, agent12848, scalar12848, tp12848, tm12848, ep12848, em12848, dsL]
  · norm_num [world12848, agent12848, scalar12848, tp12848, tm12848, ep12848, em12848, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12848, agent12848, tp12848, tm12848, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12848, agent12848, tp12848, tm12848, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12848, agent12848, scalar12848, tp12848, tm12848, ep12848, em12848, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12848, agent12848, tp12848, tm12848, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12848, agent12848, scalar12848, tp12848, tm12848, ep12848, em12848, dsL]

theorem tails12848 :
    exp (-((12848:ℝ)*ep12848)) ≤ scalar12848.upperTail ∧
    exp (-((12848:ℝ)*em12848)) ≤ scalar12848.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12848:ℝ)) (by norm_num [ep12848]) ?_)
      (show bp12848^8 ≤ scalar12848.upperTail by norm_num [bp12848, scalar12848])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12848, bp12848, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12848:ℝ)) (by norm_num [em12848]) ?_)
      (show bm12848^8 ≤ scalar12848.lowerTail by norm_num [bm12848, scalar12848])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12848, bm12848, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12848 :
    agent12848.root+dsL+scalar12848.worldRadius < √(1/100/aL) ∧
    2*(agent12848.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12848, agent12848, scalar12848, tp12848, tm12848, ep12848, em12848, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12848, agent12848, scalar12848, tp12848, tm12848, ep12848, em12848, dsL]

noncomputable def master12848 : MasterCertificate 12848 world12848 agent12848 :=
  master scalar12848 dsL tp12848 tm12848 ep12848 em12848
    (by norm_num [dsL]) (by norm_num [tp12848]) (by norm_num [tm12848])
    (by norm_num [ep12848]) (by norm_num [em12848])
    positive12848 negative12848 tails12848.1 tails12848.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12848.1 tailGuards12848.2

theorem preserves12848 : master12848.toScalarCertificate = scalar12848 := rfl

noncomputable def tp12849 : ℝ := (2329852139 / 10000000000)
noncomputable def tm12849 : ℝ := (-((3046207547 / 5000000000)))
noncomputable def ep12849 : ℝ := (51821847651317793 / 100000000000000000000)
noncomputable def em12849 : ℝ := (50454239991512563 / 100000000000000000000)
noncomputable def bp12849 : ℝ := (1740148945683065091 / 4000000000000000000)
noncomputable def bm12849 : ℝ := (889397526939403783 / 2000000000000000000)

theorem positive12849 :
    Eplus aL (agent12849.root+dsL) scalar12849.worldRadius world12849.frame
      agent12849.frame tp12849 ≤ -ep12849 := by
  apply positive_check (eT := (115637126018760705301 / 100000000000000000000)) (y := (3796543697272018387 / 10000000000000000000)) (u := (146177926694507521849 / 100000000000000000000))
  · norm_num [world12849, agent12849, scalar12849, tp12849, tm12849, ep12849, em12849, dsL]
  · norm_num [world12849, agent12849, scalar12849, tp12849, tm12849, ep12849, em12849, dsL]
  · norm_num [world12849, agent12849, scalar12849, tp12849, tm12849, ep12849, em12849, dsL]
  · norm_num [world12849, agent12849, scalar12849, tp12849, tm12849, ep12849, em12849, dsL]
  · norm_num [world12849, agent12849, scalar12849, tp12849, tm12849, ep12849, em12849, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12849, agent12849, tp12849, tm12849, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12849, agent12849, scalar12849, tp12849, tm12849, ep12849, em12849, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12849, agent12849, tp12849, tm12849, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12849, agent12849, scalar12849, tp12849, tm12849, ep12849, em12849, dsL]

theorem negative12849 :
    Eminus aL (agent12849.root+dsL) scalar12849.worldRadius world12849.frame
      agent12849.frame tm12849 ≤ -em12849 := by
  apply negative_check (lo := (34195944804423741919 / 50000000000000000000)) (hi := (68391889608847483839 / 100000000000000000000))
    (y := (-((71667391560038278701 / 100000000000000000000)))) (u := (48837393046310515351 / 100000000000000000000))
  · norm_num [world12849, agent12849, scalar12849, tp12849, tm12849, ep12849, em12849, dsL]
  · norm_num [world12849, agent12849, scalar12849, tp12849, tm12849, ep12849, em12849, dsL]
  · norm_num [world12849, agent12849, scalar12849, tp12849, tm12849, ep12849, em12849, dsL]
  · norm_num [world12849, agent12849, scalar12849, tp12849, tm12849, ep12849, em12849, dsL]
  · norm_num [world12849, agent12849, scalar12849, tp12849, tm12849, ep12849, em12849, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12849, agent12849, tp12849, tm12849, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12849, agent12849, tp12849, tm12849, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12849, agent12849, scalar12849, tp12849, tm12849, ep12849, em12849, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12849, agent12849, tp12849, tm12849, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12849, agent12849, scalar12849, tp12849, tm12849, ep12849, em12849, dsL]

theorem tails12849 :
    exp (-((12849:ℝ)*ep12849)) ≤ scalar12849.upperTail ∧
    exp (-((12849:ℝ)*em12849)) ≤ scalar12849.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12849:ℝ)) (by norm_num [ep12849]) ?_)
      (show bp12849^8 ≤ scalar12849.upperTail by norm_num [bp12849, scalar12849])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12849, bp12849, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12849:ℝ)) (by norm_num [em12849]) ?_)
      (show bm12849^8 ≤ scalar12849.lowerTail by norm_num [bm12849, scalar12849])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12849, bm12849, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12849 :
    agent12849.root+dsL+scalar12849.worldRadius < √(1/100/aL) ∧
    2*(agent12849.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12849, agent12849, scalar12849, tp12849, tm12849, ep12849, em12849, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12849, agent12849, scalar12849, tp12849, tm12849, ep12849, em12849, dsL]

noncomputable def master12849 : MasterCertificate 12849 world12849 agent12849 :=
  master scalar12849 dsL tp12849 tm12849 ep12849 em12849
    (by norm_num [dsL]) (by norm_num [tp12849]) (by norm_num [tm12849])
    (by norm_num [ep12849]) (by norm_num [em12849])
    positive12849 negative12849 tails12849.1 tails12849.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12849.1 tailGuards12849.2

theorem preserves12849 : master12849.toScalarCertificate = scalar12849 := rfl

end BstLean.Part268
