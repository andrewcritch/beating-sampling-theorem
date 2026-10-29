import BstLean.Part261Checker
import BstLean.Part268Scalar13
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12675 : ℝ := (578532871 / 2500000000)
noncomputable def tm12675 : ℝ := (-((6057651171 / 10000000000)))
noncomputable def ep12675 : ℝ := (12838675993227839 / 25000000000000000000)
noncomputable def em12675 : ℝ := (6256080352772069 / 12500000000000000000)
noncomputable def bp12675 : ℝ := (11080920259673389897 / 25000000000000000000)
noncomputable def bm12675 : ℝ := (5656302779440672529 / 12500000000000000000)

theorem positive12675 :
    Eplus aL (agent12675.root+dsL) scalar12675.worldRadius world12675.frame
      agent12675.frame tp12675 ≤ -ep12675 := by
  apply positive_check (eT := (57793799837823122503 / 50000000000000000000)) (y := (1513739692774025711 / 4000000000000000000)) (u := (14599977917126316289 / 10000000000000000000))
  · norm_num [world12675, agent12675, scalar12675, tp12675, tm12675, ep12675, em12675, dsL]
  · norm_num [world12675, agent12675, scalar12675, tp12675, tm12675, ep12675, em12675, dsL]
  · norm_num [world12675, agent12675, scalar12675, tp12675, tm12675, ep12675, em12675, dsL]
  · norm_num [world12675, agent12675, scalar12675, tp12675, tm12675, ep12675, em12675, dsL]
  · norm_num [world12675, agent12675, scalar12675, tp12675, tm12675, ep12675, em12675, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12675, agent12675, tp12675, tm12675, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12675, agent12675, scalar12675, tp12675, tm12675, ep12675, em12675, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12675, agent12675, tp12675, tm12675, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12675, agent12675, scalar12675, tp12675, tm12675, ep12675, em12675, dsL]

theorem negative12675 :
    Eminus aL (agent12675.root+dsL) scalar12675.worldRadius world12675.frame
      agent12675.frame tm12675 ≤ -em12675 := by
  apply negative_check (lo := (8555169688392640393 / 12500000000000000000)) (hi := (13688271501428224629 / 20000000000000000000))
    (y := (-((71691291567066397909 / 100000000000000000000)))) (u := (48825722300650167219 / 100000000000000000000))
  · norm_num [world12675, agent12675, scalar12675, tp12675, tm12675, ep12675, em12675, dsL]
  · norm_num [world12675, agent12675, scalar12675, tp12675, tm12675, ep12675, em12675, dsL]
  · norm_num [world12675, agent12675, scalar12675, tp12675, tm12675, ep12675, em12675, dsL]
  · norm_num [world12675, agent12675, scalar12675, tp12675, tm12675, ep12675, em12675, dsL]
  · norm_num [world12675, agent12675, scalar12675, tp12675, tm12675, ep12675, em12675, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12675, agent12675, tp12675, tm12675, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12675, agent12675, tp12675, tm12675, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12675, agent12675, scalar12675, tp12675, tm12675, ep12675, em12675, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12675, agent12675, tp12675, tm12675, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12675, agent12675, scalar12675, tp12675, tm12675, ep12675, em12675, dsL]

theorem tails12675 :
    exp (-((12675:ℝ)*ep12675)) ≤ scalar12675.upperTail ∧
    exp (-((12675:ℝ)*em12675)) ≤ scalar12675.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12675:ℝ)) (by norm_num [ep12675]) ?_)
      (show bp12675^8 ≤ scalar12675.upperTail by norm_num [bp12675, scalar12675])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12675, bp12675, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12675:ℝ)) (by norm_num [em12675]) ?_)
      (show bm12675^8 ≤ scalar12675.lowerTail by norm_num [bm12675, scalar12675])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12675, bm12675, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12675 :
    agent12675.root+dsL+scalar12675.worldRadius < √(1/100/aL) ∧
    2*(agent12675.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12675, agent12675, scalar12675, tp12675, tm12675, ep12675, em12675, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12675, agent12675, scalar12675, tp12675, tm12675, ep12675, em12675, dsL]

noncomputable def master12675 : MasterCertificate 12675 world12675 agent12675 :=
  master scalar12675 dsL tp12675 tm12675 ep12675 em12675
    (by norm_num [dsL]) (by norm_num [tp12675]) (by norm_num [tm12675])
    (by norm_num [ep12675]) (by norm_num [em12675])
    positive12675 negative12675 tails12675.1 tails12675.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12675.1 tailGuards12675.2

theorem preserves12675 : master12675.toScalarCertificate = scalar12675 := rfl

noncomputable def tp12676 : ℝ := (462843493 / 2000000000)
noncomputable def tm12676 : ℝ := (-((1514458981 / 2500000000)))
noncomputable def ep12676 : ℝ := (25678677043022919 / 50000000000000000000)
noncomputable def em12676 : ℝ := (50050917384241323 / 100000000000000000000)
noncomputable def bp12676 : ℝ := (44318974804084581079 / 100000000000000000000)
noncomputable def bm12676 : ℝ := (45245960707767290353 / 100000000000000000000)

theorem positive12676 :
    Eplus aL (agent12676.root+dsL) scalar12676.worldRadius world12676.frame
      agent12676.frame tp12676 ≤ -ep12676 := by
  apply positive_check (eT := (4623514001137907047 / 4000000000000000000)) (y := (9461074108483340721 / 25000000000000000000)) (u := (146000953181498405599 / 100000000000000000000))
  · norm_num [world12676, agent12676, scalar12676, tp12676, tm12676, ep12676, em12676, dsL]
  · norm_num [world12676, agent12676, scalar12676, tp12676, tm12676, ep12676, em12676, dsL]
  · norm_num [world12676, agent12676, scalar12676, tp12676, tm12676, ep12676, em12676, dsL]
  · norm_num [world12676, agent12676, scalar12676, tp12676, tm12676, ep12676, em12676, dsL]
  · norm_num [world12676, agent12676, scalar12676, tp12676, tm12676, ep12676, em12676, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12676, agent12676, tp12676, tm12676, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12676, agent12676, scalar12676, tp12676, tm12676, ep12676, em12676, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12676, agent12676, tp12676, tm12676, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12676, agent12676, scalar12676, tp12676, tm12676, ep12676, em12676, dsL]

theorem negative12676 :
    Eminus aL (agent12676.root+dsL) scalar12676.worldRadius world12676.frame
      agent12676.frame tm12676 ≤ -em12676 := by
  apply negative_check (lo := (68441142194932274947 / 100000000000000000000)) (hi := (17110285548733068737 / 25000000000000000000))
    (y := (-((71691378968918870401 / 100000000000000000000)))) (u := (38145062207877377 / 78125000000000000))
  · norm_num [world12676, agent12676, scalar12676, tp12676, tm12676, ep12676, em12676, dsL]
  · norm_num [world12676, agent12676, scalar12676, tp12676, tm12676, ep12676, em12676, dsL]
  · norm_num [world12676, agent12676, scalar12676, tp12676, tm12676, ep12676, em12676, dsL]
  · norm_num [world12676, agent12676, scalar12676, tp12676, tm12676, ep12676, em12676, dsL]
  · norm_num [world12676, agent12676, scalar12676, tp12676, tm12676, ep12676, em12676, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12676, agent12676, tp12676, tm12676, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12676, agent12676, tp12676, tm12676, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12676, agent12676, scalar12676, tp12676, tm12676, ep12676, em12676, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12676, agent12676, tp12676, tm12676, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12676, agent12676, scalar12676, tp12676, tm12676, ep12676, em12676, dsL]

theorem tails12676 :
    exp (-((12676:ℝ)*ep12676)) ≤ scalar12676.upperTail ∧
    exp (-((12676:ℝ)*em12676)) ≤ scalar12676.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12676:ℝ)) (by norm_num [ep12676]) ?_)
      (show bp12676^8 ≤ scalar12676.upperTail by norm_num [bp12676, scalar12676])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12676, bp12676, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12676:ℝ)) (by norm_num [em12676]) ?_)
      (show bm12676^8 ≤ scalar12676.lowerTail by norm_num [bm12676, scalar12676])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12676, bm12676, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12676 :
    agent12676.root+dsL+scalar12676.worldRadius < √(1/100/aL) ∧
    2*(agent12676.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12676, agent12676, scalar12676, tp12676, tm12676, ep12676, em12676, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12676, agent12676, scalar12676, tp12676, tm12676, ep12676, em12676, dsL]

noncomputable def master12676 : MasterCertificate 12676 world12676 agent12676 :=
  master scalar12676 dsL tp12676 tm12676 ep12676 em12676
    (by norm_num [dsL]) (by norm_num [tp12676]) (by norm_num [tm12676])
    (by norm_num [ep12676]) (by norm_num [em12676])
    positive12676 negative12676 tails12676.1 tails12676.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12676.1 tailGuards12676.2

theorem preserves12676 : master12676.toScalarCertificate = scalar12676 := rfl

noncomputable def tp12677 : ℝ := (1157151787 / 5000000000)
noncomputable def tm12677 : ℝ := (-((605802039 / 1000000000)))
noncomputable def ep12677 : ℝ := (6420000501624519 / 12500000000000000000)
noncomputable def em12677 : ℝ := (50053191799289853 / 100000000000000000000)
noncomputable def bp12677 : ℝ := (22157134453162311649 / 50000000000000000000)
noncomputable def bm12677 : ℝ := (5655187433504414907 / 12500000000000000000)

theorem positive12677 :
    Eplus aL (agent12677.root+dsL) scalar12677.worldRadius world12677.frame
      agent12677.frame tp12677 ≤ -ep12677 := by
  apply positive_check (eT := (23117620268011687007 / 20000000000000000000)) (y := (9461275717388099959 / 25000000000000000000)) (u := (73001065294968254399 / 50000000000000000000))
  · norm_num [world12677, agent12677, scalar12677, tp12677, tm12677, ep12677, em12677, dsL]
  · norm_num [world12677, agent12677, scalar12677, tp12677, tm12677, ep12677, em12677, dsL]
  · norm_num [world12677, agent12677, scalar12677, tp12677, tm12677, ep12677, em12677, dsL]
  · norm_num [world12677, agent12677, scalar12677, tp12677, tm12677, ep12677, em12677, dsL]
  · norm_num [world12677, agent12677, scalar12677, tp12677, tm12677, ep12677, em12677, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12677, agent12677, tp12677, tm12677, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12677, agent12677, scalar12677, tp12677, tm12677, ep12677, em12677, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12677, agent12677, tp12677, tm12677, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12677, agent12677, scalar12677, tp12677, tm12677, ep12677, em12677, dsL]

theorem negative12677 :
    Eminus aL (agent12677.root+dsL) scalar12677.worldRadius world12677.frame
      agent12677.frame tm12677 ≤ -em12677 := by
  apply negative_check (lo := (8555116006924688471 / 12500000000000000000)) (hi := (68440928055397507769 / 100000000000000000000))
    (y := (-((71691464116954114577 / 100000000000000000000)))) (u := (48825638051993846097 / 100000000000000000000))
  · norm_num [world12677, agent12677, scalar12677, tp12677, tm12677, ep12677, em12677, dsL]
  · norm_num [world12677, agent12677, scalar12677, tp12677, tm12677, ep12677, em12677, dsL]
  · norm_num [world12677, agent12677, scalar12677, tp12677, tm12677, ep12677, em12677, dsL]
  · norm_num [world12677, agent12677, scalar12677, tp12677, tm12677, ep12677, em12677, dsL]
  · norm_num [world12677, agent12677, scalar12677, tp12677, tm12677, ep12677, em12677, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12677, agent12677, tp12677, tm12677, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12677, agent12677, tp12677, tm12677, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12677, agent12677, scalar12677, tp12677, tm12677, ep12677, em12677, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12677, agent12677, tp12677, tm12677, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12677, agent12677, scalar12677, tp12677, tm12677, ep12677, em12677, dsL]

theorem tails12677 :
    exp (-((12677:ℝ)*ep12677)) ≤ scalar12677.upperTail ∧
    exp (-((12677:ℝ)*em12677)) ≤ scalar12677.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12677:ℝ)) (by norm_num [ep12677]) ?_)
      (show bp12677^8 ≤ scalar12677.upperTail by norm_num [bp12677, scalar12677])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12677, bp12677, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12677:ℝ)) (by norm_num [em12677]) ?_)
      (show bm12677^8 ≤ scalar12677.lowerTail by norm_num [bm12677, scalar12677])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12677, bm12677, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12677 :
    agent12677.root+dsL+scalar12677.worldRadius < √(1/100/aL) ∧
    2*(agent12677.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12677, agent12677, scalar12677, tp12677, tm12677, ep12677, em12677, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12677, agent12677, scalar12677, tp12677, tm12677, ep12677, em12677, dsL]

noncomputable def master12677 : MasterCertificate 12677 world12677 agent12677 :=
  master scalar12677 dsL tp12677 tm12677 ep12677 em12677
    (by norm_num [dsL]) (by norm_num [tp12677]) (by norm_num [tm12677])
    (by norm_num [ep12677]) (by norm_num [em12677])
    positive12677 negative12677 tails12677.1 tails12677.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12677.1 tailGuards12677.2

theorem preserves12677 : master12677.toScalarCertificate = scalar12677 := rfl

noncomputable def tp12678 : ℝ := (46287791 / 200000000)
noncomputable def tm12678 : ℝ := (-((6058204903 / 10000000000)))
noncomputable def ep12678 : ℝ := (25681325792727387 / 50000000000000000000)
noncomputable def em12678 : ℝ := (50055464027024719 / 100000000000000000000)
noncomputable def bp12678 : ℝ := (22154782434009957589 / 50000000000000000000)
noncomputable def bm12678 : ℝ := (9047407995806579051 / 20000000000000000000)

theorem positive12678 :
    Eplus aL (agent12678.root+dsL) scalar12678.worldRadius world12678.frame
      agent12678.frame tp12678 ≤ -ep12678 := by
  apply positive_check (eT := (115588351722056910963 / 100000000000000000000)) (y := (151383630161983523 / 400000000000000000)) (u := (73001652715692513311 / 50000000000000000000))
  · norm_num [world12678, agent12678, scalar12678, tp12678, tm12678, ep12678, em12678, dsL]
  · norm_num [world12678, agent12678, scalar12678, tp12678, tm12678, ep12678, em12678, dsL]
  · norm_num [world12678, agent12678, scalar12678, tp12678, tm12678, ep12678, em12678, dsL]
  · norm_num [world12678, agent12678, scalar12678, tp12678, tm12678, ep12678, em12678, dsL]
  · norm_num [world12678, agent12678, scalar12678, tp12678, tm12678, ep12678, em12678, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12678, agent12678, tp12678, tm12678, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12678, agent12678, scalar12678, tp12678, tm12678, ep12678, em12678, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12678, agent12678, tp12678, tm12678, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12678, agent12678, scalar12678, tp12678, tm12678, ep12678, em12678, dsL]

theorem negative12678 :
    Eminus aL (agent12678.root+dsL) scalar12678.worldRadius world12678.frame
      agent12678.frame tm12678 ≤ -em12678 := by
  apply negative_check (lo := (34220356828823500933 / 50000000000000000000)) (hi := (68440713657647001867 / 100000000000000000000))
    (y := (-((35845775161740323941 / 50000000000000000000)))) (u := (4882559596112536629 / 10000000000000000000))
  · norm_num [world12678, agent12678, scalar12678, tp12678, tm12678, ep12678, em12678, dsL]
  · norm_num [world12678, agent12678, scalar12678, tp12678, tm12678, ep12678, em12678, dsL]
  · norm_num [world12678, agent12678, scalar12678, tp12678, tm12678, ep12678, em12678, dsL]
  · norm_num [world12678, agent12678, scalar12678, tp12678, tm12678, ep12678, em12678, dsL]
  · norm_num [world12678, agent12678, scalar12678, tp12678, tm12678, ep12678, em12678, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12678, agent12678, tp12678, tm12678, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12678, agent12678, tp12678, tm12678, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12678, agent12678, scalar12678, tp12678, tm12678, ep12678, em12678, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12678, agent12678, tp12678, tm12678, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12678, agent12678, scalar12678, tp12678, tm12678, ep12678, em12678, dsL]

theorem tails12678 :
    exp (-((12678:ℝ)*ep12678)) ≤ scalar12678.upperTail ∧
    exp (-((12678:ℝ)*em12678)) ≤ scalar12678.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12678:ℝ)) (by norm_num [ep12678]) ?_)
      (show bp12678^8 ≤ scalar12678.upperTail by norm_num [bp12678, scalar12678])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12678, bp12678, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12678:ℝ)) (by norm_num [em12678]) ?_)
      (show bm12678^8 ≤ scalar12678.lowerTail by norm_num [bm12678, scalar12678])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12678, bm12678, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12678 :
    agent12678.root+dsL+scalar12678.worldRadius < √(1/100/aL) ∧
    2*(agent12678.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12678, agent12678, scalar12678, tp12678, tm12678, ep12678, em12678, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12678, agent12678, scalar12678, tp12678, tm12678, ep12678, em12678, dsL]

noncomputable def master12678 : MasterCertificate 12678 world12678 agent12678 :=
  master scalar12678 dsL tp12678 tm12678 ep12678 em12678
    (by norm_num [dsL]) (by norm_num [tp12678]) (by norm_num [tm12678])
    (by norm_num [ep12678]) (by norm_num [em12678])
    positive12678 negative12678 tails12678.1 tails12678.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12678.1 tailGuards12678.2

theorem preserves12678 : master12678.toScalarCertificate = scalar12678 := rfl

noncomputable def tp12679 : ℝ := (2314475469 / 10000000000)
noncomputable def tm12679 : ℝ := (-((605838919 / 1000000000)))
noncomputable def ep12679 : ℝ := (12841324475083253 / 25000000000000000000)
noncomputable def em12679 : ℝ := (50057735105506763 / 100000000000000000000)
noncomputable def bp12679 : ℝ := (44304861918850007903 / 100000000000000000000)
noncomputable def bm12679 : ℝ := (45232581496535094521 / 100000000000000000000)

theorem positive12679 :
    Eplus aL (agent12679.root+dsL) scalar12679.worldRadius world12679.frame
      agent12679.frame tp12679 ≤ -ep12679 := by
  apply positive_check (eT := (115588601724386764471 / 100000000000000000000)) (y := (37846711633864825953 / 100000000000000000000)) (u := (18250559929875311697 / 12500000000000000000))
  · norm_num [world12679, agent12679, scalar12679, tp12679, tm12679, ep12679, em12679, dsL]
  · norm_num [world12679, agent12679, scalar12679, tp12679, tm12679, ep12679, em12679, dsL]
  · norm_num [world12679, agent12679, scalar12679, tp12679, tm12679, ep12679, em12679, dsL]
  · norm_num [world12679, agent12679, scalar12679, tp12679, tm12679, ep12679, em12679, dsL]
  · norm_num [world12679, agent12679, scalar12679, tp12679, tm12679, ep12679, em12679, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12679, agent12679, tp12679, tm12679, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12679, agent12679, scalar12679, tp12679, tm12679, ep12679, em12679, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12679, agent12679, tp12679, tm12679, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12679, agent12679, scalar12679, tp12679, tm12679, ep12679, em12679, dsL]

theorem negative12679 :
    Eminus aL (agent12679.root+dsL) scalar12679.worldRadius world12679.frame
      agent12679.frame tm12679 ≤ -em12679 := by
  apply negative_check (lo := (68440500171127735283 / 100000000000000000000)) (hi := (17110125042781933821 / 25000000000000000000))
    (y := (-((7169163531264674073 / 10000000000000000000)))) (u := (12206388616169038203 / 25000000000000000000))
  · norm_num [world12679, agent12679, scalar12679, tp12679, tm12679, ep12679, em12679, dsL]
  · norm_num [world12679, agent12679, scalar12679, tp12679, tm12679, ep12679, em12679, dsL]
  · norm_num [world12679, agent12679, scalar12679, tp12679, tm12679, ep12679, em12679, dsL]
  · norm_num [world12679, agent12679, scalar12679, tp12679, tm12679, ep12679, em12679, dsL]
  · norm_num [world12679, agent12679, scalar12679, tp12679, tm12679, ep12679, em12679, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12679, agent12679, tp12679, tm12679, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12679, agent12679, tp12679, tm12679, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12679, agent12679, scalar12679, tp12679, tm12679, ep12679, em12679, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12679, agent12679, tp12679, tm12679, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12679, agent12679, scalar12679, tp12679, tm12679, ep12679, em12679, dsL]

theorem tails12679 :
    exp (-((12679:ℝ)*ep12679)) ≤ scalar12679.upperTail ∧
    exp (-((12679:ℝ)*em12679)) ≤ scalar12679.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12679:ℝ)) (by norm_num [ep12679]) ?_)
      (show bp12679^8 ≤ scalar12679.upperTail by norm_num [bp12679, scalar12679])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12679, bp12679, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12679:ℝ)) (by norm_num [em12679]) ?_)
      (show bm12679^8 ≤ scalar12679.lowerTail by norm_num [bm12679, scalar12679])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12679, bm12679, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12679 :
    agent12679.root+dsL+scalar12679.worldRadius < √(1/100/aL) ∧
    2*(agent12679.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12679, agent12679, scalar12679, tp12679, tm12679, ep12679, em12679, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12679, agent12679, scalar12679, tp12679, tm12679, ep12679, em12679, dsL]

noncomputable def master12679 : MasterCertificate 12679 world12679 agent12679 :=
  master scalar12679 dsL tp12679 tm12679 ep12679 em12679
    (by norm_num [dsL]) (by norm_num [tp12679]) (by norm_num [tm12679])
    (by norm_num [ep12679]) (by norm_num [em12679])
    positive12679 negative12679 tails12679.1 tails12679.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12679.1 tailGuards12679.2

theorem preserves12679 : master12679.toScalarCertificate = scalar12679 := rfl

noncomputable def tp12680 : ℝ := (462927181 / 2000000000)
noncomputable def tm12680 : ℝ := (-((189337471 / 312500000)))
noncomputable def ep12680 : ℝ := (25684684893343891 / 50000000000000000000)
noncomputable def em12680 : ℝ := (25030779468193407 / 50000000000000000000)
noncomputable def bp12680 : ℝ := (1384348694104229347 / 3125000000000000000)
noncomputable def bm12680 : ℝ := (45227010095346775227 / 100000000000000000000)

theorem positive12680 :
    Eplus aL (agent12680.root+dsL) scalar12680.worldRadius world12680.frame
      agent12680.frame tp12680 ≤ -ep12680 := by
  apply positive_check (eT := (57794695436351801013 / 50000000000000000000)) (y := (9461697334498128707 / 25000000000000000000)) (u := (146004592890553706599 / 100000000000000000000))
  · norm_num [world12680, agent12680, scalar12680, tp12680, tm12680, ep12680, em12680, dsL]
  · norm_num [world12680, agent12680, scalar12680, tp12680, tm12680, ep12680, em12680, dsL]
  · norm_num [world12680, agent12680, scalar12680, tp12680, tm12680, ep12680, em12680, dsL]
  · norm_num [world12680, agent12680, scalar12680, tp12680, tm12680, ep12680, em12680, dsL]
  · norm_num [world12680, agent12680, scalar12680, tp12680, tm12680, ep12680, em12680, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12680, agent12680, tp12680, tm12680, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12680, agent12680, scalar12680, tp12680, tm12680, ep12680, em12680, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12680, agent12680, tp12680, tm12680, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12680, agent12680, scalar12680, tp12680, tm12680, ep12680, em12680, dsL]

theorem negative12680 :
    Eminus aL (agent12680.root+dsL) scalar12680.worldRadius world12680.frame
      agent12680.frame tm12680 ≤ -em12680 := by
  apply negative_check (lo := (34219660126073928961 / 50000000000000000000)) (hi := (68439320252147857923 / 100000000000000000000))
    (y := (-((35844906431395771401 / 50000000000000000000)))) (u := (9765288858806223231 / 20000000000000000000))
  · norm_num [world12680, agent12680, scalar12680, tp12680, tm12680, ep12680, em12680, dsL]
  · norm_num [world12680, agent12680, scalar12680, tp12680, tm12680, ep12680, em12680, dsL]
  · norm_num [world12680, agent12680, scalar12680, tp12680, tm12680, ep12680, em12680, dsL]
  · norm_num [world12680, agent12680, scalar12680, tp12680, tm12680, ep12680, em12680, dsL]
  · norm_num [world12680, agent12680, scalar12680, tp12680, tm12680, ep12680, em12680, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12680, agent12680, tp12680, tm12680, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12680, agent12680, tp12680, tm12680, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12680, agent12680, scalar12680, tp12680, tm12680, ep12680, em12680, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12680, agent12680, tp12680, tm12680, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12680, agent12680, scalar12680, tp12680, tm12680, ep12680, em12680, dsL]

theorem tails12680 :
    exp (-((12680:ℝ)*ep12680)) ≤ scalar12680.upperTail ∧
    exp (-((12680:ℝ)*em12680)) ≤ scalar12680.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12680:ℝ)) (by norm_num [ep12680]) ?_)
      (show bp12680^8 ≤ scalar12680.upperTail by norm_num [bp12680, scalar12680])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12680, bp12680, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12680:ℝ)) (by norm_num [em12680]) ?_)
      (show bm12680^8 ≤ scalar12680.lowerTail by norm_num [bm12680, scalar12680])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12680, bm12680, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12680 :
    agent12680.root+dsL+scalar12680.worldRadius < √(1/100/aL) ∧
    2*(agent12680.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12680, agent12680, scalar12680, tp12680, tm12680, ep12680, em12680, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12680, agent12680, scalar12680, tp12680, tm12680, ep12680, em12680, dsL]

noncomputable def master12680 : MasterCertificate 12680 world12680 agent12680 :=
  master scalar12680 dsL tp12680 tm12680 ep12680 em12680
    (by norm_num [dsL]) (by norm_num [tp12680]) (by norm_num [tm12680])
    (by norm_num [ep12680]) (by norm_num [em12680])
    positive12680 negative12680 tails12680.1 tails12680.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12680.1 tailGuards12680.2

theorem preserves12680 : master12680.toScalarCertificate = scalar12680 := rfl

noncomputable def tp12681 : ℝ := (1157360873 / 5000000000)
noncomputable def tm12681 : ℝ := (-((9694373 / 16000000)))
noncomputable def ep12681 : ℝ := (5137201336531733 / 10000000000000000000)
noncomputable def em12681 : ℝ := (25031913732128837 / 50000000000000000000)
noncomputable def bp12681 : ℝ := (4429445762287724729 / 10000000000000000000)
noncomputable def bm12681 : ℝ := (5652819228555902941 / 12500000000000000000)

theorem positive12681 :
    Eplus aL (agent12681.root+dsL) scalar12681.worldRadius world12681.frame
      agent12681.frame tp12681 ≤ -ep12681 := by
  apply positive_check (eT := (18060881307077739 / 15625000000000000)) (y := (3784759282255709991 / 10000000000000000000)) (u := (146005766019634116717 / 100000000000000000000))
  · norm_num [world12681, agent12681, scalar12681, tp12681, tm12681, ep12681, em12681, dsL]
  · norm_num [world12681, agent12681, scalar12681, tp12681, tm12681, ep12681, em12681, dsL]
  · norm_num [world12681, agent12681, scalar12681, tp12681, tm12681, ep12681, em12681, dsL]
  · norm_num [world12681, agent12681, scalar12681, tp12681, tm12681, ep12681, em12681, dsL]
  · norm_num [world12681, agent12681, scalar12681, tp12681, tm12681, ep12681, em12681, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12681, agent12681, tp12681, tm12681, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12681, agent12681, scalar12681, tp12681, tm12681, ep12681, em12681, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12681, agent12681, tp12681, tm12681, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12681, agent12681, scalar12681, tp12681, tm12681, ep12681, em12681, dsL]

theorem negative12681 :
    Eminus aL (agent12681.root+dsL) scalar12681.worldRadius world12681.frame
      agent12681.frame tm12681 ≤ -em12681 := by
  apply negative_check (lo := (68439107678696823367 / 100000000000000000000)) (hi := (8554888459837102921 / 12500000000000000000))
    (y := (-((71689896764026266923 / 100000000000000000000)))) (u := (24413201664029333529 / 50000000000000000000))
  · norm_num [world12681, agent12681, scalar12681, tp12681, tm12681, ep12681, em12681, dsL]
  · norm_num [world12681, agent12681, scalar12681, tp12681, tm12681, ep12681, em12681, dsL]
  · norm_num [world12681, agent12681, scalar12681, tp12681, tm12681, ep12681, em12681, dsL]
  · norm_num [world12681, agent12681, scalar12681, tp12681, tm12681, ep12681, em12681, dsL]
  · norm_num [world12681, agent12681, scalar12681, tp12681, tm12681, ep12681, em12681, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12681, agent12681, tp12681, tm12681, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12681, agent12681, tp12681, tm12681, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12681, agent12681, scalar12681, tp12681, tm12681, ep12681, em12681, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12681, agent12681, tp12681, tm12681, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12681, agent12681, scalar12681, tp12681, tm12681, ep12681, em12681, dsL]

theorem tails12681 :
    exp (-((12681:ℝ)*ep12681)) ≤ scalar12681.upperTail ∧
    exp (-((12681:ℝ)*em12681)) ≤ scalar12681.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12681:ℝ)) (by norm_num [ep12681]) ?_)
      (show bp12681^8 ≤ scalar12681.upperTail by norm_num [bp12681, scalar12681])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12681, bp12681, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12681:ℝ)) (by norm_num [em12681]) ?_)
      (show bm12681^8 ≤ scalar12681.lowerTail by norm_num [bm12681, scalar12681])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12681, bm12681, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12681 :
    agent12681.root+dsL+scalar12681.worldRadius < √(1/100/aL) ∧
    2*(agent12681.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12681, agent12681, scalar12681, tp12681, tm12681, ep12681, em12681, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12681, agent12681, scalar12681, tp12681, tm12681, ep12681, em12681, dsL]

noncomputable def master12681 : MasterCertificate 12681 world12681 agent12681 :=
  master scalar12681 dsL tp12681 tm12681 ep12681 em12681
    (by norm_num [dsL]) (by norm_num [tp12681]) (by norm_num [tm12681])
    (by norm_num [ep12681]) (by norm_num [em12681])
    positive12681 negative12681 tails12681.1 tails12681.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12681.1 tailGuards12681.2

theorem preserves12681 : master12681.toScalarCertificate = scalar12681 := rfl

noncomputable def tp12682 : ℝ := (1157403781 / 5000000000)
noncomputable def tm12682 : ℝ := (-((6059167119 / 10000000000)))
noncomputable def ep12682 : ℝ := (10274931201569793 / 20000000000000000000)
noncomputable def em12682 : ℝ := (10013219023430283 / 20000000000000000000)
noncomputable def bp12682 : ℝ := (5536219737215996767 / 12500000000000000000)
noncomputable def bm12682 : ℝ := (45218098371383258323 / 100000000000000000000)

theorem positive12682 :
    Eplus aL (agent12682.root+dsL) scalar12682.worldRadius world12682.frame
      agent12682.frame tp12682 ≤ -ep12682 := by
  apply positive_check (eT := (115589889709731051651 / 100000000000000000000)) (y := (37848396292114720777 / 100000000000000000000)) (u := (146006939136229266677 / 100000000000000000000))
  · norm_num [world12682, agent12682, scalar12682, tp12682, tm12682, ep12682, em12682, dsL]
  · norm_num [world12682, agent12682, scalar12682, tp12682, tm12682, ep12682, em12682, dsL]
  · norm_num [world12682, agent12682, scalar12682, tp12682, tm12682, ep12682, em12682, dsL]
  · norm_num [world12682, agent12682, scalar12682, tp12682, tm12682, ep12682, em12682, dsL]
  · norm_num [world12682, agent12682, scalar12682, tp12682, tm12682, ep12682, em12682, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12682, agent12682, tp12682, tm12682, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12682, agent12682, scalar12682, tp12682, tm12682, ep12682, em12682, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12682, agent12682, tp12682, tm12682, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12682, agent12682, scalar12682, tp12682, tm12682, ep12682, em12682, dsL]

theorem negative12682 :
    Eminus aL (agent12682.root+dsL) scalar12682.worldRadius world12682.frame
      agent12682.frame tm12682 ≤ -em12682 := by
  apply negative_check (lo := (68438895301055571509 / 100000000000000000000)) (hi := (6843889530105557151 / 10000000000000000000))
    (y := (-((17922495268861802387 / 25000000000000000000)))) (u := (48826362161841579909 / 100000000000000000000))
  · norm_num [world12682, agent12682, scalar12682, tp12682, tm12682, ep12682, em12682, dsL]
  · norm_num [world12682, agent12682, scalar12682, tp12682, tm12682, ep12682, em12682, dsL]
  · norm_num [world12682, agent12682, scalar12682, tp12682, tm12682, ep12682, em12682, dsL]
  · norm_num [world12682, agent12682, scalar12682, tp12682, tm12682, ep12682, em12682, dsL]
  · norm_num [world12682, agent12682, scalar12682, tp12682, tm12682, ep12682, em12682, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12682, agent12682, tp12682, tm12682, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12682, agent12682, tp12682, tm12682, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12682, agent12682, scalar12682, tp12682, tm12682, ep12682, em12682, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12682, agent12682, tp12682, tm12682, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12682, agent12682, scalar12682, tp12682, tm12682, ep12682, em12682, dsL]

theorem tails12682 :
    exp (-((12682:ℝ)*ep12682)) ≤ scalar12682.upperTail ∧
    exp (-((12682:ℝ)*em12682)) ≤ scalar12682.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12682:ℝ)) (by norm_num [ep12682]) ?_)
      (show bp12682^8 ≤ scalar12682.upperTail by norm_num [bp12682, scalar12682])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12682, bp12682, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12682:ℝ)) (by norm_num [em12682]) ?_)
      (show bm12682^8 ≤ scalar12682.lowerTail by norm_num [bm12682, scalar12682])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12682, bm12682, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12682 :
    agent12682.root+dsL+scalar12682.worldRadius < √(1/100/aL) ∧
    2*(agent12682.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12682, agent12682, scalar12682, tp12682, tm12682, ep12682, em12682, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12682, agent12682, scalar12682, tp12682, tm12682, ep12682, em12682, dsL]

noncomputable def master12682 : MasterCertificate 12682 world12682 agent12682 :=
  master scalar12682 dsL tp12682 tm12682 ep12682 em12682
    (by norm_num [dsL]) (by norm_num [tp12682]) (by norm_num [tm12682])
    (by norm_num [ep12682]) (by norm_num [em12682])
    positive12682 negative12682 tails12682.1 tails12682.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12682.1 tailGuards12682.2

theorem preserves12682 : master12682.toScalarCertificate = scalar12682 := rfl

noncomputable def tp12683 : ℝ := (1157446669 / 5000000000)
noncomputable def tm12683 : ℝ := (-((6059351203 / 10000000000)))
noncomputable def ep12683 : ℝ := (25688648690134253 / 50000000000000000000)
noncomputable def em12683 : ℝ := (6258545200415051 / 12500000000000000000)
noncomputable def bp12683 : ℝ := (22142529635190058607 / 50000000000000000000)
noncomputable def bm12683 : ℝ := (45213643933276780701 / 100000000000000000000)

theorem positive12683 :
    Eplus aL (agent12683.root+dsL) scalar12683.worldRadius world12683.frame
      agent12683.frame tp12683 ≤ -ep12683 := by
  apply positive_check (eT := (115590138797479851423 / 100000000000000000000)) (y := (9462299845062225393 / 25000000000000000000)) (u := (36502027926335231427 / 25000000000000000000))
  · norm_num [world12683, agent12683, scalar12683, tp12683, tm12683, ep12683, em12683, dsL]
  · norm_num [world12683, agent12683, scalar12683, tp12683, tm12683, ep12683, em12683, dsL]
  · norm_num [world12683, agent12683, scalar12683, tp12683, tm12683, ep12683, em12683, dsL]
  · norm_num [world12683, agent12683, scalar12683, tp12683, tm12683, ep12683, em12683, dsL]
  · norm_num [world12683, agent12683, scalar12683, tp12683, tm12683, ep12683, em12683, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12683, agent12683, tp12683, tm12683, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12683, agent12683, scalar12683, tp12683, tm12683, ep12683, em12683, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12683, agent12683, tp12683, tm12683, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12683, agent12683, scalar12683, tp12683, tm12683, ep12683, em12683, dsL]

theorem negative12683 :
    Eminus aL (agent12683.root+dsL) scalar12683.worldRadius world12683.frame
      agent12683.frame tm12683 ≤ -em12683 := by
  apply negative_check (lo := (6843868248102388271 / 10000000000000000000)) (hi := (68438682481023882711 / 100000000000000000000))
    (y := (-((71690066830793572041 / 100000000000000000000)))) (u := (24413160145321772607 / 50000000000000000000))
  · norm_num [world12683, agent12683, scalar12683, tp12683, tm12683, ep12683, em12683, dsL]
  · norm_num [world12683, agent12683, scalar12683, tp12683, tm12683, ep12683, em12683, dsL]
  · norm_num [world12683, agent12683, scalar12683, tp12683, tm12683, ep12683, em12683, dsL]
  · norm_num [world12683, agent12683, scalar12683, tp12683, tm12683, ep12683, em12683, dsL]
  · norm_num [world12683, agent12683, scalar12683, tp12683, tm12683, ep12683, em12683, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12683, agent12683, tp12683, tm12683, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12683, agent12683, tp12683, tm12683, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12683, agent12683, scalar12683, tp12683, tm12683, ep12683, em12683, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12683, agent12683, tp12683, tm12683, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12683, agent12683, scalar12683, tp12683, tm12683, ep12683, em12683, dsL]

theorem tails12683 :
    exp (-((12683:ℝ)*ep12683)) ≤ scalar12683.upperTail ∧
    exp (-((12683:ℝ)*em12683)) ≤ scalar12683.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12683:ℝ)) (by norm_num [ep12683]) ?_)
      (show bp12683^8 ≤ scalar12683.upperTail by norm_num [bp12683, scalar12683])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12683, bp12683, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12683:ℝ)) (by norm_num [em12683]) ?_)
      (show bm12683^8 ≤ scalar12683.lowerTail by norm_num [bm12683, scalar12683])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12683, bm12683, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12683 :
    agent12683.root+dsL+scalar12683.worldRadius < √(1/100/aL) ∧
    2*(agent12683.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12683, agent12683, scalar12683, tp12683, tm12683, ep12683, em12683, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12683, agent12683, scalar12683, tp12683, tm12683, ep12683, em12683, dsL]

noncomputable def master12683 : MasterCertificate 12683 world12683 agent12683 :=
  master scalar12683 dsL tp12683 tm12683 ep12683 em12683
    (by norm_num [dsL]) (by norm_num [tp12683]) (by norm_num [tm12683])
    (by norm_num [ep12683]) (by norm_num [em12683])
    positive12683 negative12683 tails12683.1 tails12683.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12683.1 tailGuards12683.2

theorem preserves12683 : master12683.toScalarCertificate = scalar12683 := rfl

noncomputable def tp12684 : ℝ := (2314979033 / 10000000000)
noncomputable def tm12684 : ℝ := (-((6059535003 / 10000000000)))
noncomputable def ep12684 : ℝ := (51379937015968867 / 100000000000000000000)
noncomputable def em12684 : ℝ := (25035313245345761 / 50000000000000000000)
noncomputable def bp12684 : ℝ := (2767522629274346991 / 6250000000000000000)
noncomputable def bm12684 : ℝ := (45209190823817379117 / 100000000000000000000)

theorem positive12684 :
    Eplus aL (agent12684.root+dsL) scalar12684.worldRadius world12684.frame
      agent12684.frame tp12684 ≤ -ep12684 := by
  apply positive_check (eT := (7224399208247854769 / 6250000000000000000)) (y := (37850001415638334291 / 100000000000000000000)) (u := (146009282746764322041 / 100000000000000000000))
  · norm_num [world12684, agent12684, scalar12684, tp12684, tm12684, ep12684, em12684, dsL]
  · norm_num [world12684, agent12684, scalar12684, tp12684, tm12684, ep12684, em12684, dsL]
  · norm_num [world12684, agent12684, scalar12684, tp12684, tm12684, ep12684, em12684, dsL]
  · norm_num [world12684, agent12684, scalar12684, tp12684, tm12684, ep12684, em12684, dsL]
  · norm_num [world12684, agent12684, scalar12684, tp12684, tm12684, ep12684, em12684, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12684, agent12684, tp12684, tm12684, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12684, agent12684, scalar12684, tp12684, tm12684, ep12684, em12684, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12684, agent12684, tp12684, tm12684, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12684, agent12684, scalar12684, tp12684, tm12684, ep12684, em12684, dsL]

theorem negative12684 :
    Eminus aL (agent12684.root+dsL) scalar12684.worldRadius world12684.frame
      agent12684.frame tm12684 ≤ -em12684 := by
  apply negative_check (lo := (68438470820544127807 / 100000000000000000000)) (hi := (1069351106571001997 / 1562500000000000000))
    (y := (-((7169015026272053067 / 10000000000000000000)))) (u := (48826279553920657457 / 100000000000000000000))
  · norm_num [world12684, agent12684, scalar12684, tp12684, tm12684, ep12684, em12684, dsL]
  · norm_num [world12684, agent12684, scalar12684, tp12684, tm12684, ep12684, em12684, dsL]
  · norm_num [world12684, agent12684, scalar12684, tp12684, tm12684, ep12684, em12684, dsL]
  · norm_num [world12684, agent12684, scalar12684, tp12684, tm12684, ep12684, em12684, dsL]
  · norm_num [world12684, agent12684, scalar12684, tp12684, tm12684, ep12684, em12684, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12684, agent12684, tp12684, tm12684, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12684, agent12684, tp12684, tm12684, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12684, agent12684, scalar12684, tp12684, tm12684, ep12684, em12684, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12684, agent12684, tp12684, tm12684, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12684, agent12684, scalar12684, tp12684, tm12684, ep12684, em12684, dsL]

theorem tails12684 :
    exp (-((12684:ℝ)*ep12684)) ≤ scalar12684.upperTail ∧
    exp (-((12684:ℝ)*em12684)) ≤ scalar12684.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12684:ℝ)) (by norm_num [ep12684]) ?_)
      (show bp12684^8 ≤ scalar12684.upperTail by norm_num [bp12684, scalar12684])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12684, bp12684, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12684:ℝ)) (by norm_num [em12684]) ?_)
      (show bm12684^8 ≤ scalar12684.lowerTail by norm_num [bm12684, scalar12684])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12684, bm12684, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12684 :
    agent12684.root+dsL+scalar12684.worldRadius < √(1/100/aL) ∧
    2*(agent12684.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12684, agent12684, scalar12684, tp12684, tm12684, ep12684, em12684, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12684, agent12684, scalar12684, tp12684, tm12684, ep12684, em12684, dsL]

noncomputable def master12684 : MasterCertificate 12684 world12684 agent12684 :=
  master scalar12684 dsL tp12684 tm12684 ep12684 em12684
    (by norm_num [dsL]) (by norm_num [tp12684]) (by norm_num [tm12684])
    (by norm_num [ep12684]) (by norm_num [em12684])
    positive12684 negative12684 tails12684.1 tails12684.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12684.1 tailGuards12684.2

theorem preserves12684 : master12684.toScalarCertificate = scalar12684 := rfl

noncomputable def tp12685 : ℝ := (578766193 / 2500000000)
noncomputable def tm12685 : ℝ := (-((1514929677 / 2500000000)))
noncomputable def ep12685 : ℝ := (25691287857859811 / 50000000000000000000)
noncomputable def em12685 : ℝ := (50072890503355101 / 100000000000000000000)
noncomputable def bp12685 : ℝ := (44275665729519712771 / 100000000000000000000)
noncomputable def bm12685 : ℝ := (45204738523958161789 / 100000000000000000000)

theorem positive12685 :
    Eplus aL (agent12685.root+dsL) scalar12685.worldRadius world12685.frame
      agent12685.frame tp12685 ≤ -ep12685 := by
  apply positive_check (eT := (115590636217488324581 / 100000000000000000000)) (y := (9462701161842297723 / 25000000000000000000)) (u := (146010455544363475107 / 100000000000000000000))
  · norm_num [world12685, agent12685, scalar12685, tp12685, tm12685, ep12685, em12685, dsL]
  · norm_num [world12685, agent12685, scalar12685, tp12685, tm12685, ep12685, em12685, dsL]
  · norm_num [world12685, agent12685, scalar12685, tp12685, tm12685, ep12685, em12685, dsL]
  · norm_num [world12685, agent12685, scalar12685, tp12685, tm12685, ep12685, em12685, dsL]
  · norm_num [world12685, agent12685, scalar12685, tp12685, tm12685, ep12685, em12685, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12685, agent12685, tp12685, tm12685, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12685, agent12685, scalar12685, tp12685, tm12685, ep12685, em12685, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12685, agent12685, tp12685, tm12685, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12685, agent12685, scalar12685, tp12685, tm12685, ep12685, em12685, dsL]

theorem negative12685 :
    Eminus aL (agent12685.root+dsL) scalar12685.worldRadius world12685.frame
      agent12685.frame tm12685 ≤ -em12685 := by
  apply negative_check (lo := (34219129755004851657 / 50000000000000000000)) (hi := (13687651902001940663 / 20000000000000000000))
    (y := (-((8961279219196404349 / 12500000000000000000)))) (u := (48826238788461508433 / 100000000000000000000))
  · norm_num [world12685, agent12685, scalar12685, tp12685, tm12685, ep12685, em12685, dsL]
  · norm_num [world12685, agent12685, scalar12685, tp12685, tm12685, ep12685, em12685, dsL]
  · norm_num [world12685, agent12685, scalar12685, tp12685, tm12685, ep12685, em12685, dsL]
  · norm_num [world12685, agent12685, scalar12685, tp12685, tm12685, ep12685, em12685, dsL]
  · norm_num [world12685, agent12685, scalar12685, tp12685, tm12685, ep12685, em12685, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12685, agent12685, tp12685, tm12685, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12685, agent12685, tp12685, tm12685, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12685, agent12685, scalar12685, tp12685, tm12685, ep12685, em12685, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12685, agent12685, tp12685, tm12685, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12685, agent12685, scalar12685, tp12685, tm12685, ep12685, em12685, dsL]

theorem tails12685 :
    exp (-((12685:ℝ)*ep12685)) ≤ scalar12685.upperTail ∧
    exp (-((12685:ℝ)*em12685)) ≤ scalar12685.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12685:ℝ)) (by norm_num [ep12685]) ?_)
      (show bp12685^8 ≤ scalar12685.upperTail by norm_num [bp12685, scalar12685])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12685, bp12685, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12685:ℝ)) (by norm_num [em12685]) ?_)
      (show bm12685^8 ≤ scalar12685.lowerTail by norm_num [bm12685, scalar12685])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12685, bm12685, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12685 :
    agent12685.root+dsL+scalar12685.worldRadius < √(1/100/aL) ∧
    2*(agent12685.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12685, agent12685, scalar12685, tp12685, tm12685, ep12685, em12685, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12685, agent12685, scalar12685, tp12685, tm12685, ep12685, em12685, dsL]

noncomputable def master12685 : MasterCertificate 12685 world12685 agent12685 :=
  master scalar12685 dsL tp12685 tm12685 ep12685 em12685
    (by norm_num [dsL]) (by norm_num [tp12685]) (by norm_num [tm12685])
    (by norm_num [ep12685]) (by norm_num [em12685])
    positive12685 negative12685 tails12685.1 tails12685.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12685.1 tailGuards12685.2

theorem preserves12685 : master12685.toScalarCertificate = scalar12685 := rfl

noncomputable def tp12686 : ℝ := (2315150463 / 10000000000)
noncomputable def tm12686 : ℝ := (-((6059902427 / 10000000000)))
noncomputable def ep12686 : ℝ := (1284630328754797 / 2500000000000000000)
noncomputable def em12686 : ℝ := (10015030670711827 / 20000000000000000000)
noncomputable def bp12686 : ℝ := (2766935655309673699 / 6250000000000000000)
noncomputable def bm12686 : ℝ := (5650035904993091857 / 12500000000000000000)

theorem positive12686 :
    Eplus aL (agent12686.root+dsL) scalar12686.worldRadius world12686.frame
      agent12686.frame tp12686 ≤ -ep12686 := by
  apply positive_check (eT := (115590884788461611979 / 100000000000000000000)) (y := (37851607356636084349 / 100000000000000000000)) (u := (73005813794262405159 / 50000000000000000000))
  · norm_num [world12686, agent12686, scalar12686, tp12686, tm12686, ep12686, em12686, dsL]
  · norm_num [world12686, agent12686, scalar12686, tp12686, tm12686, ep12686, em12686, dsL]
  · norm_num [world12686, agent12686, scalar12686, tp12686, tm12686, ep12686, em12686, dsL]
  · norm_num [world12686, agent12686, scalar12686, tp12686, tm12686, ep12686, em12686, dsL]
  · norm_num [world12686, agent12686, scalar12686, tp12686, tm12686, ep12686, em12686, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12686, agent12686, tp12686, tm12686, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12686, agent12686, scalar12686, tp12686, tm12686, ep12686, em12686, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12686, agent12686, tp12686, tm12686, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12686, agent12686, scalar12686, tp12686, tm12686, ep12686, em12686, dsL]

theorem negative12686 :
    Eminus aL (agent12686.root+dsL) scalar12686.worldRadius world12686.frame
      agent12686.frame tm12686 ≤ -em12686 := by
  apply negative_check (lo := (8554756010327298063 / 12500000000000000000)) (hi := (13687609616523676901 / 20000000000000000000))
    (y := (-((17922579486961539951 / 25000000000000000000)))) (u := (48826197679581092997 / 100000000000000000000))
  · norm_num [world12686, agent12686, scalar12686, tp12686, tm12686, ep12686, em12686, dsL]
  · norm_num [world12686, agent12686, scalar12686, tp12686, tm12686, ep12686, em12686, dsL]
  · norm_num [world12686, agent12686, scalar12686, tp12686, tm12686, ep12686, em12686, dsL]
  · norm_num [world12686, agent12686, scalar12686, tp12686, tm12686, ep12686, em12686, dsL]
  · norm_num [world12686, agent12686, scalar12686, tp12686, tm12686, ep12686, em12686, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12686, agent12686, tp12686, tm12686, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12686, agent12686, tp12686, tm12686, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12686, agent12686, scalar12686, tp12686, tm12686, ep12686, em12686, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12686, agent12686, tp12686, tm12686, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12686, agent12686, scalar12686, tp12686, tm12686, ep12686, em12686, dsL]

theorem tails12686 :
    exp (-((12686:ℝ)*ep12686)) ≤ scalar12686.upperTail ∧
    exp (-((12686:ℝ)*em12686)) ≤ scalar12686.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12686:ℝ)) (by norm_num [ep12686]) ?_)
      (show bp12686^8 ≤ scalar12686.upperTail by norm_num [bp12686, scalar12686])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12686, bp12686, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12686:ℝ)) (by norm_num [em12686]) ?_)
      (show bm12686^8 ≤ scalar12686.lowerTail by norm_num [bm12686, scalar12686])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12686, bm12686, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12686 :
    agent12686.root+dsL+scalar12686.worldRadius < √(1/100/aL) ∧
    2*(agent12686.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12686, agent12686, scalar12686, tp12686, tm12686, ep12686, em12686, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12686, agent12686, scalar12686, tp12686, tm12686, ep12686, em12686, dsL]

noncomputable def master12686 : MasterCertificate 12686 world12686 agent12686 :=
  master scalar12686 dsL tp12686 tm12686 ep12686 em12686
    (by norm_num [dsL]) (by norm_num [tp12686]) (by norm_num [tm12686])
    (by norm_num [ep12686]) (by norm_num [em12686])
    positive12686 negative12686 tails12686.1 tails12686.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12686.1 tailGuards12686.2

theorem preserves12686 : master12686.toScalarCertificate = scalar12686 := rfl

noncomputable def tp12687 : ℝ := (2315235971 / 10000000000)
noncomputable def tm12687 : ℝ := (-((6060086027 / 10000000000)))
noncomputable def ep12687 : ℝ := (3211740514668611 / 6250000000000000000)
noncomputable def em12687 : ℝ := (25038707010324743 / 50000000000000000000)
noncomputable def bp12687 : ℝ := (11066569274030409829 / 25000000000000000000)
noncomputable def bm12687 : ℝ := (22597918851656851307 / 50000000000000000000)

theorem positive12687 :
    Eplus aL (agent12687.root+dsL) scalar12687.worldRadius world12687.frame
      agent12687.frame tp12687 ≤ -ep12687 := by
  apply positive_check (eT := (14448891508547590001 / 12500000000000000000)) (y := (9463101855514370083 / 25000000000000000000)) (u := (73006397890870756171 / 50000000000000000000))
  · norm_num [world12687, agent12687, scalar12687, tp12687, tm12687, ep12687, em12687, dsL]
  · norm_num [world12687, agent12687, scalar12687, tp12687, tm12687, ep12687, em12687, dsL]
  · norm_num [world12687, agent12687, scalar12687, tp12687, tm12687, ep12687, em12687, dsL]
  · norm_num [world12687, agent12687, scalar12687, tp12687, tm12687, ep12687, em12687, dsL]
  · norm_num [world12687, agent12687, scalar12687, tp12687, tm12687, ep12687, em12687, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12687, agent12687, tp12687, tm12687, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12687, agent12687, scalar12687, tp12687, tm12687, ep12687, em12687, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12687, agent12687, tp12687, tm12687, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12687, agent12687, scalar12687, tp12687, tm12687, ep12687, em12687, dsL]

theorem negative12687 :
    Eminus aL (agent12687.root+dsL) scalar12687.worldRadius world12687.frame
      agent12687.frame tm12687 ≤ -em12687 := by
  apply negative_check (lo := (34218918553974652771 / 50000000000000000000)) (hi := (68437837107949305543 / 100000000000000000000))
    (y := (-((716904015823853273 / 1000000000000000000)))) (u := (24413078422016373491 / 50000000000000000000))
  · norm_num [world12687, agent12687, scalar12687, tp12687, tm12687, ep12687, em12687, dsL]
  · norm_num [world12687, agent12687, scalar12687, tp12687, tm12687, ep12687, em12687, dsL]
  · norm_num [world12687, agent12687, scalar12687, tp12687, tm12687, ep12687, em12687, dsL]
  · norm_num [world12687, agent12687, scalar12687, tp12687, tm12687, ep12687, em12687, dsL]
  · norm_num [world12687, agent12687, scalar12687, tp12687, tm12687, ep12687, em12687, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12687, agent12687, tp12687, tm12687, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12687, agent12687, tp12687, tm12687, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12687, agent12687, scalar12687, tp12687, tm12687, ep12687, em12687, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12687, agent12687, tp12687, tm12687, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12687, agent12687, scalar12687, tp12687, tm12687, ep12687, em12687, dsL]

theorem tails12687 :
    exp (-((12687:ℝ)*ep12687)) ≤ scalar12687.upperTail ∧
    exp (-((12687:ℝ)*em12687)) ≤ scalar12687.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12687:ℝ)) (by norm_num [ep12687]) ?_)
      (show bp12687^8 ≤ scalar12687.upperTail by norm_num [bp12687, scalar12687])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12687, bp12687, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12687:ℝ)) (by norm_num [em12687]) ?_)
      (show bm12687^8 ≤ scalar12687.lowerTail by norm_num [bm12687, scalar12687])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12687, bm12687, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12687 :
    agent12687.root+dsL+scalar12687.worldRadius < √(1/100/aL) ∧
    2*(agent12687.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12687, agent12687, scalar12687, tp12687, tm12687, ep12687, em12687, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12687, agent12687, scalar12687, tp12687, tm12687, ep12687, em12687, dsL]

noncomputable def master12687 : MasterCertificate 12687 world12687 agent12687 :=
  master scalar12687 dsL tp12687 tm12687 ep12687 em12687
    (by norm_num [dsL]) (by norm_num [tp12687]) (by norm_num [tm12687])
    (by norm_num [ep12687]) (by norm_num [em12687])
    positive12687 negative12687 tails12687.1 tails12687.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12687.1 tailGuards12687.2

theorem preserves12687 : master12687.toScalarCertificate = scalar12687 := rfl

noncomputable def tp12688 : ℝ := (1157660789 / 5000000000)
noncomputable def tm12688 : ℝ := (-((606026947 / 1000000000)))
noncomputable def ep12688 : ℝ := (25695241429756381 / 50000000000000000000)
noncomputable def em12688 : ℝ := (6259959281692789 / 12500000000000000000)
noncomputable def bp12688 : ℝ := (44261584235973616903 / 100000000000000000000)
noncomputable def bm12688 : ℝ := (11297847165123773633 / 25000000000000000000)

theorem positive12688 :
    Eplus aL (agent12688.root+dsL) scalar12688.worldRadius world12688.frame
      agent12688.frame tp12688 ≤ -ep12688 := by
  apply positive_check (eT := (14448922512145178399 / 12500000000000000000)) (y := (1892660480011215669 / 5000000000000000000)) (u := (3650349176730198897 / 2500000000000000000))
  · norm_num [world12688, agent12688, scalar12688, tp12688, tm12688, ep12688, em12688, dsL]
  · norm_num [world12688, agent12688, scalar12688, tp12688, tm12688, ep12688, em12688, dsL]
  · norm_num [world12688, agent12688, scalar12688, tp12688, tm12688, ep12688, em12688, dsL]
  · norm_num [world12688, agent12688, scalar12688, tp12688, tm12688, ep12688, em12688, dsL]
  · norm_num [world12688, agent12688, scalar12688, tp12688, tm12688, ep12688, em12688, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12688, agent12688, tp12688, tm12688, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12688, agent12688, scalar12688, tp12688, tm12688, ep12688, em12688, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12688, agent12688, tp12688, tm12688, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12688, agent12688, scalar12688, tp12688, tm12688, ep12688, em12688, dsL]

theorem negative12688 :
    Eminus aL (agent12688.root+dsL) scalar12688.worldRadius world12688.frame
      agent12688.frame tm12688 ≤ -em12688 := by
  apply negative_check (lo := (68437626748784522141 / 100000000000000000000)) (hi := (34218813374392261071 / 50000000000000000000))
    (y := (-((71690484799846872073 / 100000000000000000000)))) (u := (48826116212161357917 / 100000000000000000000))
  · norm_num [world12688, agent12688, scalar12688, tp12688, tm12688, ep12688, em12688, dsL]
  · norm_num [world12688, agent12688, scalar12688, tp12688, tm12688, ep12688, em12688, dsL]
  · norm_num [world12688, agent12688, scalar12688, tp12688, tm12688, ep12688, em12688, dsL]
  · norm_num [world12688, agent12688, scalar12688, tp12688, tm12688, ep12688, em12688, dsL]
  · norm_num [world12688, agent12688, scalar12688, tp12688, tm12688, ep12688, em12688, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12688, agent12688, tp12688, tm12688, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12688, agent12688, tp12688, tm12688, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12688, agent12688, scalar12688, tp12688, tm12688, ep12688, em12688, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12688, agent12688, tp12688, tm12688, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12688, agent12688, scalar12688, tp12688, tm12688, ep12688, em12688, dsL]

theorem tails12688 :
    exp (-((12688:ℝ)*ep12688)) ≤ scalar12688.upperTail ∧
    exp (-((12688:ℝ)*em12688)) ≤ scalar12688.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12688:ℝ)) (by norm_num [ep12688]) ?_)
      (show bp12688^8 ≤ scalar12688.upperTail by norm_num [bp12688, scalar12688])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12688, bp12688, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12688:ℝ)) (by norm_num [em12688]) ?_)
      (show bm12688^8 ≤ scalar12688.lowerTail by norm_num [bm12688, scalar12688])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12688, bm12688, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12688 :
    agent12688.root+dsL+scalar12688.worldRadius < √(1/100/aL) ∧
    2*(agent12688.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12688, agent12688, scalar12688, tp12688, tm12688, ep12688, em12688, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12688, agent12688, scalar12688, tp12688, tm12688, ep12688, em12688, dsL]

noncomputable def master12688 : MasterCertificate 12688 world12688 agent12688 :=
  master scalar12688 dsL tp12688 tm12688 ep12688 em12688
    (by norm_num [dsL]) (by norm_num [tp12688]) (by norm_num [tm12688])
    (by norm_num [ep12688]) (by norm_num [em12688])
    positive12688 negative12688 tails12688.1 tails12688.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12688.1 tailGuards12688.2

theorem preserves12688 : master12688.toScalarCertificate = scalar12688 := rfl

noncomputable def tp12689 : ℝ := (2315407101 / 10000000000)
noncomputable def tm12689 : ℝ := (-((189389151 / 312500000)))
noncomputable def ep12689 : ℝ := (25696557873866013 / 50000000000000000000)
noncomputable def em12689 : ℝ := (50081932887956621 / 100000000000000000000)
noncomputable def bp12689 : ℝ := (44256892800872761209 / 100000000000000000000)
noncomputable def bm12689 : ℝ := (22593470472983972947 / 50000000000000000000)

theorem positive12689 :
    Eplus aL (agent12689.root+dsL) scalar12689.worldRadius world12689.frame
      agent12689.frame tp12689 ≤ -ep12689 := by
  apply positive_check (eT := (57795813775520103173 / 50000000000000000000)) (y := (7570802134437371103 / 20000000000000000000)) (u := (146015136750844532377 / 100000000000000000000))
  · norm_num [world12689, agent12689, scalar12689, tp12689, tm12689, ep12689, em12689, dsL]
  · norm_num [world12689, agent12689, scalar12689, tp12689, tm12689, ep12689, em12689, dsL]
  · norm_num [world12689, agent12689, scalar12689, tp12689, tm12689, ep12689, em12689, dsL]
  · norm_num [world12689, agent12689, scalar12689, tp12689, tm12689, ep12689, em12689, dsL]
  · norm_num [world12689, agent12689, scalar12689, tp12689, tm12689, ep12689, em12689, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12689, agent12689, tp12689, tm12689, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12689, agent12689, scalar12689, tp12689, tm12689, ep12689, em12689, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12689, agent12689, tp12689, tm12689, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12689, agent12689, scalar12689, tp12689, tm12689, ep12689, em12689, dsL]

theorem negative12689 :
    Eminus aL (agent12689.root+dsL) scalar12689.worldRadius world12689.frame
      agent12689.frame tm12689 ≤ -em12689 := by
  apply negative_check (lo := (34218708339791145169 / 50000000000000000000)) (hi := (68437416679582290339 / 100000000000000000000))
    (y := (-((71690567667373525981 / 100000000000000000000)))) (u := (12206518937795814061 / 25000000000000000000))
  · norm_num [world12689, agent12689, scalar12689, tp12689, tm12689, ep12689, em12689, dsL]
  · norm_num [world12689, agent12689, scalar12689, tp12689, tm12689, ep12689, em12689, dsL]
  · norm_num [world12689, agent12689, scalar12689, tp12689, tm12689, ep12689, em12689, dsL]
  · norm_num [world12689, agent12689, scalar12689, tp12689, tm12689, ep12689, em12689, dsL]
  · norm_num [world12689, agent12689, scalar12689, tp12689, tm12689, ep12689, em12689, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12689, agent12689, tp12689, tm12689, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12689, agent12689, tp12689, tm12689, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12689, agent12689, scalar12689, tp12689, tm12689, ep12689, em12689, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12689, agent12689, tp12689, tm12689, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12689, agent12689, scalar12689, tp12689, tm12689, ep12689, em12689, dsL]

theorem tails12689 :
    exp (-((12689:ℝ)*ep12689)) ≤ scalar12689.upperTail ∧
    exp (-((12689:ℝ)*em12689)) ≤ scalar12689.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12689:ℝ)) (by norm_num [ep12689]) ?_)
      (show bp12689^8 ≤ scalar12689.upperTail by norm_num [bp12689, scalar12689])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12689, bp12689, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12689:ℝ)) (by norm_num [em12689]) ?_)
      (show bm12689^8 ≤ scalar12689.lowerTail by norm_num [bm12689, scalar12689])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12689, bm12689, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12689 :
    agent12689.root+dsL+scalar12689.worldRadius < √(1/100/aL) ∧
    2*(agent12689.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12689, agent12689, scalar12689, tp12689, tm12689, ep12689, em12689, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12689, agent12689, scalar12689, tp12689, tm12689, ep12689, em12689, dsL]

noncomputable def master12689 : MasterCertificate 12689 world12689 agent12689 :=
  master scalar12689 dsL tp12689 tm12689 ep12689 em12689
    (by norm_num [dsL]) (by norm_num [tp12689]) (by norm_num [tm12689])
    (by norm_num [ep12689]) (by norm_num [em12689])
    positive12689 negative12689 tails12689.1 tails12689.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12689.1 tailGuards12689.2

theorem preserves12689 : master12689.toScalarCertificate = scalar12689 := rfl

noncomputable def tp12690 : ℝ := (578891751 / 2500000000)
noncomputable def tm12690 : ℝ := (-((6060861157 / 10000000000)))
noncomputable def ep12690 : ℝ := (5139717132890901 / 10000000000000000000)
noncomputable def em12690 : ℝ := (5008574136730753 / 10000000000000000000)
noncomputable def bp12690 : ℝ := (44251202922923267439 / 100000000000000000000)
noncomputable def bm12690 : ℝ := (705959103789485401 / 1562500000000000000)

theorem positive12690 :
    Eplus aL (agent12690.root+dsL) scalar12690.worldRadius world12690.frame
      agent12690.frame tp12690 ≤ -ep12690 := by
  apply positive_check (eT := (115592413054558052681 / 100000000000000000000)) (y := (3785408500279714079 / 10000000000000000000)) (u := (146015245284827125139 / 100000000000000000000))
  · norm_num [world12690, agent12690, scalar12690, tp12690, tm12690, ep12690, em12690, dsL]
  · norm_num [world12690, agent12690, scalar12690, tp12690, tm12690, ep12690, em12690, dsL]
  · norm_num [world12690, agent12690, scalar12690, tp12690, tm12690, ep12690, em12690, dsL]
  · norm_num [world12690, agent12690, scalar12690, tp12690, tm12690, ep12690, em12690, dsL]
  · norm_num [world12690, agent12690, scalar12690, tp12690, tm12690, ep12690, em12690, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12690, agent12690, tp12690, tm12690, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12690, agent12690, scalar12690, tp12690, tm12690, ep12690, em12690, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12690, agent12690, tp12690, tm12690, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12690, agent12690, scalar12690, tp12690, tm12690, ep12690, em12690, dsL]

theorem negative12690 :
    Eminus aL (agent12690.root+dsL) scalar12690.worldRadius world12690.frame
      agent12690.frame tm12690 ≤ -em12690 := by
  apply negative_check (lo := (34218121571058550069 / 50000000000000000000)) (hi := (68436243142117100139 / 100000000000000000000))
    (y := (-((71688740858163242909 / 100000000000000000000)))) (u := (12206741929644836279 / 25000000000000000000))
  · norm_num [world12690, agent12690, scalar12690, tp12690, tm12690, ep12690, em12690, dsL]
  · norm_num [world12690, agent12690, scalar12690, tp12690, tm12690, ep12690, em12690, dsL]
  · norm_num [world12690, agent12690, scalar12690, tp12690, tm12690, ep12690, em12690, dsL]
  · norm_num [world12690, agent12690, scalar12690, tp12690, tm12690, ep12690, em12690, dsL]
  · norm_num [world12690, agent12690, scalar12690, tp12690, tm12690, ep12690, em12690, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12690, agent12690, tp12690, tm12690, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12690, agent12690, tp12690, tm12690, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12690, agent12690, scalar12690, tp12690, tm12690, ep12690, em12690, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12690, agent12690, tp12690, tm12690, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12690, agent12690, scalar12690, tp12690, tm12690, ep12690, em12690, dsL]

theorem tails12690 :
    exp (-((12690:ℝ)*ep12690)) ≤ scalar12690.upperTail ∧
    exp (-((12690:ℝ)*em12690)) ≤ scalar12690.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12690:ℝ)) (by norm_num [ep12690]) ?_)
      (show bp12690^8 ≤ scalar12690.upperTail by norm_num [bp12690, scalar12690])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12690, bp12690, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12690:ℝ)) (by norm_num [em12690]) ?_)
      (show bm12690^8 ≤ scalar12690.lowerTail by norm_num [bm12690, scalar12690])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12690, bm12690, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12690 :
    agent12690.root+dsL+scalar12690.worldRadius < √(1/100/aL) ∧
    2*(agent12690.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12690, agent12690, scalar12690, tp12690, tm12690, ep12690, em12690, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12690, agent12690, scalar12690, tp12690, tm12690, ep12690, em12690, dsL]

noncomputable def master12690 : MasterCertificate 12690 world12690 agent12690 :=
  master scalar12690 dsL tp12690 tm12690 ep12690 em12690
    (by norm_num [dsL]) (by norm_num [tp12690]) (by norm_num [tm12690])
    (by norm_num [ep12690]) (by norm_num [em12690])
    positive12690 negative12690 tails12690.1 tails12690.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12690.1 tailGuards12690.2

theorem preserves12690 : master12690.toScalarCertificate = scalar12690 := rfl

noncomputable def tp12691 : ℝ := (1157826393 / 5000000000)
noncomputable def tm12691 : ℝ := (-((6061045299 / 10000000000)))
noncomputable def ep12691 : ℝ := (10279961609018689 / 20000000000000000000)
noncomputable def em12691 : ℝ := (10017600896071013 / 20000000000000000000)
noncomputable def bp12691 : ℝ := (11061627310024351463 / 25000000000000000000)
noncomputable def bm12691 : ℝ := (45176932105347808391 / 100000000000000000000)

theorem positive12691 :
    Eplus aL (agent12691.root+dsL) scalar12691.worldRadius world12691.frame
      agent12691.frame tp12691 ≤ -ep12691 := by
  apply positive_check (eT := (115592662436537907849 / 100000000000000000000)) (y := (3785488313251440163 / 10000000000000000000)) (u := (36504102670135538307 / 25000000000000000000))
  · norm_num [world12691, agent12691, scalar12691, tp12691, tm12691, ep12691, em12691, dsL]
  · norm_num [world12691, agent12691, scalar12691, tp12691, tm12691, ep12691, em12691, dsL]
  · norm_num [world12691, agent12691, scalar12691, tp12691, tm12691, ep12691, em12691, dsL]
  · norm_num [world12691, agent12691, scalar12691, tp12691, tm12691, ep12691, em12691, dsL]
  · norm_num [world12691, agent12691, scalar12691, tp12691, tm12691, ep12691, em12691, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12691, agent12691, tp12691, tm12691, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12691, agent12691, scalar12691, tp12691, tm12691, ep12691, em12691, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12691, agent12691, tp12691, tm12691, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12691, agent12691, scalar12691, tp12691, tm12691, ep12691, em12691, dsL]

theorem negative12691 :
    Eminus aL (agent12691.root+dsL) scalar12691.worldRadius world12691.frame
      agent12691.frame tm12691 ≤ -em12691 := by
  apply negative_check (lo := (68436029643066644691 / 100000000000000000000)) (hi := (17109007410766661173 / 25000000000000000000))
    (y := (-((17922204107705614719 / 25000000000000000000)))) (u := (9765386163751073751 / 20000000000000000000))
  · norm_num [world12691, agent12691, scalar12691, tp12691, tm12691, ep12691, em12691, dsL]
  · norm_num [world12691, agent12691, scalar12691, tp12691, tm12691, ep12691, em12691, dsL]
  · norm_num [world12691, agent12691, scalar12691, tp12691, tm12691, ep12691, em12691, dsL]
  · norm_num [world12691, agent12691, scalar12691, tp12691, tm12691, ep12691, em12691, dsL]
  · norm_num [world12691, agent12691, scalar12691, tp12691, tm12691, ep12691, em12691, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12691, agent12691, tp12691, tm12691, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12691, agent12691, tp12691, tm12691, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12691, agent12691, scalar12691, tp12691, tm12691, ep12691, em12691, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12691, agent12691, tp12691, tm12691, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12691, agent12691, scalar12691, tp12691, tm12691, ep12691, em12691, dsL]

theorem tails12691 :
    exp (-((12691:ℝ)*ep12691)) ≤ scalar12691.upperTail ∧
    exp (-((12691:ℝ)*em12691)) ≤ scalar12691.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12691:ℝ)) (by norm_num [ep12691]) ?_)
      (show bp12691^8 ≤ scalar12691.upperTail by norm_num [bp12691, scalar12691])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12691, bp12691, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12691:ℝ)) (by norm_num [em12691]) ?_)
      (show bm12691^8 ≤ scalar12691.lowerTail by norm_num [bm12691, scalar12691])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12691, bm12691, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12691 :
    agent12691.root+dsL+scalar12691.worldRadius < √(1/100/aL) ∧
    2*(agent12691.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12691, agent12691, scalar12691, tp12691, tm12691, ep12691, em12691, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12691, agent12691, scalar12691, tp12691, tm12691, ep12691, em12691, dsL]

noncomputable def master12691 : MasterCertificate 12691 world12691 agent12691 :=
  master scalar12691 dsL tp12691 tm12691 ep12691 em12691
    (by norm_num [dsL]) (by norm_num [tp12691]) (by norm_num [tm12691])
    (by norm_num [ep12691]) (by norm_num [em12691])
    positive12691 negative12691 tails12691.1 tails12691.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12691.1 tailGuards12691.2

theorem preserves12691 : master12691.toScalarCertificate = scalar12691 := rfl

noncomputable def tp12692 : ℝ := (463147689 / 2000000000)
noncomputable def tm12692 : ℝ := (-((6061229209 / 10000000000)))
noncomputable def ep12692 : ℝ := (5140244241175249 / 10000000000000000000)
noncomputable def em12692 : ℝ := (25045132705439363 / 50000000000000000000)
noncomputable def bp12692 : ℝ := (8848363482523335701 / 20000000000000000000)
noncomputable def bm12692 : ℝ := (2258624165755895791 / 5000000000000000000)

theorem positive12692 :
    Eplus aL (agent12692.root+dsL) scalar12692.worldRadius world12692.frame
      agent12692.frame tp12692 ≤ -ep12692 := by
  apply positive_check (eT := (112883702110817943 / 97656250000000000)) (y := (7571135934246026519 / 20000000000000000000)) (u := (73008786881208368517 / 50000000000000000000))
  · norm_num [world12692, agent12692, scalar12692, tp12692, tm12692, ep12692, em12692, dsL]
  · norm_num [world12692, agent12692, scalar12692, tp12692, tm12692, ep12692, em12692, dsL]
  · norm_num [world12692, agent12692, scalar12692, tp12692, tm12692, ep12692, em12692, dsL]
  · norm_num [world12692, agent12692, scalar12692, tp12692, tm12692, ep12692, em12692, dsL]
  · norm_num [world12692, agent12692, scalar12692, tp12692, tm12692, ep12692, em12692, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12692, agent12692, tp12692, tm12692, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12692, agent12692, scalar12692, tp12692, tm12692, ep12692, em12692, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12692, agent12692, tp12692, tm12692, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12692, agent12692, scalar12692, tp12692, tm12692, ep12692, em12692, dsL]

theorem negative12692 :
    Eminus aL (agent12692.root+dsL) scalar12692.worldRadius world12692.frame
      agent12692.frame tm12692 ≤ -em12692 := by
  apply negative_check (lo := (68435817080780533603 / 100000000000000000000)) (hi := (17108954270195133401 / 25000000000000000000))
    (y := (-((71688890343042169801 / 100000000000000000000)))) (u := (3051680920606270063 / 6250000000000000000))
  · norm_num [world12692, agent12692, scalar12692, tp12692, tm12692, ep12692, em12692, dsL]
  · norm_num [world12692, agent12692, scalar12692, tp12692, tm12692, ep12692, em12692, dsL]
  · norm_num [world12692, agent12692, scalar12692, tp12692, tm12692, ep12692, em12692, dsL]
  · norm_num [world12692, agent12692, scalar12692, tp12692, tm12692, ep12692, em12692, dsL]
  · norm_num [world12692, agent12692, scalar12692, tp12692, tm12692, ep12692, em12692, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12692, agent12692, tp12692, tm12692, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12692, agent12692, tp12692, tm12692, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12692, agent12692, scalar12692, tp12692, tm12692, ep12692, em12692, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12692, agent12692, tp12692, tm12692, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12692, agent12692, scalar12692, tp12692, tm12692, ep12692, em12692, dsL]

theorem tails12692 :
    exp (-((12692:ℝ)*ep12692)) ≤ scalar12692.upperTail ∧
    exp (-((12692:ℝ)*em12692)) ≤ scalar12692.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12692:ℝ)) (by norm_num [ep12692]) ?_)
      (show bp12692^8 ≤ scalar12692.upperTail by norm_num [bp12692, scalar12692])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12692, bp12692, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12692:ℝ)) (by norm_num [em12692]) ?_)
      (show bm12692^8 ≤ scalar12692.lowerTail by norm_num [bm12692, scalar12692])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12692, bm12692, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12692 :
    agent12692.root+dsL+scalar12692.worldRadius < √(1/100/aL) ∧
    2*(agent12692.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12692, agent12692, scalar12692, tp12692, tm12692, ep12692, em12692, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12692, agent12692, scalar12692, tp12692, tm12692, ep12692, em12692, dsL]

noncomputable def master12692 : MasterCertificate 12692 world12692 agent12692 :=
  master scalar12692 dsL tp12692 tm12692 ep12692 em12692
    (by norm_num [dsL]) (by norm_num [tp12692]) (by norm_num [tm12692])
    (by norm_num [ep12692]) (by norm_num [em12692])
    positive12692 negative12692 tails12692.1 tails12692.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12692.1 tailGuards12692.2

theorem preserves12692 : master12692.toScalarCertificate = scalar12692 := rfl

noncomputable def tp12693 : ℝ := (2315824109 / 10000000000)
noncomputable def tm12693 : ℝ := (-((3030706529 / 5000000000)))
noncomputable def ep12693 : ℝ := (3212817249374713 / 6250000000000000000)
noncomputable def em12693 : ℝ := (10018505124035241 / 20000000000000000000)
noncomputable def bp12693 : ℝ := (44237126344679023883 / 100000000000000000000)
noncomputable def bm12693 : ℝ := (9033607044908437427 / 20000000000000000000)

theorem positive12693 :
    Eplus aL (agent12693.root+dsL) scalar12693.worldRadius world12693.frame
      agent12693.frame tp12693 ≤ -ep12693 := by
  apply positive_check (eT := (57796579777613246819 / 50000000000000000000)) (y := (37856476567838911219 / 100000000000000000000)) (u := (73009368688073331789 / 50000000000000000000))
  · norm_num [world12693, agent12693, scalar12693, tp12693, tm12693, ep12693, em12693, dsL]
  · norm_num [world12693, agent12693, scalar12693, tp12693, tm12693, ep12693, em12693, dsL]
  · norm_num [world12693, agent12693, scalar12693, tp12693, tm12693, ep12693, em12693, dsL]
  · norm_num [world12693, agent12693, scalar12693, tp12693, tm12693, ep12693, em12693, dsL]
  · norm_num [world12693, agent12693, scalar12693, tp12693, tm12693, ep12693, em12693, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12693, agent12693, tp12693, tm12693, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12693, agent12693, scalar12693, tp12693, tm12693, ep12693, em12693, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12693, agent12693, tp12693, tm12693, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12693, agent12693, scalar12693, tp12693, tm12693, ep12693, em12693, dsL]

theorem negative12693 :
    Eminus aL (agent12693.root+dsL) scalar12693.worldRadius world12693.frame
      agent12693.frame tm12693 ≤ -em12693 := by
  apply negative_check (lo := (6843560472296469317 / 10000000000000000000)) (hi := (68435604722964693171 / 100000000000000000000))
    (y := (-((71688964354734822507 / 100000000000000000000)))) (u := (48826858592102434827 / 100000000000000000000))
  · norm_num [world12693, agent12693, scalar12693, tp12693, tm12693, ep12693, em12693, dsL]
  · norm_num [world12693, agent12693, scalar12693, tp12693, tm12693, ep12693, em12693, dsL]
  · norm_num [world12693, agent12693, scalar12693, tp12693, tm12693, ep12693, em12693, dsL]
  · norm_num [world12693, agent12693, scalar12693, tp12693, tm12693, ep12693, em12693, dsL]
  · norm_num [world12693, agent12693, scalar12693, tp12693, tm12693, ep12693, em12693, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12693, agent12693, tp12693, tm12693, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12693, agent12693, tp12693, tm12693, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12693, agent12693, scalar12693, tp12693, tm12693, ep12693, em12693, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12693, agent12693, tp12693, tm12693, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12693, agent12693, scalar12693, tp12693, tm12693, ep12693, em12693, dsL]

theorem tails12693 :
    exp (-((12693:ℝ)*ep12693)) ≤ scalar12693.upperTail ∧
    exp (-((12693:ℝ)*em12693)) ≤ scalar12693.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12693:ℝ)) (by norm_num [ep12693]) ?_)
      (show bp12693^8 ≤ scalar12693.upperTail by norm_num [bp12693, scalar12693])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12693, bp12693, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12693:ℝ)) (by norm_num [em12693]) ?_)
      (show bm12693^8 ≤ scalar12693.lowerTail by norm_num [bm12693, scalar12693])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12693, bm12693, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12693 :
    agent12693.root+dsL+scalar12693.worldRadius < √(1/100/aL) ∧
    2*(agent12693.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12693, agent12693, scalar12693, tp12693, tm12693, ep12693, em12693, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12693, agent12693, scalar12693, tp12693, tm12693, ep12693, em12693, dsL]

noncomputable def master12693 : MasterCertificate 12693 world12693 agent12693 :=
  master scalar12693 dsL tp12693 tm12693 ep12693 em12693
    (by norm_num [dsL]) (by norm_num [tp12693]) (by norm_num [tm12693])
    (by norm_num [ep12693]) (by norm_num [em12693])
    positive12693 negative12693 tails12693.1 tails12693.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12693.1 tailGuards12693.2

theorem preserves12693 : master12693.toScalarCertificate = scalar12693 := rfl

noncomputable def tp12694 : ℝ := (1157954863 / 5000000000)
noncomputable def tm12694 : ℝ := (-((1515399241 / 2500000000)))
noncomputable def ep12694 : ℝ := (12851926924877951 / 25000000000000000000)
noncomputable def em12694 : ℝ := (25047392045642209 / 50000000000000000000)
noncomputable def bp12694 : ℝ := (44232436794503804357 / 100000000000000000000)
noncomputable def bm12694 : ℝ := (45163588562411909211 / 100000000000000000000)

theorem positive12694 :
    Eplus aL (agent12694.root+dsL) scalar12694.worldRadius world12694.frame
      agent12694.frame tp12694 ≤ -ep12694 := by
  apply positive_check (eT := (288983519604277137 / 250000000000000000)) (y := (9464318289694269511 / 25000000000000000000)) (u := (146019900552809501371 / 100000000000000000000))
  · norm_num [world12694, agent12694, scalar12694, tp12694, tm12694, ep12694, em12694, dsL]
  · norm_num [world12694, agent12694, scalar12694, tp12694, tm12694, ep12694, em12694, dsL]
  · norm_num [world12694, agent12694, scalar12694, tp12694, tm12694, ep12694, em12694, dsL]
  · norm_num [world12694, agent12694, scalar12694, tp12694, tm12694, ep12694, em12694, dsL]
  · norm_num [world12694, agent12694, scalar12694, tp12694, tm12694, ep12694, em12694, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12694, agent12694, tp12694, tm12694, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12694, agent12694, scalar12694, tp12694, tm12694, ep12694, em12694, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12694, agent12694, tp12694, tm12694, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12694, agent12694, scalar12694, tp12694, tm12694, ep12694, em12694, dsL]

theorem negative12694 :
    Eminus aL (agent12694.root+dsL) scalar12694.worldRadius world12694.frame
      agent12694.frame tm12694 ≤ -em12694 := by
  apply negative_check (lo := (34217696032132885027 / 50000000000000000000)) (hi := (13687078412853154011 / 20000000000000000000))
    (y := (-((71689039644313910209 / 100000000000000000000)))) (u := (9765364366115991577 / 20000000000000000000))
  · norm_num [world12694, agent12694, scalar12694, tp12694, tm12694, ep12694, em12694, dsL]
  · norm_num [world12694, agent12694, scalar12694, tp12694, tm12694, ep12694, em12694, dsL]
  · norm_num [world12694, agent12694, scalar12694, tp12694, tm12694, ep12694, em12694, dsL]
  · norm_num [world12694, agent12694, scalar12694, tp12694, tm12694, ep12694, em12694, dsL]
  · norm_num [world12694, agent12694, scalar12694, tp12694, tm12694, ep12694, em12694, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12694, agent12694, tp12694, tm12694, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12694, agent12694, tp12694, tm12694, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12694, agent12694, scalar12694, tp12694, tm12694, ep12694, em12694, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12694, agent12694, tp12694, tm12694, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12694, agent12694, scalar12694, tp12694, tm12694, ep12694, em12694, dsL]

theorem tails12694 :
    exp (-((12694:ℝ)*ep12694)) ≤ scalar12694.upperTail ∧
    exp (-((12694:ℝ)*em12694)) ≤ scalar12694.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12694:ℝ)) (by norm_num [ep12694]) ?_)
      (show bp12694^8 ≤ scalar12694.upperTail by norm_num [bp12694, scalar12694])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12694, bp12694, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12694:ℝ)) (by norm_num [em12694]) ?_)
      (show bm12694^8 ≤ scalar12694.lowerTail by norm_num [bm12694, scalar12694])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12694, bm12694, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12694 :
    agent12694.root+dsL+scalar12694.worldRadius < √(1/100/aL) ∧
    2*(agent12694.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12694, agent12694, scalar12694, tp12694, tm12694, ep12694, em12694, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12694, agent12694, scalar12694, tp12694, tm12694, ep12694, em12694, dsL]

noncomputable def master12694 : MasterCertificate 12694 world12694 agent12694 :=
  master scalar12694 dsL tp12694 tm12694 ep12694 em12694
    (by norm_num [dsL]) (by norm_num [tp12694]) (by norm_num [tm12694])
    (by norm_num [ep12694]) (by norm_num [em12694])
    positive12694 negative12694 tails12694.1 tails12694.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12694.1 tailGuards12694.2

theorem preserves12694 : master12694.toScalarCertificate = scalar12694 := rfl

noncomputable def tp12695 : ℝ := (1157997639 / 5000000000)
noncomputable def tm12695 : ℝ := (-((378861283 / 625000000)))
noncomputable def ep12695 : ℝ := (2056413525966333 / 4000000000000000000)
noncomputable def em12695 : ℝ := (50097041404966201 / 100000000000000000000)
noncomputable def bp12695 : ℝ := (22113874167352160281 / 50000000000000000000)
noncomputable def bm12695 : ℝ := (4515914291250001849 / 10000000000000000000)

theorem positive12695 :
    Eplus aL (agent12695.root+dsL) scalar12695.worldRadius world12695.frame
      agent12695.frame tp12695 ≤ -ep12695 := by
  apply positive_check (eT := (3612301740334895587 / 3125000000000000000)) (y := (37858068927078097827 / 100000000000000000000)) (u := (73010531268757314041 / 50000000000000000000))
  · norm_num [world12695, agent12695, scalar12695, tp12695, tm12695, ep12695, em12695, dsL]
  · norm_num [world12695, agent12695, scalar12695, tp12695, tm12695, ep12695, em12695, dsL]
  · norm_num [world12695, agent12695, scalar12695, tp12695, tm12695, ep12695, em12695, dsL]
  · norm_num [world12695, agent12695, scalar12695, tp12695, tm12695, ep12695, em12695, dsL]
  · norm_num [world12695, agent12695, scalar12695, tp12695, tm12695, ep12695, em12695, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12695, agent12695, tp12695, tm12695, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12695, agent12695, scalar12695, tp12695, tm12695, ep12695, em12695, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12695, agent12695, tp12695, tm12695, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12695, agent12695, scalar12695, tp12695, tm12695, ep12695, em12695, dsL]

theorem negative12695 :
    Eminus aL (agent12695.root+dsL) scalar12695.worldRadius world12695.frame
      agent12695.frame tm12695 ≤ -em12695 := by
  apply negative_check (lo := (68435180813279996501 / 100000000000000000000)) (hi := (34217590406639998251 / 50000000000000000000))
    (y := (-((716891121717612519 / 1000000000000000000)))) (u := (6103348302218163513 / 12500000000000000000))
  · norm_num [world12695, agent12695, scalar12695, tp12695, tm12695, ep12695, em12695, dsL]
  · norm_num [world12695, agent12695, scalar12695, tp12695, tm12695, ep12695, em12695, dsL]
  · norm_num [world12695, agent12695, scalar12695, tp12695, tm12695, ep12695, em12695, dsL]
  · norm_num [world12695, agent12695, scalar12695, tp12695, tm12695, ep12695, em12695, dsL]
  · norm_num [world12695, agent12695, scalar12695, tp12695, tm12695, ep12695, em12695, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12695, agent12695, tp12695, tm12695, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12695, agent12695, tp12695, tm12695, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12695, agent12695, scalar12695, tp12695, tm12695, ep12695, em12695, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12695, agent12695, tp12695, tm12695, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12695, agent12695, scalar12695, tp12695, tm12695, ep12695, em12695, dsL]

theorem tails12695 :
    exp (-((12695:ℝ)*ep12695)) ≤ scalar12695.upperTail ∧
    exp (-((12695:ℝ)*em12695)) ≤ scalar12695.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12695:ℝ)) (by norm_num [ep12695]) ?_)
      (show bp12695^8 ≤ scalar12695.upperTail by norm_num [bp12695, scalar12695])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12695, bp12695, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12695:ℝ)) (by norm_num [em12695]) ?_)
      (show bm12695^8 ≤ scalar12695.lowerTail by norm_num [bm12695, scalar12695])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12695, bm12695, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12695 :
    agent12695.root+dsL+scalar12695.worldRadius < √(1/100/aL) ∧
    2*(agent12695.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12695, agent12695, scalar12695, tp12695, tm12695, ep12695, em12695, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12695, agent12695, scalar12695, tp12695, tm12695, ep12695, em12695, dsL]

noncomputable def master12695 : MasterCertificate 12695 world12695 agent12695 :=
  master scalar12695 dsL tp12695 tm12695 ep12695 em12695
    (by norm_num [dsL]) (by norm_num [tp12695]) (by norm_num [tm12695])
    (by norm_num [ep12695]) (by norm_num [em12695])
    positive12695 negative12695 tails12695.1 tails12695.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12695.1 tailGuards12695.2

theorem preserves12695 : master12695.toScalarCertificate = scalar12695 := rfl

noncomputable def tp12696 : ℝ := (463216163 / 2000000000)
noncomputable def tm12696 : ℝ := (-((6061964077 / 10000000000)))
noncomputable def ep12696 : ℝ := (25706483598511269 / 50000000000000000000)
noncomputable def em12696 : ℝ := (1252482435324703 / 2500000000000000000)
noncomputable def bp12696 : ℝ := (44223061064845141463 / 100000000000000000000)
noncomputable def bm12696 : ℝ := (45154698381014595981 / 100000000000000000000)

theorem positive12696 :
    Eplus aL (agent12696.root+dsL) scalar12696.worldRadius world12696.frame
      agent12696.frame tp12696 ≤ -ep12696 := by
  apply positive_check (eT := (115593903463904099221 / 100000000000000000000)) (y := (37858864902301142831 / 100000000000000000000)) (u := (29204444966723728423 / 20000000000000000000))
  · norm_num [world12696, agent12696, scalar12696, tp12696, tm12696, ep12696, em12696, dsL]
  · norm_num [world12696, agent12696, scalar12696, tp12696, tm12696, ep12696, em12696, dsL]
  · norm_num [world12696, agent12696, scalar12696, tp12696, tm12696, ep12696, em12696, dsL]
  · norm_num [world12696, agent12696, scalar12696, tp12696, tm12696, ep12696, em12696, dsL]
  · norm_num [world12696, agent12696, scalar12696, tp12696, tm12696, ep12696, em12696, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12696, agent12696, tp12696, tm12696, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12696, agent12696, scalar12696, tp12696, tm12696, ep12696, em12696, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12696, agent12696, tp12696, tm12696, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12696, agent12696, scalar12696, tp12696, tm12696, ep12696, em12696, dsL]

theorem negative12696 :
    Eminus aL (agent12696.root+dsL) scalar12696.worldRadius world12696.frame
      agent12696.frame tm12696 ≤ -em12696 := by
  apply negative_check (lo := (34217484784861275239 / 50000000000000000000)) (hi := (68434969569722550479 / 100000000000000000000))
    (y := (-((71689185404321208889 / 100000000000000000000)))) (u := (3051671916290797661 / 6250000000000000000))
  · norm_num [world12696, agent12696, scalar12696, tp12696, tm12696, ep12696, em12696, dsL]
  · norm_num [world12696, agent12696, scalar12696, tp12696, tm12696, ep12696, em12696, dsL]
  · norm_num [world12696, agent12696, scalar12696, tp12696, tm12696, ep12696, em12696, dsL]
  · norm_num [world12696, agent12696, scalar12696, tp12696, tm12696, ep12696, em12696, dsL]
  · norm_num [world12696, agent12696, scalar12696, tp12696, tm12696, ep12696, em12696, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12696, agent12696, tp12696, tm12696, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12696, agent12696, tp12696, tm12696, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12696, agent12696, scalar12696, tp12696, tm12696, ep12696, em12696, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12696, agent12696, tp12696, tm12696, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12696, agent12696, scalar12696, tp12696, tm12696, ep12696, em12696, dsL]

theorem tails12696 :
    exp (-((12696:ℝ)*ep12696)) ≤ scalar12696.upperTail ∧
    exp (-((12696:ℝ)*em12696)) ≤ scalar12696.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12696:ℝ)) (by norm_num [ep12696]) ?_)
      (show bp12696^8 ≤ scalar12696.upperTail by norm_num [bp12696, scalar12696])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12696, bp12696, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12696:ℝ)) (by norm_num [em12696]) ?_)
      (show bm12696^8 ≤ scalar12696.lowerTail by norm_num [bm12696, scalar12696])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12696, bm12696, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12696 :
    agent12696.root+dsL+scalar12696.worldRadius < √(1/100/aL) ∧
    2*(agent12696.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12696, agent12696, scalar12696, tp12696, tm12696, ep12696, em12696, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12696, agent12696, scalar12696, tp12696, tm12696, ep12696, em12696, dsL]

noncomputable def master12696 : MasterCertificate 12696 world12696 agent12696 :=
  master scalar12696 dsL tp12696 tm12696 ep12696 em12696
    (by norm_num [dsL]) (by norm_num [tp12696]) (by norm_num [tm12696])
    (by norm_num [ep12696]) (by norm_num [em12696])
    positive12696 negative12696 tails12696.1 tails12696.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12696.1 tailGuards12696.2

theorem preserves12696 : master12696.toScalarCertificate = scalar12696 := rfl

noncomputable def tp12697 : ℝ := (92646653 / 400000000)
noncomputable def tm12697 : ℝ := (-((6062147559 / 10000000000)))
noncomputable def ep12697 : ℝ := (5141559531936559 / 10000000000000000000)
noncomputable def em12697 : ℝ := (25050776277895159 / 50000000000000000000)
noncomputable def bp12697 : ℝ := (44218374650645213371 / 100000000000000000000)
noncomputable def bm12697 : ℝ := (4515025465231717969 / 10000000000000000000)

theorem positive12697 :
    Eplus aL (agent12697.root+dsL) scalar12697.worldRadius world12697.frame
      agent12697.frame tp12697 ≤ -ep12697 := by
  apply positive_check (eT := (23118830214899636269 / 20000000000000000000)) (y := (3785966082460661791 / 10000000000000000000)) (u := (146023387061702253999 / 100000000000000000000))
  · norm_num [world12697, agent12697, scalar12697, tp12697, tm12697, ep12697, em12697, dsL]
  · norm_num [world12697, agent12697, scalar12697, tp12697, tm12697, ep12697, em12697, dsL]
  · norm_num [world12697, agent12697, scalar12697, tp12697, tm12697, ep12697, em12697, dsL]
  · norm_num [world12697, agent12697, scalar12697, tp12697, tm12697, ep12697, em12697, dsL]
  · norm_num [world12697, agent12697, scalar12697, tp12697, tm12697, ep12697, em12697, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12697, agent12697, tp12697, tm12697, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12697, agent12697, scalar12697, tp12697, tm12697, ep12697, em12697, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12697, agent12697, tp12697, tm12697, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12697, agent12697, scalar12697, tp12697, tm12697, ep12697, em12697, dsL]

theorem negative12697 :
    Eminus aL (agent12697.root+dsL) scalar12697.worldRadius world12697.frame
      agent12697.frame tm12697 ≤ -em12697 := by
  apply negative_check (lo := (68434758556231488501 / 100000000000000000000)) (hi := (34217379278115744251 / 50000000000000000000))
    (y := (-((71689258964097168003 / 100000000000000000000)))) (u := (24413357371908789329 / 50000000000000000000))
  · norm_num [world12697, agent12697, scalar12697, tp12697, tm12697, ep12697, em12697, dsL]
  · norm_num [world12697, agent12697, scalar12697, tp12697, tm12697, ep12697, em12697, dsL]
  · norm_num [world12697, agent12697, scalar12697, tp12697, tm12697, ep12697, em12697, dsL]
  · norm_num [world12697, agent12697, scalar12697, tp12697, tm12697, ep12697, em12697, dsL]
  · norm_num [world12697, agent12697, scalar12697, tp12697, tm12697, ep12697, em12697, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12697, agent12697, tp12697, tm12697, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12697, agent12697, tp12697, tm12697, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12697, agent12697, scalar12697, tp12697, tm12697, ep12697, em12697, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12697, agent12697, tp12697, tm12697, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12697, agent12697, scalar12697, tp12697, tm12697, ep12697, em12697, dsL]

theorem tails12697 :
    exp (-((12697:ℝ)*ep12697)) ≤ scalar12697.upperTail ∧
    exp (-((12697:ℝ)*em12697)) ≤ scalar12697.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12697:ℝ)) (by norm_num [ep12697]) ?_)
      (show bp12697^8 ≤ scalar12697.upperTail by norm_num [bp12697, scalar12697])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12697, bp12697, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12697:ℝ)) (by norm_num [em12697]) ?_)
      (show bm12697^8 ≤ scalar12697.lowerTail by norm_num [bm12697, scalar12697])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12697, bm12697, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12697 :
    agent12697.root+dsL+scalar12697.worldRadius < √(1/100/aL) ∧
    2*(agent12697.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12697, agent12697, scalar12697, tp12697, tm12697, ep12697, em12697, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12697, agent12697, scalar12697, tp12697, tm12697, ep12697, em12697, dsL]

noncomputable def master12697 : MasterCertificate 12697 world12697 agent12697 :=
  master scalar12697 dsL tp12697 tm12697 ep12697 em12697
    (by norm_num [dsL]) (by norm_num [tp12697]) (by norm_num [tm12697])
    (by norm_num [ep12697]) (by norm_num [em12697])
    positive12697 negative12697 tails12697.1 tails12697.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12697.1 tailGuards12697.2

theorem preserves12697 : master12697.toScalarCertificate = scalar12697 := rfl

noncomputable def tp12698 : ℝ := (144765733 / 625000000)
noncomputable def tm12698 : ℝ := (-((303116543 / 500000000)))
noncomputable def ep12698 : ℝ := (10283644314627331 / 20000000000000000000)
noncomputable def em12698 : ℝ := (6262975745088651 / 12500000000000000000)
noncomputable def bp12698 : ℝ := (2210684487695356707 / 5000000000000000000)
noncomputable def bm12698 : ℝ := (22572906175866949931 / 50000000000000000000)

theorem positive12698 :
    Eplus aL (agent12698.root+dsL) scalar12698.worldRadius world12698.frame
      agent12698.frame tp12698 ≤ -ep12698 := by
  apply positive_check (eT := (115594397943886722311 / 100000000000000000000)) (y := (2366278461690201939 / 6250000000000000000)) (u := (73012273656646986007 / 50000000000000000000))
  · norm_num [world12698, agent12698, scalar12698, tp12698, tm12698, ep12698, em12698, dsL]
  · norm_num [world12698, agent12698, scalar12698, tp12698, tm12698, ep12698, em12698, dsL]
  · norm_num [world12698, agent12698, scalar12698, tp12698, tm12698, ep12698, em12698, dsL]
  · norm_num [world12698, agent12698, scalar12698, tp12698, tm12698, ep12698, em12698, dsL]
  · norm_num [world12698, agent12698, scalar12698, tp12698, tm12698, ep12698, em12698, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12698, agent12698, tp12698, tm12698, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12698, agent12698, scalar12698, tp12698, tm12698, ep12698, em12698, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12698, agent12698, tp12698, tm12698, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12698, agent12698, scalar12698, tp12698, tm12698, ep12698, em12698, dsL]

theorem negative12698 :
    Eminus aL (agent12698.root+dsL) scalar12698.worldRadius world12698.frame
      agent12698.frame tm12698 ≤ -em12698 := by
  apply negative_check (lo := (34217274130483458769 / 50000000000000000000)) (hi := (68434548260966917539 / 100000000000000000000))
    (y := (-((14337866297176584111 / 20000000000000000000)))) (u := (24413339666912481059 / 50000000000000000000))
  · norm_num [world12698, agent12698, scalar12698, tp12698, tm12698, ep12698, em12698, dsL]
  · norm_num [world12698, agent12698, scalar12698, tp12698, tm12698, ep12698, em12698, dsL]
  · norm_num [world12698, agent12698, scalar12698, tp12698, tm12698, ep12698, em12698, dsL]
  · norm_num [world12698, agent12698, scalar12698, tp12698, tm12698, ep12698, em12698, dsL]
  · norm_num [world12698, agent12698, scalar12698, tp12698, tm12698, ep12698, em12698, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12698, agent12698, tp12698, tm12698, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12698, agent12698, tp12698, tm12698, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12698, agent12698, scalar12698, tp12698, tm12698, ep12698, em12698, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12698, agent12698, tp12698, tm12698, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12698, agent12698, scalar12698, tp12698, tm12698, ep12698, em12698, dsL]

theorem tails12698 :
    exp (-((12698:ℝ)*ep12698)) ≤ scalar12698.upperTail ∧
    exp (-((12698:ℝ)*em12698)) ≤ scalar12698.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12698:ℝ)) (by norm_num [ep12698]) ?_)
      (show bp12698^8 ≤ scalar12698.upperTail by norm_num [bp12698, scalar12698])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12698, bp12698, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12698:ℝ)) (by norm_num [em12698]) ?_)
      (show bm12698^8 ≤ scalar12698.lowerTail by norm_num [bm12698, scalar12698])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12698, bm12698, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12698 :
    agent12698.root+dsL+scalar12698.worldRadius < √(1/100/aL) ∧
    2*(agent12698.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12698, agent12698, scalar12698, tp12698, tm12698, ep12698, em12698, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12698, agent12698, scalar12698, tp12698, tm12698, ep12698, em12698, dsL]

noncomputable def master12698 : MasterCertificate 12698 world12698 agent12698 :=
  master scalar12698 dsL tp12698 tm12698 ep12698 em12698
    (by norm_num [dsL]) (by norm_num [tp12698]) (by norm_num [tm12698])
    (by norm_num [ep12698]) (by norm_num [em12698])
    positive12698 negative12698 tails12698.1 tails12698.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12698.1 tailGuards12698.2

theorem preserves12698 : master12698.toScalarCertificate = scalar12698 := rfl

noncomputable def tp12699 : ℝ := (144771069 / 625000000)
noncomputable def tm12699 : ℝ := (-((1212502831 / 2000000000)))
noncomputable def ep12699 : ℝ := (25710423283577969 / 50000000000000000000)
noncomputable def em12699 : ℝ := (25053029104240537 / 50000000000000000000)
noncomputable def bp12699 : ℝ := (2763062871707266693 / 6250000000000000000)
noncomputable def bm12699 : ℝ := (9028274212617882847 / 20000000000000000000)

theorem positive12699 :
    Eplus aL (agent12699.root+dsL) scalar12699.worldRadius world12699.frame
      agent12699.frame tp12699 ≤ -ep12699 := by
  apply positive_check (eT := (11559464465071529231 / 10000000000000000000)) (y := (37861249793480969821 / 100000000000000000000)) (u := (146025707346306190121 / 100000000000000000000))
  · norm_num [world12699, agent12699, scalar12699, tp12699, tm12699, ep12699, em12699, dsL]
  · norm_num [world12699, agent12699, scalar12699, tp12699, tm12699, ep12699, em12699, dsL]
  · norm_num [world12699, agent12699, scalar12699, tp12699, tm12699, ep12699, em12699, dsL]
  · norm_num [world12699, agent12699, scalar12699, tp12699, tm12699, ep12699, em12699, dsL]
  · norm_num [world12699, agent12699, scalar12699, tp12699, tm12699, ep12699, em12699, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12699, agent12699, tp12699, tm12699, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12699, agent12699, scalar12699, tp12699, tm12699, ep12699, em12699, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12699, agent12699, tp12699, tm12699, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12699, agent12699, scalar12699, tp12699, tm12699, ep12699, em12699, dsL]

theorem negative12699 :
    Eminus aL (agent12699.root+dsL) scalar12699.worldRadius world12699.frame
      agent12699.frame tm12699 ≤ -em12699 := by
  apply negative_check (lo := (34217168967276603057 / 50000000000000000000)) (hi := (13686867586910641223 / 20000000000000000000))
    (y := (-((71689404511909125783 / 100000000000000000000)))) (u := (48826643677654335801 / 100000000000000000000))
  · norm_num [world12699, agent12699, scalar12699, tp12699, tm12699, ep12699, em12699, dsL]
  · norm_num [world12699, agent12699, scalar12699, tp12699, tm12699, ep12699, em12699, dsL]
  · norm_num [world12699, agent12699, scalar12699, tp12699, tm12699, ep12699, em12699, dsL]
  · norm_num [world12699, agent12699, scalar12699, tp12699, tm12699, ep12699, em12699, dsL]
  · norm_num [world12699, agent12699, scalar12699, tp12699, tm12699, ep12699, em12699, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12699, agent12699, tp12699, tm12699, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12699, agent12699, tp12699, tm12699, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12699, agent12699, scalar12699, tp12699, tm12699, ep12699, em12699, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12699, agent12699, tp12699, tm12699, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12699, agent12699, scalar12699, tp12699, tm12699, ep12699, em12699, dsL]

theorem tails12699 :
    exp (-((12699:ℝ)*ep12699)) ≤ scalar12699.upperTail ∧
    exp (-((12699:ℝ)*em12699)) ≤ scalar12699.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12699:ℝ)) (by norm_num [ep12699]) ?_)
      (show bp12699^8 ≤ scalar12699.upperTail by norm_num [bp12699, scalar12699])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12699, bp12699, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12699:ℝ)) (by norm_num [em12699]) ?_)
      (show bm12699^8 ≤ scalar12699.lowerTail by norm_num [bm12699, scalar12699])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12699, bm12699, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12699 :
    agent12699.root+dsL+scalar12699.worldRadius < √(1/100/aL) ∧
    2*(agent12699.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12699, agent12699, scalar12699, tp12699, tm12699, ep12699, em12699, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12699, agent12699, scalar12699, tp12699, tm12699, ep12699, em12699, dsL]

noncomputable def master12699 : MasterCertificate 12699 world12699 agent12699 :=
  master scalar12699 dsL tp12699 tm12699 ep12699 em12699
    (by norm_num [dsL]) (by norm_num [tp12699]) (by norm_num [tm12699])
    (by norm_num [ep12699]) (by norm_num [em12699])
    positive12699 negative12699 tails12699.1 tails12699.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12699.1 tailGuards12699.2

theorem preserves12699 : master12699.toScalarCertificate = scalar12699 := rfl

end BstLean.Part268
