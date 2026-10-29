import BstLean.Part261Checker
import BstLean.Part268Scalar6
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12500 : ℝ := (114863241 / 500000000)
noncomputable def tm12500 : ℝ := (-((6020212409 / 10000000000)))
noncomputable def ep12500 : ℝ := (10169726673277259 / 20000000000000000000)
noncomputable def em12500 : ℝ := (49607444161554801 / 100000000000000000000)
noncomputable def bp12500 : ℝ := (5647532634729028171 / 12500000000000000000)
noncomputable def bm12500 : ℝ := (46065019734383917927 / 100000000000000000000)

theorem positive12500 :
    Eplus aL (agent12500.root+dsL) scalar12500.worldRadius world12500.frame
      agent12500.frame tp12500 ≤ -ep12500 := by
  apply positive_check (eT := (115531084685703006981 / 100000000000000000000)) (y := (37709952712652004797 / 100000000000000000000)) (u := (36451235440471562543 / 25000000000000000000))
  · norm_num [world12500, agent12500, scalar12500, tp12500, tm12500, ep12500, em12500, dsL]
  · norm_num [world12500, agent12500, scalar12500, tp12500, tm12500, ep12500, em12500, dsL]
  · norm_num [world12500, agent12500, scalar12500, tp12500, tm12500, ep12500, em12500, dsL]
  · norm_num [world12500, agent12500, scalar12500, tp12500, tm12500, ep12500, em12500, dsL]
  · norm_num [world12500, agent12500, scalar12500, tp12500, tm12500, ep12500, em12500, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12500, agent12500, tp12500, tm12500, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12500, agent12500, scalar12500, tp12500, tm12500, ep12500, em12500, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12500, agent12500, tp12500, tm12500, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12500, agent12500, scalar12500, tp12500, tm12500, ep12500, em12500, dsL]

theorem negative12500 :
    Eminus aL (agent12500.root+dsL) scalar12500.worldRadius world12500.frame
      agent12500.frame tm12500 ≤ -em12500 := by
  apply negative_check (lo := (68500128390248734171 / 100000000000000000000)) (hi := (17125032097562183543 / 25000000000000000000))
    (y := (-((71703248214353501499 / 100000000000000000000)))) (u := (24409942365122552047 / 50000000000000000000))
  · norm_num [world12500, agent12500, scalar12500, tp12500, tm12500, ep12500, em12500, dsL]
  · norm_num [world12500, agent12500, scalar12500, tp12500, tm12500, ep12500, em12500, dsL]
  · norm_num [world12500, agent12500, scalar12500, tp12500, tm12500, ep12500, em12500, dsL]
  · norm_num [world12500, agent12500, scalar12500, tp12500, tm12500, ep12500, em12500, dsL]
  · norm_num [world12500, agent12500, scalar12500, tp12500, tm12500, ep12500, em12500, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12500, agent12500, tp12500, tm12500, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12500, agent12500, tp12500, tm12500, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12500, agent12500, scalar12500, tp12500, tm12500, ep12500, em12500, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12500, agent12500, tp12500, tm12500, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12500, agent12500, scalar12500, tp12500, tm12500, ep12500, em12500, dsL]

theorem tails12500 :
    exp (-((12500:ℝ)*ep12500)) ≤ scalar12500.upperTail ∧
    exp (-((12500:ℝ)*em12500)) ≤ scalar12500.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12500:ℝ)) (by norm_num [ep12500]) ?_)
      (show bp12500^8 ≤ scalar12500.upperTail by norm_num [bp12500, scalar12500])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12500, bp12500, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12500:ℝ)) (by norm_num [em12500]) ?_)
      (show bm12500^8 ≤ scalar12500.lowerTail by norm_num [bm12500, scalar12500])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12500, bm12500, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12500 :
    agent12500.root+dsL+scalar12500.worldRadius < √(1/100/aL) ∧
    2*(agent12500.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12500, agent12500, scalar12500, tp12500, tm12500, ep12500, em12500, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12500, agent12500, scalar12500, tp12500, tm12500, ep12500, em12500, dsL]

noncomputable def master12500 : MasterCertificate 12500 world12500 agent12500 :=
  master scalar12500 dsL tp12500 tm12500 ep12500 em12500
    (by norm_num [dsL]) (by norm_num [tp12500]) (by norm_num [tm12500])
    (by norm_num [ep12500]) (by norm_num [em12500])
    positive12500 negative12500 tails12500.1 tails12500.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12500.1 tailGuards12500.2

theorem preserves12500 : master12500.toScalarCertificate = scalar12500 := rfl

noncomputable def tp12501 : ℝ := (2297356667 / 10000000000)
noncomputable def tm12501 : ℝ := (-((48163287 / 80000000)))
noncomputable def ep12501 : ℝ := (50851480840691553 / 100000000000000000000)
noncomputable def em12501 : ℝ := (49609900851103807 / 100000000000000000000)
noncomputable def bp12501 : ℝ := (9035075867420817967 / 20000000000000000000)
noncomputable def bm12501 : ℝ := (23030197561882814437 / 50000000000000000000)

theorem positive12501 :
    Eplus aL (agent12501.root+dsL) scalar12501.worldRadius world12501.frame
      agent12501.frame tp12501 ≤ -ep12501 := by
  apply positive_check (eT := (7220710752748512183 / 6250000000000000000)) (y := (2356926033154593471 / 6250000000000000000)) (u := (36451550314099416183 / 25000000000000000000))
  · norm_num [world12501, agent12501, scalar12501, tp12501, tm12501, ep12501, em12501, dsL]
  · norm_num [world12501, agent12501, scalar12501, tp12501, tm12501, ep12501, em12501, dsL]
  · norm_num [world12501, agent12501, scalar12501, tp12501, tm12501, ep12501, em12501, dsL]
  · norm_num [world12501, agent12501, scalar12501, tp12501, tm12501, ep12501, em12501, dsL]
  · norm_num [world12501, agent12501, scalar12501, tp12501, tm12501, ep12501, em12501, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12501, agent12501, tp12501, tm12501, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12501, agent12501, scalar12501, tp12501, tm12501, ep12501, em12501, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12501, agent12501, tp12501, tm12501, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12501, agent12501, scalar12501, tp12501, tm12501, ep12501, em12501, dsL]

theorem negative12501 :
    Eminus aL (agent12501.root+dsL) scalar12501.worldRadius world12501.frame
      agent12501.frame tm12501 ≤ -em12501 := by
  apply negative_check (lo := (68499863677071110389 / 100000000000000000000)) (hi := (6849986367707111039 / 10000000000000000000))
    (y := (-((71703404050592011403 / 100000000000000000000)))) (u := (48819808651232374961 / 100000000000000000000))
  · norm_num [world12501, agent12501, scalar12501, tp12501, tm12501, ep12501, em12501, dsL]
  · norm_num [world12501, agent12501, scalar12501, tp12501, tm12501, ep12501, em12501, dsL]
  · norm_num [world12501, agent12501, scalar12501, tp12501, tm12501, ep12501, em12501, dsL]
  · norm_num [world12501, agent12501, scalar12501, tp12501, tm12501, ep12501, em12501, dsL]
  · norm_num [world12501, agent12501, scalar12501, tp12501, tm12501, ep12501, em12501, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12501, agent12501, tp12501, tm12501, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12501, agent12501, tp12501, tm12501, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12501, agent12501, scalar12501, tp12501, tm12501, ep12501, em12501, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12501, agent12501, tp12501, tm12501, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12501, agent12501, scalar12501, tp12501, tm12501, ep12501, em12501, dsL]

theorem tails12501 :
    exp (-((12501:ℝ)*ep12501)) ≤ scalar12501.upperTail ∧
    exp (-((12501:ℝ)*em12501)) ≤ scalar12501.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12501:ℝ)) (by norm_num [ep12501]) ?_)
      (show bp12501^8 ≤ scalar12501.upperTail by norm_num [bp12501, scalar12501])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12501, bp12501, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12501:ℝ)) (by norm_num [em12501]) ?_)
      (show bm12501^8 ≤ scalar12501.lowerTail by norm_num [bm12501, scalar12501])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12501, bm12501, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12501 :
    agent12501.root+dsL+scalar12501.worldRadius < √(1/100/aL) ∧
    2*(agent12501.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12501, agent12501, scalar12501, tp12501, tm12501, ep12501, em12501, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12501, agent12501, scalar12501, tp12501, tm12501, ep12501, em12501, dsL]

noncomputable def master12501 : MasterCertificate 12501 world12501 agent12501 :=
  master scalar12501 dsL tp12501 tm12501 ep12501 em12501
    (by norm_num [dsL]) (by norm_num [tp12501]) (by norm_num [tm12501])
    (by norm_num [ep12501]) (by norm_num [em12501])
    positive12501 negative12501 tails12501.1 tails12501.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12501.1 tailGuards12501.2

theorem preserves12501 : master12501.toScalarCertificate = scalar12501 := rfl

noncomputable def tp12502 : ℝ := (1148724381 / 5000000000)
noncomputable def tm12502 : ℝ := (-((6020609917 / 10000000000)))
noncomputable def ep12502 : ℝ := (12713582921110941 / 25000000000000000000)
noncomputable def em12502 : ℝ := (24806180758614177 / 50000000000000000000)
noncomputable def bp12502 : ℝ := (5646311927974474143 / 12500000000000000000)
noncomputable def bm12502 : ℝ := (46055767832477859897 / 100000000000000000000)

theorem positive12502 :
    Eplus aL (agent12502.root+dsL) scalar12502.worldRadius world12502.frame
      agent12502.frame tp12502 ≤ -ep12502 := by
  apply positive_check (eT := (23106332247044101711 / 20000000000000000000)) (y := (9427919462097066039 / 25000000000000000000)) (u := (145807457116738396959 / 100000000000000000000))
  · norm_num [world12502, agent12502, scalar12502, tp12502, tm12502, ep12502, em12502, dsL]
  · norm_num [world12502, agent12502, scalar12502, tp12502, tm12502, ep12502, em12502, dsL]
  · norm_num [world12502, agent12502, scalar12502, tp12502, tm12502, ep12502, em12502, dsL]
  · norm_num [world12502, agent12502, scalar12502, tp12502, tm12502, ep12502, em12502, dsL]
  · norm_num [world12502, agent12502, scalar12502, tp12502, tm12502, ep12502, em12502, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12502, agent12502, tp12502, tm12502, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12502, agent12502, scalar12502, tp12502, tm12502, ep12502, em12502, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12502, agent12502, tp12502, tm12502, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12502, agent12502, scalar12502, tp12502, tm12502, ep12502, em12502, dsL]

theorem negative12502 :
    Eminus aL (agent12502.root+dsL) scalar12502.worldRadius world12502.frame
      agent12502.frame tm12502 ≤ -em12502 := by
  apply negative_check (lo := (8562449553485251927 / 12500000000000000000)) (hi := (68499596427882015417 / 100000000000000000000))
    (y := (-((71703551539294654533 / 100000000000000000000)))) (u := (48819736647583061037 / 100000000000000000000))
  · norm_num [world12502, agent12502, scalar12502, tp12502, tm12502, ep12502, em12502, dsL]
  · norm_num [world12502, agent12502, scalar12502, tp12502, tm12502, ep12502, em12502, dsL]
  · norm_num [world12502, agent12502, scalar12502, tp12502, tm12502, ep12502, em12502, dsL]
  · norm_num [world12502, agent12502, scalar12502, tp12502, tm12502, ep12502, em12502, dsL]
  · norm_num [world12502, agent12502, scalar12502, tp12502, tm12502, ep12502, em12502, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12502, agent12502, tp12502, tm12502, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12502, agent12502, tp12502, tm12502, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12502, agent12502, scalar12502, tp12502, tm12502, ep12502, em12502, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12502, agent12502, tp12502, tm12502, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12502, agent12502, scalar12502, tp12502, tm12502, ep12502, em12502, dsL]

theorem tails12502 :
    exp (-((12502:ℝ)*ep12502)) ≤ scalar12502.upperTail ∧
    exp (-((12502:ℝ)*em12502)) ≤ scalar12502.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12502:ℝ)) (by norm_num [ep12502]) ?_)
      (show bp12502^8 ≤ scalar12502.upperTail by norm_num [bp12502, scalar12502])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12502, bp12502, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12502:ℝ)) (by norm_num [em12502]) ?_)
      (show bm12502^8 ≤ scalar12502.lowerTail by norm_num [bm12502, scalar12502])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12502, bm12502, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12502 :
    agent12502.root+dsL+scalar12502.worldRadius < √(1/100/aL) ∧
    2*(agent12502.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12502, agent12502, scalar12502, tp12502, tm12502, ep12502, em12502, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12502, agent12502, scalar12502, tp12502, tm12502, ep12502, em12502, dsL]

noncomputable def master12502 : MasterCertificate 12502 world12502 agent12502 :=
  master scalar12502 dsL tp12502 tm12502 ep12502 em12502
    (by norm_num [dsL]) (by norm_num [tp12502]) (by norm_num [tm12502])
    (by norm_num [ep12502]) (by norm_num [em12502])
    positive12502 negative12502 tails12502.1 tails12502.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12502.1 tailGuards12502.2

theorem preserves12502 : master12502.toScalarCertificate = scalar12502 := rfl

noncomputable def tp12503 : ℝ := (2297540813 / 10000000000)
noncomputable def tm12503 : ℝ := (-((3010404509 / 5000000000)))
noncomputable def ep12503 : ℝ := (25428591349497111 / 50000000000000000000)
noncomputable def em12503 : ℝ := (12403705601616291 / 25000000000000000000)
noncomputable def bp12503 : ℝ := (45165611596024020389 / 100000000000000000000)
noncomputable def bm12503 : ℝ := (5756392570273030651 / 12500000000000000000)

theorem positive12503 :
    Eplus aL (agent12503.root+dsL) scalar12503.worldRadius world12503.frame
      agent12503.frame tp12503 ≤ -ep12503 := by
  apply positive_check (eT := (57765975069680466267 / 50000000000000000000)) (y := (9428134485812025579 / 25000000000000000000)) (u := (145808711204575483537 / 100000000000000000000))
  · norm_num [world12503, agent12503, scalar12503, tp12503, tm12503, ep12503, em12503, dsL]
  · norm_num [world12503, agent12503, scalar12503, tp12503, tm12503, ep12503, em12503, dsL]
  · norm_num [world12503, agent12503, scalar12503, tp12503, tm12503, ep12503, em12503, dsL]
  · norm_num [world12503, agent12503, scalar12503, tp12503, tm12503, ep12503, em12503, dsL]
  · norm_num [world12503, agent12503, scalar12503, tp12503, tm12503, ep12503, em12503, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12503, agent12503, tp12503, tm12503, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12503, agent12503, scalar12503, tp12503, tm12503, ep12503, em12503, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12503, agent12503, tp12503, tm12503, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12503, agent12503, scalar12503, tp12503, tm12503, ep12503, em12503, dsL]

theorem negative12503 :
    Eminus aL (agent12503.root+dsL) scalar12503.worldRadius world12503.frame
      agent12503.frame tm12503 ≤ -em12503 := by
  apply negative_check (lo := (428120805427314831 / 625000000000000000)) (hi := (68499328868370372961 / 100000000000000000000))
    (y := (-((4481481183609304629 / 6250000000000000000)))) (u := (976393293761978441 / 2000000000000000000))
  · norm_num [world12503, agent12503, scalar12503, tp12503, tm12503, ep12503, em12503, dsL]
  · norm_num [world12503, agent12503, scalar12503, tp12503, tm12503, ep12503, em12503, dsL]
  · norm_num [world12503, agent12503, scalar12503, tp12503, tm12503, ep12503, em12503, dsL]
  · norm_num [world12503, agent12503, scalar12503, tp12503, tm12503, ep12503, em12503, dsL]
  · norm_num [world12503, agent12503, scalar12503, tp12503, tm12503, ep12503, em12503, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12503, agent12503, tp12503, tm12503, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12503, agent12503, tp12503, tm12503, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12503, agent12503, scalar12503, tp12503, tm12503, ep12503, em12503, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12503, agent12503, tp12503, tm12503, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12503, agent12503, scalar12503, tp12503, tm12503, ep12503, em12503, dsL]

theorem tails12503 :
    exp (-((12503:ℝ)*ep12503)) ≤ scalar12503.upperTail ∧
    exp (-((12503:ℝ)*em12503)) ≤ scalar12503.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12503:ℝ)) (by norm_num [ep12503]) ?_)
      (show bp12503^8 ≤ scalar12503.upperTail by norm_num [bp12503, scalar12503])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12503, bp12503, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12503:ℝ)) (by norm_num [em12503]) ?_)
      (show bm12503^8 ≤ scalar12503.lowerTail by norm_num [bm12503, scalar12503])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12503, bm12503, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12503 :
    agent12503.root+dsL+scalar12503.worldRadius < √(1/100/aL) ∧
    2*(agent12503.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12503, agent12503, scalar12503, tp12503, tm12503, ep12503, em12503, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12503, agent12503, scalar12503, tp12503, tm12503, ep12503, em12503, dsL]

noncomputable def master12503 : MasterCertificate 12503 world12503 agent12503 :=
  master scalar12503 dsL tp12503 tm12503 ep12503 em12503
    (by norm_num [dsL]) (by norm_num [tp12503]) (by norm_num [tm12503])
    (by norm_num [ep12503]) (by norm_num [em12503])
    positive12503 negative12503 tails12503.1 tails12503.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12503.1 tailGuards12503.2

theorem preserves12503 : master12503.toScalarCertificate = scalar12503 := rfl

noncomputable def tp12504 : ℝ := (574408207 / 2500000000)
noncomputable def tm12504 : ℝ := (-((3010503971 / 5000000000)))
noncomputable def ep12504 : ℝ := (397343993106137 / 781250000000000000)
noncomputable def em12504 : ℝ := (49617280915770981 / 100000000000000000000)
noncomputable def bp12504 : ℝ := (22580364903397858653 / 50000000000000000000)
noncomputable def bm12504 : ℝ := (46046515186361845117 / 100000000000000000000)

theorem positive12504 :
    Eplus aL (agent12504.root+dsL) scalar12504.worldRadius world12504.frame
      agent12504.frame tp12504 ≤ -ep12504 := by
  apply positive_check (eT := (115532238814503394441 / 100000000000000000000)) (y := (18856698877931215223 / 50000000000000000000)) (u := (72904982445828440931 / 50000000000000000000))
  · norm_num [world12504, agent12504, scalar12504, tp12504, tm12504, ep12504, em12504, dsL]
  · norm_num [world12504, agent12504, scalar12504, tp12504, tm12504, ep12504, em12504, dsL]
  · norm_num [world12504, agent12504, scalar12504, tp12504, tm12504, ep12504, em12504, dsL]
  · norm_num [world12504, agent12504, scalar12504, tp12504, tm12504, ep12504, em12504, dsL]
  · norm_num [world12504, agent12504, scalar12504, tp12504, tm12504, ep12504, em12504, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12504, agent12504, tp12504, tm12504, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12504, agent12504, scalar12504, tp12504, tm12504, ep12504, em12504, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12504, agent12504, tp12504, tm12504, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12504, agent12504, scalar12504, tp12504, tm12504, ep12504, em12504, dsL]

theorem negative12504 :
    Eminus aL (agent12504.root+dsL) scalar12504.worldRadius world12504.frame
      agent12504.frame tm12504 ≤ -em12504 := by
  apply negative_check (lo := (17124765503594563723 / 25000000000000000000)) (hi := (68499062014378254893 / 100000000000000000000))
    (y := (-((917809210480733 / 1280000000000000)))) (u := (48819593591556302897 / 100000000000000000000))
  · norm_num [world12504, agent12504, scalar12504, tp12504, tm12504, ep12504, em12504, dsL]
  · norm_num [world12504, agent12504, scalar12504, tp12504, tm12504, ep12504, em12504, dsL]
  · norm_num [world12504, agent12504, scalar12504, tp12504, tm12504, ep12504, em12504, dsL]
  · norm_num [world12504, agent12504, scalar12504, tp12504, tm12504, ep12504, em12504, dsL]
  · norm_num [world12504, agent12504, scalar12504, tp12504, tm12504, ep12504, em12504, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12504, agent12504, tp12504, tm12504, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12504, agent12504, tp12504, tm12504, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12504, agent12504, scalar12504, tp12504, tm12504, ep12504, em12504, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12504, agent12504, tp12504, tm12504, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12504, agent12504, scalar12504, tp12504, tm12504, ep12504, em12504, dsL]

theorem tails12504 :
    exp (-((12504:ℝ)*ep12504)) ≤ scalar12504.upperTail ∧
    exp (-((12504:ℝ)*em12504)) ≤ scalar12504.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12504:ℝ)) (by norm_num [ep12504]) ?_)
      (show bp12504^8 ≤ scalar12504.upperTail by norm_num [bp12504, scalar12504])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12504, bp12504, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12504:ℝ)) (by norm_num [em12504]) ?_)
      (show bm12504^8 ≤ scalar12504.lowerTail by norm_num [bm12504, scalar12504])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12504, bm12504, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12504 :
    agent12504.root+dsL+scalar12504.worldRadius < √(1/100/aL) ∧
    2*(agent12504.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12504, agent12504, scalar12504, tp12504, tm12504, ep12504, em12504, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12504, agent12504, scalar12504, tp12504, tm12504, ep12504, em12504, dsL]

noncomputable def master12504 : MasterCertificate 12504 world12504 agent12504 :=
  master scalar12504 dsL tp12504 tm12504 ep12504 em12504
    (by norm_num [dsL]) (by norm_num [tp12504]) (by norm_num [tm12504])
    (by norm_num [ep12504]) (by norm_num [em12504])
    positive12504 negative12504 tails12504.1 tails12504.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12504.1 tailGuards12504.2

theorem preserves12504 : master12504.toScalarCertificate = scalar12504 := rfl

noncomputable def tp12505 : ℝ := (1148862417 / 5000000000)
noncomputable def tm12505 : ℝ := (-((6021206663 / 10000000000)))
noncomputable def ep12505 : ℝ := (50862878861242883 / 100000000000000000000)
noncomputable def em12505 : ℝ := (9923947754099323 / 20000000000000000000)
noncomputable def bp12505 : ℝ := (5644481087507827209 / 12500000000000000000)
noncomputable def bm12505 : ℝ := (11510472615805598897 / 25000000000000000000)

theorem positive12505 :
    Eplus aL (agent12505.root+dsL) scalar12505.worldRadius world12505.frame
      agent12505.frame tp12505 ≤ -ep12505 := by
  apply positive_check (eT := (57766263728341773407 / 50000000000000000000)) (y := (37714257972814666973 / 100000000000000000000)) (u := (145811219179087718843 / 100000000000000000000))
  · norm_num [world12505, agent12505, scalar12505, tp12505, tm12505, ep12505, em12505, dsL]
  · norm_num [world12505, agent12505, scalar12505, tp12505, tm12505, ep12505, em12505, dsL]
  · norm_num [world12505, agent12505, scalar12505, tp12505, tm12505, ep12505, em12505, dsL]
  · norm_num [world12505, agent12505, scalar12505, tp12505, tm12505, ep12505, em12505, dsL]
  · norm_num [world12505, agent12505, scalar12505, tp12505, tm12505, ep12505, em12505, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12505, agent12505, tp12505, tm12505, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12505, agent12505, scalar12505, tp12505, tm12505, ep12505, em12505, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12505, agent12505, tp12505, tm12505, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12505, agent12505, scalar12505, tp12505, tm12505, ep12505, em12505, dsL]

theorem negative12505 :
    Eminus aL (agent12505.root+dsL) scalar12505.worldRadius world12505.frame
      agent12505.frame tm12505 ≤ -em12505 := by
  apply negative_check (lo := (13699759195549291751 / 20000000000000000000)) (hi := (17124698994436614689 / 25000000000000000000))
    (y := (-((35851994841607323923 / 50000000000000000000)))) (u := (48819522747343778693 / 100000000000000000000))
  · norm_num [world12505, agent12505, scalar12505, tp12505, tm12505, ep12505, em12505, dsL]
  · norm_num [world12505, agent12505, scalar12505, tp12505, tm12505, ep12505, em12505, dsL]
  · norm_num [world12505, agent12505, scalar12505, tp12505, tm12505, ep12505, em12505, dsL]
  · norm_num [world12505, agent12505, scalar12505, tp12505, tm12505, ep12505, em12505, dsL]
  · norm_num [world12505, agent12505, scalar12505, tp12505, tm12505, ep12505, em12505, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12505, agent12505, tp12505, tm12505, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12505, agent12505, tp12505, tm12505, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12505, agent12505, scalar12505, tp12505, tm12505, ep12505, em12505, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12505, agent12505, tp12505, tm12505, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12505, agent12505, scalar12505, tp12505, tm12505, ep12505, em12505, dsL]

theorem tails12505 :
    exp (-((12505:ℝ)*ep12505)) ≤ scalar12505.upperTail ∧
    exp (-((12505:ℝ)*em12505)) ≤ scalar12505.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12505:ℝ)) (by norm_num [ep12505]) ?_)
      (show bp12505^8 ≤ scalar12505.upperTail by norm_num [bp12505, scalar12505])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12505, bp12505, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12505:ℝ)) (by norm_num [em12505]) ?_)
      (show bm12505^8 ≤ scalar12505.lowerTail by norm_num [bm12505, scalar12505])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12505, bm12505, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12505 :
    agent12505.root+dsL+scalar12505.worldRadius < √(1/100/aL) ∧
    2*(agent12505.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12505, agent12505, scalar12505, tp12505, tm12505, ep12505, em12505, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12505, agent12505, scalar12505, tp12505, tm12505, ep12505, em12505, dsL]

noncomputable def master12505 : MasterCertificate 12505 world12505 agent12505 :=
  master scalar12505 dsL tp12505 tm12505 ep12505 em12505
    (by norm_num [dsL]) (by norm_num [tp12505]) (by norm_num [tm12505])
    (by norm_num [ep12505]) (by norm_num [em12505])
    positive12505 negative12505 tails12505.1 tails12505.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12505.1 tailGuards12505.2

theorem preserves12505 : master12505.toScalarCertificate = scalar12505 := rfl

noncomputable def tp12506 : ℝ := (1148908393 / 5000000000)
noncomputable def tm12506 : ℝ := (-((6021405427 / 10000000000)))
noncomputable def ep12506 : ℝ := (50865724957172403 / 100000000000000000000)
noncomputable def em12506 : ℝ := (4962219512781147 / 10000000000000000000)
noncomputable def bp12506 : ℝ := (4515096896245157033 / 10000000000000000000)
noncomputable def bm12506 : ℝ := (11509316749835459763 / 25000000000000000000)

theorem positive12506 :
    Eplus aL (agent12506.root+dsL) scalar12506.worldRadius world12506.frame
      agent12506.frame tp12506 ≤ -ep12506 := by
  apply positive_check (eT := (57766407869603149833 / 50000000000000000000)) (y := (4714389699267832389 / 12500000000000000000)) (u := (29162494521762750911 / 20000000000000000000))
  · norm_num [world12506, agent12506, scalar12506, tp12506, tm12506, ep12506, em12506, dsL]
  · norm_num [world12506, agent12506, scalar12506, tp12506, tm12506, ep12506, em12506, dsL]
  · norm_num [world12506, agent12506, scalar12506, tp12506, tm12506, ep12506, em12506, dsL]
  · norm_num [world12506, agent12506, scalar12506, tp12506, tm12506, ep12506, em12506, dsL]
  · norm_num [world12506, agent12506, scalar12506, tp12506, tm12506, ep12506, em12506, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12506, agent12506, tp12506, tm12506, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12506, agent12506, scalar12506, tp12506, tm12506, ep12506, em12506, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12506, agent12506, tp12506, tm12506, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12506, agent12506, scalar12506, tp12506, tm12506, ep12506, em12506, dsL]

theorem negative12506 :
    Eminus aL (agent12506.root+dsL) scalar12506.worldRadius world12506.frame
      agent12506.frame tm12506 ≤ -em12506 := by
  apply negative_check (lo := (68498529699619597367 / 100000000000000000000)) (hi := (8562316212452449671 / 12500000000000000000))
    (y := (-((71704135854736999601 / 100000000000000000000)))) (u := (12204862846789082047 / 25000000000000000000))
  · norm_num [world12506, agent12506, scalar12506, tp12506, tm12506, ep12506, em12506, dsL]
  · norm_num [world12506, agent12506, scalar12506, tp12506, tm12506, ep12506, em12506, dsL]
  · norm_num [world12506, agent12506, scalar12506, tp12506, tm12506, ep12506, em12506, dsL]
  · norm_num [world12506, agent12506, scalar12506, tp12506, tm12506, ep12506, em12506, dsL]
  · norm_num [world12506, agent12506, scalar12506, tp12506, tm12506, ep12506, em12506, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12506, agent12506, tp12506, tm12506, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12506, agent12506, tp12506, tm12506, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12506, agent12506, scalar12506, tp12506, tm12506, ep12506, em12506, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12506, agent12506, tp12506, tm12506, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12506, agent12506, scalar12506, tp12506, tm12506, ep12506, em12506, dsL]

theorem tails12506 :
    exp (-((12506:ℝ)*ep12506)) ≤ scalar12506.upperTail ∧
    exp (-((12506:ℝ)*em12506)) ≤ scalar12506.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12506:ℝ)) (by norm_num [ep12506]) ?_)
      (show bp12506^8 ≤ scalar12506.upperTail by norm_num [bp12506, scalar12506])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12506, bp12506, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12506:ℝ)) (by norm_num [em12506]) ?_)
      (show bm12506^8 ≤ scalar12506.lowerTail by norm_num [bm12506, scalar12506])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12506, bm12506, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12506 :
    agent12506.root+dsL+scalar12506.worldRadius < √(1/100/aL) ∧
    2*(agent12506.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12506, agent12506, scalar12506, tp12506, tm12506, ep12506, em12506, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12506, agent12506, scalar12506, tp12506, tm12506, ep12506, em12506, dsL]

noncomputable def master12506 : MasterCertificate 12506 world12506 agent12506 :=
  master scalar12506 dsL tp12506 tm12506 ep12506 em12506
    (by norm_num [dsL]) (by norm_num [tp12506]) (by norm_num [tm12506])
    (by norm_num [ep12506]) (by norm_num [em12506])
    positive12506 negative12506 tails12506.1 tails12506.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12506.1 tailGuards12506.2

theorem preserves12506 : master12506.toScalarCertificate = scalar12506 := rfl

noncomputable def tp12507 : ℝ := (1148954311 / 5000000000)
noncomputable def tm12507 : ℝ := (-((6021604143 / 10000000000)))
noncomputable def ep12507 : ℝ := (25434284717369111 / 50000000000000000000)
noncomputable def em12507 : ℝ := (49624649952338639 / 100000000000000000000)
noncomputable def bp12507 : ℝ := (11286522643296601243 / 25000000000000000000)
noncomputable def bm12507 : ℝ := (5754080602519003453 / 12500000000000000000)

theorem positive12507 :
    Eplus aL (agent12507.root+dsL) scalar12507.worldRadius world12507.frame
      agent12507.frame tp12507 ≤ -ep12507 := by
  apply positive_check (eT := (115533103212019530029 / 100000000000000000000)) (y := (754319514579594771 / 2000000000000000000)) (u := (145813723881806814751 / 100000000000000000000))
  · norm_num [world12507, agent12507, scalar12507, tp12507, tm12507, ep12507, em12507, dsL]
  · norm_num [world12507, agent12507, scalar12507, tp12507, tm12507, ep12507, em12507, dsL]
  · norm_num [world12507, agent12507, scalar12507, tp12507, tm12507, ep12507, em12507, dsL]
  · norm_num [world12507, agent12507, scalar12507, tp12507, tm12507, ep12507, em12507, dsL]
  · norm_num [world12507, agent12507, scalar12507, tp12507, tm12507, ep12507, em12507, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12507, agent12507, tp12507, tm12507, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12507, agent12507, scalar12507, tp12507, tm12507, ep12507, em12507, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12507, agent12507, tp12507, tm12507, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12507, agent12507, scalar12507, tp12507, tm12507, ep12507, em12507, dsL]

theorem negative12507 :
    Eminus aL (agent12507.root+dsL) scalar12507.worldRadius world12507.frame
      agent12507.frame tm12507 ≤ -em12507 := by
  apply negative_check (lo := (13699652714333942677 / 20000000000000000000)) (hi := (34249131785834856693 / 50000000000000000000))
    (y := (-((35852141178778091859 / 50000000000000000000)))) (u := (48819379865336126539 / 100000000000000000000))
  · norm_num [world12507, agent12507, scalar12507, tp12507, tm12507, ep12507, em12507, dsL]
  · norm_num [world12507, agent12507, scalar12507, tp12507, tm12507, ep12507, em12507, dsL]
  · norm_num [world12507, agent12507, scalar12507, tp12507, tm12507, ep12507, em12507, dsL]
  · norm_num [world12507, agent12507, scalar12507, tp12507, tm12507, ep12507, em12507, dsL]
  · norm_num [world12507, agent12507, scalar12507, tp12507, tm12507, ep12507, em12507, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12507, agent12507, tp12507, tm12507, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12507, agent12507, tp12507, tm12507, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12507, agent12507, scalar12507, tp12507, tm12507, ep12507, em12507, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12507, agent12507, tp12507, tm12507, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12507, agent12507, scalar12507, tp12507, tm12507, ep12507, em12507, dsL]

theorem tails12507 :
    exp (-((12507:ℝ)*ep12507)) ≤ scalar12507.upperTail ∧
    exp (-((12507:ℝ)*em12507)) ≤ scalar12507.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12507:ℝ)) (by norm_num [ep12507]) ?_)
      (show bp12507^8 ≤ scalar12507.upperTail by norm_num [bp12507, scalar12507])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12507, bp12507, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12507:ℝ)) (by norm_num [em12507]) ?_)
      (show bm12507^8 ≤ scalar12507.lowerTail by norm_num [bm12507, scalar12507])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12507, bm12507, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12507 :
    agent12507.root+dsL+scalar12507.worldRadius < √(1/100/aL) ∧
    2*(agent12507.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12507, agent12507, scalar12507, tp12507, tm12507, ep12507, em12507, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12507, agent12507, scalar12507, tp12507, tm12507, ep12507, em12507, dsL]

noncomputable def master12507 : MasterCertificate 12507 world12507 agent12507 :=
  master scalar12507 dsL tp12507 tm12507 ep12507 em12507
    (by norm_num [dsL]) (by norm_num [tp12507]) (by norm_num [tm12507])
    (by norm_num [ep12507]) (by norm_num [em12507])
    positive12507 negative12507 tails12507.1 tails12507.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12507.1 tailGuards12507.2

theorem preserves12507 : master12507.toScalarCertificate = scalar12507 := rfl

noncomputable def tp12508 : ℝ := (459600091 / 2000000000)
noncomputable def tm12508 : ℝ := (-((6021802619 / 10000000000)))
noncomputable def ep12508 : ℝ := (10174282489498669 / 20000000000000000000)
noncomputable def em12508 : ℝ := (3101693963037321 / 6250000000000000000)
noncomputable def bp12508 : ℝ := (564265167798036089 / 1250000000000000000)
noncomputable def bm12508 : ℝ := (46028023807227991973 / 100000000000000000000)

theorem positive12508 :
    Eplus aL (agent12508.root+dsL) scalar12508.worldRadius world12508.frame
      agent12508.frame tp12508 ≤ -ep12508 := by
  apply positive_check (eT := (115533390695426025477 / 100000000000000000000)) (y := (37716834319242967679 / 100000000000000000000)) (u := (7290748791480852953 / 5000000000000000000))
  · norm_num [world12508, agent12508, scalar12508, tp12508, tm12508, ep12508, em12508, dsL]
  · norm_num [world12508, agent12508, scalar12508, tp12508, tm12508, ep12508, em12508, dsL]
  · norm_num [world12508, agent12508, scalar12508, tp12508, tm12508, ep12508, em12508, dsL]
  · norm_num [world12508, agent12508, scalar12508, tp12508, tm12508, ep12508, em12508, dsL]
  · norm_num [world12508, agent12508, scalar12508, tp12508, tm12508, ep12508, em12508, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12508, agent12508, tp12508, tm12508, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12508, agent12508, scalar12508, tp12508, tm12508, ep12508, em12508, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12508, agent12508, tp12508, tm12508, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12508, agent12508, scalar12508, tp12508, tm12508, ep12508, em12508, dsL]

theorem negative12508 :
    Eminus aL (agent12508.root+dsL) scalar12508.worldRadius world12508.frame
      agent12508.frame tm12508 ≤ -em12508 := by
  apply negative_check (lo := (68497998420304454819 / 100000000000000000000)) (hi := (3424899921015222741 / 5000000000000000000))
    (y := (-((3585221371768703497 / 5000000000000000000)))) (u := (12204827259824122193 / 25000000000000000000))
  · norm_num [world12508, agent12508, scalar12508, tp12508, tm12508, ep12508, em12508, dsL]
  · norm_num [world12508, agent12508, scalar12508, tp12508, tm12508, ep12508, em12508, dsL]
  · norm_num [world12508, agent12508, scalar12508, tp12508, tm12508, ep12508, em12508, dsL]
  · norm_num [world12508, agent12508, scalar12508, tp12508, tm12508, ep12508, em12508, dsL]
  · norm_num [world12508, agent12508, scalar12508, tp12508, tm12508, ep12508, em12508, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12508, agent12508, tp12508, tm12508, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12508, agent12508, tp12508, tm12508, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12508, agent12508, scalar12508, tp12508, tm12508, ep12508, em12508, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12508, agent12508, tp12508, tm12508, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12508, agent12508, scalar12508, tp12508, tm12508, ep12508, em12508, dsL]

theorem tails12508 :
    exp (-((12508:ℝ)*ep12508)) ≤ scalar12508.upperTail ∧
    exp (-((12508:ℝ)*em12508)) ≤ scalar12508.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12508:ℝ)) (by norm_num [ep12508]) ?_)
      (show bp12508^8 ≤ scalar12508.upperTail by norm_num [bp12508, scalar12508])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12508, bp12508, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12508:ℝ)) (by norm_num [em12508]) ?_)
      (show bm12508^8 ≤ scalar12508.lowerTail by norm_num [bm12508, scalar12508])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12508, bm12508, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12508 :
    agent12508.root+dsL+scalar12508.worldRadius < √(1/100/aL) ∧
    2*(agent12508.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12508, agent12508, scalar12508, tp12508, tm12508, ep12508, em12508, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12508, agent12508, scalar12508, tp12508, tm12508, ep12508, em12508, dsL]

noncomputable def master12508 : MasterCertificate 12508 world12508 agent12508 :=
  master scalar12508 dsL tp12508 tm12508 ep12508 em12508
    (by norm_num [dsL]) (by norm_num [tp12508]) (by norm_num [tm12508])
    (by norm_num [ep12508]) (by norm_num [em12508])
    positive12508 negative12508 tails12508.1 tails12508.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12508.1 tailGuards12508.2

theorem preserves12508 : master12508.toScalarCertificate = scalar12508 := rfl

noncomputable def tp12509 : ℝ := (1149046139 / 5000000000)
noncomputable def tm12509 : ℝ := (-((6022001151 / 10000000000)))
noncomputable def ep12509 : ℝ := (50874254463320727 / 100000000000000000000)
noncomputable def em12509 : ℝ := (49629555929363477 / 100000000000000000000)
noncomputable def bp12509 : ℝ := (282102107401040479 / 625000000000000000)
noncomputable def bm12509 : ℝ := (23011701824553679187 / 50000000000000000000)

theorem positive12509 :
    Eplus aL (agent12509.root+dsL) scalar12509.worldRadius world12509.frame
      agent12509.frame tp12509 ≤ -ep12509 := by
  apply positive_check (eT := (115533678138620941021 / 100000000000000000000)) (y := (37717693192578692319 / 100000000000000000000)) (u := (145816228200942086959 / 100000000000000000000))
  · norm_num [world12509, agent12509, scalar12509, tp12509, tm12509, ep12509, em12509, dsL]
  · norm_num [world12509, agent12509, scalar12509, tp12509, tm12509, ep12509, em12509, dsL]
  · norm_num [world12509, agent12509, scalar12509, tp12509, tm12509, ep12509, em12509, dsL]
  · norm_num [world12509, agent12509, scalar12509, tp12509, tm12509, ep12509, em12509, dsL]
  · norm_num [world12509, agent12509, scalar12509, tp12509, tm12509, ep12509, em12509, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12509, agent12509, tp12509, tm12509, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12509, agent12509, scalar12509, tp12509, tm12509, ep12509, em12509, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12509, agent12509, tp12509, tm12509, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12509, agent12509, scalar12509, tp12509, tm12509, ep12509, em12509, dsL]

theorem negative12509 :
    Eminus aL (agent12509.root+dsL) scalar12509.worldRadius world12509.frame
      agent12509.frame tm12509 ≤ -em12509 := by
  apply negative_check (lo := (1070277077679833571 / 1562500000000000000)) (hi := (13699546594301869709 / 20000000000000000000))
    (y := (-((71704574115896801147 / 100000000000000000000)))) (u := (6102404678866414243 / 12500000000000000000))
  · norm_num [world12509, agent12509, scalar12509, tp12509, tm12509, ep12509, em12509, dsL]
  · norm_num [world12509, agent12509, scalar12509, tp12509, tm12509, ep12509, em12509, dsL]
  · norm_num [world12509, agent12509, scalar12509, tp12509, tm12509, ep12509, em12509, dsL]
  · norm_num [world12509, agent12509, scalar12509, tp12509, tm12509, ep12509, em12509, dsL]
  · norm_num [world12509, agent12509, scalar12509, tp12509, tm12509, ep12509, em12509, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12509, agent12509, tp12509, tm12509, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12509, agent12509, tp12509, tm12509, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12509, agent12509, scalar12509, tp12509, tm12509, ep12509, em12509, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12509, agent12509, tp12509, tm12509, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12509, agent12509, scalar12509, tp12509, tm12509, ep12509, em12509, dsL]

theorem tails12509 :
    exp (-((12509:ℝ)*ep12509)) ≤ scalar12509.upperTail ∧
    exp (-((12509:ℝ)*em12509)) ≤ scalar12509.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12509:ℝ)) (by norm_num [ep12509]) ?_)
      (show bp12509^8 ≤ scalar12509.upperTail by norm_num [bp12509, scalar12509])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12509, bp12509, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12509:ℝ)) (by norm_num [em12509]) ?_)
      (show bm12509^8 ≤ scalar12509.lowerTail by norm_num [bm12509, scalar12509])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12509, bm12509, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12509 :
    agent12509.root+dsL+scalar12509.worldRadius < √(1/100/aL) ∧
    2*(agent12509.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12509, agent12509, scalar12509, tp12509, tm12509, ep12509, em12509, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12509, agent12509, scalar12509, tp12509, tm12509, ep12509, em12509, dsL]

noncomputable def master12509 : MasterCertificate 12509 world12509 agent12509 :=
  master scalar12509 dsL tp12509 tm12509 ep12509 em12509
    (by norm_num [dsL]) (by norm_num [tp12509]) (by norm_num [tm12509])
    (by norm_num [ep12509]) (by norm_num [em12509])
    positive12509 negative12509 tails12509.1 tails12509.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12509.1 tailGuards12509.2

theorem preserves12509 : master12509.toScalarCertificate = scalar12509 := rfl

noncomputable def tp12510 : ℝ := (2298259991 / 10000000000)
noncomputable def tm12510 : ℝ := (-((3011214537 / 5000000000)))
noncomputable def ep12510 : ℝ := (25439278492716219 / 50000000000000000000)
noncomputable def em12510 : ℝ := (6204199725880221 / 12500000000000000000)
noncomputable def bp12510 : ℝ := (11282607604981707517 / 25000000000000000000)
noncomputable def bm12510 : ℝ := (23008819977900196389 / 50000000000000000000)

theorem positive12510 :
    Eplus aL (agent12510.root+dsL) scalar12510.worldRadius world12510.frame
      agent12510.frame tp12510 ≤ -ep12510 := by
  apply positive_check (eT := (7220907281183086753 / 6250000000000000000)) (y := (1508712721192782821 / 4000000000000000000)) (u := (145816410234011748191 / 100000000000000000000))
  · norm_num [world12510, agent12510, scalar12510, tp12510, tm12510, ep12510, em12510, dsL]
  · norm_num [world12510, agent12510, scalar12510, tp12510, tm12510, ep12510, em12510, dsL]
  · norm_num [world12510, agent12510, scalar12510, tp12510, tm12510, ep12510, em12510, dsL]
  · norm_num [world12510, agent12510, scalar12510, tp12510, tm12510, ep12510, em12510, dsL]
  · norm_num [world12510, agent12510, scalar12510, tp12510, tm12510, ep12510, em12510, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12510, agent12510, tp12510, tm12510, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12510, agent12510, scalar12510, tp12510, tm12510, ep12510, em12510, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12510, agent12510, tp12510, tm12510, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12510, agent12510, scalar12510, tp12510, tm12510, ep12510, em12510, dsL]

theorem negative12510 :
    Eminus aL (agent12510.root+dsL) scalar12510.worldRadius world12510.frame
      agent12510.frame tm12510 ≤ -em12510 := by
  apply negative_check (lo := (34248240123974378449 / 50000000000000000000)) (hi := (68496480247948756899 / 100000000000000000000))
    (y := (-((143405574214965563 / 200000000000000000)))) (u := (48820109842606876723 / 100000000000000000000))
  · norm_num [world12510, agent12510, scalar12510, tp12510, tm12510, ep12510, em12510, dsL]
  · norm_num [world12510, agent12510, scalar12510, tp12510, tm12510, ep12510, em12510, dsL]
  · norm_num [world12510, agent12510, scalar12510, tp12510, tm12510, ep12510, em12510, dsL]
  · norm_num [world12510, agent12510, scalar12510, tp12510, tm12510, ep12510, em12510, dsL]
  · norm_num [world12510, agent12510, scalar12510, tp12510, tm12510, ep12510, em12510, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12510, agent12510, tp12510, tm12510, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12510, agent12510, tp12510, tm12510, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12510, agent12510, scalar12510, tp12510, tm12510, ep12510, em12510, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12510, agent12510, tp12510, tm12510, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12510, agent12510, scalar12510, tp12510, tm12510, ep12510, em12510, dsL]

theorem tails12510 :
    exp (-((12510:ℝ)*ep12510)) ≤ scalar12510.upperTail ∧
    exp (-((12510:ℝ)*em12510)) ≤ scalar12510.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12510:ℝ)) (by norm_num [ep12510]) ?_)
      (show bp12510^8 ≤ scalar12510.upperTail by norm_num [bp12510, scalar12510])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12510, bp12510, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12510:ℝ)) (by norm_num [em12510]) ?_)
      (show bm12510^8 ≤ scalar12510.lowerTail by norm_num [bm12510, scalar12510])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12510, bm12510, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12510 :
    agent12510.root+dsL+scalar12510.worldRadius < √(1/100/aL) ∧
    2*(agent12510.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12510, agent12510, scalar12510, tp12510, tm12510, ep12510, em12510, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12510, agent12510, scalar12510, tp12510, tm12510, ep12510, em12510, dsL]

noncomputable def master12510 : MasterCertificate 12510 world12510 agent12510 :=
  master scalar12510 dsL tp12510 tm12510 ep12510 em12510
    (by norm_num [dsL]) (by norm_num [tp12510]) (by norm_num [tm12510])
    (by norm_num [ep12510]) (by norm_num [em12510])
    positive12510 negative12510 tails12510.1 tails12510.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12510.1 tailGuards12510.2

theorem preserves12510 : master12510.toScalarCertificate = scalar12510 := rfl

noncomputable def tp12511 : ℝ := (1149175891 / 5000000000)
noncomputable def tm12511 : ℝ := (-((6022627213 / 10000000000)))
noncomputable def ep12511 : ℝ := (10176279076628473 / 20000000000000000000)
noncomputable def em12511 : ℝ := (24818023488782121 / 50000000000000000000)
noncomputable def bp12511 : ℝ := (9025111434952489909 / 20000000000000000000)
noncomputable def bm12511 : ℝ := (11503255648779011197 / 25000000000000000000)

theorem positive12511 :
    Eplus aL (agent12511.root+dsL) scalar12511.worldRadius world12511.frame
      agent12511.frame tp12511 ≤ -ep12511 := by
  apply positive_check (eT := (57767401881728649633 / 50000000000000000000)) (y := (18859338604382355907 / 50000000000000000000)) (u := (29163532612657810929 / 20000000000000000000))
  · norm_num [world12511, agent12511, scalar12511, tp12511, tm12511, ep12511, em12511, dsL]
  · norm_num [world12511, agent12511, scalar12511, tp12511, tm12511, ep12511, em12511, dsL]
  · norm_num [world12511, agent12511, scalar12511, tp12511, tm12511, ep12511, em12511, dsL]
  · norm_num [world12511, agent12511, scalar12511, tp12511, tm12511, ep12511, em12511, dsL]
  · norm_num [world12511, agent12511, scalar12511, tp12511, tm12511, ep12511, em12511, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12511, agent12511, tp12511, tm12511, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12511, agent12511, scalar12511, tp12511, tm12511, ep12511, em12511, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12511, agent12511, tp12511, tm12511, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12511, agent12511, scalar12511, tp12511, tm12511, ep12511, em12511, dsL]

theorem negative12511 :
    Eminus aL (agent12511.root+dsL) scalar12511.worldRadius world12511.frame
      agent12511.frame tm12511 ≤ -em12511 := by
  apply negative_check (lo := (68496216403892487631 / 100000000000000000000)) (hi := (4281013525243280477 / 6250000000000000000))
    (y := (-((35851465558736179347 / 50000000000000000000)))) (u := (48820039536822404499 / 100000000000000000000))
  · norm_num [world12511, agent12511, scalar12511, tp12511, tm12511, ep12511, em12511, dsL]
  · norm_num [world12511, agent12511, scalar12511, tp12511, tm12511, ep12511, em12511, dsL]
  · norm_num [world12511, agent12511, scalar12511, tp12511, tm12511, ep12511, em12511, dsL]
  · norm_num [world12511, agent12511, scalar12511, tp12511, tm12511, ep12511, em12511, dsL]
  · norm_num [world12511, agent12511, scalar12511, tp12511, tm12511, ep12511, em12511, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12511, agent12511, tp12511, tm12511, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12511, agent12511, tp12511, tm12511, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12511, agent12511, scalar12511, tp12511, tm12511, ep12511, em12511, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12511, agent12511, tp12511, tm12511, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12511, agent12511, scalar12511, tp12511, tm12511, ep12511, em12511, dsL]

theorem tails12511 :
    exp (-((12511:ℝ)*ep12511)) ≤ scalar12511.upperTail ∧
    exp (-((12511:ℝ)*em12511)) ≤ scalar12511.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12511:ℝ)) (by norm_num [ep12511]) ?_)
      (show bp12511^8 ≤ scalar12511.upperTail by norm_num [bp12511, scalar12511])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12511, bp12511, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12511:ℝ)) (by norm_num [em12511]) ?_)
      (show bm12511^8 ≤ scalar12511.lowerTail by norm_num [bm12511, scalar12511])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12511, bm12511, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12511 :
    agent12511.root+dsL+scalar12511.worldRadius < √(1/100/aL) ∧
    2*(agent12511.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12511, agent12511, scalar12511, tp12511, tm12511, ep12511, em12511, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12511, agent12511, scalar12511, tp12511, tm12511, ep12511, em12511, dsL]

noncomputable def master12511 : MasterCertificate 12511 world12511 agent12511 :=
  master scalar12511 dsL tp12511 tm12511 ep12511 em12511
    (by norm_num [dsL]) (by norm_num [tp12511]) (by norm_num [tm12511])
    (by norm_num [ep12511]) (by norm_num [em12511])
    positive12511 negative12511 tails12511.1 tails12511.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12511.1 tailGuards12511.2

theorem preserves12511 : master12511.toScalarCertificate = scalar12511 := rfl

noncomputable def tp12512 : ℝ := (2298443407 / 10000000000)
noncomputable def tm12512 : ℝ := (-((3011412619 / 5000000000)))
noncomputable def ep12512 : ℝ := (25442116392041697 / 50000000000000000000)
noncomputable def em12512 : ℝ := (24819247606443579 / 50000000000000000000)
noncomputable def bp12512 : ℝ := (11280171209762234857 / 25000000000000000000)
noncomputable def bm12512 : ℝ := (9201681217793912101 / 20000000000000000000)

theorem positive12512 :
    Eplus aL (agent12512.root+dsL) scalar12512.worldRadius world12512.frame
      agent12512.frame tp12512 ≤ -ep12512 := by
  apply positive_check (eT := (28883772463850698953 / 25000000000000000000)) (y := (4714941740089805057 / 12500000000000000000)) (u := (145818912305990363733 / 100000000000000000000))
  · norm_num [world12512, agent12512, scalar12512, tp12512, tm12512, ep12512, em12512, dsL]
  · norm_num [world12512, agent12512, scalar12512, tp12512, tm12512, ep12512, em12512, dsL]
  · norm_num [world12512, agent12512, scalar12512, tp12512, tm12512, ep12512, em12512, dsL]
  · norm_num [world12512, agent12512, scalar12512, tp12512, tm12512, ep12512, em12512, dsL]
  · norm_num [world12512, agent12512, scalar12512, tp12512, tm12512, ep12512, em12512, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12512, agent12512, tp12512, tm12512, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12512, agent12512, scalar12512, tp12512, tm12512, ep12512, em12512, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12512, agent12512, tp12512, tm12512, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12512, agent12512, scalar12512, tp12512, tm12512, ep12512, em12512, dsL]

theorem negative12512 :
    Eminus aL (agent12512.root+dsL) scalar12512.worldRadius world12512.frame
      agent12512.frame tm12512 ≤ -em12512 := by
  apply negative_check (lo := (34247976496990532507 / 50000000000000000000)) (hi := (13699190598796213003 / 20000000000000000000))
    (y := (-((14340615012743923239 / 20000000000000000000)))) (u := (24409984631129080213 / 50000000000000000000))
  · norm_num [world12512, agent12512, scalar12512, tp12512, tm12512, ep12512, em12512, dsL]
  · norm_num [world12512, agent12512, scalar12512, tp12512, tm12512, ep12512, em12512, dsL]
  · norm_num [world12512, agent12512, scalar12512, tp12512, tm12512, ep12512, em12512, dsL]
  · norm_num [world12512, agent12512, scalar12512, tp12512, tm12512, ep12512, em12512, dsL]
  · norm_num [world12512, agent12512, scalar12512, tp12512, tm12512, ep12512, em12512, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12512, agent12512, tp12512, tm12512, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12512, agent12512, tp12512, tm12512, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12512, agent12512, scalar12512, tp12512, tm12512, ep12512, em12512, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12512, agent12512, tp12512, tm12512, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12512, agent12512, scalar12512, tp12512, tm12512, ep12512, em12512, dsL]

theorem tails12512 :
    exp (-((12512:ℝ)*ep12512)) ≤ scalar12512.upperTail ∧
    exp (-((12512:ℝ)*em12512)) ≤ scalar12512.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12512:ℝ)) (by norm_num [ep12512]) ?_)
      (show bp12512^8 ≤ scalar12512.upperTail by norm_num [bp12512, scalar12512])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12512, bp12512, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12512:ℝ)) (by norm_num [em12512]) ?_)
      (show bm12512^8 ≤ scalar12512.lowerTail by norm_num [bm12512, scalar12512])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12512, bm12512, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12512 :
    agent12512.root+dsL+scalar12512.worldRadius < √(1/100/aL) ∧
    2*(agent12512.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12512, agent12512, scalar12512, tp12512, tm12512, ep12512, em12512, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12512, agent12512, scalar12512, tp12512, tm12512, ep12512, em12512, dsL]

noncomputable def master12512 : MasterCertificate 12512 world12512 agent12512 :=
  master scalar12512 dsL tp12512 tm12512 ep12512 em12512
    (by norm_num [dsL]) (by norm_num [tp12512]) (by norm_num [tm12512])
    (by norm_num [ep12512]) (by norm_num [em12512])
    positive12512 negative12512 tails12512.1 tails12512.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12512.1 tailGuards12512.2

theorem preserves12512 : master12512.toScalarCertificate = scalar12512 := rfl

noncomputable def tp12513 : ℝ := (287316879 / 1250000000)
noncomputable def tm12513 : ℝ := (-((6023023359 / 10000000000)))
noncomputable def ep12513 : ℝ := (50887068865950059 / 100000000000000000000)
noncomputable def em12513 : ℝ := (6205117778956427 / 12500000000000000000)
noncomputable def bp12513 : ℝ := (11278953410053635631 / 25000000000000000000)
noncomputable def bm12513 : ℝ := (46003790639811879627 / 100000000000000000000)

theorem positive12513 :
    Eplus aL (agent12513.root+dsL) scalar12513.worldRadius world12513.frame
      agent12513.frame tp12513 ≤ -ep12513 := by
  apply positive_check (eT := (115535375979742122971 / 100000000000000000000)) (y := (7544078197670689547 / 20000000000000000000)) (u := (72910081039024573143 / 50000000000000000000))
  · norm_num [world12513, agent12513, scalar12513, tp12513, tm12513, ep12513, em12513, dsL]
  · norm_num [world12513, agent12513, scalar12513, tp12513, tm12513, ep12513, em12513, dsL]
  · norm_num [world12513, agent12513, scalar12513, tp12513, tm12513, ep12513, em12513, dsL]
  · norm_num [world12513, agent12513, scalar12513, tp12513, tm12513, ep12513, em12513, dsL]
  · norm_num [world12513, agent12513, scalar12513, tp12513, tm12513, ep12513, em12513, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12513, agent12513, tp12513, tm12513, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12513, agent12513, scalar12513, tp12513, tm12513, ep12513, em12513, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12513, agent12513, tp12513, tm12513, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12513, agent12513, scalar12513, tp12513, tm12513, ep12513, em12513, dsL]

theorem negative12513 :
    Eminus aL (agent12513.root+dsL) scalar12513.worldRadius world12513.frame
      agent12513.frame tm12513 ≤ -em12513 := by
  apply negative_check (lo := (68495689114520059947 / 100000000000000000000)) (hi := (17123922278630014987 / 25000000000000000000))
    (y := (-((71703220586218916479 / 100000000000000000000)))) (u := (48819898218270424863 / 100000000000000000000))
  · norm_num [world12513, agent12513, scalar12513, tp12513, tm12513, ep12513, em12513, dsL]
  · norm_num [world12513, agent12513, scalar12513, tp12513, tm12513, ep12513, em12513, dsL]
  · norm_num [world12513, agent12513, scalar12513, tp12513, tm12513, ep12513, em12513, dsL]
  · norm_num [world12513, agent12513, scalar12513, tp12513, tm12513, ep12513, em12513, dsL]
  · norm_num [world12513, agent12513, scalar12513, tp12513, tm12513, ep12513, em12513, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12513, agent12513, tp12513, tm12513, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12513, agent12513, tp12513, tm12513, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12513, agent12513, scalar12513, tp12513, tm12513, ep12513, em12513, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12513, agent12513, tp12513, tm12513, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12513, agent12513, scalar12513, tp12513, tm12513, ep12513, em12513, dsL]

theorem tails12513 :
    exp (-((12513:ℝ)*ep12513)) ≤ scalar12513.upperTail ∧
    exp (-((12513:ℝ)*em12513)) ≤ scalar12513.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12513:ℝ)) (by norm_num [ep12513]) ?_)
      (show bp12513^8 ≤ scalar12513.upperTail by norm_num [bp12513, scalar12513])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12513, bp12513, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12513:ℝ)) (by norm_num [em12513]) ?_)
      (show bm12513^8 ≤ scalar12513.lowerTail by norm_num [bm12513, scalar12513])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12513, bm12513, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12513 :
    agent12513.root+dsL+scalar12513.worldRadius < √(1/100/aL) ∧
    2*(agent12513.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12513, agent12513, scalar12513, tp12513, tm12513, ep12513, em12513, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12513, agent12513, scalar12513, tp12513, tm12513, ep12513, em12513, dsL]

noncomputable def master12513 : MasterCertificate 12513 world12513 agent12513 :=
  master scalar12513 dsL tp12513 tm12513 ep12513 em12513
    (by norm_num [dsL]) (by norm_num [tp12513]) (by norm_num [tm12513])
    (by norm_num [ep12513]) (by norm_num [em12513])
    positive12513 negative12513 tails12513.1 tails12513.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12513.1 tailGuards12513.2

theorem preserves12513 : master12513.toScalarCertificate = scalar12513 := rfl

noncomputable def tp12514 : ℝ := (1149313319 / 5000000000)
noncomputable def tm12514 : ℝ := (-((1505805291 / 2500000000)))
noncomputable def ep12514 : ℝ := (1590309483706991 / 3125000000000000000)
noncomputable def em12514 : ℝ := (49643387878719289 / 100000000000000000000)
noncomputable def bp12514 : ℝ := (45110943684158688757 / 100000000000000000000)
noncomputable def bm12514 : ℝ := (9199835271851160579 / 20000000000000000000)

theorem positive12514 :
    Eplus aL (agent12514.root+dsL) scalar12514.worldRadius world12514.frame
      agent12514.frame tp12514 ≤ -ep12514 := by
  apply positive_check (eT := (57767830999299754839 / 50000000000000000000)) (y := (301769985825088891 / 800000000000000000)) (u := (5832856484473900391 / 4000000000000000000))
  · norm_num [world12514, agent12514, scalar12514, tp12514, tm12514, ep12514, em12514, dsL]
  · norm_num [world12514, agent12514, scalar12514, tp12514, tm12514, ep12514, em12514, dsL]
  · norm_num [world12514, agent12514, scalar12514, tp12514, tm12514, ep12514, em12514, dsL]
  · norm_num [world12514, agent12514, scalar12514, tp12514, tm12514, ep12514, em12514, dsL]
  · norm_num [world12514, agent12514, scalar12514, tp12514, tm12514, ep12514, em12514, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12514, agent12514, tp12514, tm12514, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12514, agent12514, scalar12514, tp12514, tm12514, ep12514, em12514, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12514, agent12514, tp12514, tm12514, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12514, agent12514, scalar12514, tp12514, tm12514, ep12514, em12514, dsL]

theorem negative12514 :
    Eminus aL (agent12514.root+dsL) scalar12514.worldRadius world12514.frame
      agent12514.frame tm12514 ≤ -em12514 := by
  apply negative_check (lo := (68495426538394536751 / 100000000000000000000)) (hi := (4280964158649658547 / 6250000000000000000))
    (y := (-((1434067278746466173 / 2000000000000000000)))) (u := (9763965646891465427 / 20000000000000000000))
  · norm_num [world12514, agent12514, scalar12514, tp12514, tm12514, ep12514, em12514, dsL]
  · norm_num [world12514, agent12514, scalar12514, tp12514, tm12514, ep12514, em12514, dsL]
  · norm_num [world12514, agent12514, scalar12514, tp12514, tm12514, ep12514, em12514, dsL]
  · norm_num [world12514, agent12514, scalar12514, tp12514, tm12514, ep12514, em12514, dsL]
  · norm_num [world12514, agent12514, scalar12514, tp12514, tm12514, ep12514, em12514, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12514, agent12514, tp12514, tm12514, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12514, agent12514, tp12514, tm12514, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12514, agent12514, scalar12514, tp12514, tm12514, ep12514, em12514, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12514, agent12514, tp12514, tm12514, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12514, agent12514, scalar12514, tp12514, tm12514, ep12514, em12514, dsL]

theorem tails12514 :
    exp (-((12514:ℝ)*ep12514)) ≤ scalar12514.upperTail ∧
    exp (-((12514:ℝ)*em12514)) ≤ scalar12514.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12514:ℝ)) (by norm_num [ep12514]) ?_)
      (show bp12514^8 ≤ scalar12514.upperTail by norm_num [bp12514, scalar12514])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12514, bp12514, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12514:ℝ)) (by norm_num [em12514]) ?_)
      (show bm12514^8 ≤ scalar12514.lowerTail by norm_num [bm12514, scalar12514])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12514, bm12514, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12514 :
    agent12514.root+dsL+scalar12514.worldRadius < √(1/100/aL) ∧
    2*(agent12514.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12514, agent12514, scalar12514, tp12514, tm12514, ep12514, em12514, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12514, agent12514, scalar12514, tp12514, tm12514, ep12514, em12514, dsL]

noncomputable def master12514 : MasterCertificate 12514 world12514 agent12514 :=
  master scalar12514 dsL tp12514 tm12514 ep12514 em12514
    (by norm_num [dsL]) (by norm_num [tp12514]) (by norm_num [tm12514])
    (by norm_num [ep12514]) (by norm_num [em12514])
    positive12514 negative12514 tails12514.1 tails12514.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12514.1 tailGuards12514.2

theorem preserves12514 : master12514.toScalarCertificate = scalar12514 := rfl

noncomputable def tp12515 : ℝ := (287339769 / 1250000000)
noncomputable def tm12515 : ℝ := (-((6023418843 / 10000000000)))
noncomputable def ep12515 : ℝ := (25446368156185597 / 50000000000000000000)
noncomputable def em12515 : ℝ := (49645831889831247 / 100000000000000000000)
noncomputable def bp12515 : ℝ := (2819129699337337743 / 6250000000000000000)
noncomputable def bm12515 : ℝ := (2299728171871057037 / 5000000000000000000)

theorem positive12515 :
    Eplus aL (agent12515.root+dsL) scalar12515.worldRadius world12515.frame
      agent12515.frame tp12515 ≤ -ep12515 := by
  apply positive_check (eT := (28883986845520989817 / 25000000000000000000)) (y := (37722104352365132669 / 100000000000000000000)) (u := (145822660529631696233 / 100000000000000000000))
  · norm_num [world12515, agent12515, scalar12515, tp12515, tm12515, ep12515, em12515, dsL]
  · norm_num [world12515, agent12515, scalar12515, tp12515, tm12515, ep12515, em12515, dsL]
  · norm_num [world12515, agent12515, scalar12515, tp12515, tm12515, ep12515, em12515, dsL]
  · norm_num [world12515, agent12515, scalar12515, tp12515, tm12515, ep12515, em12515, dsL]
  · norm_num [world12515, agent12515, scalar12515, tp12515, tm12515, ep12515, em12515, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12515, agent12515, tp12515, tm12515, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12515, agent12515, scalar12515, tp12515, tm12515, ep12515, em12515, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12515, agent12515, tp12515, tm12515, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12515, agent12515, scalar12515, tp12515, tm12515, ep12515, em12515, dsL]

theorem negative12515 :
    Eminus aL (agent12515.root+dsL) scalar12515.worldRadius world12515.frame
      agent12515.frame tm12515 ≤ -em12515 := by
  apply negative_check (lo := (34247582223995521453 / 50000000000000000000)) (hi := (68495164447991042907 / 100000000000000000000))
    (y := (-((71703506974419719407 / 100000000000000000000)))) (u := (48819758404042489559 / 100000000000000000000))
  · norm_num [world12515, agent12515, scalar12515, tp12515, tm12515, ep12515, em12515, dsL]
  · norm_num [world12515, agent12515, scalar12515, tp12515, tm12515, ep12515, em12515, dsL]
  · norm_num [world12515, agent12515, scalar12515, tp12515, tm12515, ep12515, em12515, dsL]
  · norm_num [world12515, agent12515, scalar12515, tp12515, tm12515, ep12515, em12515, dsL]
  · norm_num [world12515, agent12515, scalar12515, tp12515, tm12515, ep12515, em12515, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12515, agent12515, tp12515, tm12515, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12515, agent12515, tp12515, tm12515, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12515, agent12515, scalar12515, tp12515, tm12515, ep12515, em12515, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12515, agent12515, tp12515, tm12515, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12515, agent12515, scalar12515, tp12515, tm12515, ep12515, em12515, dsL]

theorem tails12515 :
    exp (-((12515:ℝ)*ep12515)) ≤ scalar12515.upperTail ∧
    exp (-((12515:ℝ)*em12515)) ≤ scalar12515.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12515:ℝ)) (by norm_num [ep12515]) ?_)
      (show bp12515^8 ≤ scalar12515.upperTail by norm_num [bp12515, scalar12515])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12515, bp12515, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12515:ℝ)) (by norm_num [em12515]) ?_)
      (show bm12515^8 ≤ scalar12515.lowerTail by norm_num [bm12515, scalar12515])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12515, bm12515, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12515 :
    agent12515.root+dsL+scalar12515.worldRadius < √(1/100/aL) ∧
    2*(agent12515.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12515, agent12515, scalar12515, tp12515, tm12515, ep12515, em12515, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12515, agent12515, scalar12515, tp12515, tm12515, ep12515, em12515, dsL]

noncomputable def master12515 : MasterCertificate 12515 world12515 agent12515 :=
  master scalar12515 dsL tp12515 tm12515 ep12515 em12515
    (by norm_num [dsL]) (by norm_num [tp12515]) (by norm_num [tm12515])
    (by norm_num [ep12515]) (by norm_num [em12515])
    positive12515 negative12515 tails12515.1 tails12515.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12515.1 tailGuards12515.2

theorem preserves12515 : master12515.toScalarCertificate = scalar12515 := rfl

noncomputable def tp12516 : ℝ := (2298809597 / 10000000000)
noncomputable def tm12516 : ℝ := (-((6023616591 / 10000000000)))
noncomputable def ep12516 : ℝ := (50895568146249697 / 100000000000000000000)
noncomputable def em12516 : ℝ := (12412068739236329 / 25000000000000000000)
noncomputable def bp12516 : ℝ := (45101207606162594319 / 100000000000000000000)
noncomputable def bm12516 : ℝ := (45989951376401430241 / 100000000000000000000)

theorem positive12516 :
    Eplus aL (agent12516.root+dsL) scalar12516.worldRadius world12516.frame
      agent12516.frame tp12516 ≤ -ep12516 := by
  apply positive_check (eT := (115536232297207088213 / 100000000000000000000)) (y := (7544591923321993211 / 20000000000000000000)) (u := (18227988463005172717 / 12500000000000000000))
  · norm_num [world12516, agent12516, scalar12516, tp12516, tm12516, ep12516, em12516, dsL]
  · norm_num [world12516, agent12516, scalar12516, tp12516, tm12516, ep12516, em12516, dsL]
  · norm_num [world12516, agent12516, scalar12516, tp12516, tm12516, ep12516, em12516, dsL]
  · norm_num [world12516, agent12516, scalar12516, tp12516, tm12516, ep12516, em12516, dsL]
  · norm_num [world12516, agent12516, scalar12516, tp12516, tm12516, ep12516, em12516, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12516, agent12516, tp12516, tm12516, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12516, agent12516, scalar12516, tp12516, tm12516, ep12516, em12516, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12516, agent12516, tp12516, tm12516, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12516, agent12516, scalar12516, tp12516, tm12516, ep12516, em12516, dsL]

theorem negative12516 :
    Eminus aL (agent12516.root+dsL) scalar12516.worldRadius world12516.frame
      agent12516.frame tm12516 ≤ -em12516 := by
  apply negative_check (lo := (34247451002072260903 / 50000000000000000000)) (hi := (68494902004144521807 / 100000000000000000000))
    (y := (-((14340730265048706951 / 20000000000000000000)))) (u := (48819687932369911893 / 100000000000000000000))
  · norm_num [world12516, agent12516, scalar12516, tp12516, tm12516, ep12516, em12516, dsL]
  · norm_num [world12516, agent12516, scalar12516, tp12516, tm12516, ep12516, em12516, dsL]
  · norm_num [world12516, agent12516, scalar12516, tp12516, tm12516, ep12516, em12516, dsL]
  · norm_num [world12516, agent12516, scalar12516, tp12516, tm12516, ep12516, em12516, dsL]
  · norm_num [world12516, agent12516, scalar12516, tp12516, tm12516, ep12516, em12516, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12516, agent12516, tp12516, tm12516, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12516, agent12516, tp12516, tm12516, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12516, agent12516, scalar12516, tp12516, tm12516, ep12516, em12516, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12516, agent12516, tp12516, tm12516, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12516, agent12516, scalar12516, tp12516, tm12516, ep12516, em12516, dsL]

theorem tails12516 :
    exp (-((12516:ℝ)*ep12516)) ≤ scalar12516.upperTail ∧
    exp (-((12516:ℝ)*em12516)) ≤ scalar12516.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12516:ℝ)) (by norm_num [ep12516]) ?_)
      (show bp12516^8 ≤ scalar12516.upperTail by norm_num [bp12516, scalar12516])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12516, bp12516, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12516:ℝ)) (by norm_num [em12516]) ?_)
      (show bm12516^8 ≤ scalar12516.lowerTail by norm_num [bm12516, scalar12516])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12516, bm12516, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12516 :
    agent12516.root+dsL+scalar12516.worldRadius < √(1/100/aL) ∧
    2*(agent12516.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12516, agent12516, scalar12516, tp12516, tm12516, ep12516, em12516, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12516, agent12516, scalar12516, tp12516, tm12516, ep12516, em12516, dsL]

noncomputable def master12516 : MasterCertificate 12516 world12516 agent12516 :=
  master scalar12516 dsL tp12516 tm12516 ep12516 em12516
    (by norm_num [dsL]) (by norm_num [tp12516]) (by norm_num [tm12516])
    (by norm_num [ep12516]) (by norm_num [em12516])
    positive12516 negative12516 tails12516.1 tails12516.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12516.1 tailGuards12516.2

theorem preserves12516 : master12516.toScalarCertificate = scalar12516 := rfl

noncomputable def tp12517 : ℝ := (1149450531 / 5000000000)
noncomputable def tm12517 : ℝ := (-((240952563 / 400000000)))
noncomputable def ep12517 : ℝ := (25449199026228979 / 50000000000000000000)
noncomputable def em12517 : ℝ := (12412679056953607 / 25000000000000000000)
noncomputable def bp12517 : ℝ := (22548170794543833599 / 50000000000000000000)
noncomputable def bm12517 : ℝ := (11496335197345862617 / 25000000000000000000)

theorem positive12517 :
    Eplus aL (agent12517.root+dsL) scalar12517.worldRadius world12517.frame
      agent12517.frame tp12517 ≤ -ep12517 := by
  apply positive_check (eT := (11553651738988735273 / 10000000000000000000)) (y := (18861907894200548301 / 50000000000000000000)) (u := (7291257810627427459 / 5000000000000000000))
  · norm_num [world12517, agent12517, scalar12517, tp12517, tm12517, ep12517, em12517, dsL]
  · norm_num [world12517, agent12517, scalar12517, tp12517, tm12517, ep12517, em12517, dsL]
  · norm_num [world12517, agent12517, scalar12517, tp12517, tm12517, ep12517, em12517, dsL]
  · norm_num [world12517, agent12517, scalar12517, tp12517, tm12517, ep12517, em12517, dsL]
  · norm_num [world12517, agent12517, scalar12517, tp12517, tm12517, ep12517, em12517, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12517, agent12517, tp12517, tm12517, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12517, agent12517, scalar12517, tp12517, tm12517, ep12517, em12517, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12517, agent12517, tp12517, tm12517, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12517, agent12517, scalar12517, tp12517, tm12517, ep12517, em12517, dsL]

theorem negative12517 :
    Eminus aL (agent12517.root+dsL) scalar12517.worldRadius world12517.frame
      agent12517.frame tm12517 ≤ -em12517 := by
  apply negative_check (lo := (34247320319916033859 / 50000000000000000000)) (hi := (68494640639832067719 / 100000000000000000000))
    (y := (-((71703793884641318133 / 100000000000000000000)))) (u := (48819618335366404329 / 100000000000000000000))
  · norm_num [world12517, agent12517, scalar12517, tp12517, tm12517, ep12517, em12517, dsL]
  · norm_num [world12517, agent12517, scalar12517, tp12517, tm12517, ep12517, em12517, dsL]
  · norm_num [world12517, agent12517, scalar12517, tp12517, tm12517, ep12517, em12517, dsL]
  · norm_num [world12517, agent12517, scalar12517, tp12517, tm12517, ep12517, em12517, dsL]
  · norm_num [world12517, agent12517, scalar12517, tp12517, tm12517, ep12517, em12517, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12517, agent12517, tp12517, tm12517, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12517, agent12517, tp12517, tm12517, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12517, agent12517, scalar12517, tp12517, tm12517, ep12517, em12517, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12517, agent12517, tp12517, tm12517, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12517, agent12517, scalar12517, tp12517, tm12517, ep12517, em12517, dsL]

theorem tails12517 :
    exp (-((12517:ℝ)*ep12517)) ≤ scalar12517.upperTail ∧
    exp (-((12517:ℝ)*em12517)) ≤ scalar12517.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12517:ℝ)) (by norm_num [ep12517]) ?_)
      (show bp12517^8 ≤ scalar12517.upperTail by norm_num [bp12517, scalar12517])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12517, bp12517, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12517:ℝ)) (by norm_num [em12517]) ?_)
      (show bm12517^8 ≤ scalar12517.lowerTail by norm_num [bm12517, scalar12517])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12517, bm12517, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12517 :
    agent12517.root+dsL+scalar12517.worldRadius < √(1/100/aL) ∧
    2*(agent12517.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12517, agent12517, scalar12517, tp12517, tm12517, ep12517, em12517, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12517, agent12517, scalar12517, tp12517, tm12517, ep12517, em12517, dsL]

noncomputable def master12517 : MasterCertificate 12517 world12517 agent12517 :=
  master scalar12517 dsL tp12517 tm12517 ep12517 em12517
    (by norm_num [dsL]) (by norm_num [tp12517]) (by norm_num [tm12517])
    (by norm_num [ep12517]) (by norm_num [em12517])
    positive12517 negative12517 tails12517.1 tails12517.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12517.1 tailGuards12517.2

theorem preserves12517 : master12517.toScalarCertificate = scalar12517 := rfl

noncomputable def tp12518 : ℝ := (459798489 / 2000000000)
noncomputable def tm12518 : ℝ := (-((3012005737 / 5000000000)))
noncomputable def ep12518 : ℝ := (10180245486082259 / 20000000000000000000)
noncomputable def em12518 : ℝ := (9930631399422881 / 20000000000000000000)
noncomputable def bp12518 : ℝ := (45091476150721088647 / 100000000000000000000)
noncomputable def bm12518 : ℝ := (45980730744828444831 / 100000000000000000000)

theorem positive12518 :
    Eplus aL (agent12518.root+dsL) scalar12518.worldRadius world12518.frame
      agent12518.frame tp12518 ≤ -ep12518 := by
  apply positive_check (eT := (57768400959925632551 / 50000000000000000000)) (y := (18862335461867234617 / 50000000000000000000)) (u := (29165280644063212587 / 20000000000000000000))
  · norm_num [world12518, agent12518, scalar12518, tp12518, tm12518, ep12518, em12518, dsL]
  · norm_num [world12518, agent12518, scalar12518, tp12518, tm12518, ep12518, em12518, dsL]
  · norm_num [world12518, agent12518, scalar12518, tp12518, tm12518, ep12518, em12518, dsL]
  · norm_num [world12518, agent12518, scalar12518, tp12518, tm12518, ep12518, em12518, dsL]
  · norm_num [world12518, agent12518, scalar12518, tp12518, tm12518, ep12518, em12518, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12518, agent12518, tp12518, tm12518, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12518, agent12518, scalar12518, tp12518, tm12518, ep12518, em12518, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12518, agent12518, tp12518, tm12518, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12518, agent12518, scalar12518, tp12518, tm12518, ep12518, em12518, dsL]

theorem negative12518 :
    Eminus aL (agent12518.root+dsL) scalar12518.worldRadius world12518.frame
      agent12518.frame tm12518 ≤ -em12518 := by
  apply negative_check (lo := (8561797448091148863 / 12500000000000000000)) (hi := (13698875916945838181 / 20000000000000000000))
    (y := (-((7170393679012035801 / 10000000000000000000)))) (u := (48819548569506806363 / 100000000000000000000))
  · norm_num [world12518, agent12518, scalar12518, tp12518, tm12518, ep12518, em12518, dsL]
  · norm_num [world12518, agent12518, scalar12518, tp12518, tm12518, ep12518, em12518, dsL]
  · norm_num [world12518, agent12518, scalar12518, tp12518, tm12518, ep12518, em12518, dsL]
  · norm_num [world12518, agent12518, scalar12518, tp12518, tm12518, ep12518, em12518, dsL]
  · norm_num [world12518, agent12518, scalar12518, tp12518, tm12518, ep12518, em12518, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12518, agent12518, tp12518, tm12518, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12518, agent12518, tp12518, tm12518, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12518, agent12518, scalar12518, tp12518, tm12518, ep12518, em12518, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12518, agent12518, tp12518, tm12518, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12518, agent12518, scalar12518, tp12518, tm12518, ep12518, em12518, dsL]

theorem tails12518 :
    exp (-((12518:ℝ)*ep12518)) ≤ scalar12518.upperTail ∧
    exp (-((12518:ℝ)*em12518)) ≤ scalar12518.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12518:ℝ)) (by norm_num [ep12518]) ?_)
      (show bp12518^8 ≤ scalar12518.upperTail by norm_num [bp12518, scalar12518])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12518, bp12518, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12518:ℝ)) (by norm_num [em12518]) ?_)
      (show bm12518^8 ≤ scalar12518.lowerTail by norm_num [bm12518, scalar12518])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12518, bm12518, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12518 :
    agent12518.root+dsL+scalar12518.worldRadius < √(1/100/aL) ∧
    2*(agent12518.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12518, agent12518, scalar12518, tp12518, tm12518, ep12518, em12518, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12518, agent12518, scalar12518, tp12518, tm12518, ep12518, em12518, dsL]

noncomputable def master12518 : MasterCertificate 12518 world12518 agent12518 :=
  master scalar12518 dsL tp12518 tm12518 ep12518 em12518
    (by norm_num [dsL]) (by norm_num [tp12518]) (by norm_num [tm12518])
    (by norm_num [ep12518]) (by norm_num [em12518])
    positive12518 negative12518 tails12518.1 tails12518.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12518.1 tailGuards12518.2

theorem preserves12518 : master12518.toScalarCertificate = scalar12518 := rfl

noncomputable def tp12519 : ℝ := (143692737 / 625000000)
noncomputable def tm12519 : ℝ := (-((6024208659 / 10000000000)))
noncomputable def ep12519 : ℝ := (5090405441728131 / 10000000000000000000)
noncomputable def em12519 : ℝ := (2482779777066711 / 5000000000000000000)
noncomputable def bp12519 : ℝ := (22543306302697540589 / 50000000000000000000)
noncomputable def bm12519 : ℝ := (11494030620691222939 / 25000000000000000000)

theorem positive12519 :
    Eplus aL (agent12519.root+dsL) scalar12519.worldRadius world12519.frame
      agent12519.frame tp12519 ≤ -ep12519 := by
  apply positive_check (eT := (115537086220996077959 / 100000000000000000000)) (y := (943138150703236003 / 2500000000000000000)) (u := (9114228137101905127 / 6250000000000000000))
  · norm_num [world12519, agent12519, scalar12519, tp12519, tm12519, ep12519, em12519, dsL]
  · norm_num [world12519, agent12519, scalar12519, tp12519, tm12519, ep12519, em12519, dsL]
  · norm_num [world12519, agent12519, scalar12519, tp12519, tm12519, ep12519, em12519, dsL]
  · norm_num [world12519, agent12519, scalar12519, tp12519, tm12519, ep12519, em12519, dsL]
  · norm_num [world12519, agent12519, scalar12519, tp12519, tm12519, ep12519, em12519, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12519, agent12519, tp12519, tm12519, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12519, agent12519, scalar12519, tp12519, tm12519, ep12519, em12519, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12519, agent12519, tp12519, tm12519, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12519, agent12519, scalar12519, tp12519, tm12519, ep12519, em12519, dsL]

theorem negative12519 :
    Eminus aL (agent12519.root+dsL) scalar12519.worldRadius world12519.frame
      agent12519.frame tm12519 ≤ -em12519 := by
  apply negative_check (lo := (4280882462114509903 / 6250000000000000000)) (hi := (68494119393832158449 / 100000000000000000000))
    (y := (-((35852039132469890439 / 50000000000000000000)))) (u := (24409739751093740519 / 50000000000000000000))
  · norm_num [world12519, agent12519, scalar12519, tp12519, tm12519, ep12519, em12519, dsL]
  · norm_num [world12519, agent12519, scalar12519, tp12519, tm12519, ep12519, em12519, dsL]
  · norm_num [world12519, agent12519, scalar12519, tp12519, tm12519, ep12519, em12519, dsL]
  · norm_num [world12519, agent12519, scalar12519, tp12519, tm12519, ep12519, em12519, dsL]
  · norm_num [world12519, agent12519, scalar12519, tp12519, tm12519, ep12519, em12519, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12519, agent12519, tp12519, tm12519, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12519, agent12519, tp12519, tm12519, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12519, agent12519, scalar12519, tp12519, tm12519, ep12519, em12519, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12519, agent12519, tp12519, tm12519, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12519, agent12519, scalar12519, tp12519, tm12519, ep12519, em12519, dsL]

theorem tails12519 :
    exp (-((12519:ℝ)*ep12519)) ≤ scalar12519.upperTail ∧
    exp (-((12519:ℝ)*em12519)) ≤ scalar12519.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12519:ℝ)) (by norm_num [ep12519]) ?_)
      (show bp12519^8 ≤ scalar12519.upperTail by norm_num [bp12519, scalar12519])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12519, bp12519, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12519:ℝ)) (by norm_num [em12519]) ?_)
      (show bm12519^8 ≤ scalar12519.lowerTail by norm_num [bm12519, scalar12519])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12519, bm12519, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12519 :
    agent12519.root+dsL+scalar12519.worldRadius < √(1/100/aL) ∧
    2*(agent12519.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12519, agent12519, scalar12519, tp12519, tm12519, ep12519, em12519, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12519, agent12519, scalar12519, tp12519, tm12519, ep12519, em12519, dsL]

noncomputable def master12519 : MasterCertificate 12519 world12519 agent12519 :=
  master scalar12519 dsL tp12519 tm12519 ep12519 em12519
    (by norm_num [dsL]) (by norm_num [tp12519]) (by norm_num [tm12519])
    (by norm_num [ep12519]) (by norm_num [em12519])
    positive12519 negative12519 tails12519.1 tails12519.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12519.1 tailGuards12519.2

theorem preserves12519 : master12519.toScalarCertificate = scalar12519 := rfl

noncomputable def tp12520 : ℝ := (2299251071 / 10000000000)
noncomputable def tm12520 : ℝ := (-((3012317749 / 5000000000)))
noncomputable def ep12520 : ℝ := (25454170237208893 / 50000000000000000000)
noncomputable def em12520 : ℝ := (49659621865144813 / 100000000000000000000)
noncomputable def bp12520 : ℝ := (22540359930426665471 / 50000000000000000000)
noncomputable def bm12520 : ℝ := (45970372081786563497 / 100000000000000000000)

theorem positive12520 :
    Eplus aL (agent12520.root+dsL) scalar12520.worldRadius world12520.frame
      agent12520.frame tp12520 ≤ -ep12520 := by
  apply positive_check (eT := (57768960817621532851 / 50000000000000000000)) (y := (37725649640629845989 / 100000000000000000000)) (u := (911423940343416139 / 625000000000000000))
  · norm_num [world12520, agent12520, scalar12520, tp12520, tm12520, ep12520, em12520, dsL]
  · norm_num [world12520, agent12520, scalar12520, tp12520, tm12520, ep12520, em12520, dsL]
  · norm_num [world12520, agent12520, scalar12520, tp12520, tm12520, ep12520, em12520, dsL]
  · norm_num [world12520, agent12520, scalar12520, tp12520, tm12520, ep12520, em12520, dsL]
  · norm_num [world12520, agent12520, scalar12520, tp12520, tm12520, ep12520, em12520, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12520, agent12520, tp12520, tm12520, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12520, agent12520, scalar12520, tp12520, tm12520, ep12520, em12520, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12520, agent12520, tp12520, tm12520, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12520, agent12520, scalar12520, tp12520, tm12520, ep12520, em12520, dsL]

theorem negative12520 :
    Eminus aL (agent12520.root+dsL) scalar12520.worldRadius world12520.frame
      agent12520.frame tm12520 ≤ -em12520 := by
  apply negative_check (lo := (68492871072684001893 / 100000000000000000000)) (hi := (34246435536342000947 / 50000000000000000000))
    (y := (-((71702292536058178787 / 100000000000000000000)))) (u := (48820351293516691023 / 100000000000000000000))
  · norm_num [world12520, agent12520, scalar12520, tp12520, tm12520, ep12520, em12520, dsL]
  · norm_num [world12520, agent12520, scalar12520, tp12520, tm12520, ep12520, em12520, dsL]
  · norm_num [world12520, agent12520, scalar12520, tp12520, tm12520, ep12520, em12520, dsL]
  · norm_num [world12520, agent12520, scalar12520, tp12520, tm12520, ep12520, em12520, dsL]
  · norm_num [world12520, agent12520, scalar12520, tp12520, tm12520, ep12520, em12520, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12520, agent12520, tp12520, tm12520, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12520, agent12520, tp12520, tm12520, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12520, agent12520, scalar12520, tp12520, tm12520, ep12520, em12520, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12520, agent12520, tp12520, tm12520, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12520, agent12520, scalar12520, tp12520, tm12520, ep12520, em12520, dsL]

theorem tails12520 :
    exp (-((12520:ℝ)*ep12520)) ≤ scalar12520.upperTail ∧
    exp (-((12520:ℝ)*em12520)) ≤ scalar12520.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12520:ℝ)) (by norm_num [ep12520]) ?_)
      (show bp12520^8 ≤ scalar12520.upperTail by norm_num [bp12520, scalar12520])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12520, bp12520, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12520:ℝ)) (by norm_num [em12520]) ?_)
      (show bm12520^8 ≤ scalar12520.lowerTail by norm_num [bm12520, scalar12520])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12520, bm12520, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12520 :
    agent12520.root+dsL+scalar12520.worldRadius < √(1/100/aL) ∧
    2*(agent12520.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12520, agent12520, scalar12520, tp12520, tm12520, ep12520, em12520, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12520, agent12520, scalar12520, tp12520, tm12520, ep12520, em12520, dsL]

noncomputable def master12520 : MasterCertificate 12520 world12520 agent12520 :=
  master scalar12520 dsL tp12520 tm12520 ep12520 em12520
    (by norm_num [dsL]) (by norm_num [tp12520]) (by norm_num [tm12520])
    (by norm_num [ep12520]) (by norm_num [em12520])
    positive12520 negative12520 tails12520.1 tails12520.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12520.1 tailGuards12520.2

theorem preserves12520 : master12520.toScalarCertificate = scalar12520 := rfl

noncomputable def tp12521 : ℝ := (459868461 / 2000000000)
noncomputable def tm12521 : ℝ := (-((1506208123 / 2500000000)))
noncomputable def ep12521 : ℝ := (50911164793236631 / 100000000000000000000)
noncomputable def em12521 : ℝ := (49662057937725191 / 100000000000000000000)
noncomputable def bp12521 : ℝ := (11268964659658285129 / 25000000000000000000)
noncomputable def bm12521 : ℝ := (4596576598435859047 / 10000000000000000000)

theorem positive12521 :
    Eplus aL (agent12521.root+dsL) scalar12521.worldRadius world12521.frame
      agent12521.frame tp12521 ≤ -ep12521 := by
  apply positive_check (eT := (115538205170005151479 / 100000000000000000000)) (y := (9431625880557770711 / 25000000000000000000)) (u := (29165815131455317827 / 20000000000000000000))
  · norm_num [world12521, agent12521, scalar12521, tp12521, tm12521, ep12521, em12521, dsL]
  · norm_num [world12521, agent12521, scalar12521, tp12521, tm12521, ep12521, em12521, dsL]
  · norm_num [world12521, agent12521, scalar12521, tp12521, tm12521, ep12521, em12521, dsL]
  · norm_num [world12521, agent12521, scalar12521, tp12521, tm12521, ep12521, em12521, dsL]
  · norm_num [world12521, agent12521, scalar12521, tp12521, tm12521, ep12521, em12521, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12521, agent12521, tp12521, tm12521, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12521, agent12521, scalar12521, tp12521, tm12521, ep12521, em12521, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12521, agent12521, tp12521, tm12521, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12521, agent12521, scalar12521, tp12521, tm12521, ep12521, em12521, dsL]

theorem negative12521 :
    Eminus aL (agent12521.root+dsL) scalar12521.worldRadius world12521.frame
      agent12521.frame tm12521 ≤ -em12521 := by
  apply negative_check (lo := (1369852232332847247 / 2000000000000000000)) (hi := (68492611616642362351 / 100000000000000000000))
    (y := (-((35851216784484738187 / 50000000000000000000)))) (u := (12205070610200627143 / 25000000000000000000))
  · norm_num [world12521, agent12521, scalar12521, tp12521, tm12521, ep12521, em12521, dsL]
  · norm_num [world12521, agent12521, scalar12521, tp12521, tm12521, ep12521, em12521, dsL]
  · norm_num [world12521, agent12521, scalar12521, tp12521, tm12521, ep12521, em12521, dsL]
  · norm_num [world12521, agent12521, scalar12521, tp12521, tm12521, ep12521, em12521, dsL]
  · norm_num [world12521, agent12521, scalar12521, tp12521, tm12521, ep12521, em12521, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12521, agent12521, tp12521, tm12521, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12521, agent12521, tp12521, tm12521, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12521, agent12521, scalar12521, tp12521, tm12521, ep12521, em12521, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12521, agent12521, tp12521, tm12521, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12521, agent12521, scalar12521, tp12521, tm12521, ep12521, em12521, dsL]

theorem tails12521 :
    exp (-((12521:ℝ)*ep12521)) ≤ scalar12521.upperTail ∧
    exp (-((12521:ℝ)*em12521)) ≤ scalar12521.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12521:ℝ)) (by norm_num [ep12521]) ?_)
      (show bp12521^8 ≤ scalar12521.upperTail by norm_num [bp12521, scalar12521])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12521, bp12521, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12521:ℝ)) (by norm_num [em12521]) ?_)
      (show bm12521^8 ≤ scalar12521.lowerTail by norm_num [bm12521, scalar12521])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12521, bm12521, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12521 :
    agent12521.root+dsL+scalar12521.worldRadius < √(1/100/aL) ∧
    2*(agent12521.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12521, agent12521, scalar12521, tp12521, tm12521, ep12521, em12521, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12521, agent12521, scalar12521, tp12521, tm12521, ep12521, em12521, dsL]

noncomputable def master12521 : MasterCertificate 12521 world12521 agent12521 :=
  master scalar12521 dsL tp12521 tm12521 ep12521 em12521
    (by norm_num [dsL]) (by norm_num [tp12521]) (by norm_num [tm12521])
    (by norm_num [ep12521]) (by norm_num [em12521])
    positive12521 negative12521 tails12521.1 tails12521.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12521.1 tailGuards12521.2

theorem preserves12521 : master12521.toScalarCertificate = scalar12521 := rfl

noncomputable def tp12522 : ℝ := (459886707 / 2000000000)
noncomputable def tm12522 : ℝ := (-((6025029589 / 10000000000)))
noncomputable def ep12522 : ℝ := (50913987793456431 / 100000000000000000000)
noncomputable def em12522 : ℝ := (49664492794625043 / 100000000000000000000)
noncomputable def bp12522 : ℝ := (22535499276308293581 / 50000000000000000000)
noncomputable def bm12522 : ℝ := (45961160943105521481 / 100000000000000000000)

theorem positive12522 :
    Eplus aL (agent12522.root+dsL) scalar12522.worldRadius world12522.frame
      agent12522.frame tp12522 ≤ -ep12522 := by
  apply positive_check (eT := (11553848870818468871 / 10000000000000000000)) (y := (9431839421776565971 / 25000000000000000000)) (u := (145830321283338497351 / 100000000000000000000))
  · norm_num [world12522, agent12522, scalar12522, tp12522, tm12522, ep12522, em12522, dsL]
  · norm_num [world12522, agent12522, scalar12522, tp12522, tm12522, ep12522, em12522, dsL]
  · norm_num [world12522, agent12522, scalar12522, tp12522, tm12522, ep12522, em12522, dsL]
  · norm_num [world12522, agent12522, scalar12522, tp12522, tm12522, ep12522, em12522, dsL]
  · norm_num [world12522, agent12522, scalar12522, tp12522, tm12522, ep12522, em12522, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12522, agent12522, tp12522, tm12522, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12522, agent12522, scalar12522, tp12522, tm12522, ep12522, em12522, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12522, agent12522, tp12522, tm12522, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12522, agent12522, scalar12522, tp12522, tm12522, ep12522, em12522, dsL]

theorem negative12522 :
    Eminus aL (agent12522.root+dsL) scalar12522.worldRadius world12522.frame
      agent12522.frame tm12522 ≤ -em12522 := by
  apply negative_check (lo := (8561543957616146133 / 12500000000000000000)) (hi := (13698470332185833813 / 20000000000000000000))
    (y := (-((35851288121248149513 / 50000000000000000000)))) (u := (48820212787233434113 / 100000000000000000000))
  · norm_num [world12522, agent12522, scalar12522, tp12522, tm12522, ep12522, em12522, dsL]
  · norm_num [world12522, agent12522, scalar12522, tp12522, tm12522, ep12522, em12522, dsL]
  · norm_num [world12522, agent12522, scalar12522, tp12522, tm12522, ep12522, em12522, dsL]
  · norm_num [world12522, agent12522, scalar12522, tp12522, tm12522, ep12522, em12522, dsL]
  · norm_num [world12522, agent12522, scalar12522, tp12522, tm12522, ep12522, em12522, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12522, agent12522, tp12522, tm12522, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12522, agent12522, tp12522, tm12522, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12522, agent12522, scalar12522, tp12522, tm12522, ep12522, em12522, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12522, agent12522, tp12522, tm12522, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12522, agent12522, scalar12522, tp12522, tm12522, ep12522, em12522, dsL]

theorem tails12522 :
    exp (-((12522:ℝ)*ep12522)) ≤ scalar12522.upperTail ∧
    exp (-((12522:ℝ)*em12522)) ≤ scalar12522.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12522:ℝ)) (by norm_num [ep12522]) ?_)
      (show bp12522^8 ≤ scalar12522.upperTail by norm_num [bp12522, scalar12522])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12522, bp12522, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12522:ℝ)) (by norm_num [em12522]) ?_)
      (show bm12522^8 ≤ scalar12522.lowerTail by norm_num [bm12522, scalar12522])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12522, bm12522, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12522 :
    agent12522.root+dsL+scalar12522.worldRadius < √(1/100/aL) ∧
    2*(agent12522.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12522, agent12522, scalar12522, tp12522, tm12522, ep12522, em12522, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12522, agent12522, scalar12522, tp12522, tm12522, ep12522, em12522, dsL]

noncomputable def master12522 : MasterCertificate 12522 world12522 agent12522 :=
  master scalar12522 dsL tp12522 tm12522 ep12522 em12522
    (by norm_num [dsL]) (by norm_num [tp12522]) (by norm_num [tm12522])
    (by norm_num [ep12522]) (by norm_num [em12522])
    positive12522 negative12522 tails12522.1 tails12522.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12522.1 tailGuards12522.2

theorem preserves12522 : master12522.toScalarCertificate = scalar12522 := rfl

noncomputable def tp12523 : ℝ := (459904927 / 2000000000)
noncomputable def tm12523 : ℝ := (-((6025226573 / 10000000000)))
noncomputable def ep12523 : ℝ := (5091680981166889 / 10000000000000000000)
noncomputable def em12523 : ℝ := (12416731682385863 / 25000000000000000000)
noncomputable def bp12523 : ℝ := (2816633710332627231 / 6250000000000000000)
noncomputable def bm12523 : ℝ := (22978278373363495757 / 50000000000000000000)

theorem positive12523 :
    Eplus aL (agent12523.root+dsL) scalar12523.worldRadius world12523.frame
      agent12523.frame tp12523 ≤ -ep12523 := by
  apply positive_check (eT := (57769385667682893217 / 50000000000000000000)) (y := (37728210017635762391 / 100000000000000000000)) (u := (9114472765311570267 / 6250000000000000000))
  · norm_num [world12523, agent12523, scalar12523, tp12523, tm12523, ep12523, em12523, dsL]
  · norm_num [world12523, agent12523, scalar12523, tp12523, tm12523, ep12523, em12523, dsL]
  · norm_num [world12523, agent12523, scalar12523, tp12523, tm12523, ep12523, em12523, dsL]
  · norm_num [world12523, agent12523, scalar12523, tp12523, tm12523, ep12523, em12523, dsL]
  · norm_num [world12523, agent12523, scalar12523, tp12523, tm12523, ep12523, em12523, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12523, agent12523, tp12523, tm12523, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12523, agent12523, scalar12523, tp12523, tm12523, ep12523, em12523, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12523, agent12523, tp12523, tm12523, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12523, agent12523, scalar12523, tp12523, tm12523, ep12523, em12523, dsL]

theorem negative12523 :
    Eminus aL (agent12523.root+dsL) scalar12523.worldRadius world12523.frame
      agent12523.frame tm12523 ≤ -em12523 := by
  apply negative_check (lo := (68492092134859785097 / 100000000000000000000)) (hi := (34246046067429892549 / 50000000000000000000))
    (y := (-((35851359428856317167 / 50000000000000000000)))) (u := (24410071581115500089 / 50000000000000000000))
  · norm_num [world12523, agent12523, scalar12523, tp12523, tm12523, ep12523, em12523, dsL]
  · norm_num [world12523, agent12523, scalar12523, tp12523, tm12523, ep12523, em12523, dsL]
  · norm_num [world12523, agent12523, scalar12523, tp12523, tm12523, ep12523, em12523, dsL]
  · norm_num [world12523, agent12523, scalar12523, tp12523, tm12523, ep12523, em12523, dsL]
  · norm_num [world12523, agent12523, scalar12523, tp12523, tm12523, ep12523, em12523, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12523, agent12523, tp12523, tm12523, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12523, agent12523, tp12523, tm12523, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12523, agent12523, scalar12523, tp12523, tm12523, ep12523, em12523, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12523, agent12523, tp12523, tm12523, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12523, agent12523, scalar12523, tp12523, tm12523, ep12523, em12523, dsL]

theorem tails12523 :
    exp (-((12523:ℝ)*ep12523)) ≤ scalar12523.upperTail ∧
    exp (-((12523:ℝ)*em12523)) ≤ scalar12523.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12523:ℝ)) (by norm_num [ep12523]) ?_)
      (show bp12523^8 ≤ scalar12523.upperTail by norm_num [bp12523, scalar12523])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12523, bp12523, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12523:ℝ)) (by norm_num [em12523]) ?_)
      (show bm12523^8 ≤ scalar12523.lowerTail by norm_num [bm12523, scalar12523])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12523, bm12523, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12523 :
    agent12523.root+dsL+scalar12523.worldRadius < √(1/100/aL) ∧
    2*(agent12523.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12523, agent12523, scalar12523, tp12523, tm12523, ep12523, em12523, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12523, agent12523, scalar12523, tp12523, tm12523, ep12523, em12523, dsL]

noncomputable def master12523 : MasterCertificate 12523 world12523 agent12523 :=
  master scalar12523 dsL tp12523 tm12523 ep12523 em12523
    (by norm_num [dsL]) (by norm_num [tp12523]) (by norm_num [tm12523])
    (by norm_num [ep12523]) (by norm_num [em12523])
    positive12523 negative12523 tails12523.1 tails12523.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12523.1 tailGuards12523.2

theorem preserves12523 : master12523.toScalarCertificate = scalar12523 := rfl

noncomputable def tp12524 : ℝ := (1149807919 / 5000000000)
noncomputable def tm12524 : ℝ := (-((3012711579 / 5000000000)))
noncomputable def ep12524 : ℝ := (12729907474438623 / 25000000000000000000)
noncomputable def em12524 : ℝ := (49669358864758181 / 100000000000000000000)
noncomputable def bp12524 : ℝ := (11265320436746171453 / 25000000000000000000)
noncomputable def bm12524 : ℝ := (1435998563332322499 / 3125000000000000000)

theorem positive12524 :
    Eplus aL (agent12524.root+dsL) scalar12524.worldRadius world12524.frame
      agent12524.frame tp12524 ≤ -ep12524 := by
  apply positive_check (eT := (115539054742490911003 / 100000000000000000000)) (y := (18864532358329004891 / 50000000000000000000)) (u := (145832810671265443263 / 100000000000000000000))
  · norm_num [world12524, agent12524, scalar12524, tp12524, tm12524, ep12524, em12524, dsL]
  · norm_num [world12524, agent12524, scalar12524, tp12524, tm12524, ep12524, em12524, dsL]
  · norm_num [world12524, agent12524, scalar12524, tp12524, tm12524, ep12524, em12524, dsL]
  · norm_num [world12524, agent12524, scalar12524, tp12524, tm12524, ep12524, em12524, dsL]
  · norm_num [world12524, agent12524, scalar12524, tp12524, tm12524, ep12524, em12524, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12524, agent12524, tp12524, tm12524, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12524, agent12524, scalar12524, tp12524, tm12524, ep12524, em12524, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12524, agent12524, tp12524, tm12524, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12524, agent12524, scalar12524, tp12524, tm12524, ep12524, em12524, dsL]

theorem negative12524 :
    Eminus aL (agent12524.root+dsL) scalar12524.worldRadius world12524.frame
      agent12524.frame tm12524 ≤ -em12524 := by
  apply negative_check (lo := (13698366853749408729 / 20000000000000000000)) (hi := (34245917134373521823 / 50000000000000000000))
    (y := (-((71702858357567011021 / 100000000000000000000)))) (u := (762813672785154451 / 1562500000000000000))
  · norm_num [world12524, agent12524, scalar12524, tp12524, tm12524, ep12524, em12524, dsL]
  · norm_num [world12524, agent12524, scalar12524, tp12524, tm12524, ep12524, em12524, dsL]
  · norm_num [world12524, agent12524, scalar12524, tp12524, tm12524, ep12524, em12524, dsL]
  · norm_num [world12524, agent12524, scalar12524, tp12524, tm12524, ep12524, em12524, dsL]
  · norm_num [world12524, agent12524, scalar12524, tp12524, tm12524, ep12524, em12524, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12524, agent12524, tp12524, tm12524, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12524, agent12524, tp12524, tm12524, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12524, agent12524, scalar12524, tp12524, tm12524, ep12524, em12524, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12524, agent12524, tp12524, tm12524, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12524, agent12524, scalar12524, tp12524, tm12524, ep12524, em12524, dsL]

theorem tails12524 :
    exp (-((12524:ℝ)*ep12524)) ≤ scalar12524.upperTail ∧
    exp (-((12524:ℝ)*em12524)) ≤ scalar12524.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12524:ℝ)) (by norm_num [ep12524]) ?_)
      (show bp12524^8 ≤ scalar12524.upperTail by norm_num [bp12524, scalar12524])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12524, bp12524, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12524:ℝ)) (by norm_num [em12524]) ?_)
      (show bm12524^8 ≤ scalar12524.lowerTail by norm_num [bm12524, scalar12524])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12524, bm12524, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12524 :
    agent12524.root+dsL+scalar12524.worldRadius < √(1/100/aL) ∧
    2*(agent12524.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12524, agent12524, scalar12524, tp12524, tm12524, ep12524, em12524, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12524, agent12524, scalar12524, tp12524, tm12524, ep12524, em12524, dsL]

noncomputable def master12524 : MasterCertificate 12524 world12524 agent12524 :=
  master scalar12524 dsL tp12524 tm12524 ep12524 em12524
    (by norm_num [dsL]) (by norm_num [tp12524]) (by norm_num [tm12524])
    (by norm_num [ep12524]) (by norm_num [em12524])
    positive12524 negative12524 tails12524.1 tails12524.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12524.1 tailGuards12524.2

theorem preserves12524 : master12524.toScalarCertificate = scalar12524 := rfl

end BstLean.Part268
