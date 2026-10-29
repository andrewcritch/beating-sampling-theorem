import BstLean.Part261Checker
import BstLean.Part268Scalar31
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp13125 : ℝ := (294105879 / 1250000000)
noncomputable def tm13125 : ℝ := (-((614312747 / 1000000000)))
noncomputable def ep13125 : ℝ := (26246705010726811 / 50000000000000000000)
noncomputable def em13125 : ℝ := (25517274373397743 / 50000000000000000000)
noncomputable def bp13125 : ℝ := (21132306795791617663 / 50000000000000000000)
noncomputable def bm13125 : ℝ := (8657679306321492981 / 20000000000000000000)

theorem positive13125 :
    Eplus aL (agent13125.root+dsL) scalar13125.worldRadius world13125.frame
      agent13125.frame tp13125 ≤ -ep13125 := by
  apply positive_check (eT := (1157036122804290797 / 1000000000000000000)) (y := (38136023657428606133 / 100000000000000000000)) (u := (9151718723872967053 / 6250000000000000000))
  · norm_num [world13125, agent13125, scalar13125, tp13125, tm13125, ep13125, em13125, dsL]
  · norm_num [world13125, agent13125, scalar13125, tp13125, tm13125, ep13125, em13125, dsL]
  · norm_num [world13125, agent13125, scalar13125, tp13125, tm13125, ep13125, em13125, dsL]
  · norm_num [world13125, agent13125, scalar13125, tp13125, tm13125, ep13125, em13125, dsL]
  · norm_num [world13125, agent13125, scalar13125, tp13125, tm13125, ep13125, em13125, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13125, agent13125, tp13125, tm13125, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13125, agent13125, scalar13125, tp13125, tm13125, ep13125, em13125, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13125, agent13125, tp13125, tm13125, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13125, agent13125, scalar13125, tp13125, tm13125, ep13125, em13125, dsL]

theorem negative13125 :
    Eminus aL (agent13125.root+dsL) scalar13125.worldRadius world13125.frame
      agent13125.frame tm13125 ≤ -em13125 := by
  apply negative_check (lo := (34164526443018625897 / 50000000000000000000)) (hi := (13665810577207450359 / 20000000000000000000))
    (y := (-((8950369501710715891 / 12500000000000000000)))) (u := (48868871828017587597 / 100000000000000000000))
  · norm_num [world13125, agent13125, scalar13125, tp13125, tm13125, ep13125, em13125, dsL]
  · norm_num [world13125, agent13125, scalar13125, tp13125, tm13125, ep13125, em13125, dsL]
  · norm_num [world13125, agent13125, scalar13125, tp13125, tm13125, ep13125, em13125, dsL]
  · norm_num [world13125, agent13125, scalar13125, tp13125, tm13125, ep13125, em13125, dsL]
  · norm_num [world13125, agent13125, scalar13125, tp13125, tm13125, ep13125, em13125, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13125, agent13125, tp13125, tm13125, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13125, agent13125, tp13125, tm13125, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13125, agent13125, scalar13125, tp13125, tm13125, ep13125, em13125, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13125, agent13125, tp13125, tm13125, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13125, agent13125, scalar13125, tp13125, tm13125, ep13125, em13125, dsL]

theorem tails13125 :
    exp (-((13125:ℝ)*ep13125)) ≤ scalar13125.upperTail ∧
    exp (-((13125:ℝ)*em13125)) ≤ scalar13125.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13125:ℝ)) (by norm_num [ep13125]) ?_)
      (show bp13125^8 ≤ scalar13125.upperTail by norm_num [bp13125, scalar13125])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13125, bp13125, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13125:ℝ)) (by norm_num [em13125]) ?_)
      (show bm13125^8 ≤ scalar13125.lowerTail by norm_num [bm13125, scalar13125])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13125, bm13125, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13125 :
    agent13125.root+dsL+scalar13125.worldRadius < √(1/100/aL) ∧
    2*(agent13125.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13125, agent13125, scalar13125, tp13125, tm13125, ep13125, em13125, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13125, agent13125, scalar13125, tp13125, tm13125, ep13125, em13125, dsL]

noncomputable def master13125 : MasterCertificate 13125 world13125 agent13125 :=
  master scalar13125 dsL tp13125 tm13125 ep13125 em13125
    (by norm_num [dsL]) (by norm_num [tp13125]) (by norm_num [tm13125])
    (by norm_num [ep13125]) (by norm_num [em13125])
    positive13125 negative13125 tails13125.1 tails13125.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13125.1 tailGuards13125.2

theorem preserves13125 : master13125.toScalarCertificate = scalar13125 := rfl

noncomputable def tp13126 : ℝ := (1176459403 / 5000000000)
noncomputable def tm13126 : ℝ := (-((6143279343 / 10000000000)))
noncomputable def ep13126 : ℝ := (328097236594883 / 625000000000000000)
noncomputable def em13126 : ℝ := (1275909152258233 / 2500000000000000000)
noncomputable def bp13126 : ℝ := (42260351109848638617 / 100000000000000000000)
noncomputable def bm13126 : ℝ := (8656868888072557639 / 20000000000000000000)

theorem positive13126 :
    Eplus aL (agent13126.root+dsL) scalar13126.worldRadius world13126.frame
      agent13126.frame tp13126 ≤ -ep13126 := by
  apply positive_check (eT := (1157037746313652833 / 1000000000000000000)) (y := (19068334547849221333 / 50000000000000000000)) (u := (146428444684137361861 / 100000000000000000000))
  · norm_num [world13126, agent13126, scalar13126, tp13126, tm13126, ep13126, em13126, dsL]
  · norm_num [world13126, agent13126, scalar13126, tp13126, tm13126, ep13126, em13126, dsL]
  · norm_num [world13126, agent13126, scalar13126, tp13126, tm13126, ep13126, em13126, dsL]
  · norm_num [world13126, agent13126, scalar13126, tp13126, tm13126, ep13126, em13126, dsL]
  · norm_num [world13126, agent13126, scalar13126, tp13126, tm13126, ep13126, em13126, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13126, agent13126, tp13126, tm13126, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13126, agent13126, scalar13126, tp13126, tm13126, ep13126, em13126, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13126, agent13126, tp13126, tm13126, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13126, agent13126, scalar13126, tp13126, tm13126, ep13126, em13126, dsL]

theorem negative13126 :
    Eminus aL (agent13126.root+dsL) scalar13126.worldRadius world13126.frame
      agent13126.frame tm13126 ≤ -em13126 := by
  apply negative_check (lo := (17082238258641776891 / 25000000000000000000)) (hi := (13665790606913421513 / 20000000000000000000))
    (y := (-((8950357885274973609 / 12500000000000000000)))) (u := (48868917242607440859 / 100000000000000000000))
  · norm_num [world13126, agent13126, scalar13126, tp13126, tm13126, ep13126, em13126, dsL]
  · norm_num [world13126, agent13126, scalar13126, tp13126, tm13126, ep13126, em13126, dsL]
  · norm_num [world13126, agent13126, scalar13126, tp13126, tm13126, ep13126, em13126, dsL]
  · norm_num [world13126, agent13126, scalar13126, tp13126, tm13126, ep13126, em13126, dsL]
  · norm_num [world13126, agent13126, scalar13126, tp13126, tm13126, ep13126, em13126, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13126, agent13126, tp13126, tm13126, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13126, agent13126, tp13126, tm13126, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13126, agent13126, scalar13126, tp13126, tm13126, ep13126, em13126, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13126, agent13126, tp13126, tm13126, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13126, agent13126, scalar13126, tp13126, tm13126, ep13126, em13126, dsL]

theorem tails13126 :
    exp (-((13126:ℝ)*ep13126)) ≤ scalar13126.upperTail ∧
    exp (-((13126:ℝ)*em13126)) ≤ scalar13126.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13126:ℝ)) (by norm_num [ep13126]) ?_)
      (show bp13126^8 ≤ scalar13126.upperTail by norm_num [bp13126, scalar13126])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13126, bp13126, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13126:ℝ)) (by norm_num [em13126]) ?_)
      (show bm13126^8 ≤ scalar13126.lowerTail by norm_num [bm13126, scalar13126])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13126, bm13126, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13126 :
    agent13126.root+dsL+scalar13126.worldRadius < √(1/100/aL) ∧
    2*(agent13126.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13126, agent13126, scalar13126, tp13126, tm13126, ep13126, em13126, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13126, agent13126, scalar13126, tp13126, tm13126, ep13126, em13126, dsL]

noncomputable def master13126 : MasterCertificate 13126 world13126 agent13126 :=
  master scalar13126 dsL tp13126 tm13126 ep13126 em13126
    (by norm_num [dsL]) (by norm_num [tp13126]) (by norm_num [tm13126])
    (by norm_num [ep13126]) (by norm_num [em13126])
    positive13126 negative13126 tails13126.1 tails13126.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13126.1 tailGuards13126.2

theorem preserves13126 : master13126.toScalarCertificate = scalar13126 := rfl

noncomputable def tp13127 : ℝ := (2352990843 / 10000000000)
noncomputable def tm13127 : ℝ := (-((767928987 / 1250000000)))
noncomputable def ep13127 : ℝ := (5249770940569563 / 10000000000000000000)
noncomputable def em13127 : ℝ := (51038187657343679 / 100000000000000000000)
noncomputable def bp13127 : ℝ := (42256086253990504559 / 100000000000000000000)
noncomputable def bm13127 : ℝ := (43280289532371494177 / 100000000000000000000)

theorem positive13127 :
    Eplus aL (agent13127.root+dsL) scalar13127.worldRadius world13127.frame
      agent13127.frame tp13127 ≤ -ep13127 := by
  apply positive_check (eT := (23140787780352786187 / 20000000000000000000)) (y := (9534328141558121349 / 25000000000000000000)) (u := (14642938691106383441 / 10000000000000000000))
  · norm_num [world13127, agent13127, scalar13127, tp13127, tm13127, ep13127, em13127, dsL]
  · norm_num [world13127, agent13127, scalar13127, tp13127, tm13127, ep13127, em13127, dsL]
  · norm_num [world13127, agent13127, scalar13127, tp13127, tm13127, ep13127, em13127, dsL]
  · norm_num [world13127, agent13127, scalar13127, tp13127, tm13127, ep13127, em13127, dsL]
  · norm_num [world13127, agent13127, scalar13127, tp13127, tm13127, ep13127, em13127, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13127, agent13127, tp13127, tm13127, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13127, agent13127, scalar13127, tp13127, tm13127, ep13127, em13127, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13127, agent13127, tp13127, tm13127, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13127, agent13127, scalar13127, tp13127, tm13127, ep13127, em13127, dsL]

theorem negative13127 :
    Eminus aL (agent13127.root+dsL) scalar13127.worldRadius world13127.frame
      agent13127.frame tm13127 ≤ -em13127 := by
  apply negative_check (lo := (3416442512299831301 / 5000000000000000000)) (hi := (68328850245996626021 / 100000000000000000000))
    (y := (-((71602763448107538201 / 100000000000000000000)))) (u := (48868965932733784241 / 100000000000000000000))
  · norm_num [world13127, agent13127, scalar13127, tp13127, tm13127, ep13127, em13127, dsL]
  · norm_num [world13127, agent13127, scalar13127, tp13127, tm13127, ep13127, em13127, dsL]
  · norm_num [world13127, agent13127, scalar13127, tp13127, tm13127, ep13127, em13127, dsL]
  · norm_num [world13127, agent13127, scalar13127, tp13127, tm13127, ep13127, em13127, dsL]
  · norm_num [world13127, agent13127, scalar13127, tp13127, tm13127, ep13127, em13127, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13127, agent13127, tp13127, tm13127, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13127, agent13127, tp13127, tm13127, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13127, agent13127, scalar13127, tp13127, tm13127, ep13127, em13127, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13127, agent13127, tp13127, tm13127, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13127, agent13127, scalar13127, tp13127, tm13127, ep13127, em13127, dsL]

theorem tails13127 :
    exp (-((13127:ℝ)*ep13127)) ≤ scalar13127.upperTail ∧
    exp (-((13127:ℝ)*em13127)) ≤ scalar13127.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13127:ℝ)) (by norm_num [ep13127]) ?_)
      (show bp13127^8 ≤ scalar13127.upperTail by norm_num [bp13127, scalar13127])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13127, bp13127, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13127:ℝ)) (by norm_num [em13127]) ?_)
      (show bm13127^8 ≤ scalar13127.lowerTail by norm_num [bm13127, scalar13127])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13127, bm13127, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13127 :
    agent13127.root+dsL+scalar13127.worldRadius < √(1/100/aL) ∧
    2*(agent13127.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13127, agent13127, scalar13127, tp13127, tm13127, ep13127, em13127, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13127, agent13127, scalar13127, tp13127, tm13127, ep13127, em13127, dsL]

noncomputable def master13127 : MasterCertificate 13127 world13127 agent13127 :=
  master scalar13127 dsL tp13127 tm13127 ep13127 em13127
    (by norm_num [dsL]) (by norm_num [tp13127]) (by norm_num [tm13127])
    (by norm_num [ep13127]) (by norm_num [em13127])
    positive13127 negative13127 tails13127.1 tails13127.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13127.1 tailGuards13127.2

theorem preserves13127 : master13127.toScalarCertificate = scalar13127 := rfl

noncomputable def tp13128 : ℝ := (2353062873 / 10000000000)
noncomputable def tm13128 : ℝ := (-((3071792259 / 5000000000)))
noncomputable def ep13128 : ℝ := (52499860332646023 / 100000000000000000000)
noncomputable def em13128 : ℝ := (51040008753869527 / 100000000000000000000)
noncomputable def bp13128 : ℝ := (5281477754202241741 / 12500000000000000000)
noncomputable def bm13128 : ℝ := (8655247028258796541 / 20000000000000000000)

theorem positive13128 :
    Eplus aL (agent13128.root+dsL) scalar13128.worldRadius world13128.frame
      agent13128.frame tp13128 ≤ -ep13128 := by
  apply positive_check (eT := (115704103154924539301 / 100000000000000000000)) (y := (38137955309685506513 / 100000000000000000000)) (u := (3660758201984653747 / 2500000000000000000))
  · norm_num [world13128, agent13128, scalar13128, tp13128, tm13128, ep13128, em13128, dsL]
  · norm_num [world13128, agent13128, scalar13128, tp13128, tm13128, ep13128, em13128, dsL]
  · norm_num [world13128, agent13128, scalar13128, tp13128, tm13128, ep13128, em13128, dsL]
  · norm_num [world13128, agent13128, scalar13128, tp13128, tm13128, ep13128, em13128, dsL]
  · norm_num [world13128, agent13128, scalar13128, tp13128, tm13128, ep13128, em13128, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13128, agent13128, tp13128, tm13128, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13128, agent13128, scalar13128, tp13128, tm13128, ep13128, em13128, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13128, agent13128, tp13128, tm13128, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13128, agent13128, scalar13128, tp13128, tm13128, ep13128, em13128, dsL]

theorem negative13128 :
    Eminus aL (agent13128.root+dsL) scalar13128.worldRadius world13128.frame
      agent13128.frame tm13128 ≤ -em13128 := by
  apply negative_check (lo := (68328747108559210147 / 100000000000000000000)) (hi := (17082186777139802537 / 25000000000000000000))
    (y := (-((71602663081374733167 / 100000000000000000000)))) (u := (48869014980942860569 / 100000000000000000000))
  · norm_num [world13128, agent13128, scalar13128, tp13128, tm13128, ep13128, em13128, dsL]
  · norm_num [world13128, agent13128, scalar13128, tp13128, tm13128, ep13128, em13128, dsL]
  · norm_num [world13128, agent13128, scalar13128, tp13128, tm13128, ep13128, em13128, dsL]
  · norm_num [world13128, agent13128, scalar13128, tp13128, tm13128, ep13128, em13128, dsL]
  · norm_num [world13128, agent13128, scalar13128, tp13128, tm13128, ep13128, em13128, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13128, agent13128, tp13128, tm13128, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13128, agent13128, tp13128, tm13128, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13128, agent13128, scalar13128, tp13128, tm13128, ep13128, em13128, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13128, agent13128, tp13128, tm13128, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13128, agent13128, scalar13128, tp13128, tm13128, ep13128, em13128, dsL]

theorem tails13128 :
    exp (-((13128:ℝ)*ep13128)) ≤ scalar13128.upperTail ∧
    exp (-((13128:ℝ)*em13128)) ≤ scalar13128.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13128:ℝ)) (by norm_num [ep13128]) ?_)
      (show bp13128^8 ≤ scalar13128.upperTail by norm_num [bp13128, scalar13128])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13128, bp13128, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13128:ℝ)) (by norm_num [em13128]) ?_)
      (show bm13128^8 ≤ scalar13128.lowerTail by norm_num [bm13128, scalar13128])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13128, bm13128, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13128 :
    agent13128.root+dsL+scalar13128.worldRadius < √(1/100/aL) ∧
    2*(agent13128.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13128, agent13128, scalar13128, tp13128, tm13128, ep13128, em13128, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13128, agent13128, scalar13128, tp13128, tm13128, ep13128, em13128, dsL]

noncomputable def master13128 : MasterCertificate 13128 world13128 agent13128 :=
  master scalar13128 dsL tp13128 tm13128 ep13128 em13128
    (by norm_num [dsL]) (by norm_num [tp13128]) (by norm_num [tm13128])
    (by norm_num [ep13128]) (by norm_num [em13128])
    positive13128 negative13128 tails13128.1 tails13128.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13128.1 tailGuards13128.2

theorem preserves13128 : master13128.toScalarCertificate = scalar13128 := rfl

noncomputable def tp13129 : ℝ := (2353134833 / 10000000000)
noncomputable def tm13129 : ℝ := (-((767967131 / 1250000000)))
noncomputable def ep13129 : ℝ := (26251005201506403 / 50000000000000000000)
noncomputable def em13129 : ℝ := (51041829079333639 / 100000000000000000000)
noncomputable def bp13129 : ℝ := (844951172205698651 / 2000000000000000000)
noncomputable def bm13129 : ℝ := (2163609074029237571 / 5000000000000000000)

theorem positive13129 :
    Eplus aL (agent13129.root+dsL) scalar13129.worldRadius world13129.frame
      agent13129.frame tp13129 ≤ -ep13129 := by
  apply positive_check (eT := (28926066734756316663 / 25000000000000000000)) (y := (19069298470367847769 / 50000000000000000000)) (u := (146431267624852205377 / 100000000000000000000))
  · norm_num [world13129, agent13129, scalar13129, tp13129, tm13129, ep13129, em13129, dsL]
  · norm_num [world13129, agent13129, scalar13129, tp13129, tm13129, ep13129, em13129, dsL]
  · norm_num [world13129, agent13129, scalar13129, tp13129, tm13129, ep13129, em13129, dsL]
  · norm_num [world13129, agent13129, scalar13129, tp13129, tm13129, ep13129, em13129, dsL]
  · norm_num [world13129, agent13129, scalar13129, tp13129, tm13129, ep13129, em13129, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13129, agent13129, tp13129, tm13129, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13129, agent13129, scalar13129, tp13129, tm13129, ep13129, em13129, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13129, agent13129, tp13129, tm13129, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13129, agent13129, scalar13129, tp13129, tm13129, ep13129, em13129, dsL]

theorem negative13129 :
    Eminus aL (agent13129.root+dsL) scalar13129.worldRadius world13129.frame
      agent13129.frame tm13129 ≤ -em13129 := by
  apply negative_check (lo := (68328644304156672079 / 100000000000000000000)) (hi := (854108053801958401 / 1250000000000000000))
    (y := (-((8950320249696622511 / 12500000000000000000)))) (u := (48869064379626049617 / 100000000000000000000))
  · norm_num [world13129, agent13129, scalar13129, tp13129, tm13129, ep13129, em13129, dsL]
  · norm_num [world13129, agent13129, scalar13129, tp13129, tm13129, ep13129, em13129, dsL]
  · norm_num [world13129, agent13129, scalar13129, tp13129, tm13129, ep13129, em13129, dsL]
  · norm_num [world13129, agent13129, scalar13129, tp13129, tm13129, ep13129, em13129, dsL]
  · norm_num [world13129, agent13129, scalar13129, tp13129, tm13129, ep13129, em13129, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13129, agent13129, tp13129, tm13129, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13129, agent13129, tp13129, tm13129, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13129, agent13129, scalar13129, tp13129, tm13129, ep13129, em13129, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13129, agent13129, tp13129, tm13129, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13129, agent13129, scalar13129, tp13129, tm13129, ep13129, em13129, dsL]

theorem tails13129 :
    exp (-((13129:ℝ)*ep13129)) ≤ scalar13129.upperTail ∧
    exp (-((13129:ℝ)*em13129)) ≤ scalar13129.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13129:ℝ)) (by norm_num [ep13129]) ?_)
      (show bp13129^8 ≤ scalar13129.upperTail by norm_num [bp13129, scalar13129])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13129, bp13129, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13129:ℝ)) (by norm_num [em13129]) ?_)
      (show bm13129^8 ≤ scalar13129.lowerTail by norm_num [bm13129, scalar13129])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13129, bm13129, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13129 :
    agent13129.root+dsL+scalar13129.worldRadius < √(1/100/aL) ∧
    2*(agent13129.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13129, agent13129, scalar13129, tp13129, tm13129, ep13129, em13129, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13129, agent13129, scalar13129, tp13129, tm13129, ep13129, em13129, dsL]

noncomputable def master13129 : MasterCertificate 13129 world13129 agent13129 :=
  master scalar13129 dsL tp13129 tm13129 ep13129 em13129
    (by norm_num [dsL]) (by norm_num [tp13129]) (by norm_num [tm13129])
    (by norm_num [ep13129]) (by norm_num [em13129])
    positive13129 negative13129 tails13129.1 tails13129.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13129.1 tailGuards13129.2

theorem preserves13129 : master13129.toScalarCertificate = scalar13129 := rfl

noncomputable def tp13130 : ℝ := (588319377 / 2500000000)
noncomputable def tm13130 : ℝ := (-((6144103681 / 10000000000)))
noncomputable def ep13130 : ℝ := (52505490903484969 / 100000000000000000000)
noncomputable def em13130 : ℝ := (6380637874723863 / 12500000000000000000)
noncomputable def bp13130 : ℝ := (42242372988904837893 / 100000000000000000000)
noncomputable def bm13130 : ℝ := (43267095763147390013 / 100000000000000000000)

theorem positive13130 :
    Eplus aL (agent13130.root+dsL) scalar13130.worldRadius world13130.frame
      agent13130.frame tp13130 ≤ -ep13130 := by
  apply positive_check (eT := (57852468969504495173 / 50000000000000000000)) (y := (762770567729760827 / 2000000000000000000)) (u := (73215583620016381851 / 50000000000000000000))
  · norm_num [world13130, agent13130, scalar13130, tp13130, tm13130, ep13130, em13130, dsL]
  · norm_num [world13130, agent13130, scalar13130, tp13130, tm13130, ep13130, em13130, dsL]
  · norm_num [world13130, agent13130, scalar13130, tp13130, tm13130, ep13130, em13130, dsL]
  · norm_num [world13130, agent13130, scalar13130, tp13130, tm13130, ep13130, em13130, dsL]
  · norm_num [world13130, agent13130, scalar13130, tp13130, tm13130, ep13130, em13130, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13130, agent13130, tp13130, tm13130, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13130, agent13130, scalar13130, tp13130, tm13130, ep13130, em13130, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13130, agent13130, tp13130, tm13130, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13130, agent13130, scalar13130, tp13130, tm13130, ep13130, em13130, dsL]

theorem negative13130 :
    Eminus aL (agent13130.root+dsL) scalar13130.worldRadius world13130.frame
      agent13130.frame tm13130 ≤ -em13130 := by
  apply negative_check (lo := (34163817308395869739 / 50000000000000000000)) (hi := (68327634616791739479 / 100000000000000000000))
    (y := (-((89500757255948007 / 125000000000000000)))) (u := (48870020362102393413 / 100000000000000000000))
  · norm_num [world13130, agent13130, scalar13130, tp13130, tm13130, ep13130, em13130, dsL]
  · norm_num [world13130, agent13130, scalar13130, tp13130, tm13130, ep13130, em13130, dsL]
  · norm_num [world13130, agent13130, scalar13130, tp13130, tm13130, ep13130, em13130, dsL]
  · norm_num [world13130, agent13130, scalar13130, tp13130, tm13130, ep13130, em13130, dsL]
  · norm_num [world13130, agent13130, scalar13130, tp13130, tm13130, ep13130, em13130, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13130, agent13130, tp13130, tm13130, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13130, agent13130, tp13130, tm13130, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13130, agent13130, scalar13130, tp13130, tm13130, ep13130, em13130, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13130, agent13130, tp13130, tm13130, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13130, agent13130, scalar13130, tp13130, tm13130, ep13130, em13130, dsL]

theorem tails13130 :
    exp (-((13130:ℝ)*ep13130)) ≤ scalar13130.upperTail ∧
    exp (-((13130:ℝ)*em13130)) ≤ scalar13130.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13130:ℝ)) (by norm_num [ep13130]) ?_)
      (show bp13130^8 ≤ scalar13130.upperTail by norm_num [bp13130, scalar13130])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13130, bp13130, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13130:ℝ)) (by norm_num [em13130]) ?_)
      (show bm13130^8 ≤ scalar13130.lowerTail by norm_num [bm13130, scalar13130])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13130, bm13130, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13130 :
    agent13130.root+dsL+scalar13130.worldRadius < √(1/100/aL) ∧
    2*(agent13130.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13130, agent13130, scalar13130, tp13130, tm13130, ep13130, em13130, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13130, agent13130, scalar13130, tp13130, tm13130, ep13130, em13130, dsL]

noncomputable def master13130 : MasterCertificate 13130 world13130 agent13130 :=
  master scalar13130 dsL tp13130 tm13130 ep13130 em13130
    (by norm_num [dsL]) (by norm_num [tp13130]) (by norm_num [tm13130])
    (by norm_num [ep13130]) (by norm_num [em13130])
    positive13130 negative13130 tails13130.1 tails13130.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13130.1 tailGuards13130.2

theorem preserves13130 : master13130.toScalarCertificate = scalar13130 := rfl

noncomputable def tp13131 : ℝ := (588337359 / 2500000000)
noncomputable def tm13131 : ℝ := (-((6144256021 / 10000000000)))
noncomputable def ep13131 : ℝ := (52507638271419667 / 100000000000000000000)
noncomputable def em13131 : ℝ := (25523460399915993 / 50000000000000000000)
noncomputable def bp13131 : ℝ := (42238111868268074773 / 100000000000000000000)
noncomputable def bm13131 : ℝ := (21631522139025387489 / 50000000000000000000)

theorem positive13131 :
    Eplus aL (agent13131.root+dsL) scalar13131.worldRadius world13131.frame
      agent13131.frame tp13131 ≤ -ep13131 := by
  apply positive_check (eT := (57852550774844254209 / 50000000000000000000)) (y := (9534792566775697799 / 25000000000000000000)) (u := (36608026789081449103 / 25000000000000000000))
  · norm_num [world13131, agent13131, scalar13131, tp13131, tm13131, ep13131, em13131, dsL]
  · norm_num [world13131, agent13131, scalar13131, tp13131, tm13131, ep13131, em13131, dsL]
  · norm_num [world13131, agent13131, scalar13131, tp13131, tm13131, ep13131, em13131, dsL]
  · norm_num [world13131, agent13131, scalar13131, tp13131, tm13131, ep13131, em13131, dsL]
  · norm_num [world13131, agent13131, scalar13131, tp13131, tm13131, ep13131, em13131, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13131, agent13131, tp13131, tm13131, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13131, agent13131, scalar13131, tp13131, tm13131, ep13131, em13131, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13131, agent13131, tp13131, tm13131, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13131, agent13131, scalar13131, tp13131, tm13131, ep13131, em13131, dsL]

theorem negative13131 :
    Eminus aL (agent13131.root+dsL) scalar13131.worldRadius world13131.frame
      agent13131.frame tm13131 ≤ -em13131 := by
  apply negative_check (lo := (8540941565529102913 / 12500000000000000000)) (hi := (13665506504846564661 / 20000000000000000000))
    (y := (-((14320100832916526469 / 20000000000000000000)))) (u := (24435035016851116513 / 50000000000000000000))
  · norm_num [world13131, agent13131, scalar13131, tp13131, tm13131, ep13131, em13131, dsL]
  · norm_num [world13131, agent13131, scalar13131, tp13131, tm13131, ep13131, em13131, dsL]
  · norm_num [world13131, agent13131, scalar13131, tp13131, tm13131, ep13131, em13131, dsL]
  · norm_num [world13131, agent13131, scalar13131, tp13131, tm13131, ep13131, em13131, dsL]
  · norm_num [world13131, agent13131, scalar13131, tp13131, tm13131, ep13131, em13131, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13131, agent13131, tp13131, tm13131, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13131, agent13131, tp13131, tm13131, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13131, agent13131, scalar13131, tp13131, tm13131, ep13131, em13131, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13131, agent13131, tp13131, tm13131, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13131, agent13131, scalar13131, tp13131, tm13131, ep13131, em13131, dsL]

theorem tails13131 :
    exp (-((13131:ℝ)*ep13131)) ≤ scalar13131.upperTail ∧
    exp (-((13131:ℝ)*em13131)) ≤ scalar13131.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13131:ℝ)) (by norm_num [ep13131]) ?_)
      (show bp13131^8 ≤ scalar13131.upperTail by norm_num [bp13131, scalar13131])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13131, bp13131, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13131:ℝ)) (by norm_num [em13131]) ?_)
      (show bm13131^8 ≤ scalar13131.lowerTail by norm_num [bm13131, scalar13131])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13131, bm13131, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13131 :
    agent13131.root+dsL+scalar13131.worldRadius < √(1/100/aL) ∧
    2*(agent13131.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13131, agent13131, scalar13131, tp13131, tm13131, ep13131, em13131, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13131, agent13131, scalar13131, tp13131, tm13131, ep13131, em13131, dsL]

noncomputable def master13131 : MasterCertificate 13131 world13131 agent13131 :=
  master scalar13131 dsL tp13131 tm13131 ep13131 em13131
    (by norm_num [dsL]) (by norm_num [tp13131]) (by norm_num [tm13131])
    (by norm_num [ep13131]) (by norm_num [em13131])
    positive13131 negative13131 tails13131.1 tails13131.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13131.1 tailGuards13131.2

theorem preserves13131 : master13131.toScalarCertificate = scalar13131 := rfl

noncomputable def tp13132 : ℝ := (1176710673 / 5000000000)
noncomputable def tm13132 : ℝ := (-((245776339 / 400000000)))
noncomputable def ep13132 : ℝ := (52509784633703663 / 100000000000000000000)
noncomputable def em13132 : ℝ := (6381092209534953 / 12500000000000000000)
noncomputable def bp13132 : ℝ := (42233851647920993187 / 100000000000000000000)
noncomputable def bm13132 : ℝ := (43258993633000774979 / 100000000000000000000)

theorem positive13132 :
    Eplus aL (agent13132.root+dsL) scalar13132.worldRadius world13132.frame
      agent13132.frame tp13132 ≤ -ep13132 := by
  apply positive_check (eT := (115705265064240449959 / 100000000000000000000)) (y := (762796241862430563 / 2000000000000000000)) (u := (73216523499352691863 / 50000000000000000000))
  · norm_num [world13132, agent13132, scalar13132, tp13132, tm13132, ep13132, em13132, dsL]
  · norm_num [world13132, agent13132, scalar13132, tp13132, tm13132, ep13132, em13132, dsL]
  · norm_num [world13132, agent13132, scalar13132, tp13132, tm13132, ep13132, em13132, dsL]
  · norm_num [world13132, agent13132, scalar13132, tp13132, tm13132, ep13132, em13132, dsL]
  · norm_num [world13132, agent13132, scalar13132, tp13132, tm13132, ep13132, em13132, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13132, agent13132, tp13132, tm13132, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13132, agent13132, scalar13132, tp13132, tm13132, ep13132, em13132, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13132, agent13132, tp13132, tm13132, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13132, agent13132, scalar13132, tp13132, tm13132, ep13132, em13132, dsL]

theorem negative13132 :
    Eminus aL (agent13132.root+dsL) scalar13132.worldRadius world13132.frame
      agent13132.frame tm13132 ≤ -em13132 := by
  apply negative_check (lo := (34163714946134093149 / 50000000000000000000)) (hi := (68327429892268186299 / 100000000000000000000))
    (y := (-((35800202032609021399 / 50000000000000000000)))) (u := (9774023790471258971 / 20000000000000000000))
  · norm_num [world13132, agent13132, scalar13132, tp13132, tm13132, ep13132, em13132, dsL]
  · norm_num [world13132, agent13132, scalar13132, tp13132, tm13132, ep13132, em13132, dsL]
  · norm_num [world13132, agent13132, scalar13132, tp13132, tm13132, ep13132, em13132, dsL]
  · norm_num [world13132, agent13132, scalar13132, tp13132, tm13132, ep13132, em13132, dsL]
  · norm_num [world13132, agent13132, scalar13132, tp13132, tm13132, ep13132, em13132, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13132, agent13132, tp13132, tm13132, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13132, agent13132, tp13132, tm13132, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13132, agent13132, scalar13132, tp13132, tm13132, ep13132, em13132, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13132, agent13132, tp13132, tm13132, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13132, agent13132, scalar13132, tp13132, tm13132, ep13132, em13132, dsL]

theorem tails13132 :
    exp (-((13132:ℝ)*ep13132)) ≤ scalar13132.upperTail ∧
    exp (-((13132:ℝ)*em13132)) ≤ scalar13132.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13132:ℝ)) (by norm_num [ep13132]) ?_)
      (show bp13132^8 ≤ scalar13132.upperTail by norm_num [bp13132, scalar13132])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13132, bp13132, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13132:ℝ)) (by norm_num [em13132]) ?_)
      (show bm13132^8 ≤ scalar13132.lowerTail by norm_num [bm13132, scalar13132])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13132, bm13132, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13132 :
    agent13132.root+dsL+scalar13132.worldRadius < √(1/100/aL) ∧
    2*(agent13132.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13132, agent13132, scalar13132, tp13132, tm13132, ep13132, em13132, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13132, agent13132, scalar13132, tp13132, tm13132, ep13132, em13132, dsL]

noncomputable def master13132 : MasterCertificate 13132 world13132 agent13132 :=
  master scalar13132 dsL tp13132 tm13132 ep13132 em13132
    (by norm_num [dsL]) (by norm_num [tp13132]) (by norm_num [tm13132])
    (by norm_num [ep13132]) (by norm_num [em13132])
    positive13132 negative13132 tails13132.1 tails13132.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13132.1 tailGuards13132.2

theorem preserves13132 : master13132.toScalarCertificate = scalar13132 := rfl

noncomputable def tp13133 : ℝ := (2353493211 / 10000000000)
noncomputable def tm13133 : ℝ := (-((3072280259 / 5000000000)))
noncomputable def ep13133 : ℝ := (26255965162635777 / 50000000000000000000)
noncomputable def em13133 : ℝ := (51050553920860523 / 100000000000000000000)
noncomputable def bp13133 : ℝ := (2639349505977700653 / 6250000000000000000)
noncomputable def bm13133 : ℝ := (21627471809705991237 / 50000000000000000000)

theorem positive13133 :
    Eplus aL (agent13133.root+dsL) scalar13133.worldRadius world13133.frame
      agent13133.frame tp13133 ≤ -ep13133 := by
  apply positive_check (eT := (57852714144532931017 / 50000000000000000000)) (y := (38140453497062399347 / 100000000000000000000)) (u := (73216993114525849101 / 50000000000000000000))
  · norm_num [world13133, agent13133, scalar13133, tp13133, tm13133, ep13133, em13133, dsL]
  · norm_num [world13133, agent13133, scalar13133, tp13133, tm13133, ep13133, em13133, dsL]
  · norm_num [world13133, agent13133, scalar13133, tp13133, tm13133, ep13133, em13133, dsL]
  · norm_num [world13133, agent13133, scalar13133, tp13133, tm13133, ep13133, em13133, dsL]
  · norm_num [world13133, agent13133, scalar13133, tp13133, tm13133, ep13133, em13133, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13133, agent13133, tp13133, tm13133, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13133, agent13133, scalar13133, tp13133, tm13133, ep13133, em13133, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13133, agent13133, tp13133, tm13133, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13133, agent13133, scalar13133, tp13133, tm13133, ep13133, em13133, dsL]

theorem negative13133 :
    Eminus aL (agent13133.root+dsL) scalar13133.worldRadius world13133.frame
      agent13133.frame tm13133 ≤ -em13133 := by
  apply negative_check (lo := (6832732894433908119 / 10000000000000000000)) (hi := (68327328944339081191 / 100000000000000000000))
    (y := (-((17900075223364251913 / 25000000000000000000)))) (u := (9774033874508929533 / 20000000000000000000))
  · norm_num [world13133, agent13133, scalar13133, tp13133, tm13133, ep13133, em13133, dsL]
  · norm_num [world13133, agent13133, scalar13133, tp13133, tm13133, ep13133, em13133, dsL]
  · norm_num [world13133, agent13133, scalar13133, tp13133, tm13133, ep13133, em13133, dsL]
  · norm_num [world13133, agent13133, scalar13133, tp13133, tm13133, ep13133, em13133, dsL]
  · norm_num [world13133, agent13133, scalar13133, tp13133, tm13133, ep13133, em13133, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13133, agent13133, tp13133, tm13133, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13133, agent13133, tp13133, tm13133, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13133, agent13133, scalar13133, tp13133, tm13133, ep13133, em13133, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13133, agent13133, tp13133, tm13133, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13133, agent13133, scalar13133, tp13133, tm13133, ep13133, em13133, dsL]

theorem tails13133 :
    exp (-((13133:ℝ)*ep13133)) ≤ scalar13133.upperTail ∧
    exp (-((13133:ℝ)*em13133)) ≤ scalar13133.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13133:ℝ)) (by norm_num [ep13133]) ?_)
      (show bp13133^8 ≤ scalar13133.upperTail by norm_num [bp13133, scalar13133])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13133, bp13133, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13133:ℝ)) (by norm_num [em13133]) ?_)
      (show bm13133^8 ≤ scalar13133.lowerTail by norm_num [bm13133, scalar13133])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13133, bm13133, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13133 :
    agent13133.root+dsL+scalar13133.worldRadius < √(1/100/aL) ∧
    2*(agent13133.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13133, agent13133, scalar13133, tp13133, tm13133, ep13133, em13133, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13133, agent13133, scalar13133, tp13133, tm13133, ep13133, em13133, dsL]

noncomputable def master13133 : MasterCertificate 13133 world13133 agent13133 :=
  master scalar13133 dsL tp13133 tm13133 ep13133 em13133
    (by norm_num [dsL]) (by norm_num [tp13133]) (by norm_num [tm13133])
    (by norm_num [ep13133]) (by norm_num [em13133])
    positive13133 negative13133 tails13133.1 tails13133.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13133.1 tailGuards13133.2

theorem preserves13133 : master13133.toScalarCertificate = scalar13133 := rfl

noncomputable def tp13134 : ℝ := (2353564977 / 10000000000)
noncomputable def tm13134 : ℝ := (-((6144712683 / 10000000000)))
noncomputable def ep13134 : ℝ := (52514074387633409 / 100000000000000000000)
noncomputable def em13134 : ℝ := (1595386520159971 / 3125000000000000000)
noncomputable def bp13134 : ℝ := (5278166734485458937 / 12500000000000000000)
noncomputable def bm13134 : ℝ := (21625447434073798917 / 50000000000000000000)

theorem positive13134 :
    Eplus aL (agent13134.root+dsL) scalar13134.worldRadius world13134.frame
      agent13134.frame tp13134 ≤ -ep13134 := by
  apply positive_check (eT := (57852795418418433781 / 50000000000000000000)) (y := (19070546818592421449 / 50000000000000000000)) (u := (73217461807375365803 / 50000000000000000000))
  · norm_num [world13134, agent13134, scalar13134, tp13134, tm13134, ep13134, em13134, dsL]
  · norm_num [world13134, agent13134, scalar13134, tp13134, tm13134, ep13134, em13134, dsL]
  · norm_num [world13134, agent13134, scalar13134, tp13134, tm13134, ep13134, em13134, dsL]
  · norm_num [world13134, agent13134, scalar13134, tp13134, tm13134, ep13134, em13134, dsL]
  · norm_num [world13134, agent13134, scalar13134, tp13134, tm13134, ep13134, em13134, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13134, agent13134, tp13134, tm13134, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13134, agent13134, scalar13134, tp13134, tm13134, ep13134, em13134, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13134, agent13134, tp13134, tm13134, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13134, agent13134, scalar13134, tp13134, tm13134, ep13134, em13134, dsL]

theorem negative13134 :
    Eminus aL (agent13134.root+dsL) scalar13134.worldRadius world13134.frame
      agent13134.frame tm13134 ≤ -em13134 := by
  apply negative_check (lo := (68327227423161145879 / 100000000000000000000)) (hi := (1708180685579028647 / 2500000000000000000))
    (y := (-((71600199496924189691 / 100000000000000000000)))) (u := (48870218925227096037 / 100000000000000000000))
  · norm_num [world13134, agent13134, scalar13134, tp13134, tm13134, ep13134, em13134, dsL]
  · norm_num [world13134, agent13134, scalar13134, tp13134, tm13134, ep13134, em13134, dsL]
  · norm_num [world13134, agent13134, scalar13134, tp13134, tm13134, ep13134, em13134, dsL]
  · norm_num [world13134, agent13134, scalar13134, tp13134, tm13134, ep13134, em13134, dsL]
  · norm_num [world13134, agent13134, scalar13134, tp13134, tm13134, ep13134, em13134, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13134, agent13134, tp13134, tm13134, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13134, agent13134, tp13134, tm13134, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13134, agent13134, scalar13134, tp13134, tm13134, ep13134, em13134, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13134, agent13134, tp13134, tm13134, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13134, agent13134, scalar13134, tp13134, tm13134, ep13134, em13134, dsL]

theorem tails13134 :
    exp (-((13134:ℝ)*ep13134)) ≤ scalar13134.upperTail ∧
    exp (-((13134:ℝ)*em13134)) ≤ scalar13134.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13134:ℝ)) (by norm_num [ep13134]) ?_)
      (show bp13134^8 ≤ scalar13134.upperTail by norm_num [bp13134, scalar13134])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13134, bp13134, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13134:ℝ)) (by norm_num [em13134]) ?_)
      (show bm13134^8 ≤ scalar13134.lowerTail by norm_num [bm13134, scalar13134])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13134, bm13134, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13134 :
    agent13134.root+dsL+scalar13134.worldRadius < √(1/100/aL) ∧
    2*(agent13134.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13134, agent13134, scalar13134, tp13134, tm13134, ep13134, em13134, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13134, agent13134, scalar13134, tp13134, tm13134, ep13134, em13134, dsL]

noncomputable def master13134 : MasterCertificate 13134 world13134 agent13134 :=
  master scalar13134 dsL tp13134 tm13134 ep13134 em13134
    (by norm_num [dsL]) (by norm_num [tp13134]) (by norm_num [tm13134])
    (by norm_num [ep13134]) (by norm_num [em13134])
    positive13134 negative13134 tails13134.1 tails13134.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13134.1 tailGuards13134.2

theorem preserves13134 : master13134.toScalarCertificate = scalar13134 := rfl

noncomputable def tp13135 : ℝ := (470727363 / 2000000000)
noncomputable def tm13135 : ℝ := (-((6144864671 / 10000000000)))
noncomputable def ep13135 : ℝ := (52516217453850487 / 100000000000000000000)
noncomputable def em13135 : ℝ := (3190886403247607 / 6250000000000000000)
noncomputable def bp13135 : ℝ := (21110538274867421543 / 50000000000000000000)
noncomputable def bm13135 : ℝ := (43246846951071438551 / 100000000000000000000)

theorem positive13135 :
    Eplus aL (agent13135.root+dsL) scalar13135.worldRadius world13135.frame
      agent13135.frame tp13135 ≤ -ep13135 := by
  apply positive_check (eT := (11570575393398602717 / 10000000000000000000)) (y := (9535433822482688649 / 25000000000000000000)) (u := (146435863221473582297 / 100000000000000000000))
  · norm_num [world13135, agent13135, scalar13135, tp13135, tm13135, ep13135, em13135, dsL]
  · norm_num [world13135, agent13135, scalar13135, tp13135, tm13135, ep13135, em13135, dsL]
  · norm_num [world13135, agent13135, scalar13135, tp13135, tm13135, ep13135, em13135, dsL]
  · norm_num [world13135, agent13135, scalar13135, tp13135, tm13135, ep13135, em13135, dsL]
  · norm_num [world13135, agent13135, scalar13135, tp13135, tm13135, ep13135, em13135, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13135, agent13135, tp13135, tm13135, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13135, agent13135, scalar13135, tp13135, tm13135, ep13135, em13135, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13135, agent13135, tp13135, tm13135, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13135, agent13135, scalar13135, tp13135, tm13135, ep13135, em13135, dsL]

theorem negative13135 :
    Eminus aL (agent13135.root+dsL) scalar13135.worldRadius world13135.frame
      agent13135.frame tm13135 ≤ -em13135 := by
  apply negative_check (lo := (34163563297467054501 / 50000000000000000000)) (hi := (68327126594934109003 / 100000000000000000000))
    (y := (-((71600096854595069169 / 100000000000000000000)))) (u := (48870269086783790679 / 100000000000000000000))
  · norm_num [world13135, agent13135, scalar13135, tp13135, tm13135, ep13135, em13135, dsL]
  · norm_num [world13135, agent13135, scalar13135, tp13135, tm13135, ep13135, em13135, dsL]
  · norm_num [world13135, agent13135, scalar13135, tp13135, tm13135, ep13135, em13135, dsL]
  · norm_num [world13135, agent13135, scalar13135, tp13135, tm13135, ep13135, em13135, dsL]
  · norm_num [world13135, agent13135, scalar13135, tp13135, tm13135, ep13135, em13135, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13135, agent13135, tp13135, tm13135, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13135, agent13135, tp13135, tm13135, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13135, agent13135, scalar13135, tp13135, tm13135, ep13135, em13135, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13135, agent13135, tp13135, tm13135, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13135, agent13135, scalar13135, tp13135, tm13135, ep13135, em13135, dsL]

theorem tails13135 :
    exp (-((13135:ℝ)*ep13135)) ≤ scalar13135.upperTail ∧
    exp (-((13135:ℝ)*em13135)) ≤ scalar13135.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13135:ℝ)) (by norm_num [ep13135]) ?_)
      (show bp13135^8 ≤ scalar13135.upperTail by norm_num [bp13135, scalar13135])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13135, bp13135, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13135:ℝ)) (by norm_num [em13135]) ?_)
      (show bm13135^8 ≤ scalar13135.lowerTail by norm_num [bm13135, scalar13135])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13135, bm13135, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13135 :
    agent13135.root+dsL+scalar13135.worldRadius < √(1/100/aL) ∧
    2*(agent13135.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13135, agent13135, scalar13135, tp13135, tm13135, ep13135, em13135, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13135, agent13135, scalar13135, tp13135, tm13135, ep13135, em13135, dsL]

noncomputable def master13135 : MasterCertificate 13135 world13135 agent13135 :=
  master scalar13135 dsL tp13135 tm13135 ep13135 em13135
    (by norm_num [dsL]) (by norm_num [tp13135]) (by norm_num [tm13135])
    (by norm_num [ep13135]) (by norm_num [em13135])
    positive13135 negative13135 tails13135.1 tails13135.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13135.1 tailGuards13135.2

theorem preserves13135 : master13135.toScalarCertificate = scalar13135 := rfl

noncomputable def tp13136 : ℝ := (2353708571 / 10000000000)
noncomputable def tm13136 : ℝ := (-((1229003319 / 2000000000)))
noncomputable def ep13136 : ℝ := (1050367190195861 / 2000000000000000000)
noncomputable def em13136 : ℝ := (51055995329390487 / 100000000000000000000)
noncomputable def bp13136 : ℝ := (8443364025393090237 / 20000000000000000000)
noncomputable def bm13136 : ℝ := (10810699969172024349 / 25000000000000000000)

theorem positive13136 :
    Eplus aL (agent13136.root+dsL) scalar13136.worldRadius world13136.frame
      agent13136.frame tp13136 ≤ -ep13136 := by
  apply positive_check (eT := (7231619779752485949 / 6250000000000000000)) (y := (19071187886504800077 / 50000000000000000000)) (u := (5857472044856096769 / 4000000000000000000))
  · norm_num [world13136, agent13136, scalar13136, tp13136, tm13136, ep13136, em13136, dsL]
  · norm_num [world13136, agent13136, scalar13136, tp13136, tm13136, ep13136, em13136, dsL]
  · norm_num [world13136, agent13136, scalar13136, tp13136, tm13136, ep13136, em13136, dsL]
  · norm_num [world13136, agent13136, scalar13136, tp13136, tm13136, ep13136, em13136, dsL]
  · norm_num [world13136, agent13136, scalar13136, tp13136, tm13136, ep13136, em13136, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13136, agent13136, tp13136, tm13136, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13136, agent13136, scalar13136, tp13136, tm13136, ep13136, em13136, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13136, agent13136, tp13136, tm13136, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13136, agent13136, scalar13136, tp13136, tm13136, ep13136, em13136, dsL]

theorem negative13136 :
    Eminus aL (agent13136.root+dsL) scalar13136.worldRadius world13136.frame
      agent13136.frame tm13136 ≤ -em13136 := by
  apply negative_check (lo := (68327025981145211253 / 100000000000000000000)) (hi := (34163512990572605627 / 50000000000000000000))
    (y := (-((7159999404801435259 / 10000000000000000000)))) (u := (48870319328662251767 / 100000000000000000000))
  · norm_num [world13136, agent13136, scalar13136, tp13136, tm13136, ep13136, em13136, dsL]
  · norm_num [world13136, agent13136, scalar13136, tp13136, tm13136, ep13136, em13136, dsL]
  · norm_num [world13136, agent13136, scalar13136, tp13136, tm13136, ep13136, em13136, dsL]
  · norm_num [world13136, agent13136, scalar13136, tp13136, tm13136, ep13136, em13136, dsL]
  · norm_num [world13136, agent13136, scalar13136, tp13136, tm13136, ep13136, em13136, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13136, agent13136, tp13136, tm13136, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13136, agent13136, tp13136, tm13136, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13136, agent13136, scalar13136, tp13136, tm13136, ep13136, em13136, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13136, agent13136, tp13136, tm13136, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13136, agent13136, scalar13136, tp13136, tm13136, ep13136, em13136, dsL]

theorem tails13136 :
    exp (-((13136:ℝ)*ep13136)) ≤ scalar13136.upperTail ∧
    exp (-((13136:ℝ)*em13136)) ≤ scalar13136.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13136:ℝ)) (by norm_num [ep13136]) ?_)
      (show bp13136^8 ≤ scalar13136.upperTail by norm_num [bp13136, scalar13136])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13136, bp13136, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13136:ℝ)) (by norm_num [em13136]) ?_)
      (show bm13136^8 ≤ scalar13136.lowerTail by norm_num [bm13136, scalar13136])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13136, bm13136, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13136 :
    agent13136.root+dsL+scalar13136.worldRadius < √(1/100/aL) ∧
    2*(agent13136.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13136, agent13136, scalar13136, tp13136, tm13136, ep13136, em13136, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13136, agent13136, scalar13136, tp13136, tm13136, ep13136, em13136, dsL]

noncomputable def master13136 : MasterCertificate 13136 world13136 agent13136 :=
  master scalar13136 dsL tp13136 tm13136 ep13136 em13136
    (by norm_num [dsL]) (by norm_num [tp13136]) (by norm_num [tm13136])
    (by norm_num [ep13136]) (by norm_num [em13136])
    positive13136 negative13136 tails13136.1 tails13136.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13136.1 tailGuards13136.2

theorem preserves13136 : master13136.toScalarCertificate = scalar13136 := rfl

noncomputable def tp13137 : ℝ := (470756059 / 2000000000)
noncomputable def tm13137 : ℝ := (-((1229033671 / 2000000000)))
noncomputable def ep13137 : ℝ := (10504100084106173 / 20000000000000000000)
noncomputable def em13137 : ℝ := (25528903567431001 / 50000000000000000000)
noncomputable def bp13137 : ℝ := (42212564701080098001 / 100000000000000000000)
noncomputable def bm13137 : ℝ := (43238753746193308807 / 100000000000000000000)

theorem positive13137 :
    Eplus aL (agent13137.root+dsL) scalar13137.worldRadius world13137.frame
      agent13137.frame tp13137 ≤ -ep13137 := by
  apply positive_check (eT := (115706078821600055211 / 100000000000000000000)) (y := (7628603221905501261 / 20000000000000000000)) (u := (146437738812717839923 / 100000000000000000000))
  · norm_num [world13137, agent13137, scalar13137, tp13137, tm13137, ep13137, em13137, dsL]
  · norm_num [world13137, agent13137, scalar13137, tp13137, tm13137, ep13137, em13137, dsL]
  · norm_num [world13137, agent13137, scalar13137, tp13137, tm13137, ep13137, em13137, dsL]
  · norm_num [world13137, agent13137, scalar13137, tp13137, tm13137, ep13137, em13137, dsL]
  · norm_num [world13137, agent13137, scalar13137, tp13137, tm13137, ep13137, em13137, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13137, agent13137, tp13137, tm13137, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13137, agent13137, scalar13137, tp13137, tm13137, ep13137, em13137, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13137, agent13137, tp13137, tm13137, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13137, agent13137, scalar13137, tp13137, tm13137, ep13137, em13137, dsL]

theorem negative13137 :
    Eminus aL (agent13137.root+dsL) scalar13137.worldRadius world13137.frame
      agent13137.frame tm13137 ≤ -em13137 := by
  apply negative_check (lo := (68326926005248102843 / 100000000000000000000)) (hi := (17081731501312025711 / 25000000000000000000))
    (y := (-((17899972601437823709 / 25000000000000000000)))) (u := (24435184989496707557 / 50000000000000000000))
  · norm_num [world13137, agent13137, scalar13137, tp13137, tm13137, ep13137, em13137, dsL]
  · norm_num [world13137, agent13137, scalar13137, tp13137, tm13137, ep13137, em13137, dsL]
  · norm_num [world13137, agent13137, scalar13137, tp13137, tm13137, ep13137, em13137, dsL]
  · norm_num [world13137, agent13137, scalar13137, tp13137, tm13137, ep13137, em13137, dsL]
  · norm_num [world13137, agent13137, scalar13137, tp13137, tm13137, ep13137, em13137, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13137, agent13137, tp13137, tm13137, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13137, agent13137, tp13137, tm13137, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13137, agent13137, scalar13137, tp13137, tm13137, ep13137, em13137, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13137, agent13137, tp13137, tm13137, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13137, agent13137, scalar13137, tp13137, tm13137, ep13137, em13137, dsL]

theorem tails13137 :
    exp (-((13137:ℝ)*ep13137)) ≤ scalar13137.upperTail ∧
    exp (-((13137:ℝ)*em13137)) ≤ scalar13137.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13137:ℝ)) (by norm_num [ep13137]) ?_)
      (show bp13137^8 ≤ scalar13137.upperTail by norm_num [bp13137, scalar13137])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13137, bp13137, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13137:ℝ)) (by norm_num [em13137]) ?_)
      (show bm13137^8 ≤ scalar13137.lowerTail by norm_num [bm13137, scalar13137])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13137, bm13137, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13137 :
    agent13137.root+dsL+scalar13137.worldRadius < √(1/100/aL) ∧
    2*(agent13137.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13137, agent13137, scalar13137, tp13137, tm13137, ep13137, em13137, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13137, agent13137, scalar13137, tp13137, tm13137, ep13137, em13137, dsL]

noncomputable def master13137 : MasterCertificate 13137 world13137 agent13137 :=
  master scalar13137 dsL tp13137 tm13137 ep13137 em13137
    (by norm_num [dsL]) (by norm_num [tp13137]) (by norm_num [tm13137])
    (by norm_num [ep13137]) (by norm_num [em13137])
    positive13137 negative13137 tails13137.1 tails13137.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13137.1 tailGuards13137.2

theorem preserves13137 : master13137.toScalarCertificate = scalar13137 := rfl

noncomputable def tp13138 : ℝ := (470770391 / 2000000000)
noncomputable def tm13138 : ℝ := (-((1229064037 / 2000000000)))
noncomputable def ep13138 : ℝ := (10504528067046279 / 20000000000000000000)
noncomputable def em13138 : ℝ := (6382452252887007 / 12500000000000000000)
noncomputable def bp13138 : ℝ := (8441662033729456579 / 20000000000000000000)
noncomputable def bm13138 : ℝ := (10808677112428081061 / 25000000000000000000)

theorem positive13138 :
    Eplus aL (agent13138.root+dsL) scalar13138.worldRadius world13138.frame
      agent13138.frame tp13138 ≤ -ep13138 := by
  apply positive_check (eT := (11570624074120979851 / 10000000000000000000)) (y := (762873111795040881 / 2000000000000000000)) (u := (36609668814023247349 / 25000000000000000000))
  · norm_num [world13138, agent13138, scalar13138, tp13138, tm13138, ep13138, em13138, dsL]
  · norm_num [world13138, agent13138, scalar13138, tp13138, tm13138, ep13138, em13138, dsL]
  · norm_num [world13138, agent13138, scalar13138, tp13138, tm13138, ep13138, em13138, dsL]
  · norm_num [world13138, agent13138, scalar13138, tp13138, tm13138, ep13138, em13138, dsL]
  · norm_num [world13138, agent13138, scalar13138, tp13138, tm13138, ep13138, em13138, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13138, agent13138, tp13138, tm13138, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13138, agent13138, scalar13138, tp13138, tm13138, ep13138, em13138, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13138, agent13138, tp13138, tm13138, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13138, agent13138, scalar13138, tp13138, tm13138, ep13138, em13138, dsL]

theorem negative13138 :
    Eminus aL (agent13138.root+dsL) scalar13138.worldRadius world13138.frame
      agent13138.frame tm13138 ≤ -em13138 := by
  apply negative_check (lo := (68326825676274497227 / 100000000000000000000)) (hi := (17081706419068624307 / 25000000000000000000))
    (y := (-((17899946970443095421 / 25000000000000000000)))) (u := (24435210041433455697 / 50000000000000000000))
  · norm_num [world13138, agent13138, scalar13138, tp13138, tm13138, ep13138, em13138, dsL]
  · norm_num [world13138, agent13138, scalar13138, tp13138, tm13138, ep13138, em13138, dsL]
  · norm_num [world13138, agent13138, scalar13138, tp13138, tm13138, ep13138, em13138, dsL]
  · norm_num [world13138, agent13138, scalar13138, tp13138, tm13138, ep13138, em13138, dsL]
  · norm_num [world13138, agent13138, scalar13138, tp13138, tm13138, ep13138, em13138, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13138, agent13138, tp13138, tm13138, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13138, agent13138, tp13138, tm13138, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13138, agent13138, scalar13138, tp13138, tm13138, ep13138, em13138, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13138, agent13138, tp13138, tm13138, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13138, agent13138, scalar13138, tp13138, tm13138, ep13138, em13138, dsL]

theorem tails13138 :
    exp (-((13138:ℝ)*ep13138)) ≤ scalar13138.upperTail ∧
    exp (-((13138:ℝ)*em13138)) ≤ scalar13138.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13138:ℝ)) (by norm_num [ep13138]) ?_)
      (show bp13138^8 ≤ scalar13138.upperTail by norm_num [bp13138, scalar13138])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13138, bp13138, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13138:ℝ)) (by norm_num [em13138]) ?_)
      (show bm13138^8 ≤ scalar13138.lowerTail by norm_num [bm13138, scalar13138])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13138, bm13138, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13138 :
    agent13138.root+dsL+scalar13138.worldRadius < √(1/100/aL) ∧
    2*(agent13138.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13138, agent13138, scalar13138, tp13138, tm13138, ep13138, em13138, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13138, agent13138, scalar13138, tp13138, tm13138, ep13138, em13138, dsL]

noncomputable def master13138 : MasterCertificate 13138 world13138 agent13138 :=
  master scalar13138 dsL tp13138 tm13138 ep13138 em13138
    (by norm_num [dsL]) (by norm_num [tp13138]) (by norm_num [tm13138])
    (by norm_num [ep13138]) (by norm_num [em13138])
    positive13138 negative13138 tails13138.1 tails13138.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13138.1 tailGuards13138.2

theorem preserves13138 : master13138.toScalarCertificate = scalar13138 := rfl

noncomputable def tp13139 : ℝ := (2353923669 / 10000000000)
noncomputable def tm13139 : ℝ := (-((3072735911 / 5000000000)))
noncomputable def ep13139 : ℝ := (26262389789699099 / 50000000000000000000)
noncomputable def em13139 : ℝ := (10212285655958113 / 20000000000000000000)
noncomputable def bp13139 : ℝ := (2110202815200926583 / 5000000000000000000)
noncomputable def bm13139 : ℝ := (1729226551375293007 / 4000000000000000000)

theorem positive13139 :
    Eplus aL (agent13139.root+dsL) scalar13139.worldRadius world13139.frame
      agent13139.frame tp13139 ≤ -ep13139 := by
  apply positive_check (eT := (1446330038513103663 / 1250000000000000000)) (y := (19072148185763178873 / 50000000000000000000)) (u := (146439613611440978673 / 100000000000000000000))
  · norm_num [world13139, agent13139, scalar13139, tp13139, tm13139, ep13139, em13139, dsL]
  · norm_num [world13139, agent13139, scalar13139, tp13139, tm13139, ep13139, em13139, dsL]
  · norm_num [world13139, agent13139, scalar13139, tp13139, tm13139, ep13139, em13139, dsL]
  · norm_num [world13139, agent13139, scalar13139, tp13139, tm13139, ep13139, em13139, dsL]
  · norm_num [world13139, agent13139, scalar13139, tp13139, tm13139, ep13139, em13139, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13139, agent13139, tp13139, tm13139, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13139, agent13139, scalar13139, tp13139, tm13139, ep13139, em13139, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13139, agent13139, tp13139, tm13139, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13139, agent13139, scalar13139, tp13139, tm13139, ep13139, em13139, dsL]

theorem negative13139 :
    Eminus aL (agent13139.root+dsL) scalar13139.worldRadius world13139.frame
      agent13139.frame tm13139 ≤ -em13139 := by
  apply negative_check (lo := (68326726107977079503 / 100000000000000000000)) (hi := (4270420381748567469 / 6250000000000000000))
    (y := (-((71599684371797738369 / 100000000000000000000)))) (u := (24435235334326263957 / 50000000000000000000))
  · norm_num [world13139, agent13139, scalar13139, tp13139, tm13139, ep13139, em13139, dsL]
  · norm_num [world13139, agent13139, scalar13139, tp13139, tm13139, ep13139, em13139, dsL]
  · norm_num [world13139, agent13139, scalar13139, tp13139, tm13139, ep13139, em13139, dsL]
  · norm_num [world13139, agent13139, scalar13139, tp13139, tm13139, ep13139, em13139, dsL]
  · norm_num [world13139, agent13139, scalar13139, tp13139, tm13139, ep13139, em13139, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13139, agent13139, tp13139, tm13139, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13139, agent13139, tp13139, tm13139, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13139, agent13139, scalar13139, tp13139, tm13139, ep13139, em13139, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13139, agent13139, tp13139, tm13139, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13139, agent13139, scalar13139, tp13139, tm13139, ep13139, em13139, dsL]

theorem tails13139 :
    exp (-((13139:ℝ)*ep13139)) ≤ scalar13139.upperTail ∧
    exp (-((13139:ℝ)*em13139)) ≤ scalar13139.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13139:ℝ)) (by norm_num [ep13139]) ?_)
      (show bp13139^8 ≤ scalar13139.upperTail by norm_num [bp13139, scalar13139])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13139, bp13139, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13139:ℝ)) (by norm_num [em13139]) ?_)
      (show bm13139^8 ≤ scalar13139.lowerTail by norm_num [bm13139, scalar13139])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13139, bm13139, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13139 :
    agent13139.root+dsL+scalar13139.worldRadius < √(1/100/aL) ∧
    2*(agent13139.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13139, agent13139, scalar13139, tp13139, tm13139, ep13139, em13139, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13139, agent13139, scalar13139, tp13139, tm13139, ep13139, em13139, dsL]

noncomputable def master13139 : MasterCertificate 13139 world13139 agent13139 :=
  master scalar13139 dsL tp13139 tm13139 ep13139 em13139
    (by norm_num [dsL]) (by norm_num [tp13139]) (by norm_num [tm13139])
    (by norm_num [ep13139]) (by norm_num [em13139])
    positive13139 negative13139 tails13139.1 tails13139.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13139.1 tailGuards13139.2

theorem preserves13139 : master13139.toScalarCertificate = scalar13139 := rfl

noncomputable def tp13140 : ℝ := (2354065911 / 10000000000)
noncomputable def tm13140 : ℝ := (-((3072918719 / 5000000000)))
noncomputable def ep13140 : ℝ := (52528246360296397 / 100000000000000000000)
noncomputable def em13140 : ℝ := (25532344605489821 / 50000000000000000000)
noncomputable def bp13140 : ℝ := (42198882494579129641 / 100000000000000000000)
noncomputable def bm13140 : ℝ := (2161279466960874751 / 5000000000000000000)

theorem positive13140 :
    Eplus aL (agent13140.root+dsL) scalar13140.worldRadius world13140.frame
      agent13140.frame tp13140 ≤ -ep13140 := by
  apply positive_check (eT := (5785353559970302749 / 5000000000000000000)) (y := (4768028174040778261 / 12500000000000000000)) (u := (29287901933962289971 / 20000000000000000000))
  · norm_num [world13140, agent13140, scalar13140, tp13140, tm13140, ep13140, em13140, dsL]
  · norm_num [world13140, agent13140, scalar13140, tp13140, tm13140, ep13140, em13140, dsL]
  · norm_num [world13140, agent13140, scalar13140, tp13140, tm13140, ep13140, em13140, dsL]
  · norm_num [world13140, agent13140, scalar13140, tp13140, tm13140, ep13140, em13140, dsL]
  · norm_num [world13140, agent13140, scalar13140, tp13140, tm13140, ep13140, em13140, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13140, agent13140, tp13140, tm13140, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13140, agent13140, scalar13140, tp13140, tm13140, ep13140, em13140, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13140, agent13140, tp13140, tm13140, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13140, agent13140, scalar13140, tp13140, tm13140, ep13140, em13140, dsL]

theorem negative13140 :
    Eminus aL (agent13140.root+dsL) scalar13140.worldRadius world13140.frame
      agent13140.frame tm13140 ≤ -em13140 := by
  apply negative_check (lo := (68325720396263601157 / 100000000000000000000)) (hi := (34162860198131800579 / 50000000000000000000))
    (y := (-((71597727261990696127 / 100000000000000000000)))) (u := (48871427126786169253 / 100000000000000000000))
  · norm_num [world13140, agent13140, scalar13140, tp13140, tm13140, ep13140, em13140, dsL]
  · norm_num [world13140, agent13140, scalar13140, tp13140, tm13140, ep13140, em13140, dsL]
  · norm_num [world13140, agent13140, scalar13140, tp13140, tm13140, ep13140, em13140, dsL]
  · norm_num [world13140, agent13140, scalar13140, tp13140, tm13140, ep13140, em13140, dsL]
  · norm_num [world13140, agent13140, scalar13140, tp13140, tm13140, ep13140, em13140, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13140, agent13140, tp13140, tm13140, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13140, agent13140, tp13140, tm13140, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13140, agent13140, scalar13140, tp13140, tm13140, ep13140, em13140, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13140, agent13140, tp13140, tm13140, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13140, agent13140, scalar13140, tp13140, tm13140, ep13140, em13140, dsL]

theorem tails13140 :
    exp (-((13140:ℝ)*ep13140)) ≤ scalar13140.upperTail ∧
    exp (-((13140:ℝ)*em13140)) ≤ scalar13140.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13140:ℝ)) (by norm_num [ep13140]) ?_)
      (show bp13140^8 ≤ scalar13140.upperTail by norm_num [bp13140, scalar13140])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13140, bp13140, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13140:ℝ)) (by norm_num [em13140]) ?_)
      (show bm13140^8 ≤ scalar13140.lowerTail by norm_num [bm13140, scalar13140])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13140, bm13140, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13140 :
    agent13140.root+dsL+scalar13140.worldRadius < √(1/100/aL) ∧
    2*(agent13140.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13140, agent13140, scalar13140, tp13140, tm13140, ep13140, em13140, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13140, agent13140, scalar13140, tp13140, tm13140, ep13140, em13140, dsL]

noncomputable def master13140 : MasterCertificate 13140 world13140 agent13140 :=
  master scalar13140 dsL tp13140 tm13140 ep13140 em13140
    (by norm_num [dsL]) (by norm_num [tp13140]) (by norm_num [tm13140])
    (by norm_num [ep13140]) (by norm_num [em13140])
    positive13140 negative13140 tails13140.1 tails13140.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13140.1 tailGuards13140.2

theorem preserves13140 : master13140.toScalarCertificate = scalar13140 := rfl

noncomputable def tp13141 : ℝ := (2354137541 / 10000000000)
noncomputable def tm13141 : ℝ := (-((192062157 / 312500000)))
noncomputable def ep13141 : ℝ := (26265191767480751 / 50000000000000000000)
noncomputable def em13141 : ℝ := (51066497547461371 / 100000000000000000000)
noncomputable def bp13141 : ℝ := (21097315246562569461 / 50000000000000000000)
noncomputable def bm13141 : ℝ := (2701346651293506611 / 6250000000000000000)

theorem positive13141 :
    Eplus aL (agent13141.root+dsL) scalar13141.worldRadius world13141.frame
      agent13141.frame tp13141 ≤ -ep13141 := by
  apply positive_check (eT := (2892680824824887829 / 2500000000000000000)) (y := (38144865314765996327 / 100000000000000000000)) (u := (146440446772092877181 / 100000000000000000000))
  · norm_num [world13141, agent13141, scalar13141, tp13141, tm13141, ep13141, em13141, dsL]
  · norm_num [world13141, agent13141, scalar13141, tp13141, tm13141, ep13141, em13141, dsL]
  · norm_num [world13141, agent13141, scalar13141, tp13141, tm13141, ep13141, em13141, dsL]
  · norm_num [world13141, agent13141, scalar13141, tp13141, tm13141, ep13141, em13141, dsL]
  · norm_num [world13141, agent13141, scalar13141, tp13141, tm13141, ep13141, em13141, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13141, agent13141, tp13141, tm13141, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13141, agent13141, scalar13141, tp13141, tm13141, ep13141, em13141, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13141, agent13141, tp13141, tm13141, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13141, agent13141, scalar13141, tp13141, tm13141, ep13141, em13141, dsL]

theorem negative13141 :
    Eminus aL (agent13141.root+dsL) scalar13141.worldRadius world13141.frame
      agent13141.frame tm13141 ≤ -em13141 := by
  apply negative_check (lo := (68325620950919456071 / 100000000000000000000)) (hi := (8540702618864932009 / 12500000000000000000))
    (y := (-((71597624365201414493 / 100000000000000000000)))) (u := (48871477413941430759 / 100000000000000000000))
  · norm_num [world13141, agent13141, scalar13141, tp13141, tm13141, ep13141, em13141, dsL]
  · norm_num [world13141, agent13141, scalar13141, tp13141, tm13141, ep13141, em13141, dsL]
  · norm_num [world13141, agent13141, scalar13141, tp13141, tm13141, ep13141, em13141, dsL]
  · norm_num [world13141, agent13141, scalar13141, tp13141, tm13141, ep13141, em13141, dsL]
  · norm_num [world13141, agent13141, scalar13141, tp13141, tm13141, ep13141, em13141, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13141, agent13141, tp13141, tm13141, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13141, agent13141, tp13141, tm13141, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13141, agent13141, scalar13141, tp13141, tm13141, ep13141, em13141, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13141, agent13141, tp13141, tm13141, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13141, agent13141, scalar13141, tp13141, tm13141, ep13141, em13141, dsL]

theorem tails13141 :
    exp (-((13141:ℝ)*ep13141)) ≤ scalar13141.upperTail ∧
    exp (-((13141:ℝ)*em13141)) ≤ scalar13141.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13141:ℝ)) (by norm_num [ep13141]) ?_)
      (show bp13141^8 ≤ scalar13141.upperTail by norm_num [bp13141, scalar13141])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13141, bp13141, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13141:ℝ)) (by norm_num [em13141]) ?_)
      (show bm13141^8 ≤ scalar13141.lowerTail by norm_num [bm13141, scalar13141])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13141, bm13141, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13141 :
    agent13141.root+dsL+scalar13141.worldRadius < √(1/100/aL) ∧
    2*(agent13141.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13141, agent13141, scalar13141, tp13141, tm13141, ep13141, em13141, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13141, agent13141, scalar13141, tp13141, tm13141, ep13141, em13141, dsL]

noncomputable def master13141 : MasterCertificate 13141 world13141 agent13141 :=
  master scalar13141 dsL tp13141 tm13141 ep13141 em13141
    (by norm_num [dsL]) (by norm_num [tp13141]) (by norm_num [tm13141])
    (by norm_num [ep13141]) (by norm_num [em13141])
    positive13141 negative13141 tails13141.1 tails13141.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13141.1 tailGuards13141.2

theorem preserves13141 : master13141.toScalarCertificate = scalar13141 := rfl

noncomputable def tp13142 : ℝ := (2354209039 / 10000000000)
noncomputable def tm13142 : ℝ := (-((1229228077 / 2000000000)))
noncomputable def ep13142 : ℝ := (52532518316746387 / 100000000000000000000)
noncomputable def em13142 : ℝ := (12767075919365181 / 25000000000000000000)
noncomputable def bp13142 : ℝ := (42190380353149838823 / 100000000000000000000)
noncomputable def bm13142 : ℝ := (8643501050287311907 / 20000000000000000000)

theorem positive13142 :
    Eplus aL (agent13142.root+dsL) scalar13142.worldRadius world13142.frame
      agent13142.frame tp13142 ≤ -ep13142 := by
  apply positive_check (eT := (115707393873062201931 / 100000000000000000000)) (y := (38145503446652028969 / 100000000000000000000)) (u := (146441381258259402493 / 100000000000000000000))
  · norm_num [world13142, agent13142, scalar13142, tp13142, tm13142, ep13142, em13142, dsL]
  · norm_num [world13142, agent13142, scalar13142, tp13142, tm13142, ep13142, em13142, dsL]
  · norm_num [world13142, agent13142, scalar13142, tp13142, tm13142, ep13142, em13142, dsL]
  · norm_num [world13142, agent13142, scalar13142, tp13142, tm13142, ep13142, em13142, dsL]
  · norm_num [world13142, agent13142, scalar13142, tp13142, tm13142, ep13142, em13142, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13142, agent13142, tp13142, tm13142, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13142, agent13142, scalar13142, tp13142, tm13142, ep13142, em13142, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13142, agent13142, tp13142, tm13142, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13142, agent13142, scalar13142, tp13142, tm13142, ep13142, em13142, dsL]

theorem negative13142 :
    Eminus aL (agent13142.root+dsL) scalar13142.worldRadius world13142.frame
      agent13142.frame tm13142 ≤ -em13142 := by
  apply negative_check (lo := (68325522401657842477 / 100000000000000000000)) (hi := (34162761200828921239 / 50000000000000000000))
    (y := (-((8949689973690334811 / 12500000000000000000)))) (u := (12217882130411841953 / 25000000000000000000))
  · norm_num [world13142, agent13142, scalar13142, tp13142, tm13142, ep13142, em13142, dsL]
  · norm_num [world13142, agent13142, scalar13142, tp13142, tm13142, ep13142, em13142, dsL]
  · norm_num [world13142, agent13142, scalar13142, tp13142, tm13142, ep13142, em13142, dsL]
  · norm_num [world13142, agent13142, scalar13142, tp13142, tm13142, ep13142, em13142, dsL]
  · norm_num [world13142, agent13142, scalar13142, tp13142, tm13142, ep13142, em13142, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13142, agent13142, tp13142, tm13142, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13142, agent13142, tp13142, tm13142, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13142, agent13142, scalar13142, tp13142, tm13142, ep13142, em13142, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13142, agent13142, tp13142, tm13142, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13142, agent13142, scalar13142, tp13142, tm13142, ep13142, em13142, dsL]

theorem tails13142 :
    exp (-((13142:ℝ)*ep13142)) ≤ scalar13142.upperTail ∧
    exp (-((13142:ℝ)*em13142)) ≤ scalar13142.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13142:ℝ)) (by norm_num [ep13142]) ?_)
      (show bp13142^8 ≤ scalar13142.upperTail by norm_num [bp13142, scalar13142])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13142, bp13142, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13142:ℝ)) (by norm_num [em13142]) ?_)
      (show bm13142^8 ≤ scalar13142.lowerTail by norm_num [bm13142, scalar13142])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13142, bm13142, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13142 :
    agent13142.root+dsL+scalar13142.worldRadius < √(1/100/aL) ∧
    2*(agent13142.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13142, agent13142, scalar13142, tp13142, tm13142, ep13142, em13142, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13142, agent13142, scalar13142, tp13142, tm13142, ep13142, em13142, dsL]

noncomputable def master13142 : MasterCertificate 13142 world13142 agent13142 :=
  master scalar13142 dsL tp13142 tm13142 ep13142 em13142
    (by norm_num [dsL]) (by norm_num [tp13142]) (by norm_num [tm13142])
    (by norm_num [ep13142]) (by norm_num [em13142])
    positive13142 negative13142 tails13142.1 tails13142.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13142.1 tailGuards13142.2

theorem preserves13142 : master13142.toScalarCertificate = scalar13142 := rfl

noncomputable def tp13143 : ℝ := (4708561 / 20000000)
noncomputable def tm13143 : ℝ := (-((3073145921 / 5000000000)))
noncomputable def ep13143 : ℝ := (2626732626790693 / 5000000000000000000)
noncomputable def em13143 : ℝ := (10214021857373953 / 20000000000000000000)
noncomputable def bp13143 : ℝ := (421861308061330389 / 1000000000000000000)
noncomputable def bm13143 : ℝ := (43213464634488818891 / 100000000000000000000)

theorem positive13143 :
    Eplus aL (agent13143.root+dsL) scalar13143.worldRadius world13143.frame
      agent13143.frame tp13143 ≤ -ep13143 := by
  apply positive_check (eT := (28926888630207868961 / 25000000000000000000)) (y := (7629228208153744381 / 20000000000000000000)) (u := (146442314962867328687 / 100000000000000000000))
  · norm_num [world13143, agent13143, scalar13143, tp13143, tm13143, ep13143, em13143, dsL]
  · norm_num [world13143, agent13143, scalar13143, tp13143, tm13143, ep13143, em13143, dsL]
  · norm_num [world13143, agent13143, scalar13143, tp13143, tm13143, ep13143, em13143, dsL]
  · norm_num [world13143, agent13143, scalar13143, tp13143, tm13143, ep13143, em13143, dsL]
  · norm_num [world13143, agent13143, scalar13143, tp13143, tm13143, ep13143, em13143, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13143, agent13143, tp13143, tm13143, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13143, agent13143, scalar13143, tp13143, tm13143, ep13143, em13143, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13143, agent13143, tp13143, tm13143, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13143, agent13143, scalar13143, tp13143, tm13143, ep13143, em13143, dsL]

theorem negative13143 :
    Eminus aL (agent13143.root+dsL) scalar13143.worldRadius world13143.frame
      agent13143.frame tm13143 ≤ -em13143 := by
  apply negative_check (lo := (17081355847321854857 / 25000000000000000000)) (hi := (68325423389287419429 / 100000000000000000000))
    (y := (-((35798708148616537771 / 50000000000000000000)))) (u := (12217894774984342783 / 25000000000000000000))
  · norm_num [world13143, agent13143, scalar13143, tp13143, tm13143, ep13143, em13143, dsL]
  · norm_num [world13143, agent13143, scalar13143, tp13143, tm13143, ep13143, em13143, dsL]
  · norm_num [world13143, agent13143, scalar13143, tp13143, tm13143, ep13143, em13143, dsL]
  · norm_num [world13143, agent13143, scalar13143, tp13143, tm13143, ep13143, em13143, dsL]
  · norm_num [world13143, agent13143, scalar13143, tp13143, tm13143, ep13143, em13143, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13143, agent13143, tp13143, tm13143, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13143, agent13143, tp13143, tm13143, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13143, agent13143, scalar13143, tp13143, tm13143, ep13143, em13143, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13143, agent13143, tp13143, tm13143, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13143, agent13143, scalar13143, tp13143, tm13143, ep13143, em13143, dsL]

theorem tails13143 :
    exp (-((13143:ℝ)*ep13143)) ≤ scalar13143.upperTail ∧
    exp (-((13143:ℝ)*em13143)) ≤ scalar13143.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13143:ℝ)) (by norm_num [ep13143]) ?_)
      (show bp13143^8 ≤ scalar13143.upperTail by norm_num [bp13143, scalar13143])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13143, bp13143, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13143:ℝ)) (by norm_num [em13143]) ?_)
      (show bm13143^8 ≤ scalar13143.lowerTail by norm_num [bm13143, scalar13143])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13143, bm13143, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13143 :
    agent13143.root+dsL+scalar13143.worldRadius < √(1/100/aL) ∧
    2*(agent13143.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13143, agent13143, scalar13143, tp13143, tm13143, ep13143, em13143, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13143, agent13143, scalar13143, tp13143, tm13143, ep13143, em13143, dsL]

noncomputable def master13143 : MasterCertificate 13143 world13143 agent13143 :=
  master scalar13143 dsL tp13143 tm13143 ep13143 em13143
    (by norm_num [dsL]) (by norm_num [tp13143]) (by norm_num [tm13143])
    (by norm_num [ep13143]) (by norm_num [em13143])
    positive13143 negative13143 tails13143.1 tails13143.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13143.1 tailGuards13143.2

theorem preserves13143 : master13143.toScalarCertificate = scalar13143 := rfl

noncomputable def tp13144 : ℝ := (94174083 / 400000000)
noncomputable def tm13144 : ℝ := (-((6146443099 / 10000000000)))
noncomputable def ep13144 : ℝ := (52536786084503779 / 100000000000000000000)
noncomputable def em13144 : ℝ := (25535957132511959 / 50000000000000000000)
noncomputable def bp13144 : ℝ := (21090940963342247903 / 50000000000000000000)
noncomputable def bm13144 : ℝ := (216047123242085853 / 500000000000000000)

theorem positive13144 :
    Eplus aL (agent13144.root+dsL) scalar13144.worldRadius world13144.frame
      agent13144.frame tp13144 ≤ -ep13144 := by
  apply positive_check (eT := (23141543203808011171 / 20000000000000000000)) (y := (3814678098059303331 / 10000000000000000000)) (u := (146443252108559000663 / 100000000000000000000))
  · norm_num [world13144, agent13144, scalar13144, tp13144, tm13144, ep13144, em13144, dsL]
  · norm_num [world13144, agent13144, scalar13144, tp13144, tm13144, ep13144, em13144, dsL]
  · norm_num [world13144, agent13144, scalar13144, tp13144, tm13144, ep13144, em13144, dsL]
  · norm_num [world13144, agent13144, scalar13144, tp13144, tm13144, ep13144, em13144, dsL]
  · norm_num [world13144, agent13144, scalar13144, tp13144, tm13144, ep13144, em13144, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13144, agent13144, tp13144, tm13144, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13144, agent13144, scalar13144, tp13144, tm13144, ep13144, em13144, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13144, agent13144, tp13144, tm13144, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13144, agent13144, scalar13144, tp13144, tm13144, ep13144, em13144, dsL]

theorem negative13144 :
    Eminus aL (agent13144.root+dsL) scalar13144.worldRadius world13144.frame
      agent13144.frame tm13144 ≤ -em13144 := by
  apply negative_check (lo := (4270332822944459477 / 6250000000000000000)) (hi := (68325325167111351633 / 100000000000000000000))
    (y := (-((71597311751176840481 / 100000000000000000000)))) (u := (6108953774159080993 / 12500000000000000000))
  · norm_num [world13144, agent13144, scalar13144, tp13144, tm13144, ep13144, em13144, dsL]
  · norm_num [world13144, agent13144, scalar13144, tp13144, tm13144, ep13144, em13144, dsL]
  · norm_num [world13144, agent13144, scalar13144, tp13144, tm13144, ep13144, em13144, dsL]
  · norm_num [world13144, agent13144, scalar13144, tp13144, tm13144, ep13144, em13144, dsL]
  · norm_num [world13144, agent13144, scalar13144, tp13144, tm13144, ep13144, em13144, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13144, agent13144, tp13144, tm13144, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13144, agent13144, tp13144, tm13144, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13144, agent13144, scalar13144, tp13144, tm13144, ep13144, em13144, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13144, agent13144, tp13144, tm13144, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13144, agent13144, scalar13144, tp13144, tm13144, ep13144, em13144, dsL]

theorem tails13144 :
    exp (-((13144:ℝ)*ep13144)) ≤ scalar13144.upperTail ∧
    exp (-((13144:ℝ)*em13144)) ≤ scalar13144.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13144:ℝ)) (by norm_num [ep13144]) ?_)
      (show bp13144^8 ≤ scalar13144.upperTail by norm_num [bp13144, scalar13144])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13144, bp13144, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13144:ℝ)) (by norm_num [em13144]) ?_)
      (show bm13144^8 ≤ scalar13144.lowerTail by norm_num [bm13144, scalar13144])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13144, bm13144, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13144 :
    agent13144.root+dsL+scalar13144.worldRadius < √(1/100/aL) ∧
    2*(agent13144.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13144, agent13144, scalar13144, tp13144, tm13144, ep13144, em13144, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13144, agent13144, scalar13144, tp13144, tm13144, ep13144, em13144, dsL]

noncomputable def master13144 : MasterCertificate 13144 world13144 agent13144 :=
  master scalar13144 dsL tp13144 tm13144 ep13144 em13144
    (by norm_num [dsL]) (by norm_num [tp13144]) (by norm_num [tm13144])
    (by norm_num [ep13144]) (by norm_num [em13144])
    positive13144 negative13144 tails13144.1 tails13144.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13144.1 tailGuards13144.2

theorem preserves13144 : master13144.toScalarCertificate = scalar13144 := rfl

noncomputable def tp13145 : ℝ := (1177211737 / 5000000000)
noncomputable def tm13145 : ℝ := (-((768324271 / 1250000000)))
noncomputable def ep13145 : ℝ := (52538918013369851 / 100000000000000000000)
noncomputable def em13145 : ℝ := (6384214716386731 / 12500000000000000000)
noncomputable def bp13145 : ℝ := (8435526874558140237 / 20000000000000000000)
noncomputable def bm13145 : ℝ := (43205385918534617933 / 100000000000000000000)

theorem positive13145 :
    Eplus aL (agent13145.root+dsL) scalar13145.worldRadius world13145.frame
      agent13145.frame tp13145 ≤ -ep13145 := by
  apply positive_check (eT := (57853938144134919867 / 50000000000000000000)) (y := (3814741831504069623 / 10000000000000000000)) (u := (73222092722412599987 / 50000000000000000000))
  · norm_num [world13145, agent13145, scalar13145, tp13145, tm13145, ep13145, em13145, dsL]
  · norm_num [world13145, agent13145, scalar13145, tp13145, tm13145, ep13145, em13145, dsL]
  · norm_num [world13145, agent13145, scalar13145, tp13145, tm13145, ep13145, em13145, dsL]
  · norm_num [world13145, agent13145, scalar13145, tp13145, tm13145, ep13145, em13145, dsL]
  · norm_num [world13145, agent13145, scalar13145, tp13145, tm13145, ep13145, em13145, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13145, agent13145, tp13145, tm13145, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13145, agent13145, scalar13145, tp13145, tm13145, ep13145, em13145, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13145, agent13145, tp13145, tm13145, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13145, agent13145, scalar13145, tp13145, tm13145, ep13145, em13145, dsL]

theorem negative13145 :
    Eminus aL (agent13145.root+dsL) scalar13145.worldRadius world13145.frame
      agent13145.frame tm13145 ≤ -em13145 := by
  apply negative_check (lo := (17081306921075384691 / 25000000000000000000)) (hi := (13665045536860307753 / 20000000000000000000))
    (y := (-((17899301502728578659 / 25000000000000000000)))) (u := (48871681870290036673 / 100000000000000000000))
  · norm_num [world13145, agent13145, scalar13145, tp13145, tm13145, ep13145, em13145, dsL]
  · norm_num [world13145, agent13145, scalar13145, tp13145, tm13145, ep13145, em13145, dsL]
  · norm_num [world13145, agent13145, scalar13145, tp13145, tm13145, ep13145, em13145, dsL]
  · norm_num [world13145, agent13145, scalar13145, tp13145, tm13145, ep13145, em13145, dsL]
  · norm_num [world13145, agent13145, scalar13145, tp13145, tm13145, ep13145, em13145, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13145, agent13145, tp13145, tm13145, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13145, agent13145, tp13145, tm13145, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13145, agent13145, scalar13145, tp13145, tm13145, ep13145, em13145, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13145, agent13145, tp13145, tm13145, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13145, agent13145, scalar13145, tp13145, tm13145, ep13145, em13145, dsL]

theorem tails13145 :
    exp (-((13145:ℝ)*ep13145)) ≤ scalar13145.upperTail ∧
    exp (-((13145:ℝ)*em13145)) ≤ scalar13145.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13145:ℝ)) (by norm_num [ep13145]) ?_)
      (show bp13145^8 ≤ scalar13145.upperTail by norm_num [bp13145, scalar13145])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13145, bp13145, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13145:ℝ)) (by norm_num [em13145]) ?_)
      (show bm13145^8 ≤ scalar13145.lowerTail by norm_num [bm13145, scalar13145])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13145, bm13145, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13145 :
    agent13145.root+dsL+scalar13145.worldRadius < √(1/100/aL) ∧
    2*(agent13145.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13145, agent13145, scalar13145, tp13145, tm13145, ep13145, em13145, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13145, agent13145, scalar13145, tp13145, tm13145, ep13145, em13145, dsL]

noncomputable def master13145 : MasterCertificate 13145 world13145 agent13145 :=
  master scalar13145 dsL tp13145 tm13145 ep13145 em13145
    (by norm_num [dsL]) (by norm_num [tp13145]) (by norm_num [tm13145])
    (by norm_num [ep13145]) (by norm_num [em13145])
    positive13145 negative13145 tails13145.1 tails13145.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13145.1 tailGuards13145.2

theorem preserves13145 : master13145.toScalarCertificate = scalar13145 := rfl

noncomputable def tp13146 : ℝ := (1177247451 / 5000000000)
noncomputable def tm13146 : ℝ := (-((307337271 / 500000000)))
noncomputable def ep13146 : ℝ := (3283815589111 / 6250000000000000)
noncomputable def em13146 : ℝ := (25537760362342489 / 50000000000000000000)
noncomputable def bp13146 : ℝ := (527167342246833859 / 1250000000000000000)
noncomputable def bm13146 : ℝ := (43201347706782194857 / 100000000000000000000)

theorem positive13146 :
    Eplus aL (agent13146.root+dsL) scalar13146.worldRadius world13146.frame
      agent13146.frame tp13146 ≤ -ep13146 := by
  apply positive_check (eT := (115708036798427788867 / 100000000000000000000)) (y := (38148056362619971593 / 100000000000000000000)) (u := (36611279957846583113 / 25000000000000000000))
  · norm_num [world13146, agent13146, scalar13146, tp13146, tm13146, ep13146, em13146, dsL]
  · norm_num [world13146, agent13146, scalar13146, tp13146, tm13146, ep13146, em13146, dsL]
  · norm_num [world13146, agent13146, scalar13146, tp13146, tm13146, ep13146, em13146, dsL]
  · norm_num [world13146, agent13146, scalar13146, tp13146, tm13146, ep13146, em13146, dsL]
  · norm_num [world13146, agent13146, scalar13146, tp13146, tm13146, ep13146, em13146, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13146, agent13146, tp13146, tm13146, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13146, agent13146, scalar13146, tp13146, tm13146, ep13146, em13146, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13146, agent13146, tp13146, tm13146, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13146, agent13146, scalar13146, tp13146, tm13146, ep13146, em13146, dsL]

theorem negative13146 :
    Eminus aL (agent13146.root+dsL) scalar13146.worldRadius world13146.frame
      agent13146.frame tm13146 ≤ -em13146 := by
  apply negative_check (lo := (3416256468503718741 / 5000000000000000000)) (hi := (68325129370074374821 / 100000000000000000000))
    (y := (-((17899275649106604401 / 25000000000000000000)))) (u := (12217933102678925639 / 25000000000000000000))
  · norm_num [world13146, agent13146, scalar13146, tp13146, tm13146, ep13146, em13146, dsL]
  · norm_num [world13146, agent13146, scalar13146, tp13146, tm13146, ep13146, em13146, dsL]
  · norm_num [world13146, agent13146, scalar13146, tp13146, tm13146, ep13146, em13146, dsL]
  · norm_num [world13146, agent13146, scalar13146, tp13146, tm13146, ep13146, em13146, dsL]
  · norm_num [world13146, agent13146, scalar13146, tp13146, tm13146, ep13146, em13146, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13146, agent13146, tp13146, tm13146, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13146, agent13146, tp13146, tm13146, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13146, agent13146, scalar13146, tp13146, tm13146, ep13146, em13146, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13146, agent13146, tp13146, tm13146, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13146, agent13146, scalar13146, tp13146, tm13146, ep13146, em13146, dsL]

theorem tails13146 :
    exp (-((13146:ℝ)*ep13146)) ≤ scalar13146.upperTail ∧
    exp (-((13146:ℝ)*em13146)) ≤ scalar13146.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13146:ℝ)) (by norm_num [ep13146]) ?_)
      (show bp13146^8 ≤ scalar13146.upperTail by norm_num [bp13146, scalar13146])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13146, bp13146, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13146:ℝ)) (by norm_num [em13146]) ?_)
      (show bm13146^8 ≤ scalar13146.lowerTail by norm_num [bm13146, scalar13146])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13146, bm13146, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13146 :
    agent13146.root+dsL+scalar13146.worldRadius < √(1/100/aL) ∧
    2*(agent13146.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13146, agent13146, scalar13146, tp13146, tm13146, ep13146, em13146, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13146, agent13146, scalar13146, tp13146, tm13146, ep13146, em13146, dsL]

noncomputable def master13146 : MasterCertificate 13146 world13146 agent13146 :=
  master scalar13146 dsL tp13146 tm13146 ep13146 em13146
    (by norm_num [dsL]) (by norm_num [tp13146]) (by norm_num [tm13146])
    (by norm_num [ep13146]) (by norm_num [em13146])
    positive13146 negative13146 tails13146.1 tails13146.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13146.1 tailGuards13146.2

theorem preserves13146 : master13146.toScalarCertificate = scalar13146 := rfl

noncomputable def tp13147 : ℝ := (117728313 / 500000000)
noncomputable def tm13147 : ℝ := (-((768362051 / 1250000000)))
noncomputable def ep13147 : ℝ := (52543179213631929 / 100000000000000000000)
noncomputable def em13147 : ℝ := (25538661101112311 / 50000000000000000000)
noncomputable def bp13147 : ℝ := (1686765668618171719 / 4000000000000000000)
noncomputable def bm13147 : ℝ := (43197310753987499733 / 100000000000000000000)

theorem positive13147 :
    Eplus aL (agent13147.root+dsL) scalar13147.worldRadius world13147.frame
      agent13147.frame tp13147 ≤ -ep13147 := by
  apply positive_check (eT := (57854098419857604863 / 50000000000000000000)) (y := (38148693650442294773 / 100000000000000000000)) (u := (146446053111275240847 / 100000000000000000000))
  · norm_num [world13147, agent13147, scalar13147, tp13147, tm13147, ep13147, em13147, dsL]
  · norm_num [world13147, agent13147, scalar13147, tp13147, tm13147, ep13147, em13147, dsL]
  · norm_num [world13147, agent13147, scalar13147, tp13147, tm13147, ep13147, em13147, dsL]
  · norm_num [world13147, agent13147, scalar13147, tp13147, tm13147, ep13147, em13147, dsL]
  · norm_num [world13147, agent13147, scalar13147, tp13147, tm13147, ep13147, em13147, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13147, agent13147, tp13147, tm13147, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13147, agent13147, scalar13147, tp13147, tm13147, ep13147, em13147, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13147, agent13147, tp13147, tm13147, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13147, agent13147, scalar13147, tp13147, tm13147, ep13147, em13147, dsL]

theorem negative13147 :
    Eminus aL (agent13147.root+dsL) scalar13147.worldRadius world13147.frame
      agent13147.frame tm13147 ≤ -em13147 := by
  apply negative_check (lo := (68325032116932370583 / 100000000000000000000)) (hi := (8540629014616546323 / 12500000000000000000))
    (y := (-((71596997259901099731 / 100000000000000000000)))) (u := (48871783890527600171 / 100000000000000000000))
  · norm_num [world13147, agent13147, scalar13147, tp13147, tm13147, ep13147, em13147, dsL]
  · norm_num [world13147, agent13147, scalar13147, tp13147, tm13147, ep13147, em13147, dsL]
  · norm_num [world13147, agent13147, scalar13147, tp13147, tm13147, ep13147, em13147, dsL]
  · norm_num [world13147, agent13147, scalar13147, tp13147, tm13147, ep13147, em13147, dsL]
  · norm_num [world13147, agent13147, scalar13147, tp13147, tm13147, ep13147, em13147, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13147, agent13147, tp13147, tm13147, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13147, agent13147, tp13147, tm13147, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13147, agent13147, scalar13147, tp13147, tm13147, ep13147, em13147, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13147, agent13147, tp13147, tm13147, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13147, agent13147, scalar13147, tp13147, tm13147, ep13147, em13147, dsL]

theorem tails13147 :
    exp (-((13147:ℝ)*ep13147)) ≤ scalar13147.upperTail ∧
    exp (-((13147:ℝ)*em13147)) ≤ scalar13147.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13147:ℝ)) (by norm_num [ep13147]) ?_)
      (show bp13147^8 ≤ scalar13147.upperTail by norm_num [bp13147, scalar13147])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13147, bp13147, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13147:ℝ)) (by norm_num [em13147]) ?_)
      (show bm13147^8 ≤ scalar13147.lowerTail by norm_num [bm13147, scalar13147])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13147, bm13147, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13147 :
    agent13147.root+dsL+scalar13147.worldRadius < √(1/100/aL) ∧
    2*(agent13147.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13147, agent13147, scalar13147, tp13147, tm13147, ep13147, em13147, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13147, agent13147, scalar13147, tp13147, tm13147, ep13147, em13147, dsL]

noncomputable def master13147 : MasterCertificate 13147 world13147 agent13147 :=
  master scalar13147 dsL tp13147 tm13147 ep13147 em13147
    (by norm_num [dsL]) (by norm_num [tp13147]) (by norm_num [tm13147])
    (by norm_num [ep13147]) (by norm_num [em13147])
    positive13147 negative13147 tails13147.1 tails13147.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13147.1 tailGuards13147.2

theorem preserves13147 : master13147.toScalarCertificate = scalar13147 := rfl

noncomputable def tp13148 : ℝ := (2354637693 / 10000000000)
noncomputable def tm13148 : ℝ := (-((3073523683 / 5000000000)))
noncomputable def ep13148 : ℝ := (10509061697023397 / 20000000000000000000)
noncomputable def em13148 : ℝ := (1021582464148487 / 2000000000000000000)
noncomputable def bp13148 : ℝ := (21082448305954450637 / 50000000000000000000)
noncomputable def bm13148 : ℝ := (21596637159601096151 / 50000000000000000000)

theorem positive13148 :
    Eplus aL (agent13148.root+dsL) scalar13148.worldRadius world13148.frame
      agent13148.frame tp13148 ≤ -ep13148 := by
  apply positive_check (eT := (115708357451725431897 / 100000000000000000000)) (y := (7629866490425312591 / 20000000000000000000)) (u := (146446988614117060723 / 100000000000000000000))
  · norm_num [world13148, agent13148, scalar13148, tp13148, tm13148, ep13148, em13148, dsL]
  · norm_num [world13148, agent13148, scalar13148, tp13148, tm13148, ep13148, em13148, dsL]
  · norm_num [world13148, agent13148, scalar13148, tp13148, tm13148, ep13148, em13148, dsL]
  · norm_num [world13148, agent13148, scalar13148, tp13148, tm13148, ep13148, em13148, dsL]
  · norm_num [world13148, agent13148, scalar13148, tp13148, tm13148, ep13148, em13148, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13148, agent13148, tp13148, tm13148, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13148, agent13148, scalar13148, tp13148, tm13148, ep13148, em13148, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13148, agent13148, tp13148, tm13148, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13148, agent13148, scalar13148, tp13148, tm13148, ep13148, em13148, dsL]

theorem negative13148 :
    Eminus aL (agent13148.root+dsL) scalar13148.worldRadius world13148.frame
      agent13148.frame tm13148 ≤ -em13148 := by
  apply negative_check (lo := (68324934934197031011 / 100000000000000000000)) (hi := (17081233733549257753 / 25000000000000000000))
    (y := (-((17899223052564022143 / 25000000000000000000)))) (u := (48871835230190053853 / 100000000000000000000))
  · norm_num [world13148, agent13148, scalar13148, tp13148, tm13148, ep13148, em13148, dsL]
  · norm_num [world13148, agent13148, scalar13148, tp13148, tm13148, ep13148, em13148, dsL]
  · norm_num [world13148, agent13148, scalar13148, tp13148, tm13148, ep13148, em13148, dsL]
  · norm_num [world13148, agent13148, scalar13148, tp13148, tm13148, ep13148, em13148, dsL]
  · norm_num [world13148, agent13148, scalar13148, tp13148, tm13148, ep13148, em13148, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13148, agent13148, tp13148, tm13148, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13148, agent13148, tp13148, tm13148, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13148, agent13148, scalar13148, tp13148, tm13148, ep13148, em13148, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13148, agent13148, tp13148, tm13148, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13148, agent13148, scalar13148, tp13148, tm13148, ep13148, em13148, dsL]

theorem tails13148 :
    exp (-((13148:ℝ)*ep13148)) ≤ scalar13148.upperTail ∧
    exp (-((13148:ℝ)*em13148)) ≤ scalar13148.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13148:ℝ)) (by norm_num [ep13148]) ?_)
      (show bp13148^8 ≤ scalar13148.upperTail by norm_num [bp13148, scalar13148])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13148, bp13148, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13148:ℝ)) (by norm_num [em13148]) ?_)
      (show bm13148^8 ≤ scalar13148.lowerTail by norm_num [bm13148, scalar13148])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13148, bm13148, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13148 :
    agent13148.root+dsL+scalar13148.worldRadius < √(1/100/aL) ∧
    2*(agent13148.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13148, agent13148, scalar13148, tp13148, tm13148, ep13148, em13148, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13148, agent13148, scalar13148, tp13148, tm13148, ep13148, em13148, dsL]

noncomputable def master13148 : MasterCertificate 13148 world13148 agent13148 :=
  master scalar13148 dsL tp13148 tm13148 ep13148 em13148
    (by norm_num [dsL]) (by norm_num [tp13148]) (by norm_num [tm13148])
    (by norm_num [ep13148]) (by norm_num [em13148])
    positive13148 negative13148 tails13148.1 tails13148.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13148.1 tailGuards13148.2

theorem preserves13148 : master13148.toScalarCertificate = scalar13148 := rfl

noncomputable def tp13149 : ℝ := (2354708969 / 10000000000)
noncomputable def tm13149 : ℝ := (-((1229439667 / 2000000000)))
noncomputable def ep13149 : ℝ := (52547435801714381 / 100000000000000000000)
noncomputable def em13149 : ℝ := (51080922406796847 / 100000000000000000000)
noncomputable def bp13149 : ℝ := (42160653065947823481 / 100000000000000000000)
noncomputable def bm13149 : ℝ := (2159461967451476783 / 5000000000000000000)

theorem positive13149 :
    Eplus aL (agent13149.root+dsL) scalar13149.worldRadius world13149.frame
      agent13149.frame tp13149 ≤ -ep13149 := by
  apply positive_check (eT := (115708516971082903563 / 100000000000000000000)) (y := (38149968876119713181 / 100000000000000000000)) (u := (146447920640855664691 / 100000000000000000000))
  · norm_num [world13149, agent13149, scalar13149, tp13149, tm13149, ep13149, em13149, dsL]
  · norm_num [world13149, agent13149, scalar13149, tp13149, tm13149, ep13149, em13149, dsL]
  · norm_num [world13149, agent13149, scalar13149, tp13149, tm13149, ep13149, em13149, dsL]
  · norm_num [world13149, agent13149, scalar13149, tp13149, tm13149, ep13149, em13149, dsL]
  · norm_num [world13149, agent13149, scalar13149, tp13149, tm13149, ep13149, em13149, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13149, agent13149, tp13149, tm13149, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13149, agent13149, scalar13149, tp13149, tm13149, ep13149, em13149, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13149, agent13149, tp13149, tm13149, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13149, agent13149, scalar13149, tp13149, tm13149, ep13149, em13149, dsL]

theorem negative13149 :
    Eminus aL (agent13149.root+dsL) scalar13149.worldRadius world13149.frame
      agent13149.frame tm13149 ≤ -em13149 := by
  apply negative_check (lo := (68324837648276811181 / 100000000000000000000)) (hi := (34162418824138405591 / 50000000000000000000))
    (y := (-((71596787456490937413 / 100000000000000000000)))) (u := (12217971606326092587 / 25000000000000000000))
  · norm_num [world13149, agent13149, scalar13149, tp13149, tm13149, ep13149, em13149, dsL]
  · norm_num [world13149, agent13149, scalar13149, tp13149, tm13149, ep13149, em13149, dsL]
  · norm_num [world13149, agent13149, scalar13149, tp13149, tm13149, ep13149, em13149, dsL]
  · norm_num [world13149, agent13149, scalar13149, tp13149, tm13149, ep13149, em13149, dsL]
  · norm_num [world13149, agent13149, scalar13149, tp13149, tm13149, ep13149, em13149, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13149, agent13149, tp13149, tm13149, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13149, agent13149, tp13149, tm13149, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13149, agent13149, scalar13149, tp13149, tm13149, ep13149, em13149, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13149, agent13149, tp13149, tm13149, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13149, agent13149, scalar13149, tp13149, tm13149, ep13149, em13149, dsL]

theorem tails13149 :
    exp (-((13149:ℝ)*ep13149)) ≤ scalar13149.upperTail ∧
    exp (-((13149:ℝ)*em13149)) ≤ scalar13149.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13149:ℝ)) (by norm_num [ep13149]) ?_)
      (show bp13149^8 ≤ scalar13149.upperTail by norm_num [bp13149, scalar13149])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13149, bp13149, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13149:ℝ)) (by norm_num [em13149]) ?_)
      (show bm13149^8 ≤ scalar13149.lowerTail by norm_num [bm13149, scalar13149])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13149, bm13149, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13149 :
    agent13149.root+dsL+scalar13149.worldRadius < √(1/100/aL) ∧
    2*(agent13149.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13149, agent13149, scalar13149, tp13149, tm13149, ep13149, em13149, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13149, agent13149, scalar13149, tp13149, tm13149, ep13149, em13149, dsL]

noncomputable def master13149 : MasterCertificate 13149 world13149 agent13149 :=
  master scalar13149 dsL tp13149 tm13149 ep13149 em13149
    (by norm_num [dsL]) (by norm_num [tp13149]) (by norm_num [tm13149])
    (by norm_num [ep13149]) (by norm_num [em13149])
    positive13149 negative13149 tails13149.1 tails13149.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13149.1 tailGuards13149.2

theorem preserves13149 : master13149.toScalarCertificate = scalar13149 := rfl

end BstLean.Part268
