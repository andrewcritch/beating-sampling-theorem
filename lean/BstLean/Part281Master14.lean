import BstLean.Part261Checker
import BstLean.Part281Scalar14
namespace BstLean.Part281
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12209 : ℝ := (237874771 / 1000000000)
noncomputable def tm12209 : ℝ := (-((6152072843 / 10000000000)))
noncomputable def ep12209 : ℝ := (27383499414235959 / 50000000000000000000)
noncomputable def em12209 : ℝ := (52787986279577789 / 100000000000000000000)
noncomputable def bp12209 : ℝ := (21676097257249479663 / 50000000000000000000)
noncomputable def bm12209 : ℝ := (8936299863036679817 / 20000000000000000000)

theorem positive12209 :
    Eplus aL (agent12209.root+dsL) scalar12209.worldRadius world12209.frame
      agent12209.frame tp12209 ≤ -ep12209 := by
  apply positive_check (eT := (4649680448188382653 / 4000000000000000000)) (y := (39663764994094936147 / 100000000000000000000)) (u := (18585213552169210137 / 12500000000000000000))
  · norm_num [world12209, agent12209, scalar12209, tp12209, tm12209, ep12209, em12209, dsL]
  · norm_num [world12209, agent12209, scalar12209, tp12209, tm12209, ep12209, em12209, dsL]
  · norm_num [world12209, agent12209, scalar12209, tp12209, tm12209, ep12209, em12209, dsL]
  · norm_num [world12209, agent12209, scalar12209, tp12209, tm12209, ep12209, em12209, dsL]
  · norm_num [world12209, agent12209, scalar12209, tp12209, tm12209, ep12209, em12209, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12209, agent12209, tp12209, tm12209, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12209, agent12209, scalar12209, tp12209, tm12209, ep12209, em12209, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12209, agent12209, tp12209, tm12209, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12209, agent12209, scalar12209, tp12209, tm12209, ep12209, em12209, dsL]

theorem negative12209 :
    Eminus aL (agent12209.root+dsL) scalar12209.worldRadius world12209.frame
      agent12209.frame tm12209 ≤ -em12209 := by
  apply negative_check (lo := (33878458543395077833 / 50000000000000000000)) (hi := (67756917086790155667 / 100000000000000000000))
    (y := (-((73279770811334051883 / 100000000000000000000)))) (u := (48056263363310709907 / 100000000000000000000))
  · norm_num [world12209, agent12209, scalar12209, tp12209, tm12209, ep12209, em12209, dsL]
  · norm_num [world12209, agent12209, scalar12209, tp12209, tm12209, ep12209, em12209, dsL]
  · norm_num [world12209, agent12209, scalar12209, tp12209, tm12209, ep12209, em12209, dsL]
  · norm_num [world12209, agent12209, scalar12209, tp12209, tm12209, ep12209, em12209, dsL]
  · norm_num [world12209, agent12209, scalar12209, tp12209, tm12209, ep12209, em12209, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12209, agent12209, tp12209, tm12209, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12209, agent12209, tp12209, tm12209, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12209, agent12209, scalar12209, tp12209, tm12209, ep12209, em12209, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12209, agent12209, tp12209, tm12209, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12209, agent12209, scalar12209, tp12209, tm12209, ep12209, em12209, dsL]

theorem tails12209 :
    exp (-((12209:ℝ)*ep12209)) ≤ scalar12209.upperTail ∧
    exp (-((12209:ℝ)*em12209)) ≤ scalar12209.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12209:ℝ)) (by norm_num [ep12209]) ?_)
      (show bp12209^8 ≤ scalar12209.upperTail by norm_num [bp12209, scalar12209])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12209, bp12209, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12209:ℝ)) (by norm_num [em12209]) ?_)
      (show bm12209^8 ≤ scalar12209.lowerTail by norm_num [bm12209, scalar12209])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12209, bm12209, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12209 :
    agent12209.root+dsL+scalar12209.worldRadius < √(1/100/aL) ∧
    2*(agent12209.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12209, agent12209, scalar12209, tp12209, tm12209, ep12209, em12209, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12209, agent12209, scalar12209, tp12209, tm12209, ep12209, em12209, dsL]

noncomputable def master12209 : MasterCertificate 12209 world12209 agent12209 :=
  master scalar12209 dsL tp12209 tm12209 ep12209 em12209
    (by norm_num [dsL]) (by norm_num [tp12209]) (by norm_num [tm12209])
    (by norm_num [ep12209]) (by norm_num [em12209])
    positive12209 negative12209 tails12209.1 tails12209.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12209.1 tailGuards12209.2

theorem preserves12209 : master12209.toScalarCertificate = scalar12209 := rfl

noncomputable def tp12210 : ℝ := (118942183 / 500000000)
noncomputable def tm12210 : ℝ := (-((6152287601 / 10000000000)))
noncomputable def ep12210 : ℝ := (54769799681327939 / 100000000000000000000)
noncomputable def em12210 : ℝ := (52790415789848947 / 100000000000000000000)
noncomputable def bp12210 : ℝ := (5418421715654705587 / 12500000000000000000)
noncomputable def bm12210 : ℝ := (87259559446549039 / 195312500000000000)

theorem positive12210 :
    Eplus aL (agent12210.root+dsL) scalar12210.worldRadius world12210.frame
      agent12210.frame tp12210 ≤ -ep12210 := by
  apply positive_check (eT := (58121150978020319839 / 50000000000000000000)) (y := (2479023378841117257 / 6250000000000000000)) (u := (7434130699593604469 / 5000000000000000000))
  · norm_num [world12210, agent12210, scalar12210, tp12210, tm12210, ep12210, em12210, dsL]
  · norm_num [world12210, agent12210, scalar12210, tp12210, tm12210, ep12210, em12210, dsL]
  · norm_num [world12210, agent12210, scalar12210, tp12210, tm12210, ep12210, em12210, dsL]
  · norm_num [world12210, agent12210, scalar12210, tp12210, tm12210, ep12210, em12210, dsL]
  · norm_num [world12210, agent12210, scalar12210, tp12210, tm12210, ep12210, em12210, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12210, agent12210, tp12210, tm12210, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12210, agent12210, scalar12210, tp12210, tm12210, ep12210, em12210, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12210, agent12210, tp12210, tm12210, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12210, agent12210, scalar12210, tp12210, tm12210, ep12210, em12210, dsL]

theorem negative12210 :
    Eminus aL (agent12210.root+dsL) scalar12210.worldRadius world12210.frame
      agent12210.frame tm12210 ≤ -em12210 := by
  apply negative_check (lo := (8469577741431590237 / 12500000000000000000)) (hi := (67756621931452721897 / 100000000000000000000))
    (y := (-((73279360024988577383 / 100000000000000000000)))) (u := (6007057596535526991 / 12500000000000000000))
  · norm_num [world12210, agent12210, scalar12210, tp12210, tm12210, ep12210, em12210, dsL]
  · norm_num [world12210, agent12210, scalar12210, tp12210, tm12210, ep12210, em12210, dsL]
  · norm_num [world12210, agent12210, scalar12210, tp12210, tm12210, ep12210, em12210, dsL]
  · norm_num [world12210, agent12210, scalar12210, tp12210, tm12210, ep12210, em12210, dsL]
  · norm_num [world12210, agent12210, scalar12210, tp12210, tm12210, ep12210, em12210, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12210, agent12210, tp12210, tm12210, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12210, agent12210, tp12210, tm12210, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12210, agent12210, scalar12210, tp12210, tm12210, ep12210, em12210, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12210, agent12210, tp12210, tm12210, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12210, agent12210, scalar12210, tp12210, tm12210, ep12210, em12210, dsL]

theorem tails12210 :
    exp (-((12210:ℝ)*ep12210)) ≤ scalar12210.upperTail ∧
    exp (-((12210:ℝ)*em12210)) ≤ scalar12210.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12210:ℝ)) (by norm_num [ep12210]) ?_)
      (show bp12210^8 ≤ scalar12210.upperTail by norm_num [bp12210, scalar12210])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12210, bp12210, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12210:ℝ)) (by norm_num [em12210]) ?_)
      (show bm12210^8 ≤ scalar12210.lowerTail by norm_num [bm12210, scalar12210])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12210, bm12210, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12210 :
    agent12210.root+dsL+scalar12210.worldRadius < √(1/100/aL) ∧
    2*(agent12210.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12210, agent12210, scalar12210, tp12210, tm12210, ep12210, em12210, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12210, agent12210, scalar12210, tp12210, tm12210, ep12210, em12210, dsL]

noncomputable def master12210 : MasterCertificate 12210 world12210 agent12210 :=
  master scalar12210 dsL tp12210 tm12210 ep12210 em12210
    (by norm_num [dsL]) (by norm_num [tp12210]) (by norm_num [tm12210])
    (by norm_num [ep12210]) (by norm_num [em12210])
    positive12210 negative12210 tails12210.1 tails12210.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12210.1 tailGuards12210.2

theorem preserves12210 : master12210.toScalarCertificate = scalar12210 := rfl

noncomputable def tp12211 : ℝ := (1189469773 / 5000000000)
noncomputable def tm12211 : ℝ := (-((6152502313 / 10000000000)))
noncomputable def ep12211 : ℝ := (54772599716007083 / 100000000000000000000)
noncomputable def em12211 : ℝ := (26396422283108907 / 50000000000000000000)
noncomputable def bp12211 : ℝ := (43342553709841810769 / 100000000000000000000)
noncomputable def bm12211 : ℝ := (22336145130877987093 / 50000000000000000000)

theorem positive12211 :
    Eplus aL (agent12211.root+dsL) scalar12211.worldRadius world12211.frame
      agent12211.frame tp12211 ≤ -ep12211 := by
  apply positive_check (eT := (116242592273800285181 / 100000000000000000000)) (y := (4958122795555886379 / 12500000000000000000)) (u := (148683518435408320563 / 100000000000000000000))
  · norm_num [world12211, agent12211, scalar12211, tp12211, tm12211, ep12211, em12211, dsL]
  · norm_num [world12211, agent12211, scalar12211, tp12211, tm12211, ep12211, em12211, dsL]
  · norm_num [world12211, agent12211, scalar12211, tp12211, tm12211, ep12211, em12211, dsL]
  · norm_num [world12211, agent12211, scalar12211, tp12211, tm12211, ep12211, em12211, dsL]
  · norm_num [world12211, agent12211, scalar12211, tp12211, tm12211, ep12211, em12211, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12211, agent12211, tp12211, tm12211, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12211, agent12211, scalar12211, tp12211, tm12211, ep12211, em12211, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12211, agent12211, tp12211, tm12211, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12211, agent12211, scalar12211, tp12211, tm12211, ep12211, em12211, dsL]

theorem negative12211 :
    Eminus aL (agent12211.root+dsL) scalar12211.worldRadius world12211.frame
      agent12211.frame tm12211 ≤ -em12211 := by
  apply negative_check (lo := (67756326912959562727 / 100000000000000000000)) (hi := (8469540864119945341 / 12500000000000000000))
    (y := (-((73278949920396296693 / 100000000000000000000)))) (u := (24028328927220425923 / 50000000000000000000))
  · norm_num [world12211, agent12211, scalar12211, tp12211, tm12211, ep12211, em12211, dsL]
  · norm_num [world12211, agent12211, scalar12211, tp12211, tm12211, ep12211, em12211, dsL]
  · norm_num [world12211, agent12211, scalar12211, tp12211, tm12211, ep12211, em12211, dsL]
  · norm_num [world12211, agent12211, scalar12211, tp12211, tm12211, ep12211, em12211, dsL]
  · norm_num [world12211, agent12211, scalar12211, tp12211, tm12211, ep12211, em12211, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12211, agent12211, tp12211, tm12211, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12211, agent12211, tp12211, tm12211, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12211, agent12211, scalar12211, tp12211, tm12211, ep12211, em12211, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12211, agent12211, tp12211, tm12211, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12211, agent12211, scalar12211, tp12211, tm12211, ep12211, em12211, dsL]

theorem tails12211 :
    exp (-((12211:ℝ)*ep12211)) ≤ scalar12211.upperTail ∧
    exp (-((12211:ℝ)*em12211)) ≤ scalar12211.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12211:ℝ)) (by norm_num [ep12211]) ?_)
      (show bp12211^8 ≤ scalar12211.upperTail by norm_num [bp12211, scalar12211])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12211, bp12211, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12211:ℝ)) (by norm_num [em12211]) ?_)
      (show bm12211^8 ≤ scalar12211.lowerTail by norm_num [bm12211, scalar12211])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12211, bm12211, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12211 :
    agent12211.root+dsL+scalar12211.worldRadius < √(1/100/aL) ∧
    2*(agent12211.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12211, agent12211, scalar12211, tp12211, tm12211, ep12211, em12211, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12211, agent12211, scalar12211, tp12211, tm12211, ep12211, em12211, dsL]

noncomputable def master12211 : MasterCertificate 12211 world12211 agent12211 :=
  master scalar12211 dsL tp12211 tm12211 ep12211 em12211
    (by norm_num [dsL]) (by norm_num [tp12211]) (by norm_num [tm12211])
    (by norm_num [ep12211]) (by norm_num [em12211])
    positive12211 negative12211 tails12211.1 tails12211.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12211.1 tailGuards12211.2

theorem preserves12211 : master12211.toScalarCertificate = scalar12211 := rfl

noncomputable def tp12212 : ℝ := (1189517679 / 5000000000)
noncomputable def tm12212 : ℝ := (-((1230543367 / 2000000000)))
noncomputable def ep12212 : ℝ := (273876990240809 / 500000000000000000)
noncomputable def em12212 : ℝ := (26397635861195891 / 50000000000000000000)
noncomputable def bp12212 : ℝ := (43337735053346071997 / 100000000000000000000)
noncomputable def bm12212 : ℝ := (44667687394875794337 / 100000000000000000000)

theorem positive12212 :
    Eplus aL (agent12212.root+dsL) scalar12212.worldRadius world12212.frame
      agent12212.frame tp12212 ≤ -ep12212 := by
  apply positive_check (eT := (116242882084457511973 / 100000000000000000000)) (y := (3966559004128299701 / 10000000000000000000)) (u := (148684421953453894689 / 100000000000000000000))
  · norm_num [world12212, agent12212, scalar12212, tp12212, tm12212, ep12212, em12212, dsL]
  · norm_num [world12212, agent12212, scalar12212, tp12212, tm12212, ep12212, em12212, dsL]
  · norm_num [world12212, agent12212, scalar12212, tp12212, tm12212, ep12212, em12212, dsL]
  · norm_num [world12212, agent12212, scalar12212, tp12212, tm12212, ep12212, em12212, dsL]
  · norm_num [world12212, agent12212, scalar12212, tp12212, tm12212, ep12212, em12212, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12212, agent12212, tp12212, tm12212, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12212, agent12212, scalar12212, tp12212, tm12212, ep12212, em12212, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12212, agent12212, tp12212, tm12212, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12212, agent12212, scalar12212, tp12212, tm12212, ep12212, em12212, dsL]

theorem negative12212 :
    Eminus aL (agent12212.root+dsL) scalar12212.worldRadius world12212.frame
      agent12212.frame tm12212 ≤ -em12212 := by
  apply negative_check (lo := (846950408107523153 / 1250000000000000000)) (hi := (67756032648601852241 / 100000000000000000000))
    (y := (-((73278539010343712759 / 100000000000000000000)))) (u := (24028427662242311731 / 50000000000000000000))
  · norm_num [world12212, agent12212, scalar12212, tp12212, tm12212, ep12212, em12212, dsL]
  · norm_num [world12212, agent12212, scalar12212, tp12212, tm12212, ep12212, em12212, dsL]
  · norm_num [world12212, agent12212, scalar12212, tp12212, tm12212, ep12212, em12212, dsL]
  · norm_num [world12212, agent12212, scalar12212, tp12212, tm12212, ep12212, em12212, dsL]
  · norm_num [world12212, agent12212, scalar12212, tp12212, tm12212, ep12212, em12212, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12212, agent12212, tp12212, tm12212, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12212, agent12212, tp12212, tm12212, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12212, agent12212, scalar12212, tp12212, tm12212, ep12212, em12212, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12212, agent12212, tp12212, tm12212, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12212, agent12212, scalar12212, tp12212, tm12212, ep12212, em12212, dsL]

theorem tails12212 :
    exp (-((12212:ℝ)*ep12212)) ≤ scalar12212.upperTail ∧
    exp (-((12212:ℝ)*em12212)) ≤ scalar12212.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12212:ℝ)) (by norm_num [ep12212]) ?_)
      (show bp12212^8 ≤ scalar12212.upperTail by norm_num [bp12212, scalar12212])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12212, bp12212, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12212:ℝ)) (by norm_num [em12212]) ?_)
      (show bm12212^8 ≤ scalar12212.lowerTail by norm_num [bm12212, scalar12212])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12212, bm12212, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12212 :
    agent12212.root+dsL+scalar12212.worldRadius < √(1/100/aL) ∧
    2*(agent12212.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12212, agent12212, scalar12212, tp12212, tm12212, ep12212, em12212, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12212, agent12212, scalar12212, tp12212, tm12212, ep12212, em12212, dsL]

noncomputable def master12212 : MasterCertificate 12212 world12212 agent12212 :=
  master scalar12212 dsL tp12212 tm12212 ep12212 em12212
    (by norm_num [dsL]) (by norm_num [tp12212]) (by norm_num [tm12212])
    (by norm_num [ep12212]) (by norm_num [em12212])
    positive12212 negative12212 tails12212.1 tails12212.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12212.1 tailGuards12212.2

theorem preserves12212 : master12212.toScalarCertificate = scalar12212 := rfl

noncomputable def tp12213 : ℝ := (2379131141 / 10000000000)
noncomputable def tm12213 : ℝ := (-((6152931183 / 10000000000)))
noncomputable def ep12213 : ℝ := (6847274369524973 / 12500000000000000000)
noncomputable def em12213 : ℝ := (13199424389890573 / 25000000000000000000)
noncomputable def bp12213 : ℝ := (21666458785758826637 / 50000000000000000000)
noncomputable def bm12213 : ℝ := (44663085630593665621 / 100000000000000000000)

theorem positive12213 :
    Eplus aL (agent12213.root+dsL) scalar12213.worldRadius world12213.frame
      agent12213.frame tp12213 ≤ -ep12213 := by
  apply positive_check (eT := (11624317171896005933 / 10000000000000000000)) (y := (4958274710840916773 / 12500000000000000000)) (u := (148685325430315299127 / 100000000000000000000))
  · norm_num [world12213, agent12213, scalar12213, tp12213, tm12213, ep12213, em12213, dsL]
  · norm_num [world12213, agent12213, scalar12213, tp12213, tm12213, ep12213, em12213, dsL]
  · norm_num [world12213, agent12213, scalar12213, tp12213, tm12213, ep12213, em12213, dsL]
  · norm_num [world12213, agent12213, scalar12213, tp12213, tm12213, ep12213, em12213, dsL]
  · norm_num [world12213, agent12213, scalar12213, tp12213, tm12213, ep12213, em12213, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12213, agent12213, tp12213, tm12213, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12213, agent12213, scalar12213, tp12213, tm12213, ep12213, em12213, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12213, agent12213, tp12213, tm12213, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12213, agent12213, scalar12213, tp12213, tm12213, ep12213, em12213, dsL]

theorem negative12213 :
    Eminus aL (agent12213.root+dsL) scalar12213.worldRadius world12213.frame
      agent12213.frame tm12213 ≤ -em12213 := by
  apply negative_check (lo := (67755739069758188629 / 100000000000000000000)) (hi := (6775573906975818863 / 10000000000000000000))
    (y := (-((18319531819944536789 / 25000000000000000000)))) (u := (24028526594827089709 / 50000000000000000000))
  · norm_num [world12213, agent12213, scalar12213, tp12213, tm12213, ep12213, em12213, dsL]
  · norm_num [world12213, agent12213, scalar12213, tp12213, tm12213, ep12213, em12213, dsL]
  · norm_num [world12213, agent12213, scalar12213, tp12213, tm12213, ep12213, em12213, dsL]
  · norm_num [world12213, agent12213, scalar12213, tp12213, tm12213, ep12213, em12213, dsL]
  · norm_num [world12213, agent12213, scalar12213, tp12213, tm12213, ep12213, em12213, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12213, agent12213, tp12213, tm12213, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12213, agent12213, tp12213, tm12213, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12213, agent12213, scalar12213, tp12213, tm12213, ep12213, em12213, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12213, agent12213, tp12213, tm12213, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12213, agent12213, scalar12213, tp12213, tm12213, ep12213, em12213, dsL]

theorem tails12213 :
    exp (-((12213:ℝ)*ep12213)) ≤ scalar12213.upperTail ∧
    exp (-((12213:ℝ)*em12213)) ≤ scalar12213.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12213:ℝ)) (by norm_num [ep12213]) ?_)
      (show bp12213^8 ≤ scalar12213.upperTail by norm_num [bp12213, scalar12213])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12213, bp12213, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12213:ℝ)) (by norm_num [em12213]) ?_)
      (show bm12213^8 ≤ scalar12213.lowerTail by norm_num [bm12213, scalar12213])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12213, bm12213, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12213 :
    agent12213.root+dsL+scalar12213.worldRadius < √(1/100/aL) ∧
    2*(agent12213.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12213, agent12213, scalar12213, tp12213, tm12213, ep12213, em12213, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12213, agent12213, scalar12213, tp12213, tm12213, ep12213, em12213, dsL]

noncomputable def master12213 : MasterCertificate 12213 world12213 agent12213 :=
  master scalar12213 dsL tp12213 tm12213 ep12213 em12213
    (by norm_num [dsL]) (by norm_num [tp12213]) (by norm_num [tm12213])
    (by norm_num [ep12213]) (by norm_num [em12213])
    positive12213 negative12213 tails12213.1 tails12213.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12213.1 tailGuards12213.2

theorem preserves12213 : master12213.toScalarCertificate = scalar12213 := rfl

noncomputable def tp12214 : ℝ := (2379226873 / 10000000000)
noncomputable def tm12214 : ℝ := (-((384571591 / 625000000)))
noncomputable def ep12214 : ℝ := (13695247535193279 / 25000000000000000000)
noncomputable def em12214 : ℝ := (26400060883335129 / 50000000000000000000)
noncomputable def bp12214 : ℝ := (135400317069804639 / 312500000000000000)
noncomputable def bm12214 : ℝ := (22329242590487393453 / 50000000000000000000)

theorem positive12214 :
    Eplus aL (agent12214.root+dsL) scalar12214.worldRadius world12214.frame
      agent12214.frame tp12214 ≤ -ep12214 := by
  apply positive_check (eT := (116243461015544637139 / 100000000000000000000)) (y := (39666805225221975209 / 100000000000000000000)) (u := (148686228753647186281 / 100000000000000000000))
  · norm_num [world12214, agent12214, scalar12214, tp12214, tm12214, ep12214, em12214, dsL]
  · norm_num [world12214, agent12214, scalar12214, tp12214, tm12214, ep12214, em12214, dsL]
  · norm_num [world12214, agent12214, scalar12214, tp12214, tm12214, ep12214, em12214, dsL]
  · norm_num [world12214, agent12214, scalar12214, tp12214, tm12214, ep12214, em12214, dsL]
  · norm_num [world12214, agent12214, scalar12214, tp12214, tm12214, ep12214, em12214, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12214, agent12214, tp12214, tm12214, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12214, agent12214, scalar12214, tp12214, tm12214, ep12214, em12214, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12214, agent12214, tp12214, tm12214, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12214, agent12214, scalar12214, tp12214, tm12214, ep12214, em12214, dsL]

theorem negative12214 :
    Eminus aL (agent12214.root+dsL) scalar12214.worldRadius world12214.frame
      agent12214.frame tm12214 ≤ -em12214 := by
  apply negative_check (lo := (1355108915040039113 / 2000000000000000000)) (hi := (67755445752001955651 / 100000000000000000000))
    (y := (-((73277716283438272763 / 100000000000000000000)))) (u := (12014312675697431497 / 25000000000000000000))
  · norm_num [world12214, agent12214, scalar12214, tp12214, tm12214, ep12214, em12214, dsL]
  · norm_num [world12214, agent12214, scalar12214, tp12214, tm12214, ep12214, em12214, dsL]
  · norm_num [world12214, agent12214, scalar12214, tp12214, tm12214, ep12214, em12214, dsL]
  · norm_num [world12214, agent12214, scalar12214, tp12214, tm12214, ep12214, em12214, dsL]
  · norm_num [world12214, agent12214, scalar12214, tp12214, tm12214, ep12214, em12214, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12214, agent12214, tp12214, tm12214, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12214, agent12214, tp12214, tm12214, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12214, agent12214, scalar12214, tp12214, tm12214, ep12214, em12214, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12214, agent12214, tp12214, tm12214, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12214, agent12214, scalar12214, tp12214, tm12214, ep12214, em12214, dsL]

theorem tails12214 :
    exp (-((12214:ℝ)*ep12214)) ≤ scalar12214.upperTail ∧
    exp (-((12214:ℝ)*em12214)) ≤ scalar12214.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12214:ℝ)) (by norm_num [ep12214]) ?_)
      (show bp12214^8 ≤ scalar12214.upperTail by norm_num [bp12214, scalar12214])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12214, bp12214, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12214:ℝ)) (by norm_num [em12214]) ?_)
      (show bm12214^8 ≤ scalar12214.lowerTail by norm_num [bm12214, scalar12214])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12214, bm12214, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12214 :
    agent12214.root+dsL+scalar12214.worldRadius < √(1/100/aL) ∧
    2*(agent12214.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12214, agent12214, scalar12214, tp12214, tm12214, ep12214, em12214, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12214, agent12214, scalar12214, tp12214, tm12214, ep12214, em12214, dsL]

noncomputable def master12214 : MasterCertificate 12214 world12214 agent12214 :=
  master scalar12214 dsL tp12214 tm12214 ep12214 em12214
    (by norm_num [dsL]) (by norm_num [tp12214]) (by norm_num [tm12214])
    (by norm_num [ep12214]) (by norm_num [em12214])
    positive12214 negative12214 tails12214.1 tails12214.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12214.1 tailGuards12214.2

theorem preserves12214 : master12214.toScalarCertificate = scalar12214 := rfl

noncomputable def tp12215 : ℝ := (297415317 / 1250000000)
noncomputable def tm12215 : ℝ := (-((6153359593 / 10000000000)))
noncomputable def ep12215 : ℝ := (54783783896822819 / 100000000000000000000)
noncomputable def em12215 : ℝ := (52802544651195613 / 100000000000000000000)
noncomputable def bp12215 : ℝ := (43323286530645658827 / 100000000000000000000)
noncomputable def bm12215 : ℝ := (44653885836340934707 / 100000000000000000000)

theorem positive12215 :
    Eplus aL (agent12215.root+dsL) scalar12215.worldRadius world12215.frame
      agent12215.frame tp12215 ≤ -ep12215 := by
  apply positive_check (eT := (1162437498418212963 / 1000000000000000000)) (y := (4958426501667254363 / 12500000000000000000)) (u := (37171782741687684731 / 25000000000000000000))
  · norm_num [world12215, agent12215, scalar12215, tp12215, tm12215, ep12215, em12215, dsL]
  · norm_num [world12215, agent12215, scalar12215, tp12215, tm12215, ep12215, em12215, dsL]
  · norm_num [world12215, agent12215, scalar12215, tp12215, tm12215, ep12215, em12215, dsL]
  · norm_num [world12215, agent12215, scalar12215, tp12215, tm12215, ep12215, em12215, dsL]
  · norm_num [world12215, agent12215, scalar12215, tp12215, tm12215, ep12215, em12215, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12215, agent12215, tp12215, tm12215, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12215, agent12215, scalar12215, tp12215, tm12215, ep12215, em12215, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12215, agent12215, tp12215, tm12215, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12215, agent12215, scalar12215, tp12215, tm12215, ep12215, em12215, dsL]

theorem negative12215 :
    Eminus aL (agent12215.root+dsL) scalar12215.worldRadius world12215.frame
      agent12215.frame tm12215 ≤ -em12215 := by
  apply negative_check (lo := (67755152956842423109 / 100000000000000000000)) (hi := (6775515295684242311 / 10000000000000000000))
    (y := (-((3663865241777445937 / 5000000000000000000)))) (u := (2402872421687010191 / 5000000000000000000))
  · norm_num [world12215, agent12215, scalar12215, tp12215, tm12215, ep12215, em12215, dsL]
  · norm_num [world12215, agent12215, scalar12215, tp12215, tm12215, ep12215, em12215, dsL]
  · norm_num [world12215, agent12215, scalar12215, tp12215, tm12215, ep12215, em12215, dsL]
  · norm_num [world12215, agent12215, scalar12215, tp12215, tm12215, ep12215, em12215, dsL]
  · norm_num [world12215, agent12215, scalar12215, tp12215, tm12215, ep12215, em12215, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12215, agent12215, tp12215, tm12215, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12215, agent12215, tp12215, tm12215, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12215, agent12215, scalar12215, tp12215, tm12215, ep12215, em12215, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12215, agent12215, tp12215, tm12215, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12215, agent12215, scalar12215, tp12215, tm12215, ep12215, em12215, dsL]

theorem tails12215 :
    exp (-((12215:ℝ)*ep12215)) ≤ scalar12215.upperTail ∧
    exp (-((12215:ℝ)*em12215)) ≤ scalar12215.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12215:ℝ)) (by norm_num [ep12215]) ?_)
      (show bp12215^8 ≤ scalar12215.upperTail by norm_num [bp12215, scalar12215])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12215, bp12215, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12215:ℝ)) (by norm_num [em12215]) ?_)
      (show bm12215^8 ≤ scalar12215.lowerTail by norm_num [bm12215, scalar12215])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12215, bm12215, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12215 :
    agent12215.root+dsL+scalar12215.worldRadius < √(1/100/aL) ∧
    2*(agent12215.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12215, agent12215, scalar12215, tp12215, tm12215, ep12215, em12215, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12215, agent12215, scalar12215, tp12215, tm12215, ep12215, em12215, dsL]

noncomputable def master12215 : MasterCertificate 12215 world12215 agent12215 :=
  master scalar12215 dsL tp12215 tm12215 ep12215 em12215
    (by norm_num [dsL]) (by norm_num [tp12215]) (by norm_num [tm12215])
    (by norm_num [ep12215]) (by norm_num [em12215])
    positive12215 negative12215 tails12215.1 tails12215.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12215.1 tailGuards12215.2

theorem preserves12215 : master12215.toScalarCertificate = scalar12215 := rfl

noncomputable def tp12216 : ℝ := (2379418187 / 10000000000)
noncomputable def tm12216 : ℝ := (-((3076786831 / 5000000000)))
noncomputable def ep12216 : ℝ := (54786576208000093 / 100000000000000000000)
noncomputable def em12216 : ℝ := (52804966207102737 / 100000000000000000000)
noncomputable def bp12216 : ℝ := (1353702274600466517 / 3125000000000000000)
noncomputable def bm12216 : ℝ := (44649287600784802571 / 100000000000000000000)

theorem positive12216 :
    Eplus aL (agent12216.root+dsL) scalar12216.worldRadius world12216.frame
      agent12216.frame tp12216 ≤ -ep12216 := by
  apply positive_check (eT := (116244038617012591091 / 100000000000000000000)) (y := (39668019181151361091 / 100000000000000000000)) (u := (37172008437473307187 / 25000000000000000000))
  · norm_num [world12216, agent12216, scalar12216, tp12216, tm12216, ep12216, em12216, dsL]
  · norm_num [world12216, agent12216, scalar12216, tp12216, tm12216, ep12216, em12216, dsL]
  · norm_num [world12216, agent12216, scalar12216, tp12216, tm12216, ep12216, em12216, dsL]
  · norm_num [world12216, agent12216, scalar12216, tp12216, tm12216, ep12216, em12216, dsL]
  · norm_num [world12216, agent12216, scalar12216, tp12216, tm12216, ep12216, em12216, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12216, agent12216, tp12216, tm12216, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12216, agent12216, scalar12216, tp12216, tm12216, ep12216, em12216, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12216, agent12216, tp12216, tm12216, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12216, agent12216, scalar12216, tp12216, tm12216, ep12216, em12216, dsL]

theorem negative12216 :
    Eminus aL (agent12216.root+dsL) scalar12216.worldRadius world12216.frame
      agent12216.frame tm12216 ≤ -em12216 := by
  apply negative_check (lo := (13550972078543958277 / 20000000000000000000)) (hi := (33877430196359895693 / 50000000000000000000))
    (y := (-((18319223504600070961 / 25000000000000000000)))) (u := (12014411465596275271 / 25000000000000000000))
  · norm_num [world12216, agent12216, scalar12216, tp12216, tm12216, ep12216, em12216, dsL]
  · norm_num [world12216, agent12216, scalar12216, tp12216, tm12216, ep12216, em12216, dsL]
  · norm_num [world12216, agent12216, scalar12216, tp12216, tm12216, ep12216, em12216, dsL]
  · norm_num [world12216, agent12216, scalar12216, tp12216, tm12216, ep12216, em12216, dsL]
  · norm_num [world12216, agent12216, scalar12216, tp12216, tm12216, ep12216, em12216, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12216, agent12216, tp12216, tm12216, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12216, agent12216, tp12216, tm12216, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12216, agent12216, scalar12216, tp12216, tm12216, ep12216, em12216, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12216, agent12216, tp12216, tm12216, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12216, agent12216, scalar12216, tp12216, tm12216, ep12216, em12216, dsL]

theorem tails12216 :
    exp (-((12216:ℝ)*ep12216)) ≤ scalar12216.upperTail ∧
    exp (-((12216:ℝ)*em12216)) ≤ scalar12216.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12216:ℝ)) (by norm_num [ep12216]) ?_)
      (show bp12216^8 ≤ scalar12216.upperTail by norm_num [bp12216, scalar12216])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12216, bp12216, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12216:ℝ)) (by norm_num [em12216]) ?_)
      (show bm12216^8 ≤ scalar12216.lowerTail by norm_num [bm12216, scalar12216])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12216, bm12216, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12216 :
    agent12216.root+dsL+scalar12216.worldRadius < √(1/100/aL) ∧
    2*(agent12216.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12216, agent12216, scalar12216, tp12216, tm12216, ep12216, em12216, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12216, agent12216, scalar12216, tp12216, tm12216, ep12216, em12216, dsL]

noncomputable def master12216 : MasterCertificate 12216 world12216 agent12216 :=
  master scalar12216 dsL tp12216 tm12216 ep12216 em12216
    (by norm_num [dsL]) (by norm_num [tp12216]) (by norm_num [tm12216])
    (by norm_num [ep12216]) (by norm_num [em12216])
    positive12216 negative12216 tails12216.1 tails12216.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12216.1 tailGuards12216.2

theorem preserves12216 : master12216.toScalarCertificate = scalar12216 := rfl

noncomputable def tp12217 : ℝ := (237951377 / 1000000000)
noncomputable def tm12217 : ℝ := (-((3076893793 / 5000000000)))
noncomputable def ep12217 : ℝ := (27394683168560183 / 50000000000000000000)
noncomputable def em12217 : ℝ := (52807385701467419 / 100000000000000000000)
noncomputable def bp12217 : ℝ := (4331366071961627597 / 10000000000000000000)
noncomputable def bm12217 : ℝ := (8928938194795398089 / 20000000000000000000)

theorem positive12217 :
    Eplus aL (agent12217.root+dsL) scalar12217.worldRadius world12217.frame
      agent12217.frame tp12217 ≤ -ep12217 := by
  apply positive_check (eT := (116244326929285901887 / 100000000000000000000)) (y := (3966862588088775769 / 10000000000000000000)) (u := (1858611698031731709 / 1250000000000000000))
  · norm_num [world12217, agent12217, scalar12217, tp12217, tm12217, ep12217, em12217, dsL]
  · norm_num [world12217, agent12217, scalar12217, tp12217, tm12217, ep12217, em12217, dsL]
  · norm_num [world12217, agent12217, scalar12217, tp12217, tm12217, ep12217, em12217, dsL]
  · norm_num [world12217, agent12217, scalar12217, tp12217, tm12217, ep12217, em12217, dsL]
  · norm_num [world12217, agent12217, scalar12217, tp12217, tm12217, ep12217, em12217, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12217, agent12217, tp12217, tm12217, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12217, agent12217, scalar12217, tp12217, tm12217, ep12217, em12217, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12217, agent12217, tp12217, tm12217, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12217, agent12217, scalar12217, tp12217, tm12217, ep12217, em12217, dsL]

theorem negative12217 :
    Eminus aL (agent12217.root+dsL) scalar12217.worldRadius world12217.frame
      agent12217.frame tm12217 ≤ -em12217 := by
  apply negative_check (lo := (67754568389707891567 / 100000000000000000000)) (hi := (4234660524356743223 / 6250000000000000000))
    (y := (-((3663824135110635629 / 5000000000000000000)))) (u := (48057843531668421347 / 100000000000000000000))
  · norm_num [world12217, agent12217, scalar12217, tp12217, tm12217, ep12217, em12217, dsL]
  · norm_num [world12217, agent12217, scalar12217, tp12217, tm12217, ep12217, em12217, dsL]
  · norm_num [world12217, agent12217, scalar12217, tp12217, tm12217, ep12217, em12217, dsL]
  · norm_num [world12217, agent12217, scalar12217, tp12217, tm12217, ep12217, em12217, dsL]
  · norm_num [world12217, agent12217, scalar12217, tp12217, tm12217, ep12217, em12217, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12217, agent12217, tp12217, tm12217, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12217, agent12217, tp12217, tm12217, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12217, agent12217, scalar12217, tp12217, tm12217, ep12217, em12217, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12217, agent12217, tp12217, tm12217, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12217, agent12217, scalar12217, tp12217, tm12217, ep12217, em12217, dsL]

theorem tails12217 :
    exp (-((12217:ℝ)*ep12217)) ≤ scalar12217.upperTail ∧
    exp (-((12217:ℝ)*em12217)) ≤ scalar12217.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12217:ℝ)) (by norm_num [ep12217]) ?_)
      (show bp12217^8 ≤ scalar12217.upperTail by norm_num [bp12217, scalar12217])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12217, bp12217, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12217:ℝ)) (by norm_num [em12217]) ?_)
      (show bm12217^8 ≤ scalar12217.lowerTail by norm_num [bm12217, scalar12217])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12217, bm12217, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12217 :
    agent12217.root+dsL+scalar12217.worldRadius < √(1/100/aL) ∧
    2*(agent12217.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12217, agent12217, scalar12217, tp12217, tm12217, ep12217, em12217, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12217, agent12217, scalar12217, tp12217, tm12217, ep12217, em12217, dsL]

noncomputable def master12217 : MasterCertificate 12217 world12217 agent12217 :=
  master scalar12217 dsL tp12217 tm12217 ep12217 em12217
    (by norm_num [dsL]) (by norm_num [tp12217]) (by norm_num [tm12217])
    (by norm_num [ep12217]) (by norm_num [em12217])
    positive12217 negative12217 tails12217.1 tails12217.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12217.1 tailGuards12217.2

theorem preserves12217 : master12217.toScalarCertificate = scalar12217 := rfl

noncomputable def tp12218 : ℝ := (2379609363 / 10000000000)
noncomputable def tm12218 : ℝ := (-((3077000717 / 5000000000)))
noncomputable def ep12218 : ℝ := (54792156018456907 / 100000000000000000000)
noncomputable def em12218 : ℝ := (10561960955031687 / 20000000000000000000)
noncomputable def bp12218 : ℝ := (21654424590328203297 / 50000000000000000000)
noncomputable def bm12218 : ℝ := (4464009483717491599 / 10000000000000000000)

theorem positive12218 :
    Eplus aL (agent12218.root+dsL) scalar12218.worldRadius world12218.frame
      agent12218.frame tp12218 ≤ -ep12218 := by
  apply positive_check (eT := (23248923070452819361 / 20000000000000000000)) (y := (39669233144074266169 / 100000000000000000000)) (u := (74344919389224957793 / 50000000000000000000))
  · norm_num [world12218, agent12218, scalar12218, tp12218, tm12218, ep12218, em12218, dsL]
  · norm_num [world12218, agent12218, scalar12218, tp12218, tm12218, ep12218, em12218, dsL]
  · norm_num [world12218, agent12218, scalar12218, tp12218, tm12218, ep12218, em12218, dsL]
  · norm_num [world12218, agent12218, scalar12218, tp12218, tm12218, ep12218, em12218, dsL]
  · norm_num [world12218, agent12218, scalar12218, tp12218, tm12218, ep12218, em12218, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12218, agent12218, tp12218, tm12218, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12218, agent12218, scalar12218, tp12218, tm12218, ep12218, em12218, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12218, agent12218, tp12218, tm12218, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12218, agent12218, scalar12218, tp12218, tm12218, ep12218, em12218, dsL]

theorem negative12218 :
    Eminus aL (agent12218.root+dsL) scalar12218.worldRadius world12218.frame
      agent12218.frame tm12218 ≤ -em12218 := by
  apply negative_check (lo := (33877138325987064711 / 50000000000000000000)) (hi := (67754276651974129423 / 100000000000000000000))
    (y := (-((73276071774898737627 / 100000000000000000000)))) (u := (48058041014879756267 / 100000000000000000000))
  · norm_num [world12218, agent12218, scalar12218, tp12218, tm12218, ep12218, em12218, dsL]
  · norm_num [world12218, agent12218, scalar12218, tp12218, tm12218, ep12218, em12218, dsL]
  · norm_num [world12218, agent12218, scalar12218, tp12218, tm12218, ep12218, em12218, dsL]
  · norm_num [world12218, agent12218, scalar12218, tp12218, tm12218, ep12218, em12218, dsL]
  · norm_num [world12218, agent12218, scalar12218, tp12218, tm12218, ep12218, em12218, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12218, agent12218, tp12218, tm12218, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12218, agent12218, tp12218, tm12218, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12218, agent12218, scalar12218, tp12218, tm12218, ep12218, em12218, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12218, agent12218, tp12218, tm12218, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12218, agent12218, scalar12218, tp12218, tm12218, ep12218, em12218, dsL]

theorem tails12218 :
    exp (-((12218:ℝ)*ep12218)) ≤ scalar12218.upperTail ∧
    exp (-((12218:ℝ)*em12218)) ≤ scalar12218.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12218:ℝ)) (by norm_num [ep12218]) ?_)
      (show bp12218^8 ≤ scalar12218.upperTail by norm_num [bp12218, scalar12218])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12218, bp12218, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12218:ℝ)) (by norm_num [em12218]) ?_)
      (show bm12218^8 ≤ scalar12218.lowerTail by norm_num [bm12218, scalar12218])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12218, bm12218, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12218 :
    agent12218.root+dsL+scalar12218.worldRadius < √(1/100/aL) ∧
    2*(agent12218.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12218, agent12218, scalar12218, tp12218, tm12218, ep12218, em12218, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12218, agent12218, scalar12218, tp12218, tm12218, ep12218, em12218, dsL]

noncomputable def master12218 : MasterCertificate 12218 world12218 agent12218 :=
  master scalar12218 dsL tp12218 tm12218 ep12218 em12218
    (by norm_num [dsL]) (by norm_num [tp12218]) (by norm_num [tm12218])
    (by norm_num [ep12218]) (by norm_num [em12218])
    positive12218 negative12218 tails12218.1 tails12218.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12218.1 tailGuards12218.2

theorem preserves12218 : master12218.toScalarCertificate = scalar12218 := rfl

noncomputable def tp12219 : ℝ := (59492621 / 250000000)
noncomputable def tm12219 : ℝ := (-((6154215177 / 10000000000)))
noncomputable def ep12219 : ℝ := (27397471819709029 / 50000000000000000000)
noncomputable def em12219 : ℝ := (52812221927072487 / 100000000000000000000)
noncomputable def bp12219 : ℝ := (8660807847388607149 / 20000000000000000000)
noncomputable def bm12219 : ℝ := (44635500213774461409 / 100000000000000000000)

theorem positive12219 :
    Eplus aL (agent12219.root+dsL) scalar12219.worldRadius world12219.frame
      agent12219.frame tp12219 ≤ -ep12219 := by
  apply positive_check (eT := (3632653217480511937 / 3125000000000000000)) (y := (39669839023451852573 / 100000000000000000000)) (u := (148690739662248772507 / 100000000000000000000))
  · norm_num [world12219, agent12219, scalar12219, tp12219, tm12219, ep12219, em12219, dsL]
  · norm_num [world12219, agent12219, scalar12219, tp12219, tm12219, ep12219, em12219, dsL]
  · norm_num [world12219, agent12219, scalar12219, tp12219, tm12219, ep12219, em12219, dsL]
  · norm_num [world12219, agent12219, scalar12219, tp12219, tm12219, ep12219, em12219, dsL]
  · norm_num [world12219, agent12219, scalar12219, tp12219, tm12219, ep12219, em12219, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12219, agent12219, tp12219, tm12219, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12219, agent12219, scalar12219, tp12219, tm12219, ep12219, em12219, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12219, agent12219, tp12219, tm12219, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12219, agent12219, scalar12219, tp12219, tm12219, ep12219, em12219, dsL]

theorem negative12219 :
    Eminus aL (agent12219.root+dsL) scalar12219.worldRadius world12219.frame
      agent12219.frame tm12219 ≤ -em12219 := by
  apply negative_check (lo := (2117312040746696477 / 3125000000000000000)) (hi := (13550797060778857453 / 20000000000000000000))
    (y := (-((14655132172382591769 / 20000000000000000000)))) (u := (1501819952875522707 / 3125000000000000000))
  · norm_num [world12219, agent12219, scalar12219, tp12219, tm12219, ep12219, em12219, dsL]
  · norm_num [world12219, agent12219, scalar12219, tp12219, tm12219, ep12219, em12219, dsL]
  · norm_num [world12219, agent12219, scalar12219, tp12219, tm12219, ep12219, em12219, dsL]
  · norm_num [world12219, agent12219, scalar12219, tp12219, tm12219, ep12219, em12219, dsL]
  · norm_num [world12219, agent12219, scalar12219, tp12219, tm12219, ep12219, em12219, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12219, agent12219, tp12219, tm12219, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12219, agent12219, tp12219, tm12219, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12219, agent12219, scalar12219, tp12219, tm12219, ep12219, em12219, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12219, agent12219, tp12219, tm12219, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12219, agent12219, scalar12219, tp12219, tm12219, ep12219, em12219, dsL]

theorem tails12219 :
    exp (-((12219:ℝ)*ep12219)) ≤ scalar12219.upperTail ∧
    exp (-((12219:ℝ)*em12219)) ≤ scalar12219.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12219:ℝ)) (by norm_num [ep12219]) ?_)
      (show bp12219^8 ≤ scalar12219.upperTail by norm_num [bp12219, scalar12219])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12219, bp12219, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12219:ℝ)) (by norm_num [em12219]) ?_)
      (show bm12219^8 ≤ scalar12219.lowerTail by norm_num [bm12219, scalar12219])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12219, bm12219, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12219 :
    agent12219.root+dsL+scalar12219.worldRadius < √(1/100/aL) ∧
    2*(agent12219.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12219, agent12219, scalar12219, tp12219, tm12219, ep12219, em12219, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12219, agent12219, scalar12219, tp12219, tm12219, ep12219, em12219, dsL]

noncomputable def master12219 : MasterCertificate 12219 world12219 agent12219 :=
  master scalar12219 dsL tp12219 tm12219 ep12219 em12219
    (by norm_num [dsL]) (by norm_num [tp12219]) (by norm_num [tm12219])
    (by norm_num [ep12219]) (by norm_num [em12219])
    positive12219 negative12219 tails12219.1 tails12219.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12219.1 tailGuards12219.2

theorem preserves12219 : master12219.toScalarCertificate = scalar12219 := rfl

noncomputable def tp12220 : ℝ := (2379800277 / 10000000000)
noncomputable def tm12220 : ℝ := (-((3077214317 / 5000000000)))
noncomputable def ep12220 : ℝ := (5479772969020971 / 10000000000000000000)
noncomputable def em12220 : ℝ := (10562927521596253 / 20000000000000000000)
noncomputable def bp12220 : ℝ := (43299230564177817489 / 100000000000000000000)
noncomputable def bm12220 : ℝ := (44630906796419567111 / 100000000000000000000)

theorem positive12220 :
    Eplus aL (agent12220.root+dsL) scalar12220.worldRadius world12220.frame
      agent12220.frame tp12220 ≤ -ep12220 := by
  apply positive_check (eT := (116245190309537830937 / 100000000000000000000)) (y := (39670444831564610249 / 100000000000000000000)) (u := (74345820222770536091 / 50000000000000000000))
  · norm_num [world12220, agent12220, scalar12220, tp12220, tm12220, ep12220, em12220, dsL]
  · norm_num [world12220, agent12220, scalar12220, tp12220, tm12220, ep12220, em12220, dsL]
  · norm_num [world12220, agent12220, scalar12220, tp12220, tm12220, ep12220, em12220, dsL]
  · norm_num [world12220, agent12220, scalar12220, tp12220, tm12220, ep12220, em12220, dsL]
  · norm_num [world12220, agent12220, scalar12220, tp12220, tm12220, ep12220, em12220, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12220, agent12220, tp12220, tm12220, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12220, agent12220, scalar12220, tp12220, tm12220, ep12220, em12220, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12220, agent12220, tp12220, tm12220, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12220, agent12220, scalar12220, tp12220, tm12220, ep12220, em12220, dsL]

theorem negative12220 :
    Eminus aL (agent12220.root+dsL) scalar12220.worldRadius world12220.frame
      agent12220.frame tm12220 ≤ -em12220 := by
  apply negative_check (lo := (2117302972533967003 / 3125000000000000000)) (hi := (67753695121086944097 / 100000000000000000000))
    (y := (-((73275248328932000903 / 100000000000000000000)))) (u := (24029218374254755023 / 50000000000000000000))
  · norm_num [world12220, agent12220, scalar12220, tp12220, tm12220, ep12220, em12220, dsL]
  · norm_num [world12220, agent12220, scalar12220, tp12220, tm12220, ep12220, em12220, dsL]
  · norm_num [world12220, agent12220, scalar12220, tp12220, tm12220, ep12220, em12220, dsL]
  · norm_num [world12220, agent12220, scalar12220, tp12220, tm12220, ep12220, em12220, dsL]
  · norm_num [world12220, agent12220, scalar12220, tp12220, tm12220, ep12220, em12220, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12220, agent12220, tp12220, tm12220, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12220, agent12220, tp12220, tm12220, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12220, agent12220, scalar12220, tp12220, tm12220, ep12220, em12220, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12220, agent12220, tp12220, tm12220, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12220, agent12220, scalar12220, tp12220, tm12220, ep12220, em12220, dsL]

theorem tails12220 :
    exp (-((12220:ℝ)*ep12220)) ≤ scalar12220.upperTail ∧
    exp (-((12220:ℝ)*em12220)) ≤ scalar12220.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12220:ℝ)) (by norm_num [ep12220]) ?_)
      (show bp12220^8 ≤ scalar12220.upperTail by norm_num [bp12220, scalar12220])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12220, bp12220, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12220:ℝ)) (by norm_num [em12220]) ?_)
      (show bm12220^8 ≤ scalar12220.lowerTail by norm_num [bm12220, scalar12220])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12220, bm12220, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12220 :
    agent12220.root+dsL+scalar12220.worldRadius < √(1/100/aL) ∧
    2*(agent12220.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12220, agent12220, scalar12220, tp12220, tm12220, ep12220, em12220, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12220, agent12220, scalar12220, tp12220, tm12220, ep12220, em12220, dsL]

noncomputable def master12220 : MasterCertificate 12220 world12220 agent12220 :=
  master scalar12220 dsL tp12220 tm12220 ep12220 em12220
    (by norm_num [dsL]) (by norm_num [tp12220]) (by norm_num [tm12220])
    (by norm_num [ep12220]) (by norm_num [em12220])
    positive12220 negative12220 tails12220.1 tails12220.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12220.1 tailGuards12220.2

theorem preserves12220 : master12220.toScalarCertificate = scalar12220 := rfl

noncomputable def tp12221 : ℝ := (1189947851 / 5000000000)
noncomputable def tm12221 : ℝ := (-((6154642191 / 10000000000)))
noncomputable def ep12221 : ℝ := (27400256984404969 / 50000000000000000000)
noncomputable def em12221 : ℝ := (6602131459583877 / 12500000000000000000)
noncomputable def bp12221 : ℝ := (8658884659184690169 / 20000000000000000000)
noncomputable def bm12221 : ℝ := (44626314681350014947 / 100000000000000000000)

theorem positive12221 :
    Eplus aL (agent12221.root+dsL) scalar12221.worldRadius world12221.frame
      agent12221.frame tp12221 ≤ -ep12221 := by
  apply positive_check (eT := (7265342350537426379 / 6250000000000000000)) (y := (39671050909618928707 / 100000000000000000000)) (u := (74346270817836686883 / 50000000000000000000))
  · norm_num [world12221, agent12221, scalar12221, tp12221, tm12221, ep12221, em12221, dsL]
  · norm_num [world12221, agent12221, scalar12221, tp12221, tm12221, ep12221, em12221, dsL]
  · norm_num [world12221, agent12221, scalar12221, tp12221, tm12221, ep12221, em12221, dsL]
  · norm_num [world12221, agent12221, scalar12221, tp12221, tm12221, ep12221, em12221, dsL]
  · norm_num [world12221, agent12221, scalar12221, tp12221, tm12221, ep12221, em12221, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12221, agent12221, tp12221, tm12221, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12221, agent12221, scalar12221, tp12221, tm12221, ep12221, em12221, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12221, agent12221, tp12221, tm12221, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12221, agent12221, scalar12221, tp12221, tm12221, ep12221, em12221, dsL]

theorem negative12221 :
    Eminus aL (agent12221.root+dsL) scalar12221.worldRadius world12221.frame
      agent12221.frame tm12221 ≤ -em12221 := by
  apply negative_check (lo := (67753404449295994029 / 100000000000000000000)) (hi := (6775340444929599403 / 10000000000000000000))
    (y := (-((18318709408802207387 / 25000000000000000000)))) (u := (6007329265237248779 / 12500000000000000000))
  · norm_num [world12221, agent12221, scalar12221, tp12221, tm12221, ep12221, em12221, dsL]
  · norm_num [world12221, agent12221, scalar12221, tp12221, tm12221, ep12221, em12221, dsL]
  · norm_num [world12221, agent12221, scalar12221, tp12221, tm12221, ep12221, em12221, dsL]
  · norm_num [world12221, agent12221, scalar12221, tp12221, tm12221, ep12221, em12221, dsL]
  · norm_num [world12221, agent12221, scalar12221, tp12221, tm12221, ep12221, em12221, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12221, agent12221, tp12221, tm12221, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12221, agent12221, tp12221, tm12221, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12221, agent12221, scalar12221, tp12221, tm12221, ep12221, em12221, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12221, agent12221, tp12221, tm12221, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12221, agent12221, scalar12221, tp12221, tm12221, ep12221, em12221, dsL]

theorem tails12221 :
    exp (-((12221:ℝ)*ep12221)) ≤ scalar12221.upperTail ∧
    exp (-((12221:ℝ)*em12221)) ≤ scalar12221.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12221:ℝ)) (by norm_num [ep12221]) ?_)
      (show bp12221^8 ≤ scalar12221.upperTail by norm_num [bp12221, scalar12221])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12221, bp12221, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12221:ℝ)) (by norm_num [em12221]) ?_)
      (show bm12221^8 ≤ scalar12221.lowerTail by norm_num [bm12221, scalar12221])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12221, bm12221, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12221 :
    agent12221.root+dsL+scalar12221.worldRadius < √(1/100/aL) ∧
    2*(agent12221.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12221, agent12221, scalar12221, tp12221, tm12221, ep12221, em12221, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12221, agent12221, scalar12221, tp12221, tm12221, ep12221, em12221, dsL]

noncomputable def master12221 : MasterCertificate 12221 world12221 agent12221 :=
  master scalar12221 dsL tp12221 tm12221 ep12221 em12221
    (by norm_num [dsL]) (by norm_num [tp12221]) (by norm_num [tm12221])
    (by norm_num [ep12221]) (by norm_num [em12221])
    positive12221 negative12221 tails12221.1 tails12221.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12221.1 tailGuards12221.2

theorem preserves12221 : master12221.toScalarCertificate = scalar12221 := rfl

noncomputable def tp12222 : ℝ := (237999101 / 1000000000)
noncomputable def tm12222 : ℝ := (-((6154855441 / 10000000000)))
noncomputable def ep12222 : ℝ := (27401648439946277 / 50000000000000000000)
noncomputable def em12222 : ℝ := (52819464416327133 / 100000000000000000000)
noncomputable def bp12222 : ℝ := (21644808582242234781 / 50000000000000000000)
noncomputable def bm12222 : ℝ := (44621723675481008569 / 100000000000000000000)

theorem positive12222 :
    Eplus aL (agent12222.root+dsL) scalar12222.worldRadius world12222.frame
      agent12222.frame tp12222 ≤ -ep12222 := by
  apply positive_check (eT := (58122882042286952817 / 50000000000000000000)) (y := (39671655694349610219 / 100000000000000000000)) (u := (9293340056761261077 / 6250000000000000000))
  · norm_num [world12222, agent12222, scalar12222, tp12222, tm12222, ep12222, em12222, dsL]
  · norm_num [world12222, agent12222, scalar12222, tp12222, tm12222, ep12222, em12222, dsL]
  · norm_num [world12222, agent12222, scalar12222, tp12222, tm12222, ep12222, em12222, dsL]
  · norm_num [world12222, agent12222, scalar12222, tp12222, tm12222, ep12222, em12222, dsL]
  · norm_num [world12222, agent12222, scalar12222, tp12222, tm12222, ep12222, em12222, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12222, agent12222, tp12222, tm12222, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12222, agent12222, scalar12222, tp12222, tm12222, ep12222, em12222, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12222, agent12222, tp12222, tm12222, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12222, agent12222, scalar12222, tp12222, tm12222, ep12222, em12222, dsL]

theorem negative12222 :
    Eminus aL (agent12222.root+dsL) scalar12222.worldRadius world12222.frame
      agent12222.frame tm12222 ≤ -em12222 := by
  apply negative_check (lo := (3387655751634003597 / 5000000000000000000)) (hi := (67753115032680071941 / 100000000000000000000))
    (y := (-((73274425415051280069 / 100000000000000000000)))) (u := (1201470805742090087 / 2500000000000000000))
  · norm_num [world12222, agent12222, scalar12222, tp12222, tm12222, ep12222, em12222, dsL]
  · norm_num [world12222, agent12222, scalar12222, tp12222, tm12222, ep12222, em12222, dsL]
  · norm_num [world12222, agent12222, scalar12222, tp12222, tm12222, ep12222, em12222, dsL]
  · norm_num [world12222, agent12222, scalar12222, tp12222, tm12222, ep12222, em12222, dsL]
  · norm_num [world12222, agent12222, scalar12222, tp12222, tm12222, ep12222, em12222, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12222, agent12222, tp12222, tm12222, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12222, agent12222, tp12222, tm12222, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12222, agent12222, scalar12222, tp12222, tm12222, ep12222, em12222, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12222, agent12222, tp12222, tm12222, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12222, agent12222, scalar12222, tp12222, tm12222, ep12222, em12222, dsL]

theorem tails12222 :
    exp (-((12222:ℝ)*ep12222)) ≤ scalar12222.upperTail ∧
    exp (-((12222:ℝ)*em12222)) ≤ scalar12222.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12222:ℝ)) (by norm_num [ep12222]) ?_)
      (show bp12222^8 ≤ scalar12222.upperTail by norm_num [bp12222, scalar12222])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12222, bp12222, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12222:ℝ)) (by norm_num [em12222]) ?_)
      (show bm12222^8 ≤ scalar12222.lowerTail by norm_num [bm12222, scalar12222])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12222, bm12222, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12222 :
    agent12222.root+dsL+scalar12222.worldRadius < √(1/100/aL) ∧
    2*(agent12222.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12222, agent12222, scalar12222, tp12222, tm12222, ep12222, em12222, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12222, agent12222, scalar12222, tp12222, tm12222, ep12222, em12222, dsL]

noncomputable def master12222 : MasterCertificate 12222 world12222 agent12222 :=
  master scalar12222 dsL tp12222 tm12222 ep12222 em12222
    (by norm_num [dsL]) (by norm_num [tp12222]) (by norm_num [tm12222])
    (by norm_num [ep12222]) (by norm_num [em12222])
    positive12222 negative12222 tails12222.1 tails12222.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12222.1 tailGuards12222.2

theorem preserves12222 : master12222.toScalarCertificate = scalar12222 := rfl

noncomputable def tp12223 : ℝ := (1190043161 / 5000000000)
noncomputable def tm12223 : ℝ := (-((6155068679 / 10000000000)))
noncomputable def ep12223 : ℝ := (27403039431926191 / 50000000000000000000)
noncomputable def em12223 : ℝ := (1056437525883379 / 2000000000000000000)
noncomputable def bp12223 : ℝ := (43284811878572988167 / 100000000000000000000)
noncomputable def bm12223 : ℝ := (8923426692057831983 / 20000000000000000000)

theorem positive12223 :
    Eplus aL (agent12223.root+dsL) scalar12223.worldRadius world12223.frame
      agent12223.frame tp12223 ≤ -ep12223 := by
  apply positive_check (eT := (14530756328390238423 / 12500000000000000000)) (y := (4959032623123344631 / 12500000000000000000)) (u := (9293396308648746401 / 6250000000000000000))
  · norm_num [world12223, agent12223, scalar12223, tp12223, tm12223, ep12223, em12223, dsL]
  · norm_num [world12223, agent12223, scalar12223, tp12223, tm12223, ep12223, em12223, dsL]
  · norm_num [world12223, agent12223, scalar12223, tp12223, tm12223, ep12223, em12223, dsL]
  · norm_num [world12223, agent12223, scalar12223, tp12223, tm12223, ep12223, em12223, dsL]
  · norm_num [world12223, agent12223, scalar12223, tp12223, tm12223, ep12223, em12223, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12223, agent12223, tp12223, tm12223, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12223, agent12223, scalar12223, tp12223, tm12223, ep12223, em12223, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12223, agent12223, tp12223, tm12223, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12223, agent12223, scalar12223, tp12223, tm12223, ep12223, em12223, dsL]

theorem negative12223 :
    Eminus aL (agent12223.root+dsL) scalar12223.worldRadius world12223.frame
      agent12223.frame tm12223 ≤ -em12223 := by
  apply negative_check (lo := (6775282560703232497 / 10000000000000000000)) (hi := (67752825607032324971 / 100000000000000000000))
    (y := (-((18318503518732822969 / 25000000000000000000)))) (u := (48059029915348341931 / 100000000000000000000))
  · norm_num [world12223, agent12223, scalar12223, tp12223, tm12223, ep12223, em12223, dsL]
  · norm_num [world12223, agent12223, scalar12223, tp12223, tm12223, ep12223, em12223, dsL]
  · norm_num [world12223, agent12223, scalar12223, tp12223, tm12223, ep12223, em12223, dsL]
  · norm_num [world12223, agent12223, scalar12223, tp12223, tm12223, ep12223, em12223, dsL]
  · norm_num [world12223, agent12223, scalar12223, tp12223, tm12223, ep12223, em12223, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12223, agent12223, tp12223, tm12223, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12223, agent12223, tp12223, tm12223, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12223, agent12223, scalar12223, tp12223, tm12223, ep12223, em12223, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12223, agent12223, tp12223, tm12223, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12223, agent12223, scalar12223, tp12223, tm12223, ep12223, em12223, dsL]

theorem tails12223 :
    exp (-((12223:ℝ)*ep12223)) ≤ scalar12223.upperTail ∧
    exp (-((12223:ℝ)*em12223)) ≤ scalar12223.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12223:ℝ)) (by norm_num [ep12223]) ?_)
      (show bp12223^8 ≤ scalar12223.upperTail by norm_num [bp12223, scalar12223])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12223, bp12223, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12223:ℝ)) (by norm_num [em12223]) ?_)
      (show bm12223^8 ≤ scalar12223.lowerTail by norm_num [bm12223, scalar12223])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12223, bm12223, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12223 :
    agent12223.root+dsL+scalar12223.worldRadius < √(1/100/aL) ∧
    2*(agent12223.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12223, agent12223, scalar12223, tp12223, tm12223, ep12223, em12223, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12223, agent12223, scalar12223, tp12223, tm12223, ep12223, em12223, dsL]

noncomputable def master12223 : MasterCertificate 12223 world12223 agent12223 :=
  master scalar12223 dsL tp12223 tm12223 ep12223 em12223
    (by norm_num [dsL]) (by norm_num [tp12223]) (by norm_num [tm12223])
    (by norm_num [ep12223]) (by norm_num [em12223])
    positive12223 negative12223 tails12223.1 tails12223.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12223.1 tailGuards12223.2

theorem preserves12223 : master12223.toScalarCertificate = scalar12223 := rfl

end BstLean.Part281
