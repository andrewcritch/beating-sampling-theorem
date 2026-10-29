import BstLean.Part261Checker
import BstLean.Part268Scalar30
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp13100 : ℝ := (2350899179 / 10000000000)
noncomputable def tm13100 : ℝ := (-((3069437417 / 5000000000)))
noncomputable def ep13100 : ℝ := (5243668726955711 / 10000000000000000000)
noncomputable def em13100 : ℝ := (10197173554650743 / 20000000000000000000)
noncomputable def bp13100 : ℝ := (21186670869863248631 / 50000000000000000000)
noncomputable def bm13100 : ℝ := (169500255755883727 / 390625000000000000)

theorem positive13100 :
    Eplus aL (agent13100.root+dsL) scalar13100.worldRadius world13100.frame
      agent13100.frame tp13100 ≤ -ep13100 := by
  apply positive_check (eT := (28924615670909355167 / 25000000000000000000)) (y := (3812120868071191989 / 10000000000000000000)) (u := (146405807988839488779 / 100000000000000000000))
  · norm_num [world13100, agent13100, scalar13100, tp13100, tm13100, ep13100, em13100, dsL]
  · norm_num [world13100, agent13100, scalar13100, tp13100, tm13100, ep13100, em13100, dsL]
  · norm_num [world13100, agent13100, scalar13100, tp13100, tm13100, ep13100, em13100, dsL]
  · norm_num [world13100, agent13100, scalar13100, tp13100, tm13100, ep13100, em13100, dsL]
  · norm_num [world13100, agent13100, scalar13100, tp13100, tm13100, ep13100, em13100, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13100, agent13100, tp13100, tm13100, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13100, agent13100, scalar13100, tp13100, tm13100, ep13100, em13100, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13100, agent13100, tp13100, tm13100, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13100, agent13100, scalar13100, tp13100, tm13100, ep13100, em13100, dsL]

theorem negative13100 :
    Eminus aL (agent13100.root+dsL) scalar13100.worldRadius world13100.frame
      agent13100.frame tm13100 ≤ -em13100 := by
  apply negative_check (lo := (17083365647527716193 / 25000000000000000000)) (hi := (68333462590110864773 / 100000000000000000000))
    (y := (-((1432178344045737117 / 2000000000000000000)))) (u := (48865958749228598617 / 100000000000000000000))
  · norm_num [world13100, agent13100, scalar13100, tp13100, tm13100, ep13100, em13100, dsL]
  · norm_num [world13100, agent13100, scalar13100, tp13100, tm13100, ep13100, em13100, dsL]
  · norm_num [world13100, agent13100, scalar13100, tp13100, tm13100, ep13100, em13100, dsL]
  · norm_num [world13100, agent13100, scalar13100, tp13100, tm13100, ep13100, em13100, dsL]
  · norm_num [world13100, agent13100, scalar13100, tp13100, tm13100, ep13100, em13100, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13100, agent13100, tp13100, tm13100, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13100, agent13100, tp13100, tm13100, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13100, agent13100, scalar13100, tp13100, tm13100, ep13100, em13100, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13100, agent13100, tp13100, tm13100, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13100, agent13100, scalar13100, tp13100, tm13100, ep13100, em13100, dsL]

theorem tails13100 :
    exp (-((13100:ℝ)*ep13100)) ≤ scalar13100.upperTail ∧
    exp (-((13100:ℝ)*em13100)) ≤ scalar13100.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13100:ℝ)) (by norm_num [ep13100]) ?_)
      (show bp13100^8 ≤ scalar13100.upperTail by norm_num [bp13100, scalar13100])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13100, bp13100, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13100:ℝ)) (by norm_num [em13100]) ?_)
      (show bm13100^8 ≤ scalar13100.lowerTail by norm_num [bm13100, scalar13100])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13100, bm13100, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13100 :
    agent13100.root+dsL+scalar13100.worldRadius < √(1/100/aL) ∧
    2*(agent13100.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13100, agent13100, scalar13100, tp13100, tm13100, ep13100, em13100, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13100, agent13100, scalar13100, tp13100, tm13100, ep13100, em13100, dsL]

noncomputable def master13100 : MasterCertificate 13100 world13100 agent13100 :=
  master scalar13100 dsL tp13100 tm13100 ep13100 em13100
    (by norm_num [dsL]) (by norm_num [tp13100]) (by norm_num [tm13100])
    (by norm_num [ep13100]) (by norm_num [em13100])
    positive13100 negative13100 tails13100.1 tails13100.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13100.1 tailGuards13100.2

theorem preserves13100 : master13100.toScalarCertificate = scalar13100 := rfl

noncomputable def tp13101 : ℝ := (1175485913 / 5000000000)
noncomputable def tm13101 : ℝ := (-((306951437 / 500000000)))
noncomputable def ep13101 : ℝ := (26219431172957757 / 50000000000000000000)
noncomputable def em13101 : ℝ := (50987710382491141 / 100000000000000000000)
noncomputable def bp13101 : ℝ := (42369055238228098047 / 100000000000000000000)
noncomputable def bm13101 : ℝ := (43387990830331140557 / 100000000000000000000)

theorem positive13101 :
    Eplus aL (agent13101.root+dsL) scalar13101.worldRadius world13101.frame
      agent13101.frame tp13101 ≤ -ep13101 := by
  apply positive_check (eT := (115698630491673279309 / 100000000000000000000)) (y := (4765232651564338381 / 12500000000000000000)) (u := (73203381668207356723 / 50000000000000000000))
  · norm_num [world13101, agent13101, scalar13101, tp13101, tm13101, ep13101, em13101, dsL]
  · norm_num [world13101, agent13101, scalar13101, tp13101, tm13101, ep13101, em13101, dsL]
  · norm_num [world13101, agent13101, scalar13101, tp13101, tm13101, ep13101, em13101, dsL]
  · norm_num [world13101, agent13101, scalar13101, tp13101, tm13101, ep13101, em13101, dsL]
  · norm_num [world13101, agent13101, scalar13101, tp13101, tm13101, ep13101, em13101, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13101, agent13101, tp13101, tm13101, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13101, agent13101, scalar13101, tp13101, tm13101, ep13101, em13101, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13101, agent13101, tp13101, tm13101, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13101, agent13101, scalar13101, tp13101, tm13101, ep13101, em13101, dsL]

theorem negative13101 :
    Eminus aL (agent13101.root+dsL) scalar13101.worldRadius world13101.frame
      agent13101.frame tm13101 ≤ -em13101 := by
  apply negative_check (lo := (68333355502704498641 / 100000000000000000000)) (hi := (34166677751352249321 / 50000000000000000000))
    (y := (-((71608829568792179649 / 100000000000000000000)))) (u := (1954640062887788849 / 4000000000000000000))
  · norm_num [world13101, agent13101, scalar13101, tp13101, tm13101, ep13101, em13101, dsL]
  · norm_num [world13101, agent13101, scalar13101, tp13101, tm13101, ep13101, em13101, dsL]
  · norm_num [world13101, agent13101, scalar13101, tp13101, tm13101, ep13101, em13101, dsL]
  · norm_num [world13101, agent13101, scalar13101, tp13101, tm13101, ep13101, em13101, dsL]
  · norm_num [world13101, agent13101, scalar13101, tp13101, tm13101, ep13101, em13101, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13101, agent13101, tp13101, tm13101, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13101, agent13101, tp13101, tm13101, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13101, agent13101, scalar13101, tp13101, tm13101, ep13101, em13101, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13101, agent13101, tp13101, tm13101, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13101, agent13101, scalar13101, tp13101, tm13101, ep13101, em13101, dsL]

theorem tails13101 :
    exp (-((13101:ℝ)*ep13101)) ≤ scalar13101.upperTail ∧
    exp (-((13101:ℝ)*em13101)) ≤ scalar13101.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13101:ℝ)) (by norm_num [ep13101]) ?_)
      (show bp13101^8 ≤ scalar13101.upperTail by norm_num [bp13101, scalar13101])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13101, bp13101, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13101:ℝ)) (by norm_num [em13101]) ?_)
      (show bm13101^8 ≤ scalar13101.lowerTail by norm_num [bm13101, scalar13101])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13101, bm13101, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13101 :
    agent13101.root+dsL+scalar13101.worldRadius < √(1/100/aL) ∧
    2*(agent13101.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13101, agent13101, scalar13101, tp13101, tm13101, ep13101, em13101, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13101, agent13101, scalar13101, tp13101, tm13101, ep13101, em13101, dsL]

noncomputable def master13101 : MasterCertificate 13101 world13101 agent13101 :=
  master scalar13101 dsL tp13101 tm13101 ep13101 em13101
    (by norm_num [dsL]) (by norm_num [tp13101]) (by norm_num [tm13101])
    (by norm_num [ep13101]) (by norm_num [em13101])
    positive13101 negative13101 tails13101.1 tails13101.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13101.1 tailGuards13101.2

theorem preserves13101 : master13101.toScalarCertificate = scalar13101 := rfl

noncomputable def tp13102 : ℝ := (1175522239 / 5000000000)
noncomputable def tm13102 : ℝ := (-((6139182629 / 10000000000)))
noncomputable def ep13102 : ℝ := (52441036777391137 / 100000000000000000000)
noncomputable def em13102 : ℝ := (50989552389403009 / 100000000000000000000)
noncomputable def bp13102 : ℝ := (42364769387425492299 / 100000000000000000000)
noncomputable def bm13102 : ℝ := (43383916797892480943 / 100000000000000000000)

theorem positive13102 :
    Eplus aL (agent13102.root+dsL) scalar13102.worldRadius world13102.frame
      agent13102.frame tp13102 ≤ -ep13102 := by
  apply positive_check (eT := (115698798368604121079 / 100000000000000000000)) (y := (38122514298484160027 / 100000000000000000000)) (u := (73203859750783340313 / 50000000000000000000))
  · norm_num [world13102, agent13102, scalar13102, tp13102, tm13102, ep13102, em13102, dsL]
  · norm_num [world13102, agent13102, scalar13102, tp13102, tm13102, ep13102, em13102, dsL]
  · norm_num [world13102, agent13102, scalar13102, tp13102, tm13102, ep13102, em13102, dsL]
  · norm_num [world13102, agent13102, scalar13102, tp13102, tm13102, ep13102, em13102, dsL]
  · norm_num [world13102, agent13102, scalar13102, tp13102, tm13102, ep13102, em13102, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13102, agent13102, tp13102, tm13102, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13102, agent13102, scalar13102, tp13102, tm13102, ep13102, em13102, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13102, agent13102, tp13102, tm13102, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13102, agent13102, scalar13102, tp13102, tm13102, ep13102, em13102, dsL]

theorem negative13102 :
    Eminus aL (agent13102.root+dsL) scalar13102.worldRadius world13102.frame
      agent13102.frame tm13102 ≤ -em13102 := by
  apply negative_check (lo := (109333197488987273 / 160000000000000000)) (hi := (34166624215308522813 / 50000000000000000000))
    (y := (-((35804371526093665367 / 50000000000000000000)))) (u := (3054127740588655957 / 6250000000000000000))
  · norm_num [world13102, agent13102, scalar13102, tp13102, tm13102, ep13102, em13102, dsL]
  · norm_num [world13102, agent13102, scalar13102, tp13102, tm13102, ep13102, em13102, dsL]
  · norm_num [world13102, agent13102, scalar13102, tp13102, tm13102, ep13102, em13102, dsL]
  · norm_num [world13102, agent13102, scalar13102, tp13102, tm13102, ep13102, em13102, dsL]
  · norm_num [world13102, agent13102, scalar13102, tp13102, tm13102, ep13102, em13102, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13102, agent13102, tp13102, tm13102, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13102, agent13102, tp13102, tm13102, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13102, agent13102, scalar13102, tp13102, tm13102, ep13102, em13102, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13102, agent13102, tp13102, tm13102, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13102, agent13102, scalar13102, tp13102, tm13102, ep13102, em13102, dsL]

theorem tails13102 :
    exp (-((13102:ℝ)*ep13102)) ≤ scalar13102.upperTail ∧
    exp (-((13102:ℝ)*em13102)) ≤ scalar13102.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13102:ℝ)) (by norm_num [ep13102]) ?_)
      (show bp13102^8 ≤ scalar13102.upperTail by norm_num [bp13102, scalar13102])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13102, bp13102, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13102:ℝ)) (by norm_num [em13102]) ?_)
      (show bm13102^8 ≤ scalar13102.lowerTail by norm_num [bm13102, scalar13102])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13102, bm13102, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13102 :
    agent13102.root+dsL+scalar13102.worldRadius < √(1/100/aL) ∧
    2*(agent13102.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13102, agent13102, scalar13102, tp13102, tm13102, ep13102, em13102, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13102, agent13102, scalar13102, tp13102, tm13102, ep13102, em13102, dsL]

noncomputable def master13102 : MasterCertificate 13102 world13102 agent13102 :=
  master scalar13102 dsL tp13102 tm13102 ep13102 em13102
    (by norm_num [dsL]) (by norm_num [tp13102]) (by norm_num [tm13102])
    (by norm_num [ep13102]) (by norm_num [em13102])
    positive13102 negative13102 tails13102.1 tails13102.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13102.1 tailGuards13102.2

theorem preserves13102 : master13102.toScalarCertificate = scalar13102 := rfl

noncomputable def tp13103 : ℝ := (73472407 / 312500000)
noncomputable def tm13103 : ℝ := (-((6139336357 / 10000000000)))
noncomputable def ep13103 : ℝ := (26221605075844461 / 50000000000000000000)
noncomputable def em13103 : ℝ := (50991393417590143 / 100000000000000000000)
noncomputable def bp13103 : ℝ := (10590121118341637483 / 25000000000000000000)
noncomputable def bm13103 : ℝ := (5422480455452816263 / 12500000000000000000)

theorem positive13103 :
    Eplus aL (agent13103.root+dsL) scalar13103.worldRadius world13103.frame
      agent13103.frame tp13103 ≤ -ep13103 := by
  apply positive_check (eT := (28924741379476838583 / 25000000000000000000)) (y := (38123165697372023219 / 100000000000000000000)) (u := (36602168300732364089 / 25000000000000000000))
  · norm_num [world13103, agent13103, scalar13103, tp13103, tm13103, ep13103, em13103, dsL]
  · norm_num [world13103, agent13103, scalar13103, tp13103, tm13103, ep13103, em13103, dsL]
  · norm_num [world13103, agent13103, scalar13103, tp13103, tm13103, ep13103, em13103, dsL]
  · norm_num [world13103, agent13103, scalar13103, tp13103, tm13103, ep13103, em13103, dsL]
  · norm_num [world13103, agent13103, scalar13103, tp13103, tm13103, ep13103, em13103, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13103, agent13103, tp13103, tm13103, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13103, agent13103, scalar13103, tp13103, tm13103, ep13103, em13103, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13103, agent13103, tp13103, tm13103, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13103, agent13103, scalar13103, tp13103, tm13103, ep13103, em13103, dsL]

theorem negative13103 :
    Eminus aL (agent13103.root+dsL) scalar13103.worldRadius world13103.frame
      agent13103.frame tm13103 ≤ -em13103 := by
  apply negative_check (lo := (8541642748016818101 / 12500000000000000000)) (hi := (68333141984134544809 / 100000000000000000000))
    (y := (-((71608655037024475257 / 100000000000000000000)))) (u := (9773217371793099573 / 20000000000000000000))
  · norm_num [world13103, agent13103, scalar13103, tp13103, tm13103, ep13103, em13103, dsL]
  · norm_num [world13103, agent13103, scalar13103, tp13103, tm13103, ep13103, em13103, dsL]
  · norm_num [world13103, agent13103, scalar13103, tp13103, tm13103, ep13103, em13103, dsL]
  · norm_num [world13103, agent13103, scalar13103, tp13103, tm13103, ep13103, em13103, dsL]
  · norm_num [world13103, agent13103, scalar13103, tp13103, tm13103, ep13103, em13103, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13103, agent13103, tp13103, tm13103, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13103, agent13103, tp13103, tm13103, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13103, agent13103, scalar13103, tp13103, tm13103, ep13103, em13103, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13103, agent13103, tp13103, tm13103, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13103, agent13103, scalar13103, tp13103, tm13103, ep13103, em13103, dsL]

theorem tails13103 :
    exp (-((13103:ℝ)*ep13103)) ≤ scalar13103.upperTail ∧
    exp (-((13103:ℝ)*em13103)) ≤ scalar13103.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13103:ℝ)) (by norm_num [ep13103]) ?_)
      (show bp13103^8 ≤ scalar13103.upperTail by norm_num [bp13103, scalar13103])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13103, bp13103, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13103:ℝ)) (by norm_num [em13103]) ?_)
      (show bm13103^8 ≤ scalar13103.lowerTail by norm_num [bm13103, scalar13103])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13103, bm13103, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13103 :
    agent13103.root+dsL+scalar13103.worldRadius < √(1/100/aL) ∧
    2*(agent13103.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13103, agent13103, scalar13103, tp13103, tm13103, ep13103, em13103, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13103, agent13103, scalar13103, tp13103, tm13103, ep13103, em13103, dsL]

noncomputable def master13103 : MasterCertificate 13103 world13103 agent13103 :=
  master scalar13103 dsL tp13103 tm13103 ep13103 em13103
    (by norm_num [dsL]) (by norm_num [tp13103]) (by norm_num [tm13103])
    (by norm_num [ep13103]) (by norm_num [em13103])
    positive13103 negative13103 tails13103.1 tails13103.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13103.1 tailGuards13103.2

theorem preserves13103 : master13103.toScalarCertificate = scalar13103 := rfl

noncomputable def tp13104 : ℝ := (1175594821 / 5000000000)
noncomputable def tm13104 : ℝ := (-((1227898011 / 2000000000)))
noncomputable def ep13104 : ℝ := (5244538236588683 / 10000000000000000000)
noncomputable def em13104 : ℝ := (50993233360263639 / 100000000000000000000)
noncomputable def bp13104 : ℝ := (4235620056742939713 / 10000000000000000000)
noncomputable def bm13104 : ℝ := (43375771443377965999 / 100000000000000000000)

theorem positive13104 :
    Eplus aL (agent13104.root+dsL) scalar13104.worldRadius world13104.frame
      agent13104.frame tp13104 ≤ -ep13104 := by
  apply positive_check (eT := (57849566608446024943 / 50000000000000000000)) (y := (7624763753029682051 / 20000000000000000000)) (u := (36602407338479533523 / 25000000000000000000))
  · norm_num [world13104, agent13104, scalar13104, tp13104, tm13104, ep13104, em13104, dsL]
  · norm_num [world13104, agent13104, scalar13104, tp13104, tm13104, ep13104, em13104, dsL]
  · norm_num [world13104, agent13104, scalar13104, tp13104, tm13104, ep13104, em13104, dsL]
  · norm_num [world13104, agent13104, scalar13104, tp13104, tm13104, ep13104, em13104, dsL]
  · norm_num [world13104, agent13104, scalar13104, tp13104, tm13104, ep13104, em13104, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13104, agent13104, tp13104, tm13104, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13104, agent13104, scalar13104, tp13104, tm13104, ep13104, em13104, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13104, agent13104, tp13104, tm13104, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13104, agent13104, scalar13104, tp13104, tm13104, ep13104, em13104, dsL]

theorem negative13104 :
    Eminus aL (agent13104.root+dsL) scalar13104.worldRadius world13104.frame
      agent13104.frame tm13104 ≤ -em13104 := by
  apply negative_check (lo := (68333035608058583383 / 100000000000000000000)) (hi := (8541629451007322923 / 12500000000000000000))
    (y := (-((35804283737675185721 / 50000000000000000000)))) (u := (24433064823473976767 / 50000000000000000000))
  · norm_num [world13104, agent13104, scalar13104, tp13104, tm13104, ep13104, em13104, dsL]
  · norm_num [world13104, agent13104, scalar13104, tp13104, tm13104, ep13104, em13104, dsL]
  · norm_num [world13104, agent13104, scalar13104, tp13104, tm13104, ep13104, em13104, dsL]
  · norm_num [world13104, agent13104, scalar13104, tp13104, tm13104, ep13104, em13104, dsL]
  · norm_num [world13104, agent13104, scalar13104, tp13104, tm13104, ep13104, em13104, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13104, agent13104, tp13104, tm13104, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13104, agent13104, tp13104, tm13104, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13104, agent13104, scalar13104, tp13104, tm13104, ep13104, em13104, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13104, agent13104, tp13104, tm13104, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13104, agent13104, scalar13104, tp13104, tm13104, ep13104, em13104, dsL]

theorem tails13104 :
    exp (-((13104:ℝ)*ep13104)) ≤ scalar13104.upperTail ∧
    exp (-((13104:ℝ)*em13104)) ≤ scalar13104.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13104:ℝ)) (by norm_num [ep13104]) ?_)
      (show bp13104^8 ≤ scalar13104.upperTail by norm_num [bp13104, scalar13104])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13104, bp13104, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13104:ℝ)) (by norm_num [em13104]) ?_)
      (show bm13104^8 ≤ scalar13104.lowerTail by norm_num [bm13104, scalar13104])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13104, bm13104, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13104 :
    agent13104.root+dsL+scalar13104.worldRadius < √(1/100/aL) ∧
    2*(agent13104.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13104, agent13104, scalar13104, tp13104, tm13104, ep13104, em13104, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13104, agent13104, scalar13104, tp13104, tm13104, ep13104, em13104, dsL]

noncomputable def master13104 : MasterCertificate 13104 world13104 agent13104 :=
  master scalar13104 dsL tp13104 tm13104 ep13104 em13104
    (by norm_num [dsL]) (by norm_num [tp13104]) (by norm_num [tm13104])
    (by norm_num [ep13104]) (by norm_num [em13104])
    positive13104 negative13104 tails13104.1 tails13104.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13104.1 tailGuards13104.2

theorem preserves13104 : master13104.toScalarCertificate = scalar13104 := rfl

noncomputable def tp13105 : ℝ := (2351262083 / 10000000000)
noncomputable def tm13105 : ℝ := (-((3069821733 / 5000000000)))
noncomputable def ep13105 : ℝ := (52447552936404823 / 100000000000000000000)
noncomputable def em13105 : ℝ := (2549753588480219 / 5000000000000000000)
noncomputable def bp13105 : ℝ := (42351918005076957957 / 100000000000000000000)
noncomputable def bm13105 : ℝ := (21685850257653090379 / 50000000000000000000)

theorem positive13105 :
    Eplus aL (agent13105.root+dsL) scalar13105.worldRadius world13105.frame
      agent13105.frame tp13105 ≤ -ep13105 := by
  apply positive_check (eT := (3615603114962561751 / 3125000000000000000)) (y := (38124469212117837871 / 100000000000000000000)) (u := (9150661354625773881 / 6250000000000000000))
  · norm_num [world13105, agent13105, scalar13105, tp13105, tm13105, ep13105, em13105, dsL]
  · norm_num [world13105, agent13105, scalar13105, tp13105, tm13105, ep13105, em13105, dsL]
  · norm_num [world13105, agent13105, scalar13105, tp13105, tm13105, ep13105, em13105, dsL]
  · norm_num [world13105, agent13105, scalar13105, tp13105, tm13105, ep13105, em13105, dsL]
  · norm_num [world13105, agent13105, scalar13105, tp13105, tm13105, ep13105, em13105, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13105, agent13105, tp13105, tm13105, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13105, agent13105, scalar13105, tp13105, tm13105, ep13105, em13105, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13105, agent13105, tp13105, tm13105, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13105, agent13105, scalar13105, tp13105, tm13105, ep13105, em13105, dsL]

theorem negative13105 :
    Eminus aL (agent13105.root+dsL) scalar13105.worldRadius world13105.frame
      agent13105.frame tm13105 ≤ -em13105 := by
  apply negative_check (lo := (68332930391536089297 / 100000000000000000000)) (hi := (34166465195768044649 / 50000000000000000000))
    (y := (-((14321695555255845697 / 20000000000000000000)))) (u := (24433086739716004511 / 50000000000000000000))
  · norm_num [world13105, agent13105, scalar13105, tp13105, tm13105, ep13105, em13105, dsL]
  · norm_num [world13105, agent13105, scalar13105, tp13105, tm13105, ep13105, em13105, dsL]
  · norm_num [world13105, agent13105, scalar13105, tp13105, tm13105, ep13105, em13105, dsL]
  · norm_num [world13105, agent13105, scalar13105, tp13105, tm13105, ep13105, em13105, dsL]
  · norm_num [world13105, agent13105, scalar13105, tp13105, tm13105, ep13105, em13105, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13105, agent13105, tp13105, tm13105, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13105, agent13105, tp13105, tm13105, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13105, agent13105, scalar13105, tp13105, tm13105, ep13105, em13105, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13105, agent13105, tp13105, tm13105, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13105, agent13105, scalar13105, tp13105, tm13105, ep13105, em13105, dsL]

theorem tails13105 :
    exp (-((13105:ℝ)*ep13105)) ≤ scalar13105.upperTail ∧
    exp (-((13105:ℝ)*em13105)) ≤ scalar13105.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13105:ℝ)) (by norm_num [ep13105]) ?_)
      (show bp13105^8 ≤ scalar13105.upperTail by norm_num [bp13105, scalar13105])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13105, bp13105, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13105:ℝ)) (by norm_num [em13105]) ?_)
      (show bm13105^8 ≤ scalar13105.lowerTail by norm_num [bm13105, scalar13105])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13105, bm13105, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13105 :
    agent13105.root+dsL+scalar13105.worldRadius < √(1/100/aL) ∧
    2*(agent13105.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13105, agent13105, scalar13105, tp13105, tm13105, ep13105, em13105, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13105, agent13105, scalar13105, tp13105, tm13105, ep13105, em13105, dsL]

noncomputable def master13105 : MasterCertificate 13105 world13105 agent13105 :=
  master scalar13105 dsL tp13105 tm13105 ep13105 em13105
    (by norm_num [dsL]) (by norm_num [tp13105]) (by norm_num [tm13105])
    (by norm_num [ep13105]) (by norm_num [em13105])
    positive13105 negative13105 tails13105.1 tails13105.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13105.1 tailGuards13105.2

theorem preserves13105 : master13105.toScalarCertificate = scalar13105 := rfl

noncomputable def tp13106 : ℝ := (1175667287 / 5000000000)
noncomputable def tm13106 : ℝ := (-((3069898527 / 5000000000)))
noncomputable def ep13106 : ℝ := (52449723294903747 / 100000000000000000000)
noncomputable def em13106 : ℝ := (50996910028315483 / 100000000000000000000)
noncomputable def bp13106 : ℝ := (1693905431720842551 / 4000000000000000000)
noncomputable def bm13106 : ℝ := (43367629877000727981 / 100000000000000000000)

theorem positive13106 :
    Eplus aL (agent13106.root+dsL) scalar13106.worldRadius world13106.frame
      agent13106.frame tp13106 ≤ -ep13106 := by
  apply positive_check (eT := (57849733266262531251 / 50000000000000000000)) (y := (9531280135026636399 / 25000000000000000000)) (u := (146411535290214835967 / 100000000000000000000))
  · norm_num [world13106, agent13106, scalar13106, tp13106, tm13106, ep13106, em13106, dsL]
  · norm_num [world13106, agent13106, scalar13106, tp13106, tm13106, ep13106, em13106, dsL]
  · norm_num [world13106, agent13106, scalar13106, tp13106, tm13106, ep13106, em13106, dsL]
  · norm_num [world13106, agent13106, scalar13106, tp13106, tm13106, ep13106, em13106, dsL]
  · norm_num [world13106, agent13106, scalar13106, tp13106, tm13106, ep13106, em13106, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13106, agent13106, tp13106, tm13106, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13106, agent13106, scalar13106, tp13106, tm13106, ep13106, em13106, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13106, agent13106, tp13106, tm13106, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13106, agent13106, scalar13106, tp13106, tm13106, ep13106, em13106, dsL]

theorem negative13106 :
    Eminus aL (agent13106.root+dsL) scalar13106.worldRadius world13106.frame
      agent13106.frame tm13106 ≤ -em13106 := by
  apply negative_check (lo := (68332824368141112369 / 100000000000000000000)) (hi := (6833282436814111237 / 10000000000000000000))
    (y := (-((71608390194287392717 / 100000000000000000000)))) (u := (12216554069354704473 / 25000000000000000000))
  · norm_num [world13106, agent13106, scalar13106, tp13106, tm13106, ep13106, em13106, dsL]
  · norm_num [world13106, agent13106, scalar13106, tp13106, tm13106, ep13106, em13106, dsL]
  · norm_num [world13106, agent13106, scalar13106, tp13106, tm13106, ep13106, em13106, dsL]
  · norm_num [world13106, agent13106, scalar13106, tp13106, tm13106, ep13106, em13106, dsL]
  · norm_num [world13106, agent13106, scalar13106, tp13106, tm13106, ep13106, em13106, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13106, agent13106, tp13106, tm13106, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13106, agent13106, tp13106, tm13106, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13106, agent13106, scalar13106, tp13106, tm13106, ep13106, em13106, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13106, agent13106, tp13106, tm13106, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13106, agent13106, scalar13106, tp13106, tm13106, ep13106, em13106, dsL]

theorem tails13106 :
    exp (-((13106:ℝ)*ep13106)) ≤ scalar13106.upperTail ∧
    exp (-((13106:ℝ)*em13106)) ≤ scalar13106.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13106:ℝ)) (by norm_num [ep13106]) ?_)
      (show bp13106^8 ≤ scalar13106.upperTail by norm_num [bp13106, scalar13106])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13106, bp13106, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13106:ℝ)) (by norm_num [em13106]) ?_)
      (show bm13106^8 ≤ scalar13106.lowerTail by norm_num [bm13106, scalar13106])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13106, bm13106, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13106 :
    agent13106.root+dsL+scalar13106.worldRadius < √(1/100/aL) ∧
    2*(agent13106.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13106, agent13106, scalar13106, tp13106, tm13106, ep13106, em13106, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13106, agent13106, scalar13106, tp13106, tm13106, ep13106, em13106, dsL]

noncomputable def master13106 : MasterCertificate 13106 world13106 agent13106 :=
  master scalar13106 dsL tp13106 tm13106 ep13106 em13106
    (by norm_num [dsL]) (by norm_num [tp13106]) (by norm_num [tm13106])
    (by norm_num [ep13106]) (by norm_num [em13106])
    positive13106 negative13106 tails13106.1 tails13106.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13106.1 tailGuards13106.2

theorem preserves13106 : master13106.toScalarCertificate = scalar13106 := rfl

noncomputable def tp13107 : ℝ := (94056281 / 400000000)
noncomputable def tm13107 : ℝ := (-((6139950619 / 10000000000)))
noncomputable def ep13107 : ℝ := (26225946084164107 / 50000000000000000000)
noncomputable def em13107 : ℝ := (10199749372214933 / 20000000000000000000)
noncomputable def bp13107 : ℝ := (10585838703612466357 / 25000000000000000000)
noncomputable def bm13107 : ℝ := (43363560434538801563 / 100000000000000000000)

theorem positive13107 :
    Eplus aL (agent13107.root+dsL) scalar13107.worldRadius world13107.frame
      agent13107.frame tp13107 ≤ -ep13107 := by
  apply positive_check (eT := (115699633132264236141 / 100000000000000000000)) (y := (4765721473455203251 / 12500000000000000000)) (u := (73206244397417160587 / 50000000000000000000))
  · norm_num [world13107, agent13107, scalar13107, tp13107, tm13107, ep13107, em13107, dsL]
  · norm_num [world13107, agent13107, scalar13107, tp13107, tm13107, ep13107, em13107, dsL]
  · norm_num [world13107, agent13107, scalar13107, tp13107, tm13107, ep13107, em13107, dsL]
  · norm_num [world13107, agent13107, scalar13107, tp13107, tm13107, ep13107, em13107, dsL]
  · norm_num [world13107, agent13107, scalar13107, tp13107, tm13107, ep13107, em13107, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13107, agent13107, tp13107, tm13107, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13107, agent13107, scalar13107, tp13107, tm13107, ep13107, em13107, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13107, agent13107, tp13107, tm13107, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13107, agent13107, scalar13107, tp13107, tm13107, ep13107, em13107, dsL]

theorem negative13107 :
    Eminus aL (agent13107.root+dsL) scalar13107.worldRadius world13107.frame
      agent13107.frame tm13107 ≤ -em13107 := by
  apply negative_check (lo := (13666543677095329037 / 20000000000000000000)) (hi := (34166359192738322593 / 50000000000000000000))
    (y := (-((2864332131747297981 / 4000000000000000000)))) (u := (4886625874247482701 / 10000000000000000000))
  · norm_num [world13107, agent13107, scalar13107, tp13107, tm13107, ep13107, em13107, dsL]
  · norm_num [world13107, agent13107, scalar13107, tp13107, tm13107, ep13107, em13107, dsL]
  · norm_num [world13107, agent13107, scalar13107, tp13107, tm13107, ep13107, em13107, dsL]
  · norm_num [world13107, agent13107, scalar13107, tp13107, tm13107, ep13107, em13107, dsL]
  · norm_num [world13107, agent13107, scalar13107, tp13107, tm13107, ep13107, em13107, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13107, agent13107, tp13107, tm13107, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13107, agent13107, tp13107, tm13107, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13107, agent13107, scalar13107, tp13107, tm13107, ep13107, em13107, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13107, agent13107, tp13107, tm13107, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13107, agent13107, scalar13107, tp13107, tm13107, ep13107, em13107, dsL]

theorem tails13107 :
    exp (-((13107:ℝ)*ep13107)) ≤ scalar13107.upperTail ∧
    exp (-((13107:ℝ)*em13107)) ≤ scalar13107.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13107:ℝ)) (by norm_num [ep13107]) ?_)
      (show bp13107^8 ≤ scalar13107.upperTail by norm_num [bp13107, scalar13107])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13107, bp13107, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13107:ℝ)) (by norm_num [em13107]) ?_)
      (show bm13107^8 ≤ scalar13107.lowerTail by norm_num [bm13107, scalar13107])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13107, bm13107, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13107 :
    agent13107.root+dsL+scalar13107.worldRadius < √(1/100/aL) ∧
    2*(agent13107.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13107, agent13107, scalar13107, tp13107, tm13107, ep13107, em13107, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13107, agent13107, scalar13107, tp13107, tm13107, ep13107, em13107, dsL]

noncomputable def master13107 : MasterCertificate 13107 world13107 agent13107 :=
  master scalar13107 dsL tp13107 tm13107 ep13107 em13107
    (by norm_num [dsL]) (by norm_num [tp13107]) (by norm_num [tm13107])
    (by norm_num [ep13107]) (by norm_num [em13107])
    positive13107 negative13107 tails13107.1 tails13107.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13107.1 tailGuards13107.2

theorem preserves13107 : master13107.toScalarCertificate = scalar13107 := rfl

noncomputable def tp13108 : ℝ := (146967469 / 625000000)
noncomputable def tm13108 : ℝ := (-((6140103883 / 10000000000)))
noncomputable def ep13108 : ℝ := (52454060170207 / 100000000000000000)
noncomputable def em13108 : ℝ := (796884107960169 / 1562500000000000000)
noncomputable def bp13108 : ℝ := (10584768660922973379 / 25000000000000000000)
noncomputable def bm13108 : ℝ := (43359491732087724883 / 100000000000000000000)

theorem positive13108 :
    Eplus aL (agent13108.root+dsL) scalar13108.worldRadius world13108.frame
      agent13108.frame tp13108 ≤ -ep13108 := by
  apply positive_check (eT := (115699799965928382879 / 100000000000000000000)) (y := (19063211816150699127 / 50000000000000000000)) (u := (73206721589967160357 / 50000000000000000000))
  · norm_num [world13108, agent13108, scalar13108, tp13108, tm13108, ep13108, em13108, dsL]
  · norm_num [world13108, agent13108, scalar13108, tp13108, tm13108, ep13108, em13108, dsL]
  · norm_num [world13108, agent13108, scalar13108, tp13108, tm13108, ep13108, em13108, dsL]
  · norm_num [world13108, agent13108, scalar13108, tp13108, tm13108, ep13108, em13108, dsL]
  · norm_num [world13108, agent13108, scalar13108, tp13108, tm13108, ep13108, em13108, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13108, agent13108, tp13108, tm13108, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13108, agent13108, scalar13108, tp13108, tm13108, ep13108, em13108, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13108, agent13108, tp13108, tm13108, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13108, agent13108, scalar13108, tp13108, tm13108, ep13108, em13108, dsL]

theorem negative13108 :
    Eminus aL (agent13108.root+dsL) scalar13108.worldRadius world13108.frame
      agent13108.frame tm13108 ≤ -em13108 := by
  apply negative_check (lo := (3416630681082588063 / 5000000000000000000)) (hi := (68332613621651761261 / 100000000000000000000))
    (y := (-((2237756677398125409 / 3125000000000000000)))) (u := (24433151267470708913 / 50000000000000000000))
  · norm_num [world13108, agent13108, scalar13108, tp13108, tm13108, ep13108, em13108, dsL]
  · norm_num [world13108, agent13108, scalar13108, tp13108, tm13108, ep13108, em13108, dsL]
  · norm_num [world13108, agent13108, scalar13108, tp13108, tm13108, ep13108, em13108, dsL]
  · norm_num [world13108, agent13108, scalar13108, tp13108, tm13108, ep13108, em13108, dsL]
  · norm_num [world13108, agent13108, scalar13108, tp13108, tm13108, ep13108, em13108, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13108, agent13108, tp13108, tm13108, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13108, agent13108, tp13108, tm13108, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13108, agent13108, scalar13108, tp13108, tm13108, ep13108, em13108, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13108, agent13108, tp13108, tm13108, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13108, agent13108, scalar13108, tp13108, tm13108, ep13108, em13108, dsL]

theorem tails13108 :
    exp (-((13108:ℝ)*ep13108)) ≤ scalar13108.upperTail ∧
    exp (-((13108:ℝ)*em13108)) ≤ scalar13108.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13108:ℝ)) (by norm_num [ep13108]) ?_)
      (show bp13108^8 ≤ scalar13108.upperTail by norm_num [bp13108, scalar13108])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13108, bp13108, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13108:ℝ)) (by norm_num [em13108]) ?_)
      (show bm13108^8 ≤ scalar13108.lowerTail by norm_num [bm13108, scalar13108])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13108, bm13108, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13108 :
    agent13108.root+dsL+scalar13108.worldRadius < √(1/100/aL) ∧
    2*(agent13108.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13108, agent13108, scalar13108, tp13108, tm13108, ep13108, em13108, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13108, agent13108, scalar13108, tp13108, tm13108, ep13108, em13108, dsL]

noncomputable def master13108 : MasterCertificate 13108 world13108 agent13108 :=
  master scalar13108 dsL tp13108 tm13108 ep13108 em13108
    (by norm_num [dsL]) (by norm_num [tp13108]) (by norm_num [tm13108])
    (by norm_num [ep13108]) (by norm_num [em13108])
    positive13108 negative13108 tails13108.1 tails13108.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13108.1 tailGuards13108.2

theorem preserves13108 : master13108.toScalarCertificate = scalar13108 := rfl

noncomputable def tp13109 : ℝ := (2351551849 / 10000000000)
noncomputable def tm13109 : ℝ := (-((3070128509 / 5000000000)))
noncomputable def ep13109 : ℝ := (52456226095593267 / 100000000000000000000)
noncomputable def em13109 : ℝ := (2550120851424093 / 5000000000000000000)
noncomputable def bp13109 : ℝ := (21167398058304974747 / 50000000000000000000)
noncomputable def bm13109 : ℝ := (43355424583057015339 / 100000000000000000000)

theorem positive13109 :
    Eplus aL (agent13109.root+dsL) scalar13109.worldRadius world13109.frame
      agent13109.frame tp13109 ≤ -ep13109 := by
  apply positive_check (eT := (115699965871149964201 / 100000000000000000000)) (y := (19063536878244658439 / 50000000000000000000)) (u := (36603598763059242661 / 25000000000000000000))
  · norm_num [world13109, agent13109, scalar13109, tp13109, tm13109, ep13109, em13109, dsL]
  · norm_num [world13109, agent13109, scalar13109, tp13109, tm13109, ep13109, em13109, dsL]
  · norm_num [world13109, agent13109, scalar13109, tp13109, tm13109, ep13109, em13109, dsL]
  · norm_num [world13109, agent13109, scalar13109, tp13109, tm13109, ep13109, em13109, dsL]
  · norm_num [world13109, agent13109, scalar13109, tp13109, tm13109, ep13109, em13109, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13109, agent13109, tp13109, tm13109, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13109, agent13109, scalar13109, tp13109, tm13109, ep13109, em13109, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13109, agent13109, tp13109, tm13109, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13109, agent13109, scalar13109, tp13109, tm13109, ep13109, em13109, dsL]

theorem negative13109 :
    Eminus aL (agent13109.root+dsL) scalar13109.worldRadius world13109.frame
      agent13109.frame tm13109 ≤ -em13109 := by
  apply negative_check (lo := (34166254673853466513 / 50000000000000000000)) (hi := (68332509347706933027 / 100000000000000000000))
    (y := (-((71608123718791046793 / 100000000000000000000)))) (u := (48866346494084686293 / 100000000000000000000))
  · norm_num [world13109, agent13109, scalar13109, tp13109, tm13109, ep13109, em13109, dsL]
  · norm_num [world13109, agent13109, scalar13109, tp13109, tm13109, ep13109, em13109, dsL]
  · norm_num [world13109, agent13109, scalar13109, tp13109, tm13109, ep13109, em13109, dsL]
  · norm_num [world13109, agent13109, scalar13109, tp13109, tm13109, ep13109, em13109, dsL]
  · norm_num [world13109, agent13109, scalar13109, tp13109, tm13109, ep13109, em13109, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13109, agent13109, tp13109, tm13109, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13109, agent13109, tp13109, tm13109, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13109, agent13109, scalar13109, tp13109, tm13109, ep13109, em13109, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13109, agent13109, tp13109, tm13109, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13109, agent13109, scalar13109, tp13109, tm13109, ep13109, em13109, dsL]

theorem tails13109 :
    exp (-((13109:ℝ)*ep13109)) ≤ scalar13109.upperTail ∧
    exp (-((13109:ℝ)*em13109)) ≤ scalar13109.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13109:ℝ)) (by norm_num [ep13109]) ?_)
      (show bp13109^8 ≤ scalar13109.upperTail by norm_num [bp13109, scalar13109])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13109, bp13109, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13109:ℝ)) (by norm_num [em13109]) ?_)
      (show bm13109^8 ≤ scalar13109.lowerTail by norm_num [bm13109, scalar13109])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13109, bm13109, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13109 :
    agent13109.root+dsL+scalar13109.worldRadius < √(1/100/aL) ∧
    2*(agent13109.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13109, agent13109, scalar13109, tp13109, tm13109, ep13109, em13109, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13109, agent13109, scalar13109, tp13109, tm13109, ep13109, em13109, dsL]

noncomputable def master13109 : MasterCertificate 13109 world13109 agent13109 :=
  master scalar13109 dsL tp13109 tm13109 ep13109 em13109
    (by norm_num [dsL]) (by norm_num [tp13109]) (by norm_num [tm13109])
    (by norm_num [ep13109]) (by norm_num [em13109])
    positive13109 negative13109 tails13109.1 tails13109.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13109.1 tailGuards13109.2

theorem preserves13109 : master13109.toScalarCertificate = scalar13109 := rfl

noncomputable def tp13110 : ℝ := (1175847533 / 5000000000)
noncomputable def tm13110 : ℝ := (-((3070312523 / 5000000000)))
noncomputable def ep13110 : ℝ := (52459728020626939 / 100000000000000000000)
noncomputable def em13110 : ℝ := (10201142080943907 / 20000000000000000000)
noncomputable def bp13110 : ℝ := (5291198878926273191 / 12500000000000000000)
noncomputable def bm13110 : ℝ := (21675160471547541293 / 50000000000000000000)

theorem positive13110 :
    Eplus aL (agent13110.root+dsL) scalar13110.worldRadius world13110.frame
      agent13110.frame tp13110 ≤ -ep13110 := by
  apply positive_check (eT := (2314012806240675023 / 2000000000000000000)) (y := (38127012249870448171 / 100000000000000000000)) (u := (146414304997720731689 / 100000000000000000000))
  · norm_num [world13110, agent13110, scalar13110, tp13110, tm13110, ep13110, em13110, dsL]
  · norm_num [world13110, agent13110, scalar13110, tp13110, tm13110, ep13110, em13110, dsL]
  · norm_num [world13110, agent13110, scalar13110, tp13110, tm13110, ep13110, em13110, dsL]
  · norm_num [world13110, agent13110, scalar13110, tp13110, tm13110, ep13110, em13110, dsL]
  · norm_num [world13110, agent13110, scalar13110, tp13110, tm13110, ep13110, em13110, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13110, agent13110, tp13110, tm13110, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13110, agent13110, scalar13110, tp13110, tm13110, ep13110, em13110, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13110, agent13110, tp13110, tm13110, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13110, agent13110, scalar13110, tp13110, tm13110, ep13110, em13110, dsL]

theorem negative13110 :
    Eminus aL (agent13110.root+dsL) scalar13110.worldRadius world13110.frame
      agent13110.frame tm13110 ≤ -em13110 := by
  apply negative_check (lo := (68331494412517595439 / 100000000000000000000)) (hi := (854143680156469943 / 1250000000000000000))
    (y := (-((8950772273608698639 / 12500000000000000000)))) (u := (24433648606362739861 / 50000000000000000000))
  · norm_num [world13110, agent13110, scalar13110, tp13110, tm13110, ep13110, em13110, dsL]
  · norm_num [world13110, agent13110, scalar13110, tp13110, tm13110, ep13110, em13110, dsL]
  · norm_num [world13110, agent13110, scalar13110, tp13110, tm13110, ep13110, em13110, dsL]
  · norm_num [world13110, agent13110, scalar13110, tp13110, tm13110, ep13110, em13110, dsL]
  · norm_num [world13110, agent13110, scalar13110, tp13110, tm13110, ep13110, em13110, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13110, agent13110, tp13110, tm13110, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13110, agent13110, tp13110, tm13110, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13110, agent13110, scalar13110, tp13110, tm13110, ep13110, em13110, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13110, agent13110, tp13110, tm13110, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13110, agent13110, scalar13110, tp13110, tm13110, ep13110, em13110, dsL]

theorem tails13110 :
    exp (-((13110:ℝ)*ep13110)) ≤ scalar13110.upperTail ∧
    exp (-((13110:ℝ)*em13110)) ≤ scalar13110.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13110:ℝ)) (by norm_num [ep13110]) ?_)
      (show bp13110^8 ≤ scalar13110.upperTail by norm_num [bp13110, scalar13110])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13110, bp13110, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13110:ℝ)) (by norm_num [em13110]) ?_)
      (show bm13110^8 ≤ scalar13110.lowerTail by norm_num [bm13110, scalar13110])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13110, bm13110, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13110 :
    agent13110.root+dsL+scalar13110.worldRadius < √(1/100/aL) ∧
    2*(agent13110.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13110, agent13110, scalar13110, tp13110, tm13110, ep13110, em13110, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13110, agent13110, scalar13110, tp13110, tm13110, ep13110, em13110, dsL]

noncomputable def master13110 : MasterCertificate 13110 world13110 agent13110 :=
  master scalar13110 dsL tp13110 tm13110 ep13110 em13110
    (by norm_num [dsL]) (by norm_num [tp13110]) (by norm_num [tm13110])
    (by norm_num [ep13110]) (by norm_num [em13110])
    positive13110 negative13110 tails13110.1 tails13110.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13110.1 tailGuards13110.2

theorem preserves13110 : master13110.toScalarCertificate = scalar13110 := rfl

noncomputable def tp13111 : ℝ := (2351767401 / 10000000000)
noncomputable def tm13111 : ℝ := (-((6140778177 / 10000000000)))
noncomputable def ep13111 : ℝ := (13115472951640053 / 25000000000000000000)
noncomputable def em13111 : ℝ := (5100754253407963 / 10000000000000000000)
noncomputable def bp13111 : ℝ := (42325314417684090371 / 100000000000000000000)
noncomputable def bm13111 : ℝ := (8669251118231407791 / 20000000000000000000)

theorem positive13111 :
    Eplus aL (agent13111.root+dsL) scalar13111.worldRadius world13111.frame
      agent13111.frame tp13111 ≤ -ep13111 := by
  apply positive_check (eT := (115700806201664452221 / 100000000000000000000)) (y := (9531915676712315493 / 25000000000000000000)) (u := (228773839629504579 / 156250000000000000))
  · norm_num [world13111, agent13111, scalar13111, tp13111, tm13111, ep13111, em13111, dsL]
  · norm_num [world13111, agent13111, scalar13111, tp13111, tm13111, ep13111, em13111, dsL]
  · norm_num [world13111, agent13111, scalar13111, tp13111, tm13111, ep13111, em13111, dsL]
  · norm_num [world13111, agent13111, scalar13111, tp13111, tm13111, ep13111, em13111, dsL]
  · norm_num [world13111, agent13111, scalar13111, tp13111, tm13111, ep13111, em13111, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13111, agent13111, tp13111, tm13111, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13111, agent13111, scalar13111, tp13111, tm13111, ep13111, em13111, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13111, agent13111, tp13111, tm13111, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13111, agent13111, scalar13111, tp13111, tm13111, ep13111, em13111, dsL]

theorem negative13111 :
    Eminus aL (agent13111.root+dsL) scalar13111.worldRadius world13111.frame
      agent13111.frame tm13111 ≤ -em13111 := by
  apply negative_check (lo := (13666278012488894831 / 20000000000000000000)) (hi := (17082847515611118539 / 25000000000000000000))
    (y := (-((7160608889371749537 / 10000000000000000000)))) (u := (9773468169774466481 / 20000000000000000000))
  · norm_num [world13111, agent13111, scalar13111, tp13111, tm13111, ep13111, em13111, dsL]
  · norm_num [world13111, agent13111, scalar13111, tp13111, tm13111, ep13111, em13111, dsL]
  · norm_num [world13111, agent13111, scalar13111, tp13111, tm13111, ep13111, em13111, dsL]
  · norm_num [world13111, agent13111, scalar13111, tp13111, tm13111, ep13111, em13111, dsL]
  · norm_num [world13111, agent13111, scalar13111, tp13111, tm13111, ep13111, em13111, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13111, agent13111, tp13111, tm13111, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13111, agent13111, tp13111, tm13111, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13111, agent13111, scalar13111, tp13111, tm13111, ep13111, em13111, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13111, agent13111, tp13111, tm13111, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13111, agent13111, scalar13111, tp13111, tm13111, ep13111, em13111, dsL]

theorem tails13111 :
    exp (-((13111:ℝ)*ep13111)) ≤ scalar13111.upperTail ∧
    exp (-((13111:ℝ)*em13111)) ≤ scalar13111.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13111:ℝ)) (by norm_num [ep13111]) ?_)
      (show bp13111^8 ≤ scalar13111.upperTail by norm_num [bp13111, scalar13111])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13111, bp13111, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13111:ℝ)) (by norm_num [em13111]) ?_)
      (show bm13111^8 ≤ scalar13111.lowerTail by norm_num [bm13111, scalar13111])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13111, bm13111, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13111 :
    agent13111.root+dsL+scalar13111.worldRadius < √(1/100/aL) ∧
    2*(agent13111.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13111, agent13111, scalar13111, tp13111, tm13111, ep13111, em13111, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13111, agent13111, scalar13111, tp13111, tm13111, ep13111, em13111, dsL]

noncomputable def master13111 : MasterCertificate 13111 world13111 agent13111 :=
  master scalar13111 dsL tp13111 tm13111 ep13111 em13111
    (by norm_num [dsL]) (by norm_num [tp13111]) (by norm_num [tm13111])
    (by norm_num [ep13111]) (by norm_num [em13111])
    positive13111 negative13111 tails13111.1 tails13111.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13111.1 tailGuards13111.2

theorem preserves13111 : master13111.toScalarCertificate = scalar13111 := rfl

noncomputable def tp13112 : ℝ := (587959911 / 2500000000)
noncomputable def tm13112 : ℝ := (-((1228186239 / 2000000000)))
noncomputable def ep13112 : ℝ := (13116013729020989 / 25000000000000000000)
noncomputable def em13112 : ℝ := (12752343506521129 / 25000000000000000000)
noncomputable def bp13112 : ℝ := (10580259619070404603 / 25000000000000000000)
noncomputable def bm13112 : ℝ := (8668438174941206203 / 20000000000000000000)

theorem positive13112 :
    Eplus aL (agent13112.root+dsL) scalar13112.worldRadius world13112.frame
      agent13112.frame tp13112 ≤ -ep13112 := by
  apply positive_check (eT := (57850485732122143039 / 50000000000000000000)) (y := (19064155962482012469 / 50000000000000000000)) (u := (146416207920342099483 / 100000000000000000000))
  · norm_num [world13112, agent13112, scalar13112, tp13112, tm13112, ep13112, em13112, dsL]
  · norm_num [world13112, agent13112, scalar13112, tp13112, tm13112, ep13112, em13112, dsL]
  · norm_num [world13112, agent13112, scalar13112, tp13112, tm13112, ep13112, em13112, dsL]
  · norm_num [world13112, agent13112, scalar13112, tp13112, tm13112, ep13112, em13112, dsL]
  · norm_num [world13112, agent13112, scalar13112, tp13112, tm13112, ep13112, em13112, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13112, agent13112, tp13112, tm13112, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13112, agent13112, scalar13112, tp13112, tm13112, ep13112, em13112, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13112, agent13112, tp13112, tm13112, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13112, agent13112, scalar13112, tp13112, tm13112, ep13112, em13112, dsL]

theorem negative13112 :
    Eminus aL (agent13112.root+dsL) scalar13112.worldRadius world13112.frame
      agent13112.frame tm13112 ≤ -em13112 := by
  apply negative_check (lo := (13666257226889881773 / 20000000000000000000)) (hi := (34165643067224704433 / 50000000000000000000))
    (y := (-((35802999691530483157 / 50000000000000000000)))) (u := (4886738459036953117 / 10000000000000000000))
  · norm_num [world13112, agent13112, scalar13112, tp13112, tm13112, ep13112, em13112, dsL]
  · norm_num [world13112, agent13112, scalar13112, tp13112, tm13112, ep13112, em13112, dsL]
  · norm_num [world13112, agent13112, scalar13112, tp13112, tm13112, ep13112, em13112, dsL]
  · norm_num [world13112, agent13112, scalar13112, tp13112, tm13112, ep13112, em13112, dsL]
  · norm_num [world13112, agent13112, scalar13112, tp13112, tm13112, ep13112, em13112, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13112, agent13112, tp13112, tm13112, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13112, agent13112, tp13112, tm13112, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13112, agent13112, scalar13112, tp13112, tm13112, ep13112, em13112, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13112, agent13112, tp13112, tm13112, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13112, agent13112, scalar13112, tp13112, tm13112, ep13112, em13112, dsL]

theorem tails13112 :
    exp (-((13112:ℝ)*ep13112)) ≤ scalar13112.upperTail ∧
    exp (-((13112:ℝ)*em13112)) ≤ scalar13112.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13112:ℝ)) (by norm_num [ep13112]) ?_)
      (show bp13112^8 ≤ scalar13112.upperTail by norm_num [bp13112, scalar13112])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13112, bp13112, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13112:ℝ)) (by norm_num [em13112]) ?_)
      (show bm13112^8 ≤ scalar13112.lowerTail by norm_num [bm13112, scalar13112])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13112, bm13112, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13112 :
    agent13112.root+dsL+scalar13112.worldRadius < √(1/100/aL) ∧
    2*(agent13112.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13112, agent13112, scalar13112, tp13112, tm13112, ep13112, em13112, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13112, agent13112, scalar13112, tp13112, tm13112, ep13112, em13112, dsL]

noncomputable def master13112 : MasterCertificate 13112 world13112 agent13112 :=
  master scalar13112 dsL tp13112 tm13112 ep13112 em13112
    (by norm_num [dsL]) (by norm_num [tp13112]) (by norm_num [tm13112])
    (by norm_num [ep13112]) (by norm_num [em13112])
    positive13112 negative13112 tails13112.1 tails13112.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13112.1 tailGuards13112.2

theorem preserves13112 : master13112.toScalarCertificate = scalar13112 := rfl

noncomputable def tp13113 : ℝ := (2351911911 / 10000000000)
noncomputable def tm13113 : ℝ := (-((767635511 / 1250000000)))
noncomputable def ep13113 : ℝ := (1639569276897963 / 3125000000000000000)
noncomputable def em13113 : ℝ := (10202240896830497 / 20000000000000000000)
noncomputable def bp13113 : ℝ := (2115838177300193131 / 5000000000000000000)
noncomputable def bm13113 : ℝ := (21669063537728277473 / 50000000000000000000)

theorem positive13113 :
    Eplus aL (agent13113.root+dsL) scalar13113.worldRadius world13113.frame
      agent13113.frame tp13113 ≤ -ep13113 := by
  apply positive_check (eT := (23140227386412727029 / 20000000000000000000)) (y := (19064480834508911057 / 50000000000000000000)) (u := (146417159254037470927 / 100000000000000000000))
  · norm_num [world13113, agent13113, scalar13113, tp13113, tm13113, ep13113, em13113, dsL]
  · norm_num [world13113, agent13113, scalar13113, tp13113, tm13113, ep13113, em13113, dsL]
  · norm_num [world13113, agent13113, scalar13113, tp13113, tm13113, ep13113, em13113, dsL]
  · norm_num [world13113, agent13113, scalar13113, tp13113, tm13113, ep13113, em13113, dsL]
  · norm_num [world13113, agent13113, scalar13113, tp13113, tm13113, ep13113, em13113, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13113, agent13113, tp13113, tm13113, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13113, agent13113, scalar13113, tp13113, tm13113, ep13113, em13113, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13113, agent13113, tp13113, tm13113, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13113, agent13113, scalar13113, tp13113, tm13113, ep13113, em13113, dsL]

theorem negative13113 :
    Eminus aL (agent13113.root+dsL) scalar13113.worldRadius world13113.frame
      agent13113.frame tm13113 ≤ -em13113 := by
  apply negative_check (lo := (68331182679340113163 / 100000000000000000000)) (hi := (17082795669835028291 / 25000000000000000000))
    (y := (-((17901477209689520137 / 25000000000000000000)))) (u := (9773485767404455687 / 20000000000000000000))
  · norm_num [world13113, agent13113, scalar13113, tp13113, tm13113, ep13113, em13113, dsL]
  · norm_num [world13113, agent13113, scalar13113, tp13113, tm13113, ep13113, em13113, dsL]
  · norm_num [world13113, agent13113, scalar13113, tp13113, tm13113, ep13113, em13113, dsL]
  · norm_num [world13113, agent13113, scalar13113, tp13113, tm13113, ep13113, em13113, dsL]
  · norm_num [world13113, agent13113, scalar13113, tp13113, tm13113, ep13113, em13113, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13113, agent13113, tp13113, tm13113, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13113, agent13113, tp13113, tm13113, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13113, agent13113, scalar13113, tp13113, tm13113, ep13113, em13113, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13113, agent13113, tp13113, tm13113, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13113, agent13113, scalar13113, tp13113, tm13113, ep13113, em13113, dsL]

theorem tails13113 :
    exp (-((13113:ℝ)*ep13113)) ≤ scalar13113.upperTail ∧
    exp (-((13113:ℝ)*em13113)) ≤ scalar13113.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13113:ℝ)) (by norm_num [ep13113]) ?_)
      (show bp13113^8 ≤ scalar13113.upperTail by norm_num [bp13113, scalar13113])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13113, bp13113, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13113:ℝ)) (by norm_num [em13113]) ?_)
      (show bm13113^8 ≤ scalar13113.lowerTail by norm_num [bm13113, scalar13113])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13113, bm13113, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13113 :
    agent13113.root+dsL+scalar13113.worldRadius < √(1/100/aL) ∧
    2*(agent13113.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13113, agent13113, scalar13113, tp13113, tm13113, ep13113, em13113, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13113, agent13113, scalar13113, tp13113, tm13113, ep13113, em13113, dsL]

noncomputable def master13113 : MasterCertificate 13113 world13113 agent13113 :=
  master scalar13113 dsL tp13113 tm13113 ep13113 em13113
    (by norm_num [dsL]) (by norm_num [tp13113]) (by norm_num [tm13113])
    (by norm_num [ep13113]) (by norm_num [em13113])
    positive13113 negative13113 tails13113.1 tails13113.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13113.1 tailGuards13113.2

theorem preserves13113 : master13113.toScalarCertificate = scalar13113 := rfl

noncomputable def tp13114 : ℝ := (1175992043 / 5000000000)
noncomputable def tm13114 : ℝ := (-((767654613 / 1250000000)))
noncomputable def ep13114 : ℝ := (52468378273474429 / 100000000000000000000)
noncomputable def em13114 : ℝ := (51013034400242783 / 100000000000000000000)
noncomputable def bp13114 : ℝ := (4231248918778958517 / 10000000000000000000)
noncomputable def bm13114 : ℝ := (43334063843925063627 / 100000000000000000000)

theorem positive13114 :
    Eplus aL (agent13114.root+dsL) scalar13114.worldRadius world13114.frame
      agent13114.frame tp13114 ≤ -ep13114 := by
  apply positive_check (eT := (57850650886443600379 / 50000000000000000000)) (y := (9532402581805280019 / 25000000000000000000)) (u := (73209054502016160189 / 50000000000000000000))
  · norm_num [world13114, agent13114, scalar13114, tp13114, tm13114, ep13114, em13114, dsL]
  · norm_num [world13114, agent13114, scalar13114, tp13114, tm13114, ep13114, em13114, dsL]
  · norm_num [world13114, agent13114, scalar13114, tp13114, tm13114, ep13114, em13114, dsL]
  · norm_num [world13114, agent13114, scalar13114, tp13114, tm13114, ep13114, em13114, dsL]
  · norm_num [world13114, agent13114, scalar13114, tp13114, tm13114, ep13114, em13114, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13114, agent13114, tp13114, tm13114, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13114, agent13114, scalar13114, tp13114, tm13114, ep13114, em13114, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13114, agent13114, tp13114, tm13114, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13114, agent13114, scalar13114, tp13114, tm13114, ep13114, em13114, dsL]

theorem negative13114 :
    Eminus aL (agent13114.root+dsL) scalar13114.worldRadius world13114.frame
      agent13114.frame tm13114 ≤ -em13114 := by
  apply negative_check (lo := (34165539746847784033 / 50000000000000000000)) (hi := (68331079493695568067 / 100000000000000000000))
    (y := (-((71605818712516213037 / 100000000000000000000)))) (u := (48867472879419233399 / 100000000000000000000))
  · norm_num [world13114, agent13114, scalar13114, tp13114, tm13114, ep13114, em13114, dsL]
  · norm_num [world13114, agent13114, scalar13114, tp13114, tm13114, ep13114, em13114, dsL]
  · norm_num [world13114, agent13114, scalar13114, tp13114, tm13114, ep13114, em13114, dsL]
  · norm_num [world13114, agent13114, scalar13114, tp13114, tm13114, ep13114, em13114, dsL]
  · norm_num [world13114, agent13114, scalar13114, tp13114, tm13114, ep13114, em13114, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13114, agent13114, tp13114, tm13114, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13114, agent13114, tp13114, tm13114, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13114, agent13114, scalar13114, tp13114, tm13114, ep13114, em13114, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13114, agent13114, tp13114, tm13114, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13114, agent13114, scalar13114, tp13114, tm13114, ep13114, em13114, dsL]

theorem tails13114 :
    exp (-((13114:ℝ)*ep13114)) ≤ scalar13114.upperTail ∧
    exp (-((13114:ℝ)*em13114)) ≤ scalar13114.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13114:ℝ)) (by norm_num [ep13114]) ?_)
      (show bp13114^8 ≤ scalar13114.upperTail by norm_num [bp13114, scalar13114])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13114, bp13114, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13114:ℝ)) (by norm_num [em13114]) ?_)
      (show bm13114^8 ≤ scalar13114.lowerTail by norm_num [bm13114, scalar13114])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13114, bm13114, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13114 :
    agent13114.root+dsL+scalar13114.worldRadius < √(1/100/aL) ∧
    2*(agent13114.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13114, agent13114, scalar13114, tp13114, tm13114, ep13114, em13114, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13114, agent13114, scalar13114, tp13114, tm13114, ep13114, em13114, dsL]

noncomputable def master13114 : MasterCertificate 13114 world13114 agent13114 :=
  master scalar13114 dsL tp13114 tm13114 ep13114 em13114
    (by norm_num [dsL]) (by norm_num [tp13114]) (by norm_num [tm13114])
    (by norm_num [ep13114]) (by norm_num [em13114])
    positive13114 negative13114 tails13114.1 tails13114.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13114.1 tailGuards13114.2

theorem preserves13114 : master13114.toScalarCertificate = scalar13114 := rfl

noncomputable def tp13115 : ℝ := (2352056243 / 10000000000)
noncomputable def tm13115 : ℝ := (-((1535347397 / 2500000000)))
noncomputable def ep13115 : ℝ := (52470538340575697 / 100000000000000000000)
noncomputable def em13115 : ℝ := (25507431546172273 / 50000000000000000000)
noncomputable def bp13115 : ℝ := (42308215966030291151 / 100000000000000000000)
noncomputable def bm13115 : ℝ := (43330001664571808343 / 100000000000000000000)

theorem positive13115 :
    Eplus aL (agent13115.root+dsL) scalar13115.worldRadius world13115.frame
      agent13115.frame tp13115 ≤ -ep13115 := by
  apply positive_check (eT := (115701466517599560689 / 100000000000000000000)) (y := (1191570588430280109 / 3125000000000000000)) (u := (146419058532278569779 / 100000000000000000000))
  · norm_num [world13115, agent13115, scalar13115, tp13115, tm13115, ep13115, em13115, dsL]
  · norm_num [world13115, agent13115, scalar13115, tp13115, tm13115, ep13115, em13115, dsL]
  · norm_num [world13115, agent13115, scalar13115, tp13115, tm13115, ep13115, em13115, dsL]
  · norm_num [world13115, agent13115, scalar13115, tp13115, tm13115, ep13115, em13115, dsL]
  · norm_num [world13115, agent13115, scalar13115, tp13115, tm13115, ep13115, em13115, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13115, agent13115, tp13115, tm13115, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13115, agent13115, scalar13115, tp13115, tm13115, ep13115, em13115, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13115, agent13115, tp13115, tm13115, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13115, agent13115, scalar13115, tp13115, tm13115, ep13115, em13115, dsL]

theorem negative13115 :
    Eminus aL (agent13115.root+dsL) scalar13115.worldRadius world13115.frame
      agent13115.frame tm13115 ≤ -em13115 := by
  apply negative_check (lo := (68330976810605348461 / 100000000000000000000)) (hi := (34165488405302674231 / 50000000000000000000))
    (y := (-((71605727360766992569 / 100000000000000000000)))) (u := (12216879380182724723 / 25000000000000000000))
  · norm_num [world13115, agent13115, scalar13115, tp13115, tm13115, ep13115, em13115, dsL]
  · norm_num [world13115, agent13115, scalar13115, tp13115, tm13115, ep13115, em13115, dsL]
  · norm_num [world13115, agent13115, scalar13115, tp13115, tm13115, ep13115, em13115, dsL]
  · norm_num [world13115, agent13115, scalar13115, tp13115, tm13115, ep13115, em13115, dsL]
  · norm_num [world13115, agent13115, scalar13115, tp13115, tm13115, ep13115, em13115, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13115, agent13115, tp13115, tm13115, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13115, agent13115, tp13115, tm13115, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13115, agent13115, scalar13115, tp13115, tm13115, ep13115, em13115, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13115, agent13115, tp13115, tm13115, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13115, agent13115, scalar13115, tp13115, tm13115, ep13115, em13115, dsL]

theorem tails13115 :
    exp (-((13115:ℝ)*ep13115)) ≤ scalar13115.upperTail ∧
    exp (-((13115:ℝ)*em13115)) ≤ scalar13115.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13115:ℝ)) (by norm_num [ep13115]) ?_)
      (show bp13115^8 ≤ scalar13115.upperTail by norm_num [bp13115, scalar13115])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13115, bp13115, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13115:ℝ)) (by norm_num [em13115]) ?_)
      (show bm13115^8 ≤ scalar13115.lowerTail by norm_num [bm13115, scalar13115])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13115, bm13115, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13115 :
    agent13115.root+dsL+scalar13115.worldRadius < √(1/100/aL) ∧
    2*(agent13115.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13115, agent13115, scalar13115, tp13115, tm13115, ep13115, em13115, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13115, agent13115, scalar13115, tp13115, tm13115, ep13115, em13115, dsL]

noncomputable def master13115 : MasterCertificate 13115 world13115 agent13115 :=
  master scalar13115 dsL tp13115 tm13115 ep13115 em13115
    (by norm_num [dsL]) (by norm_num [tp13115]) (by norm_num [tm13115])
    (by norm_num [ep13115]) (by norm_num [em13115])
    positive13115 negative13115 tails13115.1 tails13115.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13115.1 tailGuards13115.2

theorem preserves13115 : master13115.toScalarCertificate = scalar13115 := rfl

noncomputable def tp13116 : ℝ := (18376003 / 78125000)
noncomputable def tm13116 : ℝ := (-((1535385589 / 2500000000)))
noncomputable def ep13116 : ℝ := (26236348623843513 / 50000000000000000000)
noncomputable def em13116 : ℝ := (12754172674836617 / 25000000000000000000)
noncomputable def bp13116 : ℝ := (10575985937980395313 / 25000000000000000000)
noncomputable def bm13116 : ℝ := (43325940438714534173 / 100000000000000000000)

theorem positive13116 :
    Eplus aL (agent13116.root+dsL) scalar13116.worldRadius world13116.frame
      agent13116.frame tp13116 ≤ -ep13116 := by
  apply positive_check (eT := (14462703897573609187 / 12500000000000000000)) (y := (38130907466596000233 / 100000000000000000000)) (u := (73210004131647079929 / 50000000000000000000))
  · norm_num [world13116, agent13116, scalar13116, tp13116, tm13116, ep13116, em13116, dsL]
  · norm_num [world13116, agent13116, scalar13116, tp13116, tm13116, ep13116, em13116, dsL]
  · norm_num [world13116, agent13116, scalar13116, tp13116, tm13116, ep13116, em13116, dsL]
  · norm_num [world13116, agent13116, scalar13116, tp13116, tm13116, ep13116, em13116, dsL]
  · norm_num [world13116, agent13116, scalar13116, tp13116, tm13116, ep13116, em13116, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13116, agent13116, tp13116, tm13116, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13116, agent13116, scalar13116, tp13116, tm13116, ep13116, em13116, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13116, agent13116, tp13116, tm13116, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13116, agent13116, scalar13116, tp13116, tm13116, ep13116, em13116, dsL]

theorem negative13116 :
    Eminus aL (agent13116.root+dsL) scalar13116.worldRadius world13116.frame
      agent13116.frame tm13116 ≤ -em13116 := by
  apply negative_check (lo := (68330873714817819649 / 100000000000000000000)) (hi := (1366617474296356393 / 2000000000000000000))
    (y := (-((14321127510454629919 / 20000000000000000000)))) (u := (48867561407932069927 / 100000000000000000000))
  · norm_num [world13116, agent13116, scalar13116, tp13116, tm13116, ep13116, em13116, dsL]
  · norm_num [world13116, agent13116, scalar13116, tp13116, tm13116, ep13116, em13116, dsL]
  · norm_num [world13116, agent13116, scalar13116, tp13116, tm13116, ep13116, em13116, dsL]
  · norm_num [world13116, agent13116, scalar13116, tp13116, tm13116, ep13116, em13116, dsL]
  · norm_num [world13116, agent13116, scalar13116, tp13116, tm13116, ep13116, em13116, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13116, agent13116, tp13116, tm13116, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13116, agent13116, tp13116, tm13116, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13116, agent13116, scalar13116, tp13116, tm13116, ep13116, em13116, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13116, agent13116, tp13116, tm13116, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13116, agent13116, scalar13116, tp13116, tm13116, ep13116, em13116, dsL]

theorem tails13116 :
    exp (-((13116:ℝ)*ep13116)) ≤ scalar13116.upperTail ∧
    exp (-((13116:ℝ)*em13116)) ≤ scalar13116.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13116:ℝ)) (by norm_num [ep13116]) ?_)
      (show bp13116^8 ≤ scalar13116.upperTail by norm_num [bp13116, scalar13116])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13116, bp13116, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13116:ℝ)) (by norm_num [em13116]) ?_)
      (show bm13116^8 ≤ scalar13116.lowerTail by norm_num [bm13116, scalar13116])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13116, bm13116, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13116 :
    agent13116.root+dsL+scalar13116.worldRadius < √(1/100/aL) ∧
    2*(agent13116.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13116, agent13116, scalar13116, tp13116, tm13116, ep13116, em13116, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13116, agent13116, scalar13116, tp13116, tm13116, ep13116, em13116, dsL]

noncomputable def master13116 : MasterCertificate 13116 world13116 agent13116 :=
  master scalar13116 dsL tp13116 tm13116 ep13116 em13116
    (by norm_num [dsL]) (by norm_num [tp13116]) (by norm_num [tm13116])
    (by norm_num [ep13116]) (by norm_num [em13116])
    positive13116 negative13116 tails13116.1 tails13116.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13116.1 tailGuards13116.2

theorem preserves13116 : master13116.toScalarCertificate = scalar13116 := rfl

noncomputable def tp13117 : ℝ := (2352200559 / 10000000000)
noncomputable def tm13117 : ℝ := (-((1228339007 / 2000000000)))
noncomputable def ep13117 : ℝ := (5247485466961323 / 10000000000000000000)
noncomputable def em13117 : ℝ := (25509258467963371 / 50000000000000000000)
noncomputable def bp13117 : ℝ := (42299672770970430501 / 100000000000000000000)
noncomputable def bm13117 : ℝ := (13538087615312983 / 31250000000000000)

theorem positive13117 :
    Eplus aL (agent13117.root+dsL) scalar13117.worldRadius world13117.frame
      agent13117.frame tp13117 ≤ -ep13117 := by
  apply positive_check (eT := (57850898060269406453 / 50000000000000000000)) (y := (38131557005776671897 / 100000000000000000000)) (u := (73210479660852458901 / 50000000000000000000))
  · norm_num [world13117, agent13117, scalar13117, tp13117, tm13117, ep13117, em13117, dsL]
  · norm_num [world13117, agent13117, scalar13117, tp13117, tm13117, ep13117, em13117, dsL]
  · norm_num [world13117, agent13117, scalar13117, tp13117, tm13117, ep13117, em13117, dsL]
  · norm_num [world13117, agent13117, scalar13117, tp13117, tm13117, ep13117, em13117, dsL]
  · norm_num [world13117, agent13117, scalar13117, tp13117, tm13117, ep13117, em13117, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13117, agent13117, tp13117, tm13117, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13117, agent13117, scalar13117, tp13117, tm13117, ep13117, em13117, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13117, agent13117, tp13117, tm13117, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13117, agent13117, scalar13117, tp13117, tm13117, ep13117, em13117, dsL]

theorem negative13117 :
    Eminus aL (agent13117.root+dsL) scalar13117.worldRadius world13117.frame
      agent13117.frame tm13117 ≤ -em13117 := by
  apply negative_check (lo := (13666154187871330433 / 20000000000000000000)) (hi := (34165385469678326083 / 50000000000000000000))
    (y := (-((4475346700985517599 / 6250000000000000000)))) (u := (12216901388299749931 / 25000000000000000000))
  · norm_num [world13117, agent13117, scalar13117, tp13117, tm13117, ep13117, em13117, dsL]
  · norm_num [world13117, agent13117, scalar13117, tp13117, tm13117, ep13117, em13117, dsL]
  · norm_num [world13117, agent13117, scalar13117, tp13117, tm13117, ep13117, em13117, dsL]
  · norm_num [world13117, agent13117, scalar13117, tp13117, tm13117, ep13117, em13117, dsL]
  · norm_num [world13117, agent13117, scalar13117, tp13117, tm13117, ep13117, em13117, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13117, agent13117, tp13117, tm13117, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13117, agent13117, tp13117, tm13117, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13117, agent13117, scalar13117, tp13117, tm13117, ep13117, em13117, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13117, agent13117, tp13117, tm13117, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13117, agent13117, scalar13117, tp13117, tm13117, ep13117, em13117, dsL]

theorem tails13117 :
    exp (-((13117:ℝ)*ep13117)) ≤ scalar13117.upperTail ∧
    exp (-((13117:ℝ)*em13117)) ≤ scalar13117.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13117:ℝ)) (by norm_num [ep13117]) ?_)
      (show bp13117^8 ≤ scalar13117.upperTail by norm_num [bp13117, scalar13117])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13117, bp13117, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13117:ℝ)) (by norm_num [em13117]) ?_)
      (show bm13117^8 ≤ scalar13117.lowerTail by norm_num [bm13117, scalar13117])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13117, bm13117, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13117 :
    agent13117.root+dsL+scalar13117.worldRadius < √(1/100/aL) ∧
    2*(agent13117.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13117, agent13117, scalar13117, tp13117, tm13117, ep13117, em13117, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13117, agent13117, scalar13117, tp13117, tm13117, ep13117, em13117, dsL]

noncomputable def master13117 : MasterCertificate 13117 world13117 agent13117 :=
  master scalar13117 dsL tp13117 tm13117 ep13117 em13117
    (by norm_num [dsL]) (by norm_num [tp13117]) (by norm_num [tm13117])
    (by norm_num [ep13117]) (by norm_num [em13117])
    positive13117 negative13117 tails13117.1 tails13117.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13117.1 tailGuards13117.2

theorem preserves13117 : master13117.toScalarCertificate = scalar13117 := rfl

noncomputable def tp13118 : ℝ := (1176136283 / 5000000000)
noncomputable def tm13118 : ℝ := (-((383865471 / 625000000)))
noncomputable def ep13118 : ℝ := (2623850531908819 / 5000000000000000000)
noncomputable def em13118 : ℝ := (10204068367548389 / 20000000000000000000)
noncomputable def bp13118 : ℝ := (4229540300105616087 / 10000000000000000000)
noncomputable def bm13118 : ℝ := (10829455357518688989 / 25000000000000000000)

theorem positive13118 :
    Eplus aL (agent13118.root+dsL) scalar13118.worldRadius world13118.frame
      agent13118.frame tp13118 ≤ -ep13118 := by
  apply positive_check (eT := (57850979944148618151 / 50000000000000000000)) (y := (19066102014962883611 / 50000000000000000000)) (u := (146421906703735958233 / 100000000000000000000))
  · norm_num [world13118, agent13118, scalar13118, tp13118, tm13118, ep13118, em13118, dsL]
  · norm_num [world13118, agent13118, scalar13118, tp13118, tm13118, ep13118, em13118, dsL]
  · norm_num [world13118, agent13118, scalar13118, tp13118, tm13118, ep13118, em13118, dsL]
  · norm_num [world13118, agent13118, scalar13118, tp13118, tm13118, ep13118, em13118, dsL]
  · norm_num [world13118, agent13118, scalar13118, tp13118, tm13118, ep13118, em13118, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13118, agent13118, tp13118, tm13118, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13118, agent13118, scalar13118, tp13118, tm13118, ep13118, em13118, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13118, agent13118, tp13118, tm13118, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13118, agent13118, scalar13118, tp13118, tm13118, ep13118, em13118, dsL]

theorem negative13118 :
    Eminus aL (agent13118.root+dsL) scalar13118.worldRadius world13118.frame
      agent13118.frame tm13118 ≤ -em13118 := by
  apply negative_check (lo := (13666133772259571267 / 20000000000000000000)) (hi := (4270666803831116021 / 6250000000000000000))
    (y := (-((716054559090125269 / 1000000000000000000)))) (u := (48867650172644615627 / 100000000000000000000))
  · norm_num [world13118, agent13118, scalar13118, tp13118, tm13118, ep13118, em13118, dsL]
  · norm_num [world13118, agent13118, scalar13118, tp13118, tm13118, ep13118, em13118, dsL]
  · norm_num [world13118, agent13118, scalar13118, tp13118, tm13118, ep13118, em13118, dsL]
  · norm_num [world13118, agent13118, scalar13118, tp13118, tm13118, ep13118, em13118, dsL]
  · norm_num [world13118, agent13118, scalar13118, tp13118, tm13118, ep13118, em13118, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13118, agent13118, tp13118, tm13118, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13118, agent13118, tp13118, tm13118, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13118, agent13118, scalar13118, tp13118, tm13118, ep13118, em13118, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13118, agent13118, tp13118, tm13118, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13118, agent13118, scalar13118, tp13118, tm13118, ep13118, em13118, dsL]

theorem tails13118 :
    exp (-((13118:ℝ)*ep13118)) ≤ scalar13118.upperTail ∧
    exp (-((13118:ℝ)*em13118)) ≤ scalar13118.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13118:ℝ)) (by norm_num [ep13118]) ?_)
      (show bp13118^8 ≤ scalar13118.upperTail by norm_num [bp13118, scalar13118])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13118, bp13118, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13118:ℝ)) (by norm_num [em13118]) ?_)
      (show bm13118^8 ≤ scalar13118.lowerTail by norm_num [bm13118, scalar13118])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13118, bm13118, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13118 :
    agent13118.root+dsL+scalar13118.worldRadius < √(1/100/aL) ∧
    2*(agent13118.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13118, agent13118, scalar13118, tp13118, tm13118, ep13118, em13118, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13118, agent13118, scalar13118, tp13118, tm13118, ep13118, em13118, dsL]

noncomputable def master13118 : MasterCertificate 13118 world13118 agent13118 :=
  master scalar13118 dsL tp13118 tm13118 ep13118 em13118
    (by norm_num [dsL]) (by norm_num [tp13118]) (by norm_num [tm13118])
    (by norm_num [ep13118]) (by norm_num [em13118])
    positive13118 negative13118 tails13118.1 tails13118.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13118.1 tailGuards13118.2

theorem preserves13118 : master13118.toScalarCertificate = scalar13118 := rfl

noncomputable def tp13119 : ℝ := (2352344647 / 10000000000)
noncomputable def tm13119 : ℝ := (-((3070999971 / 5000000000)))
noncomputable def ep13119 : ℝ := (52479166852068589 / 100000000000000000000)
noncomputable def em13119 : ℝ := (51022166950971221 / 100000000000000000000)
noncomputable def bp13119 : ℝ := (42291133264049681613 / 100000000000000000000)
noncomputable def bm13119 : ℝ := (433137625236664003 / 1000000000000000000)

theorem positive13119 :
    Eplus aL (agent13119.root+dsL) scalar13119.worldRadius world13119.frame
      agent13119.frame tp13119 ≤ -ep13119 := by
  apply positive_check (eT := (115702124219975358681 / 100000000000000000000)) (y := (19066426252942944481 / 50000000000000000000)) (u := (36605714054419991337 / 25000000000000000000))
  · norm_num [world13119, agent13119, scalar13119, tp13119, tm13119, ep13119, em13119, dsL]
  · norm_num [world13119, agent13119, scalar13119, tp13119, tm13119, ep13119, em13119, dsL]
  · norm_num [world13119, agent13119, scalar13119, tp13119, tm13119, ep13119, em13119, dsL]
  · norm_num [world13119, agent13119, scalar13119, tp13119, tm13119, ep13119, em13119, dsL]
  · norm_num [world13119, agent13119, scalar13119, tp13119, tm13119, ep13119, em13119, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13119, agent13119, tp13119, tm13119, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13119, agent13119, scalar13119, tp13119, tm13119, ep13119, em13119, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13119, agent13119, tp13119, tm13119, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13119, agent13119, scalar13119, tp13119, tm13119, ep13119, em13119, dsL]

theorem negative13119 :
    Eminus aL (agent13119.root+dsL) scalar13119.worldRadius world13119.frame
      agent13119.frame tm13119 ≤ -em13119 := by
  apply negative_check (lo := (4270660445559210111 / 6250000000000000000)) (hi := (68330567128947361777 / 100000000000000000000))
    (y := (-((2237667637589045943 / 3125000000000000000)))) (u := (95444716581204539 / 195312500000000000))
  · norm_num [world13119, agent13119, scalar13119, tp13119, tm13119, ep13119, em13119, dsL]
  · norm_num [world13119, agent13119, scalar13119, tp13119, tm13119, ep13119, em13119, dsL]
  · norm_num [world13119, agent13119, scalar13119, tp13119, tm13119, ep13119, em13119, dsL]
  · norm_num [world13119, agent13119, scalar13119, tp13119, tm13119, ep13119, em13119, dsL]
  · norm_num [world13119, agent13119, scalar13119, tp13119, tm13119, ep13119, em13119, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13119, agent13119, tp13119, tm13119, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13119, agent13119, tp13119, tm13119, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13119, agent13119, scalar13119, tp13119, tm13119, ep13119, em13119, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13119, agent13119, tp13119, tm13119, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13119, agent13119, scalar13119, tp13119, tm13119, ep13119, em13119, dsL]

theorem tails13119 :
    exp (-((13119:ℝ)*ep13119)) ≤ scalar13119.upperTail ∧
    exp (-((13119:ℝ)*em13119)) ≤ scalar13119.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13119:ℝ)) (by norm_num [ep13119]) ?_)
      (show bp13119^8 ≤ scalar13119.upperTail by norm_num [bp13119, scalar13119])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13119, bp13119, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13119:ℝ)) (by norm_num [em13119]) ?_)
      (show bm13119^8 ≤ scalar13119.lowerTail by norm_num [bm13119, scalar13119])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13119, bm13119, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13119 :
    agent13119.root+dsL+scalar13119.worldRadius < √(1/100/aL) ∧
    2*(agent13119.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13119, agent13119, scalar13119, tp13119, tm13119, ep13119, em13119, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13119, agent13119, scalar13119, tp13119, tm13119, ep13119, em13119, dsL]

noncomputable def master13119 : MasterCertificate 13119 world13119 agent13119 :=
  master scalar13119 dsL tp13119 tm13119 ep13119 em13119
    (by norm_num [dsL]) (by norm_num [tp13119]) (by norm_num [tm13119])
    (by norm_num [ep13119]) (by norm_num [em13119])
    positive13119 negative13119 tails13119.1 tails13119.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13119.1 tailGuards13119.2

theorem preserves13119 : master13119.toScalarCertificate = scalar13119 := rfl

noncomputable def tp13120 : ℝ := (1176243743 / 5000000000)
noncomputable def tm13120 : ℝ := (-((6142366797 / 10000000000)))
noncomputable def ep13120 : ℝ := (10496531002363113 / 20000000000000000000)
noncomputable def em13120 : ℝ := (12756361826161139 / 25000000000000000000)
noncomputable def bp13120 : ℝ := (42285940029683774329 / 100000000000000000000)
noncomputable def bm13120 : ℝ := (43308670185366946053 / 100000000000000000000)

theorem positive13120 :
    Eplus aL (agent13120.root+dsL) scalar13120.worldRadius world13120.frame
      agent13120.frame tp13120 ≤ -ep13120 := by
  apply positive_check (eT := (3615712380394645587 / 3125000000000000000)) (y := (19066394827687856727 / 50000000000000000000)) (u := (7321138209509836943 / 5000000000000000000))
  · norm_num [world13120, agent13120, scalar13120, tp13120, tm13120, ep13120, em13120, dsL]
  · norm_num [world13120, agent13120, scalar13120, tp13120, tm13120, ep13120, em13120, dsL]
  · norm_num [world13120, agent13120, scalar13120, tp13120, tm13120, ep13120, em13120, dsL]
  · norm_num [world13120, agent13120, scalar13120, tp13120, tm13120, ep13120, em13120, dsL]
  · norm_num [world13120, agent13120, scalar13120, tp13120, tm13120, ep13120, em13120, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13120, agent13120, tp13120, tm13120, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13120, agent13120, scalar13120, tp13120, tm13120, ep13120, em13120, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13120, agent13120, tp13120, tm13120, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13120, agent13120, scalar13120, tp13120, tm13120, ep13120, em13120, dsL]

theorem negative13120 :
    Eminus aL (agent13120.root+dsL) scalar13120.worldRadius world13120.frame
      agent13120.frame tm13120 ≤ -em13120 := by
  apply negative_check (lo := (17082389208162941599 / 25000000000000000000)) (hi := (68329556832651766397 / 100000000000000000000))
    (y := (-((71603416911387696411 / 100000000000000000000)))) (u := (48868646593029405791 / 100000000000000000000))
  · norm_num [world13120, agent13120, scalar13120, tp13120, tm13120, ep13120, em13120, dsL]
  · norm_num [world13120, agent13120, scalar13120, tp13120, tm13120, ep13120, em13120, dsL]
  · norm_num [world13120, agent13120, scalar13120, tp13120, tm13120, ep13120, em13120, dsL]
  · norm_num [world13120, agent13120, scalar13120, tp13120, tm13120, ep13120, em13120, dsL]
  · norm_num [world13120, agent13120, scalar13120, tp13120, tm13120, ep13120, em13120, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13120, agent13120, tp13120, tm13120, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13120, agent13120, tp13120, tm13120, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13120, agent13120, scalar13120, tp13120, tm13120, ep13120, em13120, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13120, agent13120, tp13120, tm13120, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13120, agent13120, scalar13120, tp13120, tm13120, ep13120, em13120, dsL]

theorem tails13120 :
    exp (-((13120:ℝ)*ep13120)) ≤ scalar13120.upperTail ∧
    exp (-((13120:ℝ)*em13120)) ≤ scalar13120.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13120:ℝ)) (by norm_num [ep13120]) ?_)
      (show bp13120^8 ≤ scalar13120.upperTail by norm_num [bp13120, scalar13120])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13120, bp13120, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13120:ℝ)) (by norm_num [em13120]) ?_)
      (show bm13120^8 ≤ scalar13120.lowerTail by norm_num [bm13120, scalar13120])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13120, bm13120, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13120 :
    agent13120.root+dsL+scalar13120.worldRadius < √(1/100/aL) ∧
    2*(agent13120.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13120, agent13120, scalar13120, tp13120, tm13120, ep13120, em13120, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13120, agent13120, scalar13120, tp13120, tm13120, ep13120, em13120, dsL]

noncomputable def master13120 : MasterCertificate 13120 world13120 agent13120 :=
  master scalar13120 dsL tp13120 tm13120 ep13120 em13120
    (by norm_num [dsL]) (by norm_num [tp13120]) (by norm_num [tm13120])
    (by norm_num [ep13120]) (by norm_num [em13120])
    positive13120 negative13120 tails13120.1 tails13120.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13120.1 tailGuards13120.2

theorem preserves13120 : master13120.toScalarCertificate = scalar13120 := rfl

noncomputable def tp13121 : ℝ := (1176279731 / 5000000000)
noncomputable def tm13121 : ℝ := (-((6142519041 / 10000000000)))
noncomputable def ep13121 : ℝ := (52484808178813853 / 100000000000000000000)
noncomputable def em13121 : ℝ := (51027269592252651 / 100000000000000000000)
noncomputable def bp13121 : ℝ := (42281672834666540577 / 100000000000000000000)
noncomputable def bm13121 : ℝ := (10826153417345066409 / 25000000000000000000)

theorem positive13121 :
    Eplus aL (agent13121.root+dsL) scalar13121.worldRadius world13121.frame
      agent13121.frame tp13121 ≤ -ep13121 := by
  apply positive_check (eT := (28925739951814696567 / 25000000000000000000)) (y := (4766679626028526171 / 12500000000000000000)) (u := (36605928016301368027 / 25000000000000000000))
  · norm_num [world13121, agent13121, scalar13121, tp13121, tm13121, ep13121, em13121, dsL]
  · norm_num [world13121, agent13121, scalar13121, tp13121, tm13121, ep13121, em13121, dsL]
  · norm_num [world13121, agent13121, scalar13121, tp13121, tm13121, ep13121, em13121, dsL]
  · norm_num [world13121, agent13121, scalar13121, tp13121, tm13121, ep13121, em13121, dsL]
  · norm_num [world13121, agent13121, scalar13121, tp13121, tm13121, ep13121, em13121, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13121, agent13121, tp13121, tm13121, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13121, agent13121, scalar13121, tp13121, tm13121, ep13121, em13121, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13121, agent13121, tp13121, tm13121, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13121, agent13121, scalar13121, tp13121, tm13121, ep13121, em13121, dsL]

theorem negative13121 :
    Eminus aL (agent13121.root+dsL) scalar13121.worldRadius world13121.frame
      agent13121.frame tm13121 ≤ -em13121 := by
  apply negative_check (lo := (68329455693423802913 / 100000000000000000000)) (hi := (34164727846711901457 / 50000000000000000000))
    (y := (-((35801662353211468129 / 50000000000000000000)))) (u := (6108586456546068641 / 12500000000000000000))
  · norm_num [world13121, agent13121, scalar13121, tp13121, tm13121, ep13121, em13121, dsL]
  · norm_num [world13121, agent13121, scalar13121, tp13121, tm13121, ep13121, em13121, dsL]
  · norm_num [world13121, agent13121, scalar13121, tp13121, tm13121, ep13121, em13121, dsL]
  · norm_num [world13121, agent13121, scalar13121, tp13121, tm13121, ep13121, em13121, dsL]
  · norm_num [world13121, agent13121, scalar13121, tp13121, tm13121, ep13121, em13121, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13121, agent13121, tp13121, tm13121, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13121, agent13121, tp13121, tm13121, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13121, agent13121, scalar13121, tp13121, tm13121, ep13121, em13121, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13121, agent13121, tp13121, tm13121, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13121, agent13121, scalar13121, tp13121, tm13121, ep13121, em13121, dsL]

theorem tails13121 :
    exp (-((13121:ℝ)*ep13121)) ≤ scalar13121.upperTail ∧
    exp (-((13121:ℝ)*em13121)) ≤ scalar13121.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13121:ℝ)) (by norm_num [ep13121]) ?_)
      (show bp13121^8 ≤ scalar13121.upperTail by norm_num [bp13121, scalar13121])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13121, bp13121, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13121:ℝ)) (by norm_num [em13121]) ?_)
      (show bm13121^8 ≤ scalar13121.lowerTail by norm_num [bm13121, scalar13121])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13121, bm13121, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13121 :
    agent13121.root+dsL+scalar13121.worldRadius < √(1/100/aL) ∧
    2*(agent13121.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13121, agent13121, scalar13121, tp13121, tm13121, ep13121, em13121, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13121, agent13121, scalar13121, tp13121, tm13121, ep13121, em13121, dsL]

noncomputable def master13121 : MasterCertificate 13121 world13121 agent13121 :=
  master scalar13121 dsL tp13121 tm13121 ep13121 em13121
    (by norm_num [dsL]) (by norm_num [tp13121]) (by norm_num [tm13121])
    (by norm_num [ep13121]) (by norm_num [em13121])
    positive13121 negative13121 tails13121.1 tails13121.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13121.1 tailGuards13121.2

theorem preserves13121 : master13121.toScalarCertificate = scalar13121 := rfl

noncomputable def tp13122 : ℝ := (117631567 / 500000000)
noncomputable def tm13122 : ℝ := (-((1228534277 / 2000000000)))
noncomputable def ep13122 : ℝ := (1640217510319829 / 3125000000000000000)
noncomputable def em13122 : ℝ := (25514545472775243 / 50000000000000000000)
noncomputable def bp13122 : ℝ := (10569351636736472533 / 25000000000000000000)
noncomputable def bm13122 : ℝ := (21650278999832474539 / 50000000000000000000)

theorem positive13122 :
    Eplus aL (agent13122.root+dsL) scalar13122.worldRadius world13122.frame
      agent13122.frame tp13122 ≤ -ep13122 := by
  apply positive_check (eT := (28925780692985364953 / 25000000000000000000)) (y := (38134082914004256339 / 100000000000000000000)) (u := (73212328913736783463 / 50000000000000000000))
  · norm_num [world13122, agent13122, scalar13122, tp13122, tm13122, ep13122, em13122, dsL]
  · norm_num [world13122, agent13122, scalar13122, tp13122, tm13122, ep13122, em13122, dsL]
  · norm_num [world13122, agent13122, scalar13122, tp13122, tm13122, ep13122, em13122, dsL]
  · norm_num [world13122, agent13122, scalar13122, tp13122, tm13122, ep13122, em13122, dsL]
  · norm_num [world13122, agent13122, scalar13122, tp13122, tm13122, ep13122, em13122, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13122, agent13122, tp13122, tm13122, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13122, agent13122, scalar13122, tp13122, tm13122, ep13122, em13122, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13122, agent13122, tp13122, tm13122, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13122, agent13122, scalar13122, tp13122, tm13122, ep13122, em13122, dsL]

theorem negative13122 :
    Eminus aL (agent13122.root+dsL) scalar13122.worldRadius world13122.frame
      agent13122.frame tm13122 ≤ -em13122 := by
  apply negative_check (lo := (68329354073817167077 / 100000000000000000000)) (hi := (34164677036908583539 / 50000000000000000000))
    (y := (-((17900808477622928651 / 25000000000000000000)))) (u := (24434368011586177087 / 50000000000000000000))
  · norm_num [world13122, agent13122, scalar13122, tp13122, tm13122, ep13122, em13122, dsL]
  · norm_num [world13122, agent13122, scalar13122, tp13122, tm13122, ep13122, em13122, dsL]
  · norm_num [world13122, agent13122, scalar13122, tp13122, tm13122, ep13122, em13122, dsL]
  · norm_num [world13122, agent13122, scalar13122, tp13122, tm13122, ep13122, em13122, dsL]
  · norm_num [world13122, agent13122, scalar13122, tp13122, tm13122, ep13122, em13122, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13122, agent13122, tp13122, tm13122, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13122, agent13122, tp13122, tm13122, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13122, agent13122, scalar13122, tp13122, tm13122, ep13122, em13122, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13122, agent13122, tp13122, tm13122, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13122, agent13122, scalar13122, tp13122, tm13122, ep13122, em13122, dsL]

theorem tails13122 :
    exp (-((13122:ℝ)*ep13122)) ≤ scalar13122.upperTail ∧
    exp (-((13122:ℝ)*em13122)) ≤ scalar13122.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13122:ℝ)) (by norm_num [ep13122]) ?_)
      (show bp13122^8 ≤ scalar13122.upperTail by norm_num [bp13122, scalar13122])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13122, bp13122, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13122:ℝ)) (by norm_num [em13122]) ?_)
      (show bm13122^8 ≤ scalar13122.lowerTail by norm_num [bm13122, scalar13122])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13122, bm13122, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13122 :
    agent13122.root+dsL+scalar13122.worldRadius < √(1/100/aL) ∧
    2*(agent13122.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13122, agent13122, scalar13122, tp13122, tm13122, ep13122, em13122, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13122, agent13122, scalar13122, tp13122, tm13122, ep13122, em13122, dsL]

noncomputable def master13122 : MasterCertificate 13122 world13122 agent13122 :=
  master scalar13122 dsL tp13122 tm13122 ep13122 em13122
    (by norm_num [dsL]) (by norm_num [tp13122]) (by norm_num [tm13122])
    (by norm_num [ep13122]) (by norm_num [em13122])
    positive13122 negative13122 tails13122.1 tails13122.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13122.1 tailGuards13122.2

theorem preserves13122 : master13122.toScalarCertificate = scalar13122 := rfl

noncomputable def tp13123 : ℝ := (1176351641 / 5000000000)
noncomputable def tm13123 : ℝ := (-((3071411687 / 5000000000)))
noncomputable def ep13123 : ℝ := (26244555521224287 / 50000000000000000000)
noncomputable def em13123 : ℝ := (25515455488134337 / 50000000000000000000)
noncomputable def bp13123 : ℝ := (21136570730127771807 / 50000000000000000000)
noncomputable def bm13123 : ℝ := (2706031465747794873 / 6250000000000000000)

theorem positive13123 :
    Eplus aL (agent13123.root+dsL) scalar13123.worldRadius world13123.frame
      agent13123.frame tp13123 ≤ -ep13123 := by
  apply positive_check (eT := (57851643114402096313 / 50000000000000000000)) (y := (19067365173032205623 / 50000000000000000000)) (u := (73212802915360574639 / 50000000000000000000))
  · norm_num [world13123, agent13123, scalar13123, tp13123, tm13123, ep13123, em13123, dsL]
  · norm_num [world13123, agent13123, scalar13123, tp13123, tm13123, ep13123, em13123, dsL]
  · norm_num [world13123, agent13123, scalar13123, tp13123, tm13123, ep13123, em13123, dsL]
  · norm_num [world13123, agent13123, scalar13123, tp13123, tm13123, ep13123, em13123, dsL]
  · norm_num [world13123, agent13123, scalar13123, tp13123, tm13123, ep13123, em13123, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13123, agent13123, tp13123, tm13123, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13123, agent13123, scalar13123, tp13123, tm13123, ep13123, em13123, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13123, agent13123, tp13123, tm13123, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13123, agent13123, scalar13123, tp13123, tm13123, ep13123, em13123, dsL]

theorem negative13123 :
    Eminus aL (agent13123.root+dsL) scalar13123.worldRadius world13123.frame
      agent13123.frame tm13123 ≤ -em13123 := by
  apply negative_check (lo := (68329253901264909507 / 100000000000000000000)) (hi := (17082313475316227377 / 25000000000000000000))
    (y := (-((35801570224264275699 / 50000000000000000000)))) (u := (48868781696873758241 / 100000000000000000000))
  · norm_num [world13123, agent13123, scalar13123, tp13123, tm13123, ep13123, em13123, dsL]
  · norm_num [world13123, agent13123, scalar13123, tp13123, tm13123, ep13123, em13123, dsL]
  · norm_num [world13123, agent13123, scalar13123, tp13123, tm13123, ep13123, em13123, dsL]
  · norm_num [world13123, agent13123, scalar13123, tp13123, tm13123, ep13123, em13123, dsL]
  · norm_num [world13123, agent13123, scalar13123, tp13123, tm13123, ep13123, em13123, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13123, agent13123, tp13123, tm13123, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13123, agent13123, tp13123, tm13123, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13123, agent13123, scalar13123, tp13123, tm13123, ep13123, em13123, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13123, agent13123, tp13123, tm13123, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13123, agent13123, scalar13123, tp13123, tm13123, ep13123, em13123, dsL]

theorem tails13123 :
    exp (-((13123:ℝ)*ep13123)) ≤ scalar13123.upperTail ∧
    exp (-((13123:ℝ)*em13123)) ≤ scalar13123.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13123:ℝ)) (by norm_num [ep13123]) ?_)
      (show bp13123^8 ≤ scalar13123.upperTail by norm_num [bp13123, scalar13123])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13123, bp13123, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13123:ℝ)) (by norm_num [em13123]) ?_)
      (show bm13123^8 ≤ scalar13123.lowerTail by norm_num [bm13123, scalar13123])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13123, bm13123, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13123 :
    agent13123.root+dsL+scalar13123.worldRadius < √(1/100/aL) ∧
    2*(agent13123.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13123, agent13123, scalar13123, tp13123, tm13123, ep13123, em13123, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13123, agent13123, scalar13123, tp13123, tm13123, ep13123, em13123, dsL]

noncomputable def master13123 : MasterCertificate 13123 world13123 agent13123 :=
  master scalar13123 dsL tp13123 tm13123 ep13123 em13123
    (by norm_num [dsL]) (by norm_num [tp13123]) (by norm_num [tm13123])
    (by norm_num [ep13123]) (by norm_num [em13123])
    positive13123 negative13123 tails13123.1 tails13123.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13123.1 tailGuards13123.2

theorem preserves13123 : master13123.toScalarCertificate = scalar13123 := rfl

noncomputable def tp13124 : ℝ := (1176387581 / 5000000000)
noncomputable def tm13124 : ℝ := (-((1535743873 / 2500000000)))
noncomputable def ep13124 : ℝ := (52491261037372787 / 100000000000000000000)
noncomputable def em13124 : ℝ := (12758182581658131 / 25000000000000000000)
noncomputable def bp13124 : ℝ := (42268877073954765147 / 100000000000000000000)
noncomputable def bm13124 : ℝ := (5411556196266712013 / 12500000000000000000)

theorem positive13124 :
    Eplus aL (agent13124.root+dsL) scalar13124.worldRadius world13124.frame
      agent13124.frame tp13124 ≤ -ep13124 := by
  apply positive_check (eT := (11570344927394138709 / 10000000000000000000)) (y := (7627075391786150019 / 20000000000000000000)) (u := (146426552640589159243 / 100000000000000000000))
  · norm_num [world13124, agent13124, scalar13124, tp13124, tm13124, ep13124, em13124, dsL]
  · norm_num [world13124, agent13124, scalar13124, tp13124, tm13124, ep13124, em13124, dsL]
  · norm_num [world13124, agent13124, scalar13124, tp13124, tm13124, ep13124, em13124, dsL]
  · norm_num [world13124, agent13124, scalar13124, tp13124, tm13124, ep13124, em13124, dsL]
  · norm_num [world13124, agent13124, scalar13124, tp13124, tm13124, ep13124, em13124, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13124, agent13124, tp13124, tm13124, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13124, agent13124, scalar13124, tp13124, tm13124, ep13124, em13124, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13124, agent13124, tp13124, tm13124, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13124, agent13124, scalar13124, tp13124, tm13124, ep13124, em13124, dsL]

theorem negative13124 :
    Eminus aL (agent13124.root+dsL) scalar13124.worldRadius world13124.frame
      agent13124.frame tm13124 ≤ -em13124 := by
  apply negative_check (lo := (34164576562765353911 / 50000000000000000000)) (hi := (68329153125530707823 / 100000000000000000000))
    (y := (-((35801524338071774517 / 50000000000000000000)))) (u := (3054301659058801383 / 6250000000000000000))
  · norm_num [world13124, agent13124, scalar13124, tp13124, tm13124, ep13124, em13124, dsL]
  · norm_num [world13124, agent13124, scalar13124, tp13124, tm13124, ep13124, em13124, dsL]
  · norm_num [world13124, agent13124, scalar13124, tp13124, tm13124, ep13124, em13124, dsL]
  · norm_num [world13124, agent13124, scalar13124, tp13124, tm13124, ep13124, em13124, dsL]
  · norm_num [world13124, agent13124, scalar13124, tp13124, tm13124, ep13124, em13124, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13124, agent13124, tp13124, tm13124, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13124, agent13124, tp13124, tm13124, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13124, agent13124, scalar13124, tp13124, tm13124, ep13124, em13124, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13124, agent13124, tp13124, tm13124, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13124, agent13124, scalar13124, tp13124, tm13124, ep13124, em13124, dsL]

theorem tails13124 :
    exp (-((13124:ℝ)*ep13124)) ≤ scalar13124.upperTail ∧
    exp (-((13124:ℝ)*em13124)) ≤ scalar13124.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13124:ℝ)) (by norm_num [ep13124]) ?_)
      (show bp13124^8 ≤ scalar13124.upperTail by norm_num [bp13124, scalar13124])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13124, bp13124, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13124:ℝ)) (by norm_num [em13124]) ?_)
      (show bm13124^8 ≤ scalar13124.lowerTail by norm_num [bm13124, scalar13124])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13124, bm13124, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13124 :
    agent13124.root+dsL+scalar13124.worldRadius < √(1/100/aL) ∧
    2*(agent13124.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13124, agent13124, scalar13124, tp13124, tm13124, ep13124, em13124, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13124, agent13124, scalar13124, tp13124, tm13124, ep13124, em13124, dsL]

noncomputable def master13124 : MasterCertificate 13124 world13124 agent13124 :=
  master scalar13124 dsL tp13124 tm13124 ep13124 em13124
    (by norm_num [dsL]) (by norm_num [tp13124]) (by norm_num [tm13124])
    (by norm_num [ep13124]) (by norm_num [em13124])
    positive13124 negative13124 tails13124.1 tails13124.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13124.1 tailGuards13124.2

theorem preserves13124 : master13124.toScalarCertificate = scalar13124 := rfl

end BstLean.Part268
