import BstLean.Part261Checker
import BstLean.Part268Scalar33
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp13175 : ℝ := (2356763043 / 10000000000)
noncomputable def tm13175 : ℝ := (-((384483353 / 625000000)))
noncomputable def ep13175 : ℝ := (13151587845462477 / 25000000000000000000)
noncomputable def em13175 : ℝ := (25565851019007443 / 50000000000000000000)
noncomputable def bp13175 : ℝ := (5255986932581133949 / 12500000000000000000)
noncomputable def bm13175 : ℝ := (43081555895094780171 / 100000000000000000000)

theorem positive13175 :
    Eplus aL (agent13175.root+dsL) scalar13175.worldRadius world13175.frame
      agent13175.frame tp13175 ≤ -ep13175 := by
  apply positive_check (eT := (57857057840830812433 / 50000000000000000000)) (y := (19082157836518029953 / 50000000000000000000)) (u := (146468932733863335619 / 100000000000000000000))
  · norm_num [world13175, agent13175, scalar13175, tp13175, tm13175, ep13175, em13175, dsL]
  · norm_num [world13175, agent13175, scalar13175, tp13175, tm13175, ep13175, em13175, dsL]
  · norm_num [world13175, agent13175, scalar13175, tp13175, tm13175, ep13175, em13175, dsL]
  · norm_num [world13175, agent13175, scalar13175, tp13175, tm13175, ep13175, em13175, dsL]
  · norm_num [world13175, agent13175, scalar13175, tp13175, tm13175, ep13175, em13175, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13175, agent13175, tp13175, tm13175, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13175, agent13175, scalar13175, tp13175, tm13175, ep13175, em13175, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13175, agent13175, tp13175, tm13175, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13175, agent13175, scalar13175, tp13175, tm13175, ep13175, em13175, dsL]

theorem negative13175 :
    Eminus aL (agent13175.root+dsL) scalar13175.worldRadius world13175.frame
      agent13175.frame tm13175 ≤ -em13175 := by
  apply negative_check (lo := (34159853467634425053 / 50000000000000000000)) (hi := (68319706935268850107 / 100000000000000000000))
    (y := (-((71588415509948906569 / 100000000000000000000)))) (u := (48875978124785035573 / 100000000000000000000))
  · norm_num [world13175, agent13175, scalar13175, tp13175, tm13175, ep13175, em13175, dsL]
  · norm_num [world13175, agent13175, scalar13175, tp13175, tm13175, ep13175, em13175, dsL]
  · norm_num [world13175, agent13175, scalar13175, tp13175, tm13175, ep13175, em13175, dsL]
  · norm_num [world13175, agent13175, scalar13175, tp13175, tm13175, ep13175, em13175, dsL]
  · norm_num [world13175, agent13175, scalar13175, tp13175, tm13175, ep13175, em13175, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13175, agent13175, tp13175, tm13175, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13175, agent13175, tp13175, tm13175, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13175, agent13175, scalar13175, tp13175, tm13175, ep13175, em13175, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13175, agent13175, tp13175, tm13175, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13175, agent13175, scalar13175, tp13175, tm13175, ep13175, em13175, dsL]

theorem tails13175 :
    exp (-((13175:ℝ)*ep13175)) ≤ scalar13175.upperTail ∧
    exp (-((13175:ℝ)*em13175)) ≤ scalar13175.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13175:ℝ)) (by norm_num [ep13175]) ?_)
      (show bp13175^8 ≤ scalar13175.upperTail by norm_num [bp13175, scalar13175])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13175, bp13175, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13175:ℝ)) (by norm_num [em13175]) ?_)
      (show bm13175^8 ≤ scalar13175.lowerTail by norm_num [bm13175, scalar13175])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13175, bm13175, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13175 :
    agent13175.root+dsL+scalar13175.worldRadius < √(1/100/aL) ∧
    2*(agent13175.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13175, agent13175, scalar13175, tp13175, tm13175, ep13175, em13175, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13175, agent13175, scalar13175, tp13175, tm13175, ep13175, em13175, dsL]

noncomputable def master13175 : MasterCertificate 13175 world13175 agent13175 :=
  master scalar13175 dsL tp13175 tm13175 ep13175 em13175
    (by norm_num [dsL]) (by norm_num [tp13175]) (by norm_num [tm13175])
    (by norm_num [ep13175]) (by norm_num [em13175])
    positive13175 negative13175 tails13175.1 tails13175.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13175.1 tailGuards13175.2

theorem preserves13175 : master13175.toScalarCertificate = scalar13175 := rfl

noncomputable def tp13176 : ℝ := (2356833539 / 10000000000)
noncomputable def tm13176 : ℝ := (-((246075293 / 400000000)))
noncomputable def ep13176 : ℝ := (52608450109866889 / 100000000000000000000)
noncomputable def em13176 : ℝ := (25566737363723193 / 50000000000000000000)
noncomputable def bp13176 : ℝ := (21021838629808137589 / 50000000000000000000)
noncomputable def bm13176 : ℝ := (43077544722736160201 / 100000000000000000000)

theorem positive13176 :
    Eplus aL (agent13176.root+dsL) scalar13176.worldRadius world13176.frame
      agent13176.frame tp13176 ≤ -ep13176 := by
  apply positive_check (eT := (115714270472266256887 / 100000000000000000000)) (y := (7632989392109392431 / 20000000000000000000)) (u := (146469857376861611127 / 100000000000000000000))
  · norm_num [world13176, agent13176, scalar13176, tp13176, tm13176, ep13176, em13176, dsL]
  · norm_num [world13176, agent13176, scalar13176, tp13176, tm13176, ep13176, em13176, dsL]
  · norm_num [world13176, agent13176, scalar13176, tp13176, tm13176, ep13176, em13176, dsL]
  · norm_num [world13176, agent13176, scalar13176, tp13176, tm13176, ep13176, em13176, dsL]
  · norm_num [world13176, agent13176, scalar13176, tp13176, tm13176, ep13176, em13176, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13176, agent13176, tp13176, tm13176, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13176, agent13176, scalar13176, tp13176, tm13176, ep13176, em13176, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13176, agent13176, tp13176, tm13176, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13176, agent13176, scalar13176, tp13176, tm13176, ep13176, em13176, dsL]

theorem negative13176 :
    Eminus aL (agent13176.root+dsL) scalar13176.worldRadius world13176.frame
      agent13176.frame tm13176 ≤ -em13176 := by
  apply negative_check (lo := (68319617880573473021 / 100000000000000000000)) (hi := (34159808940286736511 / 50000000000000000000))
    (y := (-((35794151792559770811 / 50000000000000000000)))) (u := (48876032829170766077 / 100000000000000000000))
  · norm_num [world13176, agent13176, scalar13176, tp13176, tm13176, ep13176, em13176, dsL]
  · norm_num [world13176, agent13176, scalar13176, tp13176, tm13176, ep13176, em13176, dsL]
  · norm_num [world13176, agent13176, scalar13176, tp13176, tm13176, ep13176, em13176, dsL]
  · norm_num [world13176, agent13176, scalar13176, tp13176, tm13176, ep13176, em13176, dsL]
  · norm_num [world13176, agent13176, scalar13176, tp13176, tm13176, ep13176, em13176, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13176, agent13176, tp13176, tm13176, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13176, agent13176, tp13176, tm13176, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13176, agent13176, scalar13176, tp13176, tm13176, ep13176, em13176, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13176, agent13176, tp13176, tm13176, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13176, agent13176, scalar13176, tp13176, tm13176, ep13176, em13176, dsL]

theorem tails13176 :
    exp (-((13176:ℝ)*ep13176)) ≤ scalar13176.upperTail ∧
    exp (-((13176:ℝ)*em13176)) ≤ scalar13176.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13176:ℝ)) (by norm_num [ep13176]) ?_)
      (show bp13176^8 ≤ scalar13176.upperTail by norm_num [bp13176, scalar13176])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13176, bp13176, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13176:ℝ)) (by norm_num [em13176]) ?_)
      (show bm13176^8 ≤ scalar13176.lowerTail by norm_num [bm13176, scalar13176])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13176, bm13176, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13176 :
    agent13176.root+dsL+scalar13176.worldRadius < √(1/100/aL) ∧
    2*(agent13176.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13176, agent13176, scalar13176, tp13176, tm13176, ep13176, em13176, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13176, agent13176, scalar13176, tp13176, tm13176, ep13176, em13176, dsL]

noncomputable def master13176 : MasterCertificate 13176 world13176 agent13176 :=
  master scalar13176 dsL tp13176 tm13176 ep13176 em13176
    (by norm_num [dsL]) (by norm_num [tp13176]) (by norm_num [tm13176])
    (by norm_num [ep13176]) (by norm_num [em13176])
    positive13176 negative13176 tails13176.1 tails13176.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13176.1 tailGuards13176.2

theorem preserves13176 : master13176.toScalarCertificate = scalar13176 := rfl

noncomputable def tp13177 : ℝ := (18855231 / 80000000)
noncomputable def tm13177 : ℝ := (-((307601547 / 500000000)))
noncomputable def ep13177 : ℝ := (52610547227410197 / 100000000000000000000)
noncomputable def em13177 : ℝ := (51135245913466099 / 100000000000000000000)
noncomputable def bp13177 : ℝ := (2627466273520991893 / 6250000000000000000)
noncomputable def bm13177 : ℝ := (43073534799586719381 / 100000000000000000000)

theorem positive13177 :
    Eplus aL (agent13177.root+dsL) scalar13177.worldRadius world13177.frame
      agent13177.frame tp13177 ≤ -ep13177 := by
  apply positive_check (eT := (115714424149342654831 / 100000000000000000000)) (y := (954139397994641639 / 2500000000000000000)) (u := (29294155723091720639 / 20000000000000000000))
  · norm_num [world13177, agent13177, scalar13177, tp13177, tm13177, ep13177, em13177, dsL]
  · norm_num [world13177, agent13177, scalar13177, tp13177, tm13177, ep13177, em13177, dsL]
  · norm_num [world13177, agent13177, scalar13177, tp13177, tm13177, ep13177, em13177, dsL]
  · norm_num [world13177, agent13177, scalar13177, tp13177, tm13177, ep13177, em13177, dsL]
  · norm_num [world13177, agent13177, scalar13177, tp13177, tm13177, ep13177, em13177, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13177, agent13177, tp13177, tm13177, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13177, agent13177, scalar13177, tp13177, tm13177, ep13177, em13177, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13177, agent13177, tp13177, tm13177, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13177, agent13177, scalar13177, tp13177, tm13177, ep13177, em13177, dsL]

theorem negative13177 :
    Eminus aL (agent13177.root+dsL) scalar13177.worldRadius world13177.frame
      agent13177.frame tm13177 ≤ -em13177 := by
  apply negative_check (lo := (68319529031562616131 / 100000000000000000000)) (hi := (17079882257890654033 / 25000000000000000000))
    (y := (-((8948523958300816419 / 12500000000000000000)))) (u := (2443804376531414477 / 5000000000000000000))
  · norm_num [world13177, agent13177, scalar13177, tp13177, tm13177, ep13177, em13177, dsL]
  · norm_num [world13177, agent13177, scalar13177, tp13177, tm13177, ep13177, em13177, dsL]
  · norm_num [world13177, agent13177, scalar13177, tp13177, tm13177, ep13177, em13177, dsL]
  · norm_num [world13177, agent13177, scalar13177, tp13177, tm13177, ep13177, em13177, dsL]
  · norm_num [world13177, agent13177, scalar13177, tp13177, tm13177, ep13177, em13177, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13177, agent13177, tp13177, tm13177, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13177, agent13177, tp13177, tm13177, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13177, agent13177, scalar13177, tp13177, tm13177, ep13177, em13177, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13177, agent13177, tp13177, tm13177, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13177, agent13177, scalar13177, tp13177, tm13177, ep13177, em13177, dsL]

theorem tails13177 :
    exp (-((13177:ℝ)*ep13177)) ≤ scalar13177.upperTail ∧
    exp (-((13177:ℝ)*em13177)) ≤ scalar13177.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13177:ℝ)) (by norm_num [ep13177]) ?_)
      (show bp13177^8 ≤ scalar13177.upperTail by norm_num [bp13177, scalar13177])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13177, bp13177, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13177:ℝ)) (by norm_num [em13177]) ?_)
      (show bm13177^8 ≤ scalar13177.lowerTail by norm_num [bm13177, scalar13177])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13177, bm13177, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13177 :
    agent13177.root+dsL+scalar13177.worldRadius < √(1/100/aL) ∧
    2*(agent13177.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13177, agent13177, scalar13177, tp13177, tm13177, ep13177, em13177, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13177, agent13177, scalar13177, tp13177, tm13177, ep13177, em13177, dsL]

noncomputable def master13177 : MasterCertificate 13177 world13177 agent13177 :=
  master scalar13177 dsL tp13177 tm13177 ep13177 em13177
    (by norm_num [dsL]) (by norm_num [tp13177]) (by norm_num [tm13177])
    (by norm_num [ep13177]) (by norm_num [em13177])
    positive13177 negative13177 tails13177.1 tails13177.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13177.1 tailGuards13177.2

theorem preserves13177 : master13177.toScalarCertificate = scalar13177 := rfl

noncomputable def tp13178 : ℝ := (2356974483 / 10000000000)
noncomputable def tm13178 : ℝ := (-((6152180151 / 10000000000)))
noncomputable def ep13178 : ℝ := (52612646694325787 / 100000000000000000000)
noncomputable def em13178 : ℝ := (25568509918267613 / 50000000000000000000)
noncomputable def bp13178 : ℝ := (42035242068851589241 / 100000000000000000000)
noncomputable def bm13178 : ℝ := (21534761558580351593 / 50000000000000000000)

theorem positive13178 :
    Eplus aL (agent13178.root+dsL) scalar13178.worldRadius world13178.frame
      agent13178.frame tp13178 ≤ -ep13178 := by
  apply positive_check (eT := (57857289904278547491 / 50000000000000000000)) (y := (4770775623563282063 / 12500000000000000000)) (u := (36617925005052452639 / 25000000000000000000))
  · norm_num [world13178, agent13178, scalar13178, tp13178, tm13178, ep13178, em13178, dsL]
  · norm_num [world13178, agent13178, scalar13178, tp13178, tm13178, ep13178, em13178, dsL]
  · norm_num [world13178, agent13178, scalar13178, tp13178, tm13178, ep13178, em13178, dsL]
  · norm_num [world13178, agent13178, scalar13178, tp13178, tm13178, ep13178, em13178, dsL]
  · norm_num [world13178, agent13178, scalar13178, tp13178, tm13178, ep13178, em13178, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13178, agent13178, tp13178, tm13178, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13178, agent13178, scalar13178, tp13178, tm13178, ep13178, em13178, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13178, agent13178, tp13178, tm13178, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13178, agent13178, scalar13178, tp13178, tm13178, ep13178, em13178, dsL]

theorem negative13178 :
    Eminus aL (agent13178.root+dsL) scalar13178.worldRadius world13178.frame
      agent13178.frame tm13178 ≤ -em13178 := by
  apply negative_check (lo := (34159718802183706677 / 50000000000000000000)) (hi := (13663887520873482671 / 20000000000000000000))
    (y := (-((14317615214769276949 / 20000000000000000000)))) (u := (48876144027781818937 / 100000000000000000000))
  · norm_num [world13178, agent13178, scalar13178, tp13178, tm13178, ep13178, em13178, dsL]
  · norm_num [world13178, agent13178, scalar13178, tp13178, tm13178, ep13178, em13178, dsL]
  · norm_num [world13178, agent13178, scalar13178, tp13178, tm13178, ep13178, em13178, dsL]
  · norm_num [world13178, agent13178, scalar13178, tp13178, tm13178, ep13178, em13178, dsL]
  · norm_num [world13178, agent13178, scalar13178, tp13178, tm13178, ep13178, em13178, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13178, agent13178, tp13178, tm13178, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13178, agent13178, tp13178, tm13178, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13178, agent13178, scalar13178, tp13178, tm13178, ep13178, em13178, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13178, agent13178, tp13178, tm13178, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13178, agent13178, scalar13178, tp13178, tm13178, ep13178, em13178, dsL]

theorem tails13178 :
    exp (-((13178:ℝ)*ep13178)) ≤ scalar13178.upperTail ∧
    exp (-((13178:ℝ)*em13178)) ≤ scalar13178.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13178:ℝ)) (by norm_num [ep13178]) ?_)
      (show bp13178^8 ≤ scalar13178.upperTail by norm_num [bp13178, scalar13178])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13178, bp13178, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13178:ℝ)) (by norm_num [em13178]) ?_)
      (show bm13178^8 ≤ scalar13178.lowerTail by norm_num [bm13178, scalar13178])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13178, bm13178, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13178 :
    agent13178.root+dsL+scalar13178.worldRadius < √(1/100/aL) ∧
    2*(agent13178.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13178, agent13178, scalar13178, tp13178, tm13178, ep13178, em13178, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13178, agent13178, scalar13178, tp13178, tm13178, ep13178, em13178, dsL]

noncomputable def master13178 : MasterCertificate 13178 world13178 agent13178 :=
  master scalar13178 dsL tp13178 tm13178 ep13178 em13178
    (by norm_num [dsL]) (by norm_num [tp13178]) (by norm_num [tm13178])
    (by norm_num [ep13178]) (by norm_num [em13178])
    positive13178 negative13178 tails13178.1 tails13178.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13178.1 tailGuards13178.2

theorem preserves13178 : master13178.toScalarCertificate = scalar13178 := rfl

noncomputable def tp13179 : ℝ := (23570451 / 100000000)
noncomputable def tm13179 : ℝ := (-((769041181 / 1250000000)))
noncomputable def ep13179 : ℝ := (10522949421371413 / 20000000000000000000)
noncomputable def em13179 : ℝ := (51138794977801783 / 100000000000000000000)
noncomputable def bp13179 : ℝ := (10507755827319958653 / 25000000000000000000)
noncomputable def bm13179 : ℝ := (10766377688281853433 / 25000000000000000000)

theorem positive13179 :
    Eplus aL (agent13179.root+dsL) scalar13179.worldRadius world13179.frame
      agent13179.frame tp13179 ≤ -ep13179 := by
  apply positive_check (eT := (11571473556521319491 / 10000000000000000000)) (y := (38166831520218970541 / 100000000000000000000)) (u := (36618154428683852289 / 25000000000000000000))
  · norm_num [world13179, agent13179, scalar13179, tp13179, tm13179, ep13179, em13179, dsL]
  · norm_num [world13179, agent13179, scalar13179, tp13179, tm13179, ep13179, em13179, dsL]
  · norm_num [world13179, agent13179, scalar13179, tp13179, tm13179, ep13179, em13179, dsL]
  · norm_num [world13179, agent13179, scalar13179, tp13179, tm13179, ep13179, em13179, dsL]
  · norm_num [world13179, agent13179, scalar13179, tp13179, tm13179, ep13179, em13179, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13179, agent13179, tp13179, tm13179, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13179, agent13179, scalar13179, tp13179, tm13179, ep13179, em13179, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13179, agent13179, tp13179, tm13179, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13179, agent13179, scalar13179, tp13179, tm13179, ep13179, em13179, dsL]

theorem negative13179 :
    Eminus aL (agent13179.root+dsL) scalar13179.worldRadius world13179.frame
      agent13179.frame tm13179 ≤ -em13179 := by
  apply negative_check (lo := (68319345756844828441 / 100000000000000000000)) (hi := (34159672878422414221 / 50000000000000000000))
    (y := (-((35793977886882135667 / 50000000000000000000)))) (u := (48876202825858585287 / 100000000000000000000))
  · norm_num [world13179, agent13179, scalar13179, tp13179, tm13179, ep13179, em13179, dsL]
  · norm_num [world13179, agent13179, scalar13179, tp13179, tm13179, ep13179, em13179, dsL]
  · norm_num [world13179, agent13179, scalar13179, tp13179, tm13179, ep13179, em13179, dsL]
  · norm_num [world13179, agent13179, scalar13179, tp13179, tm13179, ep13179, em13179, dsL]
  · norm_num [world13179, agent13179, scalar13179, tp13179, tm13179, ep13179, em13179, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13179, agent13179, tp13179, tm13179, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13179, agent13179, tp13179, tm13179, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13179, agent13179, scalar13179, tp13179, tm13179, ep13179, em13179, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13179, agent13179, tp13179, tm13179, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13179, agent13179, scalar13179, tp13179, tm13179, ep13179, em13179, dsL]

theorem tails13179 :
    exp (-((13179:ℝ)*ep13179)) ≤ scalar13179.upperTail ∧
    exp (-((13179:ℝ)*em13179)) ≤ scalar13179.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13179:ℝ)) (by norm_num [ep13179]) ?_)
      (show bp13179^8 ≤ scalar13179.upperTail by norm_num [bp13179, scalar13179])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13179, bp13179, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13179:ℝ)) (by norm_num [em13179]) ?_)
      (show bm13179^8 ≤ scalar13179.lowerTail by norm_num [bm13179, scalar13179])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13179, bm13179, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13179 :
    agent13179.root+dsL+scalar13179.worldRadius < √(1/100/aL) ∧
    2*(agent13179.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13179, agent13179, scalar13179, tp13179, tm13179, ep13179, em13179, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13179, agent13179, scalar13179, tp13179, tm13179, ep13179, em13179, dsL]

noncomputable def master13179 : MasterCertificate 13179 world13179 agent13179 :=
  master scalar13179 dsL tp13179 tm13179 ep13179 em13179
    (by norm_num [dsL]) (by norm_num [tp13179]) (by norm_num [tm13179])
    (by norm_num [ep13179]) (by norm_num [em13179])
    positive13179 negative13179 tails13179.1 tails13179.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13179.1 tailGuards13179.2

theorem preserves13179 : master13179.toScalarCertificate = scalar13179 := rfl

noncomputable def tp13180 : ℝ := (2357185923 / 10000000000)
noncomputable def tm13180 : ℝ := (-((6152691733 / 10000000000)))
noncomputable def ep13180 : ℝ := (13154542000564979 / 25000000000000000000)
noncomputable def em13180 : ℝ := (51142013224723247 / 100000000000000000000)
noncomputable def bp13180 : ℝ := (42025890471114961153 / 100000000000000000000)
noncomputable def bm13180 : ℝ := (1345639837177939329 / 3125000000000000000)

theorem positive13180 :
    Eplus aL (agent13180.root+dsL) scalar13180.worldRadius world13180.frame
      agent13180.frame tp13180 ≤ -ep13180 := by
  apply positive_check (eT := (72322121505681761 / 62500000000000000)) (y := (9541687019932235843 / 25000000000000000000)) (u := (36618123874329105443 / 25000000000000000000))
  · norm_num [world13180, agent13180, scalar13180, tp13180, tm13180, ep13180, em13180, dsL]
  · norm_num [world13180, agent13180, scalar13180, tp13180, tm13180, ep13180, em13180, dsL]
  · norm_num [world13180, agent13180, scalar13180, tp13180, tm13180, ep13180, em13180, dsL]
  · norm_num [world13180, agent13180, scalar13180, tp13180, tm13180, ep13180, em13180, dsL]
  · norm_num [world13180, agent13180, scalar13180, tp13180, tm13180, ep13180, em13180, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13180, agent13180, tp13180, tm13180, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13180, agent13180, scalar13180, tp13180, tm13180, ep13180, em13180, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13180, agent13180, tp13180, tm13180, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13180, agent13180, scalar13180, tp13180, tm13180, ep13180, em13180, dsL]

theorem negative13180 :
    Eminus aL (agent13180.root+dsL) scalar13180.worldRadius world13180.frame
      agent13180.frame tm13180 ≤ -em13180 := by
  apply negative_check (lo := (68318352809255524779 / 100000000000000000000)) (hi := (3415917640462776239 / 5000000000000000000))
    (y := (-((71585987501706063631 / 100000000000000000000)))) (u := (9775432970393906819 / 20000000000000000000))
  · norm_num [world13180, agent13180, scalar13180, tp13180, tm13180, ep13180, em13180, dsL]
  · norm_num [world13180, agent13180, scalar13180, tp13180, tm13180, ep13180, em13180, dsL]
  · norm_num [world13180, agent13180, scalar13180, tp13180, tm13180, ep13180, em13180, dsL]
  · norm_num [world13180, agent13180, scalar13180, tp13180, tm13180, ep13180, em13180, dsL]
  · norm_num [world13180, agent13180, scalar13180, tp13180, tm13180, ep13180, em13180, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13180, agent13180, tp13180, tm13180, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13180, agent13180, tp13180, tm13180, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13180, agent13180, scalar13180, tp13180, tm13180, ep13180, em13180, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13180, agent13180, tp13180, tm13180, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13180, agent13180, scalar13180, tp13180, tm13180, ep13180, em13180, dsL]

theorem tails13180 :
    exp (-((13180:ℝ)*ep13180)) ≤ scalar13180.upperTail ∧
    exp (-((13180:ℝ)*em13180)) ≤ scalar13180.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13180:ℝ)) (by norm_num [ep13180]) ?_)
      (show bp13180^8 ≤ scalar13180.upperTail by norm_num [bp13180, scalar13180])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13180, bp13180, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13180:ℝ)) (by norm_num [em13180]) ?_)
      (show bm13180^8 ≤ scalar13180.lowerTail by norm_num [bm13180, scalar13180])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13180, bm13180, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13180 :
    agent13180.root+dsL+scalar13180.worldRadius < √(1/100/aL) ∧
    2*(agent13180.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13180, agent13180, scalar13180, tp13180, tm13180, ep13180, em13180, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13180, agent13180, scalar13180, tp13180, tm13180, ep13180, em13180, dsL]

noncomputable def master13180 : MasterCertificate 13180 world13180 agent13180 :=
  master scalar13180 dsL tp13180 tm13180 ep13180 em13180
    (by norm_num [dsL]) (by norm_num [tp13180]) (by norm_num [tm13180])
    (by norm_num [ep13180]) (by norm_num [em13180])
    positive13180 negative13180 tails13180.1 tails13180.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13180.1 tailGuards13180.2

theorem preserves13180 : master13180.toScalarCertificate = scalar13180 := rfl

noncomputable def tp13181 : ℝ := (2357256473 / 10000000000)
noncomputable def tm13181 : ℝ := (-((6152840901 / 10000000000)))
noncomputable def ep13181 : ℝ := (13155066594573133 / 25000000000000000000)
noncomputable def em13181 : ℝ := (63929733094493 / 125000000000000000)
noncomputable def bp13181 : ℝ := (5252709193675801423 / 12500000000000000000)
noncomputable def bm13181 : ℝ := (43056464149842797533 / 100000000000000000000)

theorem positive13181 :
    Eplus aL (agent13181.root+dsL) scalar13181.worldRadius world13181.frame
      agent13181.frame tp13181 ≤ -ep13181 := by
  apply positive_check (eT := (28928887435451860143 / 25000000000000000000)) (y := (19083687021177510957 / 50000000000000000000)) (u := (3661835309081633391 / 2500000000000000000))
  · norm_num [world13181, agent13181, scalar13181, tp13181, tm13181, ep13181, em13181, dsL]
  · norm_num [world13181, agent13181, scalar13181, tp13181, tm13181, ep13181, em13181, dsL]
  · norm_num [world13181, agent13181, scalar13181, tp13181, tm13181, ep13181, em13181, dsL]
  · norm_num [world13181, agent13181, scalar13181, tp13181, tm13181, ep13181, em13181, dsL]
  · norm_num [world13181, agent13181, scalar13181, tp13181, tm13181, ep13181, em13181, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13181, agent13181, tp13181, tm13181, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13181, agent13181, scalar13181, tp13181, tm13181, ep13181, em13181, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13181, agent13181, tp13181, tm13181, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13181, agent13181, scalar13181, tp13181, tm13181, ep13181, em13181, dsL]

theorem negative13181 :
    Eminus aL (agent13181.root+dsL) scalar13181.worldRadius world13181.frame
      agent13181.frame tm13181 ≤ -em13181 := by
  apply negative_check (lo := (68318261414411238379 / 100000000000000000000)) (hi := (3415913070720561919 / 5000000000000000000))
    (y := (-((14317173411371434247 / 20000000000000000000)))) (u := (48877223722032335909 / 100000000000000000000))
  · norm_num [world13181, agent13181, scalar13181, tp13181, tm13181, ep13181, em13181, dsL]
  · norm_num [world13181, agent13181, scalar13181, tp13181, tm13181, ep13181, em13181, dsL]
  · norm_num [world13181, agent13181, scalar13181, tp13181, tm13181, ep13181, em13181, dsL]
  · norm_num [world13181, agent13181, scalar13181, tp13181, tm13181, ep13181, em13181, dsL]
  · norm_num [world13181, agent13181, scalar13181, tp13181, tm13181, ep13181, em13181, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13181, agent13181, tp13181, tm13181, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13181, agent13181, tp13181, tm13181, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13181, agent13181, scalar13181, tp13181, tm13181, ep13181, em13181, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13181, agent13181, tp13181, tm13181, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13181, agent13181, scalar13181, tp13181, tm13181, ep13181, em13181, dsL]

theorem tails13181 :
    exp (-((13181:ℝ)*ep13181)) ≤ scalar13181.upperTail ∧
    exp (-((13181:ℝ)*em13181)) ≤ scalar13181.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13181:ℝ)) (by norm_num [ep13181]) ?_)
      (show bp13181^8 ≤ scalar13181.upperTail by norm_num [bp13181, scalar13181])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13181, bp13181, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13181:ℝ)) (by norm_num [em13181]) ?_)
      (show bm13181^8 ≤ scalar13181.lowerTail by norm_num [bm13181, scalar13181])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13181, bm13181, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13181 :
    agent13181.root+dsL+scalar13181.worldRadius < √(1/100/aL) ∧
    2*(agent13181.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13181, agent13181, scalar13181, tp13181, tm13181, ep13181, em13181, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13181, agent13181, scalar13181, tp13181, tm13181, ep13181, em13181, dsL]

noncomputable def master13181 : MasterCertificate 13181 world13181 agent13181 :=
  master scalar13181 dsL tp13181 tm13181 ep13181 em13181
    (by norm_num [dsL]) (by norm_num [tp13181]) (by norm_num [tm13181])
    (by norm_num [ep13181]) (by norm_num [em13181])
    positive13181 negative13181 tails13181.1 tails13181.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13181.1 tailGuards13181.2

theorem preserves13181 : master13181.toScalarCertificate = scalar13181 := rfl

noncomputable def tp13182 : ℝ := (94293079 / 400000000)
noncomputable def tm13182 : ℝ := (-((384561879 / 625000000)))
noncomputable def ep13182 : ℝ := (13155590908401453 / 25000000000000000000)
noncomputable def em13182 : ℝ := (51145558676495013 / 100000000000000000000)
noncomputable def bp13182 : ℝ := (21008728803164460827 / 50000000000000000000)
noncomputable def bm13182 : ℝ := (2690778402345630843 / 6250000000000000000)

theorem positive13182 :
    Eplus aL (agent13182.root+dsL) scalar13182.worldRadius world13182.frame
      agent13182.frame tp13182 ≤ -ep13182 := by
  apply positive_check (eT := (115715704763581955451 / 100000000000000000000)) (y := (38167999575945779831 / 100000000000000000000)) (u := (36618582151631724731 / 25000000000000000000))
  · norm_num [world13182, agent13182, scalar13182, tp13182, tm13182, ep13182, em13182, dsL]
  · norm_num [world13182, agent13182, scalar13182, tp13182, tm13182, ep13182, em13182, dsL]
  · norm_num [world13182, agent13182, scalar13182, tp13182, tm13182, ep13182, em13182, dsL]
  · norm_num [world13182, agent13182, scalar13182, tp13182, tm13182, ep13182, em13182, dsL]
  · norm_num [world13182, agent13182, scalar13182, tp13182, tm13182, ep13182, em13182, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13182, agent13182, tp13182, tm13182, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13182, agent13182, scalar13182, tp13182, tm13182, ep13182, em13182, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13182, agent13182, tp13182, tm13182, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13182, agent13182, scalar13182, tp13182, tm13182, ep13182, em13182, dsL]

theorem negative13182 :
    Eminus aL (agent13182.root+dsL) scalar13182.worldRadius world13182.frame
      agent13182.frame tm13182 ≤ -em13182 := by
  apply negative_check (lo := (68318169984195919157 / 100000000000000000000)) (hi := (34159084992097959579 / 50000000000000000000))
    (y := (-((35792873644894606459 / 50000000000000000000)))) (u := (48877282260885142341 / 100000000000000000000))
  · norm_num [world13182, agent13182, scalar13182, tp13182, tm13182, ep13182, em13182, dsL]
  · norm_num [world13182, agent13182, scalar13182, tp13182, tm13182, ep13182, em13182, dsL]
  · norm_num [world13182, agent13182, scalar13182, tp13182, tm13182, ep13182, em13182, dsL]
  · norm_num [world13182, agent13182, scalar13182, tp13182, tm13182, ep13182, em13182, dsL]
  · norm_num [world13182, agent13182, scalar13182, tp13182, tm13182, ep13182, em13182, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13182, agent13182, tp13182, tm13182, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13182, agent13182, tp13182, tm13182, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13182, agent13182, scalar13182, tp13182, tm13182, ep13182, em13182, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13182, agent13182, tp13182, tm13182, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13182, agent13182, scalar13182, tp13182, tm13182, ep13182, em13182, dsL]

theorem tails13182 :
    exp (-((13182:ℝ)*ep13182)) ≤ scalar13182.upperTail ∧
    exp (-((13182:ℝ)*em13182)) ≤ scalar13182.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13182:ℝ)) (by norm_num [ep13182]) ?_)
      (show bp13182^8 ≤ scalar13182.upperTail by norm_num [bp13182, scalar13182])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13182, bp13182, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13182:ℝ)) (by norm_num [em13182]) ?_)
      (show bm13182^8 ≤ scalar13182.lowerTail by norm_num [bm13182, scalar13182])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13182, bm13182, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13182 :
    agent13182.root+dsL+scalar13182.worldRadius < √(1/100/aL) ∧
    2*(agent13182.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13182, agent13182, scalar13182, tp13182, tm13182, ep13182, em13182, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13182, agent13182, scalar13182, tp13182, tm13182, ep13182, em13182, dsL]

noncomputable def master13182 : MasterCertificate 13182 world13182 agent13182 :=
  master scalar13182 dsL tp13182 tm13182 ep13182 em13182
    (by norm_num [dsL]) (by norm_num [tp13182]) (by norm_num [tm13182])
    (by norm_num [ep13182]) (by norm_num [em13182])
    positive13182 negative13182 tails13182.1 tails13182.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13182.1 tailGuards13182.2

theorem preserves13182 : master13182.toScalarCertificate = scalar13182 := rfl

noncomputable def tp13183 : ℝ := (94295899 / 400000000)
noncomputable def tm13183 : ℝ := (-((1538284731 / 2500000000)))
noncomputable def ep13183 : ℝ := (13156114855808183 / 25000000000000000000)
noncomputable def em13183 : ℝ := (159835404765877 / 312500000000000000)
noncomputable def bp13183 : ℝ := (21006621440339475867 / 50000000000000000000)
noncomputable def bm13183 : ℝ := (21524222933607182707 / 50000000000000000000)

theorem positive13183 :
    Eplus aL (agent13183.root+dsL) scalar13183.worldRadius world13183.frame
      agent13183.frame tp13183 ≤ -ep13183 := by
  apply positive_check (eT := (14464482475500264389 / 12500000000000000000)) (y := (19084312688990888003 / 50000000000000000000)) (u := (146475245248725710077 / 100000000000000000000))
  · norm_num [world13183, agent13183, scalar13183, tp13183, tm13183, ep13183, em13183, dsL]
  · norm_num [world13183, agent13183, scalar13183, tp13183, tm13183, ep13183, em13183, dsL]
  · norm_num [world13183, agent13183, scalar13183, tp13183, tm13183, ep13183, em13183, dsL]
  · norm_num [world13183, agent13183, scalar13183, tp13183, tm13183, ep13183, em13183, dsL]
  · norm_num [world13183, agent13183, scalar13183, tp13183, tm13183, ep13183, em13183, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13183, agent13183, tp13183, tm13183, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13183, agent13183, scalar13183, tp13183, tm13183, ep13183, em13183, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13183, agent13183, tp13183, tm13183, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13183, agent13183, scalar13183, tp13183, tm13183, ep13183, em13183, dsL]

theorem negative13183 :
    Eminus aL (agent13183.root+dsL) scalar13183.worldRadius world13183.frame
      agent13183.frame tm13183 ≤ -em13183 := by
  apply negative_check (lo := (34159039889619317843 / 50000000000000000000)) (hi := (68318079779238635687 / 100000000000000000000))
    (y := (-((14317124987700230477 / 20000000000000000000)))) (u := (2443867103145307089 / 5000000000000000000))
  · norm_num [world13183, agent13183, scalar13183, tp13183, tm13183, ep13183, em13183, dsL]
  · norm_num [world13183, agent13183, scalar13183, tp13183, tm13183, ep13183, em13183, dsL]
  · norm_num [world13183, agent13183, scalar13183, tp13183, tm13183, ep13183, em13183, dsL]
  · norm_num [world13183, agent13183, scalar13183, tp13183, tm13183, ep13183, em13183, dsL]
  · norm_num [world13183, agent13183, scalar13183, tp13183, tm13183, ep13183, em13183, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13183, agent13183, tp13183, tm13183, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13183, agent13183, tp13183, tm13183, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13183, agent13183, scalar13183, tp13183, tm13183, ep13183, em13183, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13183, agent13183, tp13183, tm13183, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13183, agent13183, scalar13183, tp13183, tm13183, ep13183, em13183, dsL]

theorem tails13183 :
    exp (-((13183:ℝ)*ep13183)) ≤ scalar13183.upperTail ∧
    exp (-((13183:ℝ)*em13183)) ≤ scalar13183.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13183:ℝ)) (by norm_num [ep13183]) ?_)
      (show bp13183^8 ≤ scalar13183.upperTail by norm_num [bp13183, scalar13183])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13183, bp13183, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13183:ℝ)) (by norm_num [em13183]) ?_)
      (show bm13183^8 ≤ scalar13183.lowerTail by norm_num [bm13183, scalar13183])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13183, bm13183, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13183 :
    agent13183.root+dsL+scalar13183.worldRadius < √(1/100/aL) ∧
    2*(agent13183.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13183, agent13183, scalar13183, tp13183, tm13183, ep13183, em13183, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13183, agent13183, scalar13183, tp13183, tm13183, ep13183, em13183, dsL]

noncomputable def master13183 : MasterCertificate 13183 world13183 agent13183 :=
  master scalar13183 dsL tp13183 tm13183 ep13183 em13183
    (by norm_num [dsL]) (by norm_num [tp13183]) (by norm_num [tm13183])
    (by norm_num [ep13183]) (by norm_num [em13183])
    positive13183 negative13183 tails13183.1 tails13183.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13183.1 tailGuards13183.2

theorem preserves13183 : master13183.toScalarCertificate = scalar13183 := rfl

noncomputable def tp13184 : ℝ := (2357467963 / 10000000000)
noncomputable def tm13184 : ℝ := (-((153832201 / 250000000)))
noncomputable def ep13184 : ℝ := (6578319320946097 / 12500000000000000000)
noncomputable def em13184 : ℝ := (10229819952978837 / 20000000000000000000)
noncomputable def bp13184 : ℝ := (164097768767339361 / 390625000000000000)
noncomputable def bm13184 : ℝ := (43044437911415667709 / 100000000000000000000)

theorem positive13184 :
    Eplus aL (agent13184.root+dsL) scalar13184.worldRadius world13184.frame
      agent13184.frame tp13184 ≤ -ep13184 := by
  apply positive_check (eT := (57858007395685258931 / 50000000000000000000)) (y := (9542312831939368573 / 25000000000000000000)) (u := (36619040528266087533 / 25000000000000000000))
  · norm_num [world13184, agent13184, scalar13184, tp13184, tm13184, ep13184, em13184, dsL]
  · norm_num [world13184, agent13184, scalar13184, tp13184, tm13184, ep13184, em13184, dsL]
  · norm_num [world13184, agent13184, scalar13184, tp13184, tm13184, ep13184, em13184, dsL]
  · norm_num [world13184, agent13184, scalar13184, tp13184, tm13184, ep13184, em13184, dsL]
  · norm_num [world13184, agent13184, scalar13184, tp13184, tm13184, ep13184, em13184, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13184, agent13184, tp13184, tm13184, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13184, agent13184, scalar13184, tp13184, tm13184, ep13184, em13184, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13184, agent13184, tp13184, tm13184, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13184, agent13184, scalar13184, tp13184, tm13184, ep13184, em13184, dsL]

theorem negative13184 :
    Eminus aL (agent13184.root+dsL) scalar13184.worldRadius world13184.frame
      agent13184.frame tm13184 ≤ -em13184 := by
  apply negative_check (lo := (13663597686982657063 / 20000000000000000000)) (hi := (17079497108728321329 / 25000000000000000000))
    (y := (-((2237047058965981367 / 3125000000000000000)))) (u := (2443870012609676609 / 5000000000000000000))
  · norm_num [world13184, agent13184, scalar13184, tp13184, tm13184, ep13184, em13184, dsL]
  · norm_num [world13184, agent13184, scalar13184, tp13184, tm13184, ep13184, em13184, dsL]
  · norm_num [world13184, agent13184, scalar13184, tp13184, tm13184, ep13184, em13184, dsL]
  · norm_num [world13184, agent13184, scalar13184, tp13184, tm13184, ep13184, em13184, dsL]
  · norm_num [world13184, agent13184, scalar13184, tp13184, tm13184, ep13184, em13184, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13184, agent13184, tp13184, tm13184, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13184, agent13184, tp13184, tm13184, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13184, agent13184, scalar13184, tp13184, tm13184, ep13184, em13184, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13184, agent13184, tp13184, tm13184, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13184, agent13184, scalar13184, tp13184, tm13184, ep13184, em13184, dsL]

theorem tails13184 :
    exp (-((13184:ℝ)*ep13184)) ≤ scalar13184.upperTail ∧
    exp (-((13184:ℝ)*em13184)) ≤ scalar13184.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13184:ℝ)) (by norm_num [ep13184]) ?_)
      (show bp13184^8 ≤ scalar13184.upperTail by norm_num [bp13184, scalar13184])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13184, bp13184, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13184:ℝ)) (by norm_num [em13184]) ?_)
      (show bm13184^8 ≤ scalar13184.lowerTail by norm_num [bm13184, scalar13184])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13184, bm13184, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13184 :
    agent13184.root+dsL+scalar13184.worldRadius < √(1/100/aL) ∧
    2*(agent13184.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13184, agent13184, scalar13184, tp13184, tm13184, ep13184, em13184, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13184, agent13184, scalar13184, tp13184, tm13184, ep13184, em13184, dsL]

noncomputable def master13184 : MasterCertificate 13184 world13184 agent13184 :=
  master scalar13184 dsL tp13184 tm13184 ep13184 em13184
    (by norm_num [dsL]) (by norm_num [tp13184]) (by norm_num [tm13184])
    (by norm_num [ep13184]) (by norm_num [em13184])
    positive13184 negative13184 tails13184.1 tails13184.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13184.1 tailGuards13184.2

theorem preserves13184 : master13184.toScalarCertificate = scalar13184 := rfl

noncomputable def tp13185 : ℝ := (1178769187 / 5000000000)
noncomputable def tm13185 : ℝ := (-((769179619 / 1250000000)))
noncomputable def ep13185 : ℝ := (526286490204033 / 1000000000000000000)
noncomputable def em13185 : ℝ := (10230173869566803 / 20000000000000000000)
noncomputable def bp13185 : ℝ := (21002407704795494249 / 50000000000000000000)
noncomputable def bm13185 : ℝ := (860808612085029839 / 2000000000000000000)

theorem positive13185 :
    Eplus aL (agent13185.root+dsL) scalar13185.worldRadius world13185.frame
      agent13185.frame tp13185 ≤ -ep13185 := by
  apply positive_check (eT := (115716169260044624137 / 100000000000000000000)) (y := (3816987619221072399 / 10000000000000000000)) (u := (146477077393393506807 / 100000000000000000000))
  · norm_num [world13185, agent13185, scalar13185, tp13185, tm13185, ep13185, em13185, dsL]
  · norm_num [world13185, agent13185, scalar13185, tp13185, tm13185, ep13185, em13185, dsL]
  · norm_num [world13185, agent13185, scalar13185, tp13185, tm13185, ep13185, em13185, dsL]
  · norm_num [world13185, agent13185, scalar13185, tp13185, tm13185, ep13185, em13185, dsL]
  · norm_num [world13185, agent13185, scalar13185, tp13185, tm13185, ep13185, em13185, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13185, agent13185, tp13185, tm13185, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13185, agent13185, scalar13185, tp13185, tm13185, ep13185, em13185, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13185, agent13185, tp13185, tm13185, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13185, agent13185, scalar13185, tp13185, tm13185, ep13185, em13185, dsL]

theorem negative13185 :
    Eminus aL (agent13185.root+dsL) scalar13185.worldRadius world13185.frame
      agent13185.frame tm13185 ≤ -em13185 := by
  apply negative_check (lo := (2732715915879981837 / 4000000000000000000)) (hi := (34158948948499772963 / 50000000000000000000))
    (y := (-((71585385327856968867 / 100000000000000000000)))) (u := (48877459178360628983 / 100000000000000000000))
  · norm_num [world13185, agent13185, scalar13185, tp13185, tm13185, ep13185, em13185, dsL]
  · norm_num [world13185, agent13185, scalar13185, tp13185, tm13185, ep13185, em13185, dsL]
  · norm_num [world13185, agent13185, scalar13185, tp13185, tm13185, ep13185, em13185, dsL]
  · norm_num [world13185, agent13185, scalar13185, tp13185, tm13185, ep13185, em13185, dsL]
  · norm_num [world13185, agent13185, scalar13185, tp13185, tm13185, ep13185, em13185, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13185, agent13185, tp13185, tm13185, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13185, agent13185, tp13185, tm13185, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13185, agent13185, scalar13185, tp13185, tm13185, ep13185, em13185, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13185, agent13185, tp13185, tm13185, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13185, agent13185, scalar13185, tp13185, tm13185, ep13185, em13185, dsL]

theorem tails13185 :
    exp (-((13185:ℝ)*ep13185)) ≤ scalar13185.upperTail ∧
    exp (-((13185:ℝ)*em13185)) ≤ scalar13185.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13185:ℝ)) (by norm_num [ep13185]) ?_)
      (show bp13185^8 ≤ scalar13185.upperTail by norm_num [bp13185, scalar13185])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13185, bp13185, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13185:ℝ)) (by norm_num [em13185]) ?_)
      (show bm13185^8 ≤ scalar13185.lowerTail by norm_num [bm13185, scalar13185])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13185, bm13185, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13185 :
    agent13185.root+dsL+scalar13185.worldRadius < √(1/100/aL) ∧
    2*(agent13185.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13185, agent13185, scalar13185, tp13185, tm13185, ep13185, em13185, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13185, agent13185, scalar13185, tp13185, tm13185, ep13185, em13185, dsL]

noncomputable def master13185 : MasterCertificate 13185 world13185 agent13185 :=
  master scalar13185 dsL tp13185 tm13185 ep13185 em13185
    (by norm_num [dsL]) (by norm_num [tp13185]) (by norm_num [tm13185])
    (by norm_num [ep13185]) (by norm_num [em13185])
    positive13185 negative13185 tails13185.1 tails13185.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13185.1 tailGuards13185.2

theorem preserves13185 : master13185.toScalarCertificate = scalar13185 := rfl

noncomputable def tp13186 : ℝ := (235760871 / 1000000000)
noncomputable def tm13186 : ℝ := (-((384599107 / 625000000)))
noncomputable def ep13186 : ℝ := (5263074172773399 / 10000000000000000000)
noncomputable def em13186 : ℝ := (6394079667550523 / 12500000000000000000)
noncomputable def bp13186 : ℝ := (8400120685156670053 / 20000000000000000000)
noncomputable def bm13186 : ℝ := (2689776537993095139 / 6250000000000000000)

theorem positive13186 :
    Eplus aL (agent13186.root+dsL) scalar13186.worldRadius world13186.frame
      agent13186.frame tp13186 ≤ -ep13186 := by
  apply positive_check (eT := (115716323224336071933 / 100000000000000000000)) (y := (19085250026826055323 / 50000000000000000000)) (u := (146477991210250306823 / 100000000000000000000))
  · norm_num [world13186, agent13186, scalar13186, tp13186, tm13186, ep13186, em13186, dsL]
  · norm_num [world13186, agent13186, scalar13186, tp13186, tm13186, ep13186, em13186, dsL]
  · norm_num [world13186, agent13186, scalar13186, tp13186, tm13186, ep13186, em13186, dsL]
  · norm_num [world13186, agent13186, scalar13186, tp13186, tm13186, ep13186, em13186, dsL]
  · norm_num [world13186, agent13186, scalar13186, tp13186, tm13186, ep13186, em13186, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13186, agent13186, tp13186, tm13186, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13186, agent13186, scalar13186, tp13186, tm13186, ep13186, em13186, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13186, agent13186, tp13186, tm13186, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13186, agent13186, scalar13186, tp13186, tm13186, ep13186, em13186, dsL]

theorem negative13186 :
    Eminus aL (agent13186.root+dsL) scalar13186.worldRadius world13186.frame
      agent13186.frame tm13186 ≤ -em13186 := by
  apply negative_check (lo := (68317807945563722581 / 100000000000000000000)) (hi := (34158903972781861291 / 50000000000000000000))
    (y := (-((7158526362440341567 / 10000000000000000000)))) (u := (6109689832994082013 / 12500000000000000000))
  · norm_num [world13186, agent13186, scalar13186, tp13186, tm13186, ep13186, em13186, dsL]
  · norm_num [world13186, agent13186, scalar13186, tp13186, tm13186, ep13186, em13186, dsL]
  · norm_num [world13186, agent13186, scalar13186, tp13186, tm13186, ep13186, em13186, dsL]
  · norm_num [world13186, agent13186, scalar13186, tp13186, tm13186, ep13186, em13186, dsL]
  · norm_num [world13186, agent13186, scalar13186, tp13186, tm13186, ep13186, em13186, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13186, agent13186, tp13186, tm13186, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13186, agent13186, tp13186, tm13186, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13186, agent13186, scalar13186, tp13186, tm13186, ep13186, em13186, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13186, agent13186, tp13186, tm13186, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13186, agent13186, scalar13186, tp13186, tm13186, ep13186, em13186, dsL]

theorem tails13186 :
    exp (-((13186:ℝ)*ep13186)) ≤ scalar13186.upperTail ∧
    exp (-((13186:ℝ)*em13186)) ≤ scalar13186.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13186:ℝ)) (by norm_num [ep13186]) ?_)
      (show bp13186^8 ≤ scalar13186.upperTail by norm_num [bp13186, scalar13186])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13186, bp13186, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13186:ℝ)) (by norm_num [em13186]) ?_)
      (show bm13186^8 ≤ scalar13186.lowerTail by norm_num [bm13186, scalar13186])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13186, bm13186, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13186 :
    agent13186.root+dsL+scalar13186.worldRadius < √(1/100/aL) ∧
    2*(agent13186.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13186, agent13186, scalar13186, tp13186, tm13186, ep13186, em13186, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13186, agent13186, scalar13186, tp13186, tm13186, ep13186, em13186, dsL]

noncomputable def master13186 : MasterCertificate 13186 world13186 agent13186 :=
  master scalar13186 dsL tp13186 tm13186 ep13186 em13186
    (by norm_num [dsL]) (by norm_num [tp13186]) (by norm_num [tm13186])
    (by norm_num [ep13186]) (by norm_num [em13186])
    positive13186 negative13186 tails13186.1 tails13186.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13186.1 tailGuards13186.2

theorem preserves13186 : master13186.toScalarCertificate = scalar13186 := rfl

noncomputable def tp13187 : ℝ := (2357679113 / 10000000000)
noncomputable def tm13187 : ℝ := (-((6153734337 / 10000000000)))
noncomputable def ep13187 : ℝ := (26316416820233029 / 50000000000000000000)
noncomputable def em13187 : ℝ := (51154404569460657 / 100000000000000000000)
noncomputable def bp13187 : ℝ := (5249549024334918739 / 12500000000000000000)
noncomputable def bm13187 : ℝ := (21516209667885708593 / 50000000000000000000)

theorem positive13187 :
    Eplus aL (agent13187.root+dsL) scalar13187.worldRadius world13187.frame
      agent13187.frame tp13187 ≤ -ep13187 := by
  apply positive_check (eT := (7232279856350318451 / 6250000000000000000)) (y := (9542781397399678101 / 25000000000000000000)) (u := (146478907485604999971 / 100000000000000000000))
  · norm_num [world13187, agent13187, scalar13187, tp13187, tm13187, ep13187, em13187, dsL]
  · norm_num [world13187, agent13187, scalar13187, tp13187, tm13187, ep13187, em13187, dsL]
  · norm_num [world13187, agent13187, scalar13187, tp13187, tm13187, ep13187, em13187, dsL]
  · norm_num [world13187, agent13187, scalar13187, tp13187, tm13187, ep13187, em13187, dsL]
  · norm_num [world13187, agent13187, scalar13187, tp13187, tm13187, ep13187, em13187, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13187, agent13187, tp13187, tm13187, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13187, agent13187, scalar13187, tp13187, tm13187, ep13187, em13187, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13187, agent13187, tp13187, tm13187, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13187, agent13187, scalar13187, tp13187, tm13187, ep13187, em13187, dsL]

theorem negative13187 :
    Eminus aL (agent13187.root+dsL) scalar13187.worldRadius world13187.frame
      agent13187.frame tm13187 ≤ -em13187 := by
  apply negative_check (lo := (13663543701738564987 / 20000000000000000000)) (hi := (8539714813586603117 / 12500000000000000000))
    (y := (-((143170283537384337 / 200000000000000000)))) (u := (48877578224036952707 / 100000000000000000000))
  · norm_num [world13187, agent13187, scalar13187, tp13187, tm13187, ep13187, em13187, dsL]
  · norm_num [world13187, agent13187, scalar13187, tp13187, tm13187, ep13187, em13187, dsL]
  · norm_num [world13187, agent13187, scalar13187, tp13187, tm13187, ep13187, em13187, dsL]
  · norm_num [world13187, agent13187, scalar13187, tp13187, tm13187, ep13187, em13187, dsL]
  · norm_num [world13187, agent13187, scalar13187, tp13187, tm13187, ep13187, em13187, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13187, agent13187, tp13187, tm13187, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13187, agent13187, tp13187, tm13187, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13187, agent13187, scalar13187, tp13187, tm13187, ep13187, em13187, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13187, agent13187, tp13187, tm13187, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13187, agent13187, scalar13187, tp13187, tm13187, ep13187, em13187, dsL]

theorem tails13187 :
    exp (-((13187:ℝ)*ep13187)) ≤ scalar13187.upperTail ∧
    exp (-((13187:ℝ)*em13187)) ≤ scalar13187.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13187:ℝ)) (by norm_num [ep13187]) ?_)
      (show bp13187^8 ≤ scalar13187.upperTail by norm_num [bp13187, scalar13187])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13187, bp13187, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13187:ℝ)) (by norm_num [em13187]) ?_)
      (show bm13187^8 ≤ scalar13187.lowerTail by norm_num [bm13187, scalar13187])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13187, bm13187, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13187 :
    agent13187.root+dsL+scalar13187.worldRadius < √(1/100/aL) ∧
    2*(agent13187.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13187, agent13187, scalar13187, tp13187, tm13187, ep13187, em13187, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13187, agent13187, scalar13187, tp13187, tm13187, ep13187, em13187, dsL]

noncomputable def master13187 : MasterCertificate 13187 world13187 agent13187 :=
  master scalar13187 dsL tp13187 tm13187 ep13187 em13187
    (by norm_num [dsL]) (by norm_num [tp13187]) (by norm_num [tm13187])
    (by norm_num [ep13187]) (by norm_num [em13187])
    positive13187 negative13187 tails13187.1 tails13187.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13187.1 tailGuards13187.2

theorem preserves13187 : master13187.toScalarCertificate = scalar13187 := rfl

noncomputable def tp13188 : ℝ := (2357749421 / 10000000000)
noncomputable def tm13188 : ℝ := (-((1230776591 / 2000000000)))
noncomputable def ep13188 : ℝ := (6579365530207963 / 12500000000000000000)
noncomputable def em13188 : ℝ := (51156170605270241 / 100000000000000000000)
noncomputable def bp13188 : ℝ := (41992182074106609851 / 100000000000000000000)
noncomputable def bm13188 : ℝ := (21514207546353691033 / 50000000000000000000)

theorem positive13188 :
    Eplus aL (agent13188.root+dsL) scalar13188.worldRadius world13188.frame
      agent13188.frame tp13188 ≤ -ep13188 := by
  apply positive_check (eT := (7232289470702390219 / 6250000000000000000)) (y := (9542937405727423967 / 25000000000000000000)) (u := (146479821565633353763 / 100000000000000000000))
  · norm_num [world13188, agent13188, scalar13188, tp13188, tm13188, ep13188, em13188, dsL]
  · norm_num [world13188, agent13188, scalar13188, tp13188, tm13188, ep13188, em13188, dsL]
  · norm_num [world13188, agent13188, scalar13188, tp13188, tm13188, ep13188, em13188, dsL]
  · norm_num [world13188, agent13188, scalar13188, tp13188, tm13188, ep13188, em13188, dsL]
  · norm_num [world13188, agent13188, scalar13188, tp13188, tm13188, ep13188, em13188, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13188, agent13188, tp13188, tm13188, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13188, agent13188, scalar13188, tp13188, tm13188, ep13188, em13188, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13188, agent13188, tp13188, tm13188, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13188, agent13188, scalar13188, tp13188, tm13188, ep13188, em13188, dsL]

theorem negative13188 :
    Eminus aL (agent13188.root+dsL) scalar13188.worldRadius world13188.frame
      agent13188.frame tm13188 ≤ -em13188 := by
  apply negative_check (lo := (68317629044897675721 / 100000000000000000000)) (hi := (34158814522448837861 / 50000000000000000000))
    (y := (-((71585019871418343691 / 100000000000000000000)))) (u := (24438818902254316437 / 50000000000000000000))
  · norm_num [world13188, agent13188, scalar13188, tp13188, tm13188, ep13188, em13188, dsL]
  · norm_num [world13188, agent13188, scalar13188, tp13188, tm13188, ep13188, em13188, dsL]
  · norm_num [world13188, agent13188, scalar13188, tp13188, tm13188, ep13188, em13188, dsL]
  · norm_num [world13188, agent13188, scalar13188, tp13188, tm13188, ep13188, em13188, dsL]
  · norm_num [world13188, agent13188, scalar13188, tp13188, tm13188, ep13188, em13188, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13188, agent13188, tp13188, tm13188, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13188, agent13188, tp13188, tm13188, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13188, agent13188, scalar13188, tp13188, tm13188, ep13188, em13188, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13188, agent13188, tp13188, tm13188, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13188, agent13188, scalar13188, tp13188, tm13188, ep13188, em13188, dsL]

theorem tails13188 :
    exp (-((13188:ℝ)*ep13188)) ≤ scalar13188.upperTail ∧
    exp (-((13188:ℝ)*em13188)) ≤ scalar13188.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13188:ℝ)) (by norm_num [ep13188]) ?_)
      (show bp13188^8 ≤ scalar13188.upperTail by norm_num [bp13188, scalar13188])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13188, bp13188, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13188:ℝ)) (by norm_num [em13188]) ?_)
      (show bm13188^8 ≤ scalar13188.lowerTail by norm_num [bm13188, scalar13188])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13188, bm13188, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13188 :
    agent13188.root+dsL+scalar13188.worldRadius < √(1/100/aL) ∧
    2*(agent13188.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13188, agent13188, scalar13188, tp13188, tm13188, ep13188, em13188, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13188, agent13188, scalar13188, tp13188, tm13188, ep13188, em13188, dsL]

noncomputable def master13188 : MasterCertificate 13188 world13188 agent13188 :=
  master scalar13188 dsL tp13188 tm13188 ep13188 em13188
    (by norm_num [dsL]) (by norm_num [tp13188]) (by norm_num [tm13188])
    (by norm_num [ep13188]) (by norm_num [em13188])
    positive13188 negative13188 tails13188.1 tails13188.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13188.1 tailGuards13188.2

theorem preserves13188 : master13188.toScalarCertificate = scalar13188 := rfl

noncomputable def tp13189 : ℝ := (94312789 / 400000000)
noncomputable def tm13189 : ℝ := (-((6154031627 / 10000000000)))
noncomputable def ep13189 : ℝ := (52637014487045173 / 100000000000000000000)
noncomputable def em13189 : ℝ := (51157936278779493 / 100000000000000000000)
noncomputable def bp13189 : ℝ := (839759448049019737 / 2000000000000000000)
noncomputable def bm13189 : ℝ := (672256426394880207 / 1562500000000000000)

theorem positive13189 :
    Eplus aL (agent13189.root+dsL) scalar13189.worldRadius world13189.frame
      agent13189.frame tp13189 ≤ -ep13189 := by
  apply positive_check (eT := (7232299085322798191 / 6250000000000000000)) (y := (19086186971856916189 / 50000000000000000000)) (u := (73240368036243987677 / 50000000000000000000))
  · norm_num [world13189, agent13189, scalar13189, tp13189, tm13189, ep13189, em13189, dsL]
  · norm_num [world13189, agent13189, scalar13189, tp13189, tm13189, ep13189, em13189, dsL]
  · norm_num [world13189, agent13189, scalar13189, tp13189, tm13189, ep13189, em13189, dsL]
  · norm_num [world13189, agent13189, scalar13189, tp13189, tm13189, ep13189, em13189, dsL]
  · norm_num [world13189, agent13189, scalar13189, tp13189, tm13189, ep13189, em13189, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13189, agent13189, tp13189, tm13189, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13189, agent13189, scalar13189, tp13189, tm13189, ep13189, em13189, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13189, agent13189, tp13189, tm13189, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13189, agent13189, scalar13189, tp13189, tm13189, ep13189, em13189, dsL]

theorem negative13189 :
    Eminus aL (agent13189.root+dsL) scalar13189.worldRadius world13189.frame
      agent13189.frame tm13189 ≤ -em13189 := by
  apply negative_check (lo := (68317539296247647519 / 100000000000000000000)) (hi := (426984620601547797 / 625000000000000000))
    (y := (-((71584899345269887877 / 100000000000000000000)))) (u := (6109712089359804503 / 12500000000000000000))
  · norm_num [world13189, agent13189, scalar13189, tp13189, tm13189, ep13189, em13189, dsL]
  · norm_num [world13189, agent13189, scalar13189, tp13189, tm13189, ep13189, em13189, dsL]
  · norm_num [world13189, agent13189, scalar13189, tp13189, tm13189, ep13189, em13189, dsL]
  · norm_num [world13189, agent13189, scalar13189, tp13189, tm13189, ep13189, em13189, dsL]
  · norm_num [world13189, agent13189, scalar13189, tp13189, tm13189, ep13189, em13189, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13189, agent13189, tp13189, tm13189, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13189, agent13189, tp13189, tm13189, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13189, agent13189, scalar13189, tp13189, tm13189, ep13189, em13189, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13189, agent13189, tp13189, tm13189, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13189, agent13189, scalar13189, tp13189, tm13189, ep13189, em13189, dsL]

theorem tails13189 :
    exp (-((13189:ℝ)*ep13189)) ≤ scalar13189.upperTail ∧
    exp (-((13189:ℝ)*em13189)) ≤ scalar13189.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13189:ℝ)) (by norm_num [ep13189]) ?_)
      (show bp13189^8 ≤ scalar13189.upperTail by norm_num [bp13189, scalar13189])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13189, bp13189, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13189:ℝ)) (by norm_num [em13189]) ?_)
      (show bm13189^8 ≤ scalar13189.lowerTail by norm_num [bm13189, scalar13189])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13189, bm13189, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13189 :
    agent13189.root+dsL+scalar13189.worldRadius < √(1/100/aL) ∧
    2*(agent13189.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13189, agent13189, scalar13189, tp13189, tm13189, ep13189, em13189, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13189, agent13189, scalar13189, tp13189, tm13189, ep13189, em13189, dsL]

noncomputable def master13189 : MasterCertificate 13189 world13189 agent13189 :=
  master scalar13189 dsL tp13189 tm13189 ep13189 em13189
    (by norm_num [dsL]) (by norm_num [tp13189]) (by norm_num [tm13189])
    (by norm_num [ep13189]) (by norm_num [em13189])
    positive13189 negative13189 tails13189.1 tails13189.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13189.1 tailGuards13189.2

theorem preserves13189 : master13189.toScalarCertificate = scalar13189 := rfl

noncomputable def tp13190 : ℝ := (589490037 / 2500000000)
noncomputable def tm13190 : ℝ := (-((6154392889 / 10000000000)))
noncomputable def ep13190 : ℝ := (105280845186383 / 200000000000000000)
noncomputable def em13190 : ℝ := (51161142423650301 / 100000000000000000000)
noncomputable def bp13190 : ℝ := (41982850710499651563 / 100000000000000000000)
noncomputable def bm13190 : ℝ := (4301938595576972159 / 10000000000000000000)

theorem positive13190 :
    Eplus aL (agent13190.root+dsL) scalar13190.worldRadius world13190.frame
      agent13190.frame tp13190 ≤ -ep13190 := by
  apply positive_check (eT := (115717441567745366823 / 100000000000000000000)) (y := (9543072152236797689 / 25000000000000000000)) (u := (146480611073547006751 / 100000000000000000000))
  · norm_num [world13190, agent13190, scalar13190, tp13190, tm13190, ep13190, em13190, dsL]
  · norm_num [world13190, agent13190, scalar13190, tp13190, tm13190, ep13190, em13190, dsL]
  · norm_num [world13190, agent13190, scalar13190, tp13190, tm13190, ep13190, em13190, dsL]
  · norm_num [world13190, agent13190, scalar13190, tp13190, tm13190, ep13190, em13190, dsL]
  · norm_num [world13190, agent13190, scalar13190, tp13190, tm13190, ep13190, em13190, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13190, agent13190, tp13190, tm13190, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13190, agent13190, scalar13190, tp13190, tm13190, ep13190, em13190, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13190, agent13190, tp13190, tm13190, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13190, agent13190, scalar13190, tp13190, tm13190, ep13190, em13190, dsL]

theorem negative13190 :
    Eminus aL (agent13190.root+dsL) scalar13190.worldRadius world13190.frame
      agent13190.frame tm13190 ≤ -em13190 := by
  apply negative_check (lo := (68316550341324442469 / 100000000000000000000)) (hi := (6831655034132444247 / 10000000000000000000))
    (y := (-((71582930669277906531 / 100000000000000000000)))) (u := (48878658967830885641 / 100000000000000000000))
  · norm_num [world13190, agent13190, scalar13190, tp13190, tm13190, ep13190, em13190, dsL]
  · norm_num [world13190, agent13190, scalar13190, tp13190, tm13190, ep13190, em13190, dsL]
  · norm_num [world13190, agent13190, scalar13190, tp13190, tm13190, ep13190, em13190, dsL]
  · norm_num [world13190, agent13190, scalar13190, tp13190, tm13190, ep13190, em13190, dsL]
  · norm_num [world13190, agent13190, scalar13190, tp13190, tm13190, ep13190, em13190, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13190, agent13190, tp13190, tm13190, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13190, agent13190, tp13190, tm13190, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13190, agent13190, scalar13190, tp13190, tm13190, ep13190, em13190, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13190, agent13190, tp13190, tm13190, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13190, agent13190, scalar13190, tp13190, tm13190, ep13190, em13190, dsL]

theorem tails13190 :
    exp (-((13190:ℝ)*ep13190)) ≤ scalar13190.upperTail ∧
    exp (-((13190:ℝ)*em13190)) ≤ scalar13190.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13190:ℝ)) (by norm_num [ep13190]) ?_)
      (show bp13190^8 ≤ scalar13190.upperTail by norm_num [bp13190, scalar13190])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13190, bp13190, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13190:ℝ)) (by norm_num [em13190]) ?_)
      (show bm13190^8 ≤ scalar13190.lowerTail by norm_num [bm13190, scalar13190])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13190, bm13190, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13190 :
    agent13190.root+dsL+scalar13190.worldRadius < √(1/100/aL) ∧
    2*(agent13190.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13190, agent13190, scalar13190, tp13190, tm13190, ep13190, em13190, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13190, agent13190, scalar13190, tp13190, tm13190, ep13190, em13190, dsL]

noncomputable def master13190 : MasterCertificate 13190 world13190 agent13190 :=
  master scalar13190 dsL tp13190 tm13190 ep13190 em13190
    (by norm_num [dsL]) (by norm_num [tp13190]) (by norm_num [tm13190])
    (by norm_num [ep13190]) (by norm_num [em13190])
    positive13190 negative13190 tails13190.1 tails13190.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13190.1 tailGuards13190.2

theorem preserves13190 : master13190.toScalarCertificate = scalar13190 := rfl

noncomputable def tp13191 : ℝ := (235803031 / 1000000000)
noncomputable def tm13191 : ℝ := (-((384658821 / 625000000)))
noncomputable def ep13191 : ℝ := (26321254543065023 / 50000000000000000000)
noncomputable def em13191 : ℝ := (51162904637179479 / 100000000000000000000)
noncomputable def bp13191 : ℝ := (41978644063770982077 / 100000000000000000000)
noncomputable def bm13191 : ℝ := (4301538498934894893 / 10000000000000000000)

theorem positive13191 :
    Eplus aL (agent13191.root+dsL) scalar13191.worldRadius world13191.frame
      agent13191.frame tp13191 ≤ -ep13191 := by
  apply positive_check (eT := (7232349652536205203 / 6250000000000000000)) (y := (38172911201868886099 / 100000000000000000000)) (u := (18310190381787770951 / 12500000000000000000))
  · norm_num [world13191, agent13191, scalar13191, tp13191, tm13191, ep13191, em13191, dsL]
  · norm_num [world13191, agent13191, scalar13191, tp13191, tm13191, ep13191, em13191, dsL]
  · norm_num [world13191, agent13191, scalar13191, tp13191, tm13191, ep13191, em13191, dsL]
  · norm_num [world13191, agent13191, scalar13191, tp13191, tm13191, ep13191, em13191, dsL]
  · norm_num [world13191, agent13191, scalar13191, tp13191, tm13191, ep13191, em13191, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13191, agent13191, tp13191, tm13191, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13191, agent13191, scalar13191, tp13191, tm13191, ep13191, em13191, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13191, agent13191, tp13191, tm13191, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13191, agent13191, scalar13191, tp13191, tm13191, ep13191, em13191, dsL]

theorem negative13191 :
    Eminus aL (agent13191.root+dsL) scalar13191.worldRadius world13191.frame
      agent13191.frame tm13191 ≤ -em13191 := by
  apply negative_check (lo := (53372236169572739 / 78125000000000000)) (hi := (68316462297053105921 / 100000000000000000000))
    (y := (-((14316561356187536963 / 20000000000000000000)))) (u := (24439359761413856901 / 50000000000000000000))
  · norm_num [world13191, agent13191, scalar13191, tp13191, tm13191, ep13191, em13191, dsL]
  · norm_num [world13191, agent13191, scalar13191, tp13191, tm13191, ep13191, em13191, dsL]
  · norm_num [world13191, agent13191, scalar13191, tp13191, tm13191, ep13191, em13191, dsL]
  · norm_num [world13191, agent13191, scalar13191, tp13191, tm13191, ep13191, em13191, dsL]
  · norm_num [world13191, agent13191, scalar13191, tp13191, tm13191, ep13191, em13191, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13191, agent13191, tp13191, tm13191, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13191, agent13191, tp13191, tm13191, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13191, agent13191, scalar13191, tp13191, tm13191, ep13191, em13191, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13191, agent13191, tp13191, tm13191, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13191, agent13191, scalar13191, tp13191, tm13191, ep13191, em13191, dsL]

theorem tails13191 :
    exp (-((13191:ℝ)*ep13191)) ≤ scalar13191.upperTail ∧
    exp (-((13191:ℝ)*em13191)) ≤ scalar13191.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13191:ℝ)) (by norm_num [ep13191]) ?_)
      (show bp13191^8 ≤ scalar13191.upperTail by norm_num [bp13191, scalar13191])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13191, bp13191, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13191:ℝ)) (by norm_num [em13191]) ?_)
      (show bm13191^8 ≤ scalar13191.lowerTail by norm_num [bm13191, scalar13191])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13191, bm13191, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13191 :
    agent13191.root+dsL+scalar13191.worldRadius < √(1/100/aL) ∧
    2*(agent13191.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13191, agent13191, scalar13191, tp13191, tm13191, ep13191, em13191, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13191, agent13191, scalar13191, tp13191, tm13191, ep13191, em13191, dsL]

noncomputable def master13191 : MasterCertificate 13191 world13191 agent13191 :=
  master scalar13191 dsL tp13191 tm13191 ep13191 em13191
    (by norm_num [dsL]) (by norm_num [tp13191]) (by norm_num [tm13191])
    (by norm_num [ep13191]) (by norm_num [em13191])
    positive13191 negative13191 tails13191.1 tails13191.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13191.1 tailGuards13191.2

theorem preserves13191 : master13191.toScalarCertificate = scalar13191 := rfl

noncomputable def tp13192 : ℝ := (2358100573 / 10000000000)
noncomputable def tm13192 : ℝ := (-((3077344823 / 5000000000)))
noncomputable def ep13192 : ℝ := (526445963283819 / 1000000000000000000)
noncomputable def em13192 : ℝ := (51164667529887311 / 100000000000000000000)
noncomputable def bp13192 : ℝ := (41974437100952842427 / 100000000000000000000)
noncomputable def bm13192 : ℝ := (43011383723832449037 / 100000000000000000000)

theorem positive13192 :
    Eplus aL (agent13192.root+dsL) scalar13192.worldRadius world13192.frame
      agent13192.frame tp13192 ≤ -ep13192 := by
  apply positive_check (eT := (2892943701749058589 / 2500000000000000000)) (y := (298230747324926523 / 781250000000000000)) (u := (146482437769410118901 / 100000000000000000000))
  · norm_num [world13192, agent13192, scalar13192, tp13192, tm13192, ep13192, em13192, dsL]
  · norm_num [world13192, agent13192, scalar13192, tp13192, tm13192, ep13192, em13192, dsL]
  · norm_num [world13192, agent13192, scalar13192, tp13192, tm13192, ep13192, em13192, dsL]
  · norm_num [world13192, agent13192, scalar13192, tp13192, tm13192, ep13192, em13192, dsL]
  · norm_num [world13192, agent13192, scalar13192, tp13192, tm13192, ep13192, em13192, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13192, agent13192, tp13192, tm13192, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13192, agent13192, scalar13192, tp13192, tm13192, ep13192, em13192, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13192, agent13192, tp13192, tm13192, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13192, agent13192, scalar13192, tp13192, tm13192, ep13192, em13192, dsL]

theorem negative13192 :
    Eminus aL (agent13192.root+dsL) scalar13192.worldRadius world13192.frame
      agent13192.frame tm13192 ≤ -em13192 := by
  apply negative_check (lo := (68316373083935310707 / 100000000000000000000)) (hi := (17079093270983827677 / 25000000000000000000))
    (y := (-((35791343114845304969 / 50000000000000000000)))) (u := (1527461826461536549 / 3125000000000000000))
  · norm_num [world13192, agent13192, scalar13192, tp13192, tm13192, ep13192, em13192, dsL]
  · norm_num [world13192, agent13192, scalar13192, tp13192, tm13192, ep13192, em13192, dsL]
  · norm_num [world13192, agent13192, scalar13192, tp13192, tm13192, ep13192, em13192, dsL]
  · norm_num [world13192, agent13192, scalar13192, tp13192, tm13192, ep13192, em13192, dsL]
  · norm_num [world13192, agent13192, scalar13192, tp13192, tm13192, ep13192, em13192, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13192, agent13192, tp13192, tm13192, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13192, agent13192, tp13192, tm13192, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13192, agent13192, scalar13192, tp13192, tm13192, ep13192, em13192, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13192, agent13192, tp13192, tm13192, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13192, agent13192, scalar13192, tp13192, tm13192, ep13192, em13192, dsL]

theorem tails13192 :
    exp (-((13192:ℝ)*ep13192)) ≤ scalar13192.upperTail ∧
    exp (-((13192:ℝ)*em13192)) ≤ scalar13192.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13192:ℝ)) (by norm_num [ep13192]) ?_)
      (show bp13192^8 ≤ scalar13192.upperTail by norm_num [bp13192, scalar13192])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13192, bp13192, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13192:ℝ)) (by norm_num [em13192]) ?_)
      (show bm13192^8 ≤ scalar13192.lowerTail by norm_num [bm13192, scalar13192])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13192, bm13192, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13192 :
    agent13192.root+dsL+scalar13192.worldRadius < √(1/100/aL) ∧
    2*(agent13192.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13192, agent13192, scalar13192, tp13192, tm13192, ep13192, em13192, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13192, agent13192, scalar13192, tp13192, tm13192, ep13192, em13192, dsL]

noncomputable def master13192 : MasterCertificate 13192 world13192 agent13192 :=
  master scalar13192 dsL tp13192 tm13192 ep13192 em13192
    (by norm_num [dsL]) (by norm_num [tp13192]) (by norm_num [tm13192])
    (by norm_num [ep13192]) (by norm_num [em13192])
    positive13192 negative13192 tails13192.1 tails13192.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13192.1 tailGuards13192.2

theorem preserves13192 : master13192.toScalarCertificate = scalar13192 := rfl

noncomputable def tp13193 : ℝ := (2358170733 / 10000000000)
noncomputable def tm13193 : ℝ := (-((6154837813 / 10000000000)))
noncomputable def ep13193 : ℝ := (10529336336076221 / 20000000000000000000)
noncomputable def em13193 : ℝ := (51166428681435431 / 100000000000000000000)
noncomputable def bp13193 : ℝ := (10492557912265035429 / 25000000000000000000)
noncomputable def bm13193 : ℝ := (8601476775175497917 / 20000000000000000000)

theorem positive13193 :
    Eplus aL (agent13193.root+dsL) scalar13193.worldRadius world13193.frame
      agent13193.frame tp13193 ≤ -ep13193 := by
  apply positive_check (eT := (11571790099444673123 / 10000000000000000000)) (y := (38174158775014077807 / 100000000000000000000)) (u := (1831041881623074803 / 1250000000000000000))
  · norm_num [world13193, agent13193, scalar13193, tp13193, tm13193, ep13193, em13193, dsL]
  · norm_num [world13193, agent13193, scalar13193, tp13193, tm13193, ep13193, em13193, dsL]
  · norm_num [world13193, agent13193, scalar13193, tp13193, tm13193, ep13193, em13193, dsL]
  · norm_num [world13193, agent13193, scalar13193, tp13193, tm13193, ep13193, em13193, dsL]
  · norm_num [world13193, agent13193, scalar13193, tp13193, tm13193, ep13193, em13193, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13193, agent13193, tp13193, tm13193, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13193, agent13193, scalar13193, tp13193, tm13193, ep13193, em13193, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13193, agent13193, tp13193, tm13193, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13193, agent13193, scalar13193, tp13193, tm13193, ep13193, em13193, dsL]

theorem negative13193 :
    Eminus aL (agent13193.root+dsL) scalar13193.worldRadius world13193.frame
      agent13193.frame tm13193 ≤ -em13193 := by
  apply negative_check (lo := (68316285264972815577 / 100000000000000000000)) (hi := (34158142632486407789 / 50000000000000000000))
    (y := (-((7158256299376384631 / 10000000000000000000)))) (u := (48878838683021895529 / 100000000000000000000))
  · norm_num [world13193, agent13193, scalar13193, tp13193, tm13193, ep13193, em13193, dsL]
  · norm_num [world13193, agent13193, scalar13193, tp13193, tm13193, ep13193, em13193, dsL]
  · norm_num [world13193, agent13193, scalar13193, tp13193, tm13193, ep13193, em13193, dsL]
  · norm_num [world13193, agent13193, scalar13193, tp13193, tm13193, ep13193, em13193, dsL]
  · norm_num [world13193, agent13193, scalar13193, tp13193, tm13193, ep13193, em13193, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13193, agent13193, tp13193, tm13193, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13193, agent13193, tp13193, tm13193, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13193, agent13193, scalar13193, tp13193, tm13193, ep13193, em13193, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13193, agent13193, tp13193, tm13193, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13193, agent13193, scalar13193, tp13193, tm13193, ep13193, em13193, dsL]

theorem tails13193 :
    exp (-((13193:ℝ)*ep13193)) ≤ scalar13193.upperTail ∧
    exp (-((13193:ℝ)*em13193)) ≤ scalar13193.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13193:ℝ)) (by norm_num [ep13193]) ?_)
      (show bp13193^8 ≤ scalar13193.upperTail by norm_num [bp13193, scalar13193])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13193, bp13193, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13193:ℝ)) (by norm_num [em13193]) ?_)
      (show bm13193^8 ≤ scalar13193.lowerTail by norm_num [bm13193, scalar13193])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13193, bm13193, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13193 :
    agent13193.root+dsL+scalar13193.worldRadius < √(1/100/aL) ∧
    2*(agent13193.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13193, agent13193, scalar13193, tp13193, tm13193, ep13193, em13193, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13193, agent13193, scalar13193, tp13193, tm13193, ep13193, em13193, dsL]

noncomputable def master13193 : MasterCertificate 13193 world13193 agent13193 :=
  master scalar13193 dsL tp13193 tm13193 ep13193 em13193
    (by norm_num [dsL]) (by norm_num [tp13193]) (by norm_num [tm13193])
    (by norm_num [ep13193]) (by norm_num [em13193])
    positive13193 negative13193 tails13193.1 tails13193.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13193.1 tailGuards13193.2

theorem preserves13193 : master13193.toScalarCertificate = scalar13193 := rfl

noncomputable def tp13194 : ℝ := (2358240877 / 10000000000)
noncomputable def tm13194 : ℝ := (-((6154985807 / 10000000000)))
noncomputable def ep13194 : ℝ := (329054787823311 / 625000000000000000)
noncomputable def em13194 : ℝ := (25584094465136399 / 50000000000000000000)
noncomputable def bp13194 : ℝ := (4196602707846259699 / 10000000000000000000)
noncomputable def bm13194 : ℝ := (21501692425391322317 / 50000000000000000000)

theorem positive13194 :
    Eplus aL (agent13194.root+dsL) scalar13194.worldRadius world13194.frame
      agent13194.frame tp13194 ≤ -ep13194 := by
  apply positive_check (eT := (14464756729659740189 / 12500000000000000000)) (y := (38174781866799643617 / 100000000000000000000)) (u := (73242131629206961347 / 50000000000000000000))
  · norm_num [world13194, agent13194, scalar13194, tp13194, tm13194, ep13194, em13194, dsL]
  · norm_num [world13194, agent13194, scalar13194, tp13194, tm13194, ep13194, em13194, dsL]
  · norm_num [world13194, agent13194, scalar13194, tp13194, tm13194, ep13194, em13194, dsL]
  · norm_num [world13194, agent13194, scalar13194, tp13194, tm13194, ep13194, em13194, dsL]
  · norm_num [world13194, agent13194, scalar13194, tp13194, tm13194, ep13194, em13194, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13194, agent13194, tp13194, tm13194, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13194, agent13194, scalar13194, tp13194, tm13194, ep13194, em13194, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13194, agent13194, tp13194, tm13194, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13194, agent13194, scalar13194, tp13194, tm13194, ep13194, em13194, dsL]

theorem negative13194 :
    Eminus aL (agent13194.root+dsL) scalar13194.worldRadius world13194.frame
      agent13194.frame tm13194 ≤ -em13194 := by
  apply negative_check (lo := (34158099060579457679 / 50000000000000000000)) (hi := (68316198121158915359 / 100000000000000000000))
    (y := (-((17895609635609439473 / 25000000000000000000)))) (u := (48878899513422665281 / 100000000000000000000))
  · norm_num [world13194, agent13194, scalar13194, tp13194, tm13194, ep13194, em13194, dsL]
  · norm_num [world13194, agent13194, scalar13194, tp13194, tm13194, ep13194, em13194, dsL]
  · norm_num [world13194, agent13194, scalar13194, tp13194, tm13194, ep13194, em13194, dsL]
  · norm_num [world13194, agent13194, scalar13194, tp13194, tm13194, ep13194, em13194, dsL]
  · norm_num [world13194, agent13194, scalar13194, tp13194, tm13194, ep13194, em13194, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13194, agent13194, tp13194, tm13194, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13194, agent13194, tp13194, tm13194, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13194, agent13194, scalar13194, tp13194, tm13194, ep13194, em13194, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13194, agent13194, tp13194, tm13194, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13194, agent13194, scalar13194, tp13194, tm13194, ep13194, em13194, dsL]

theorem tails13194 :
    exp (-((13194:ℝ)*ep13194)) ≤ scalar13194.upperTail ∧
    exp (-((13194:ℝ)*em13194)) ≤ scalar13194.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13194:ℝ)) (by norm_num [ep13194]) ?_)
      (show bp13194^8 ≤ scalar13194.upperTail by norm_num [bp13194, scalar13194])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13194, bp13194, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13194:ℝ)) (by norm_num [em13194]) ?_)
      (show bm13194^8 ≤ scalar13194.lowerTail by norm_num [bm13194, scalar13194])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13194, bm13194, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13194 :
    agent13194.root+dsL+scalar13194.worldRadius < √(1/100/aL) ∧
    2*(agent13194.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13194, agent13194, scalar13194, tp13194, tm13194, ep13194, em13194, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13194, agent13194, scalar13194, tp13194, tm13194, ep13194, em13194, dsL]

noncomputable def master13194 : MasterCertificate 13194 world13194 agent13194 :=
  master scalar13194 dsL tp13194 tm13194 ep13194 em13194
    (by norm_num [dsL]) (by norm_num [tp13194]) (by norm_num [tm13194])
    (by norm_num [ep13194]) (by norm_num [em13194])
    positive13194 negative13194 tails13194.1 tails13194.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13194.1 tailGuards13194.2

theorem preserves13194 : master13194.toScalarCertificate = scalar13194 := rfl

noncomputable def tp13195 : ℝ := (1179155471 / 5000000000)
noncomputable def tm13195 : ℝ := (-((1538783511 / 2500000000)))
noncomputable def ep13195 : ℝ := (52650849307264799 / 100000000000000000000)
noncomputable def em13195 : ℝ := (51169948133635407 / 100000000000000000000)
noncomputable def bp13195 : ℝ := (10490455870670372107 / 25000000000000000000)
noncomputable def bm13195 : ℝ := (335932708982690267 / 781250000000000000)

theorem positive13195 :
    Eplus aL (agent13195.root+dsL) scalar13195.worldRadius world13195.frame
      agent13195.frame tp13195 ≤ -ep13195 := by
  apply positive_check (eT := (28929551536793850187 / 25000000000000000000)) (y := (38175403989181882603 / 100000000000000000000)) (u := (9155323410789803319 / 6250000000000000000))
  · norm_num [world13195, agent13195, scalar13195, tp13195, tm13195, ep13195, em13195, dsL]
  · norm_num [world13195, agent13195, scalar13195, tp13195, tm13195, ep13195, em13195, dsL]
  · norm_num [world13195, agent13195, scalar13195, tp13195, tm13195, ep13195, em13195, dsL]
  · norm_num [world13195, agent13195, scalar13195, tp13195, tm13195, ep13195, em13195, dsL]
  · norm_num [world13195, agent13195, scalar13195, tp13195, tm13195, ep13195, em13195, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13195, agent13195, tp13195, tm13195, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13195, agent13195, scalar13195, tp13195, tm13195, ep13195, em13195, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13195, agent13195, tp13195, tm13195, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13195, agent13195, scalar13195, tp13195, tm13195, ep13195, em13195, dsL]

theorem negative13195 :
    Eminus aL (agent13195.root+dsL) scalar13195.worldRadius world13195.frame
      agent13195.frame tm13195 ≤ -em13195 := by
  apply negative_check (lo := (34158054946585950657 / 50000000000000000000)) (hi := (13663221978634380263 / 20000000000000000000))
    (y := (-((71582317136073739549 / 100000000000000000000)))) (u := (48878958855553359261 / 100000000000000000000))
  · norm_num [world13195, agent13195, scalar13195, tp13195, tm13195, ep13195, em13195, dsL]
  · norm_num [world13195, agent13195, scalar13195, tp13195, tm13195, ep13195, em13195, dsL]
  · norm_num [world13195, agent13195, scalar13195, tp13195, tm13195, ep13195, em13195, dsL]
  · norm_num [world13195, agent13195, scalar13195, tp13195, tm13195, ep13195, em13195, dsL]
  · norm_num [world13195, agent13195, scalar13195, tp13195, tm13195, ep13195, em13195, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13195, agent13195, tp13195, tm13195, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13195, agent13195, tp13195, tm13195, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13195, agent13195, scalar13195, tp13195, tm13195, ep13195, em13195, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13195, agent13195, tp13195, tm13195, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13195, agent13195, scalar13195, tp13195, tm13195, ep13195, em13195, dsL]

theorem tails13195 :
    exp (-((13195:ℝ)*ep13195)) ≤ scalar13195.upperTail ∧
    exp (-((13195:ℝ)*em13195)) ≤ scalar13195.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13195:ℝ)) (by norm_num [ep13195]) ?_)
      (show bp13195^8 ≤ scalar13195.upperTail by norm_num [bp13195, scalar13195])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13195, bp13195, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13195:ℝ)) (by norm_num [em13195]) ?_)
      (show bm13195^8 ≤ scalar13195.lowerTail by norm_num [bm13195, scalar13195])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13195, bm13195, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13195 :
    agent13195.root+dsL+scalar13195.worldRadius < √(1/100/aL) ∧
    2*(agent13195.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13195, agent13195, scalar13195, tp13195, tm13195, ep13195, em13195, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13195, agent13195, scalar13195, tp13195, tm13195, ep13195, em13195, dsL]

noncomputable def master13195 : MasterCertificate 13195 world13195 agent13195 :=
  master scalar13195 dsL tp13195 tm13195 ep13195 em13195
    (by norm_num [dsL]) (by norm_num [tp13195]) (by norm_num [tm13195])
    (by norm_num [ep13195]) (by norm_num [em13195])
    positive13195 negative13195 tails13195.1 tails13195.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13195.1 tailGuards13195.2

theorem preserves13195 : master13195.toScalarCertificate = scalar13195 := rfl

noncomputable def tp13196 : ℝ := (471676199 / 2000000000)
noncomputable def tm13196 : ℝ := (-((6155281917 / 10000000000)))
noncomputable def ep13196 : ℝ := (52652931396025139 / 100000000000000000000)
noncomputable def em13196 : ℝ := (51171706239329571 / 100000000000000000000)
noncomputable def bp13196 : ℝ := (41957620896953529221 / 100000000000000000000)
noncomputable def bm13196 : ℝ := (42995389609878806199 / 100000000000000000000)

theorem positive13196 :
    Eplus aL (agent13196.root+dsL) scalar13196.worldRadius world13196.frame
      agent13196.frame tp13196 ≤ -ep13196 := by
  apply positive_check (eT := (7232397400257076451 / 6250000000000000000)) (y := (19088013102915213489 / 50000000000000000000)) (u := (9155380376913519503 / 6250000000000000000))
  · norm_num [world13196, agent13196, scalar13196, tp13196, tm13196, ep13196, em13196, dsL]
  · norm_num [world13196, agent13196, scalar13196, tp13196, tm13196, ep13196, em13196, dsL]
  · norm_num [world13196, agent13196, scalar13196, tp13196, tm13196, ep13196, em13196, dsL]
  · norm_num [world13196, agent13196, scalar13196, tp13196, tm13196, ep13196, em13196, dsL]
  · norm_num [world13196, agent13196, scalar13196, tp13196, tm13196, ep13196, em13196, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13196, agent13196, tp13196, tm13196, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13196, agent13196, scalar13196, tp13196, tm13196, ep13196, em13196, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13196, agent13196, tp13196, tm13196, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13196, agent13196, scalar13196, tp13196, tm13196, ep13196, em13196, dsL]

theorem negative13196 :
    Eminus aL (agent13196.root+dsL) scalar13196.worldRadius world13196.frame
      agent13196.frame tm13196 ≤ -em13196 := by
  apply negative_check (lo := (68316023148025816407 / 100000000000000000000)) (hi := (8539502893503227051 / 12500000000000000000))
    (y := (-((1789554814116840367 / 2500000000000000000)))) (u := (9775803948958939473 / 20000000000000000000))
  · norm_num [world13196, agent13196, scalar13196, tp13196, tm13196, ep13196, em13196, dsL]
  · norm_num [world13196, agent13196, scalar13196, tp13196, tm13196, ep13196, em13196, dsL]
  · norm_num [world13196, agent13196, scalar13196, tp13196, tm13196, ep13196, em13196, dsL]
  · norm_num [world13196, agent13196, scalar13196, tp13196, tm13196, ep13196, em13196, dsL]
  · norm_num [world13196, agent13196, scalar13196, tp13196, tm13196, ep13196, em13196, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13196, agent13196, tp13196, tm13196, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13196, agent13196, tp13196, tm13196, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13196, agent13196, scalar13196, tp13196, tm13196, ep13196, em13196, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13196, agent13196, tp13196, tm13196, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13196, agent13196, scalar13196, tp13196, tm13196, ep13196, em13196, dsL]

theorem tails13196 :
    exp (-((13196:ℝ)*ep13196)) ≤ scalar13196.upperTail ∧
    exp (-((13196:ℝ)*em13196)) ≤ scalar13196.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13196:ℝ)) (by norm_num [ep13196]) ?_)
      (show bp13196^8 ≤ scalar13196.upperTail by norm_num [bp13196, scalar13196])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13196, bp13196, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13196:ℝ)) (by norm_num [em13196]) ?_)
      (show bm13196^8 ≤ scalar13196.lowerTail by norm_num [bm13196, scalar13196])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13196, bm13196, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13196 :
    agent13196.root+dsL+scalar13196.worldRadius < √(1/100/aL) ∧
    2*(agent13196.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13196, agent13196, scalar13196, tp13196, tm13196, ep13196, em13196, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13196, agent13196, scalar13196, tp13196, tm13196, ep13196, em13196, dsL]

noncomputable def master13196 : MasterCertificate 13196 world13196 agent13196 :=
  master scalar13196 dsL tp13196 tm13196 ep13196 em13196
    (by norm_num [dsL]) (by norm_num [tp13196]) (by norm_num [tm13196])
    (by norm_num [ep13196]) (by norm_num [em13196])
    positive13196 negative13196 tails13196.1 tails13196.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13196.1 tailGuards13196.2

theorem preserves13196 : master13196.toScalarCertificate = scalar13196 := rfl

noncomputable def tp13197 : ℝ := (471690197 / 2000000000)
noncomputable def tm13197 : ℝ := (-((6155429849 / 10000000000)))
noncomputable def ep13197 : ℝ := (822734563668611 / 1562500000000000000)
noncomputable def em13197 : ℝ := (25586731524625631 / 50000000000000000000)
noncomputable def bp13197 : ℝ := (41953419489569175959 / 100000000000000000000)
noncomputable def bm13197 : ℝ := (21495696785769390007 / 50000000000000000000)

theorem positive13197 :
    Eplus aL (agent13197.root+dsL) scalar13197.worldRadius world13197.frame
      agent13197.frame tp13197 ≤ -ep13197 := by
  apply positive_check (eT := (57859255121364587131 / 50000000000000000000)) (y := (7635329546070851471 / 20000000000000000000)) (u := (29297399296078864597 / 20000000000000000000))
  · norm_num [world13197, agent13197, scalar13197, tp13197, tm13197, ep13197, em13197, dsL]
  · norm_num [world13197, agent13197, scalar13197, tp13197, tm13197, ep13197, em13197, dsL]
  · norm_num [world13197, agent13197, scalar13197, tp13197, tm13197, ep13197, em13197, dsL]
  · norm_num [world13197, agent13197, scalar13197, tp13197, tm13197, ep13197, em13197, dsL]
  · norm_num [world13197, agent13197, scalar13197, tp13197, tm13197, ep13197, em13197, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13197, agent13197, tp13197, tm13197, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13197, agent13197, scalar13197, tp13197, tm13197, ep13197, em13197, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13197, agent13197, tp13197, tm13197, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13197, agent13197, scalar13197, tp13197, tm13197, ep13197, em13197, dsL]

theorem negative13197 :
    Eminus aL (agent13197.root+dsL) scalar13197.worldRadius world13197.frame
      agent13197.frame tm13197 ≤ -em13197 := by
  apply negative_check (lo := (34157968048452689521 / 50000000000000000000)) (hi := (68315936096905379043 / 100000000000000000000))
    (y := (-((17895517319166489473 / 25000000000000000000)))) (u := (48879080006801450797 / 100000000000000000000))
  · norm_num [world13197, agent13197, scalar13197, tp13197, tm13197, ep13197, em13197, dsL]
  · norm_num [world13197, agent13197, scalar13197, tp13197, tm13197, ep13197, em13197, dsL]
  · norm_num [world13197, agent13197, scalar13197, tp13197, tm13197, ep13197, em13197, dsL]
  · norm_num [world13197, agent13197, scalar13197, tp13197, tm13197, ep13197, em13197, dsL]
  · norm_num [world13197, agent13197, scalar13197, tp13197, tm13197, ep13197, em13197, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13197, agent13197, tp13197, tm13197, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13197, agent13197, tp13197, tm13197, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13197, agent13197, scalar13197, tp13197, tm13197, ep13197, em13197, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13197, agent13197, tp13197, tm13197, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13197, agent13197, scalar13197, tp13197, tm13197, ep13197, em13197, dsL]

theorem tails13197 :
    exp (-((13197:ℝ)*ep13197)) ≤ scalar13197.upperTail ∧
    exp (-((13197:ℝ)*em13197)) ≤ scalar13197.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13197:ℝ)) (by norm_num [ep13197]) ?_)
      (show bp13197^8 ≤ scalar13197.upperTail by norm_num [bp13197, scalar13197])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13197, bp13197, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13197:ℝ)) (by norm_num [em13197]) ?_)
      (show bm13197^8 ≤ scalar13197.lowerTail by norm_num [bm13197, scalar13197])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13197, bm13197, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13197 :
    agent13197.root+dsL+scalar13197.worldRadius < √(1/100/aL) ∧
    2*(agent13197.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13197, agent13197, scalar13197, tp13197, tm13197, ep13197, em13197, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13197, agent13197, scalar13197, tp13197, tm13197, ep13197, em13197, dsL]

noncomputable def master13197 : MasterCertificate 13197 world13197 agent13197 :=
  master scalar13197 dsL tp13197 tm13197 ep13197 em13197
    (by norm_num [dsL]) (by norm_num [tp13197]) (by norm_num [tm13197])
    (by norm_num [ep13197]) (by norm_num [em13197])
    positive13197 negative13197 tails13197.1 tails13197.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13197.1 tailGuards13197.2

theorem preserves13197 : master13197.toScalarCertificate = scalar13197 := rfl

noncomputable def tp13198 : ℝ := (2358521017 / 10000000000)
noncomputable def tm13198 : ℝ := (-((1231115579 / 2000000000)))
noncomputable def ep13198 : ℝ := (6582136532247159 / 12500000000000000000)
noncomputable def em13198 : ℝ := (12793804851489337 / 25000000000000000000)
noncomputable def bp13198 : ℝ := (20974609313826656273 / 50000000000000000000)
noncomputable def bm13198 : ℝ := (21493699018603359023 / 50000000000000000000)

theorem positive13198 :
    Eplus aL (agent13198.root+dsL) scalar13198.worldRadius world13198.frame
      agent13198.frame tp13198 ≤ -ep13198 := by
  apply positive_check (eT := (28929665603797857511 / 25000000000000000000)) (y := (38177270188510095727 / 100000000000000000000)) (u := (73243954151744506767 / 50000000000000000000))
  · norm_num [world13198, agent13198, scalar13198, tp13198, tm13198, ep13198, em13198, dsL]
  · norm_num [world13198, agent13198, scalar13198, tp13198, tm13198, ep13198, em13198, dsL]
  · norm_num [world13198, agent13198, scalar13198, tp13198, tm13198, ep13198, em13198, dsL]
  · norm_num [world13198, agent13198, scalar13198, tp13198, tm13198, ep13198, em13198, dsL]
  · norm_num [world13198, agent13198, scalar13198, tp13198, tm13198, ep13198, em13198, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13198, agent13198, tp13198, tm13198, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13198, agent13198, scalar13198, tp13198, tm13198, ep13198, em13198, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13198, agent13198, tp13198, tm13198, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13198, agent13198, scalar13198, tp13198, tm13198, ep13198, em13198, dsL]

theorem negative13198 :
    Eminus aL (agent13198.root+dsL) scalar13198.worldRadius world13198.frame
      agent13198.frame tm13198 ≤ -em13198 := by
  apply negative_check (lo := (17078962126799770173 / 25000000000000000000)) (hi := (68315848507199080693 / 100000000000000000000))
    (y := (-((3579097382113220629 / 5000000000000000000)))) (u := (48879139460614056061 / 100000000000000000000))
  · norm_num [world13198, agent13198, scalar13198, tp13198, tm13198, ep13198, em13198, dsL]
  · norm_num [world13198, agent13198, scalar13198, tp13198, tm13198, ep13198, em13198, dsL]
  · norm_num [world13198, agent13198, scalar13198, tp13198, tm13198, ep13198, em13198, dsL]
  · norm_num [world13198, agent13198, scalar13198, tp13198, tm13198, ep13198, em13198, dsL]
  · norm_num [world13198, agent13198, scalar13198, tp13198, tm13198, ep13198, em13198, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13198, agent13198, tp13198, tm13198, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13198, agent13198, tp13198, tm13198, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13198, agent13198, scalar13198, tp13198, tm13198, ep13198, em13198, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13198, agent13198, tp13198, tm13198, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13198, agent13198, scalar13198, tp13198, tm13198, ep13198, em13198, dsL]

theorem tails13198 :
    exp (-((13198:ℝ)*ep13198)) ≤ scalar13198.upperTail ∧
    exp (-((13198:ℝ)*em13198)) ≤ scalar13198.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13198:ℝ)) (by norm_num [ep13198]) ?_)
      (show bp13198^8 ≤ scalar13198.upperTail by norm_num [bp13198, scalar13198])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13198, bp13198, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13198:ℝ)) (by norm_num [em13198]) ?_)
      (show bm13198^8 ≤ scalar13198.lowerTail by norm_num [bm13198, scalar13198])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13198, bm13198, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13198 :
    agent13198.root+dsL+scalar13198.worldRadius < √(1/100/aL) ∧
    2*(agent13198.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13198, agent13198, scalar13198, tp13198, tm13198, ep13198, em13198, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13198, agent13198, scalar13198, tp13198, tm13198, ep13198, em13198, dsL]

noncomputable def master13198 : MasterCertificate 13198 world13198 agent13198 :=
  master scalar13198 dsL tp13198 tm13198 ep13198 em13198
    (by norm_num [dsL]) (by norm_num [tp13198]) (by norm_num [tm13198])
    (by norm_num [ep13198]) (by norm_num [em13198])
    positive13198 negative13198 tails13198.1 tails13198.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13198.1 tailGuards13198.2

theorem preserves13198 : master13198.toScalarCertificate = scalar13198 := rfl

noncomputable def tp13199 : ℝ := (589647737 / 2500000000)
noncomputable def tm13199 : ℝ := (-((6155725593 / 10000000000)))
noncomputable def ep13199 : ℝ := (52659171274475027 / 100000000000000000000)
noncomputable def em13199 : ℝ := (25588487332569649 / 50000000000000000000)
noncomputable def bp13199 : ℝ := (8389003755127708701 / 20000000000000000000)
noncomputable def bm13199 : ℝ := (42983403463810023927 / 100000000000000000000)

theorem positive13199 :
    Eplus aL (agent13199.root+dsL) scalar13199.worldRadius world13199.frame
      agent13199.frame tp13199 ≤ -ep13199 := by
  apply positive_check (eT := (23143762779435618299 / 20000000000000000000)) (y := (7635578238452995513 / 20000000000000000000)) (u := (73244409000862326621 / 50000000000000000000))
  · norm_num [world13199, agent13199, scalar13199, tp13199, tm13199, ep13199, em13199, dsL]
  · norm_num [world13199, agent13199, scalar13199, tp13199, tm13199, ep13199, em13199, dsL]
  · norm_num [world13199, agent13199, scalar13199, tp13199, tm13199, ep13199, em13199, dsL]
  · norm_num [world13199, agent13199, scalar13199, tp13199, tm13199, ep13199, em13199, dsL]
  · norm_num [world13199, agent13199, scalar13199, tp13199, tm13199, ep13199, em13199, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13199, agent13199, tp13199, tm13199, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13199, agent13199, scalar13199, tp13199, tm13199, ep13199, em13199, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13199, agent13199, tp13199, tm13199, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13199, agent13199, scalar13199, tp13199, tm13199, ep13199, em13199, dsL]

theorem negative13199 :
    Eminus aL (agent13199.root+dsL) scalar13199.worldRadius world13199.frame
      agent13199.frame tm13199 ≤ -em13199 := by
  apply negative_check (lo := (68315762332605505039 / 100000000000000000000)) (hi := (853947029157568813 / 1250000000000000000))
    (y := (-((14316364599068452193 / 20000000000000000000)))) (u := (24439600193497469667 / 50000000000000000000))
  · norm_num [world13199, agent13199, scalar13199, tp13199, tm13199, ep13199, em13199, dsL]
  · norm_num [world13199, agent13199, scalar13199, tp13199, tm13199, ep13199, em13199, dsL]
  · norm_num [world13199, agent13199, scalar13199, tp13199, tm13199, ep13199, em13199, dsL]
  · norm_num [world13199, agent13199, scalar13199, tp13199, tm13199, ep13199, em13199, dsL]
  · norm_num [world13199, agent13199, scalar13199, tp13199, tm13199, ep13199, em13199, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13199, agent13199, tp13199, tm13199, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13199, agent13199, tp13199, tm13199, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13199, agent13199, scalar13199, tp13199, tm13199, ep13199, em13199, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13199, agent13199, tp13199, tm13199, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13199, agent13199, scalar13199, tp13199, tm13199, ep13199, em13199, dsL]

theorem tails13199 :
    exp (-((13199:ℝ)*ep13199)) ≤ scalar13199.upperTail ∧
    exp (-((13199:ℝ)*em13199)) ≤ scalar13199.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13199:ℝ)) (by norm_num [ep13199]) ?_)
      (show bp13199^8 ≤ scalar13199.upperTail by norm_num [bp13199, scalar13199])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13199, bp13199, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13199:ℝ)) (by norm_num [em13199]) ?_)
      (show bm13199^8 ≤ scalar13199.lowerTail by norm_num [bm13199, scalar13199])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13199, bm13199, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13199 :
    agent13199.root+dsL+scalar13199.worldRadius < √(1/100/aL) ∧
    2*(agent13199.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13199, agent13199, scalar13199, tp13199, tm13199, ep13199, em13199, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13199, agent13199, scalar13199, tp13199, tm13199, ep13199, em13199, dsL]

noncomputable def master13199 : MasterCertificate 13199 world13199 agent13199 :=
  master scalar13199 dsL tp13199 tm13199 ep13199 em13199
    (by norm_num [dsL]) (by norm_num [tp13199]) (by norm_num [tm13199])
    (by norm_num [ep13199]) (by norm_num [em13199])
    positive13199 negative13199 tails13199.1 tails13199.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13199.1 tailGuards13199.2

theorem preserves13199 : master13199.toScalarCertificate = scalar13199 := rfl

end BstLean.Part268
