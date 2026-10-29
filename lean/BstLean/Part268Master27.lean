import BstLean.Part261Checker
import BstLean.Part268Scalar27
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp13025 : ℝ := (234479643 / 1000000000)
noncomputable def tm13025 : ℝ := (-((6125410467 / 10000000000)))
noncomputable def ep13025 : ℝ := (1633119010613851 / 3125000000000000000)
noncomputable def em13025 : ℝ := (10166639219836517 / 20000000000000000000)
noncomputable def bp13025 : ℝ := (42704964642843958637 / 100000000000000000000)
noncomputable def bm13025 : ℝ := (43708483425818938007 / 100000000000000000000)

theorem positive13025 :
    Eplus aL (agent13025.root+dsL) scalar13025.worldRadius world13025.frame
      agent13025.frame tp13025 ≤ -ep13025 := by
  apply positive_check (eT := (23136254011547868311 / 20000000000000000000)) (y := (4759631852690002103 / 12500000000000000000)) (u := (73170589221900239981 / 50000000000000000000))
  · norm_num [world13025, agent13025, scalar13025, tp13025, tm13025, ep13025, em13025, dsL]
  · norm_num [world13025, agent13025, scalar13025, tp13025, tm13025, ep13025, em13025, dsL]
  · norm_num [world13025, agent13025, scalar13025, tp13025, tm13025, ep13025, em13025, dsL]
  · norm_num [world13025, agent13025, scalar13025, tp13025, tm13025, ep13025, em13025, dsL]
  · norm_num [world13025, agent13025, scalar13025, tp13025, tm13025, ep13025, em13025, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13025, agent13025, tp13025, tm13025, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13025, agent13025, scalar13025, tp13025, tm13025, ep13025, em13025, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13025, agent13025, tp13025, tm13025, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13025, agent13025, scalar13025, tp13025, tm13025, ep13025, em13025, dsL]

theorem negative13025 :
    Eminus aL (agent13025.root+dsL) scalar13025.worldRadius world13025.frame
      agent13025.frame tm13025 ≤ -em13025 := by
  apply negative_check (lo := (17087372373819100041 / 25000000000000000000)) (hi := (13669897899055280033 / 20000000000000000000))
    (y := (-((35814665577624520327 / 50000000000000000000)))) (u := (24427992146759998751 / 50000000000000000000))
  · norm_num [world13025, agent13025, scalar13025, tp13025, tm13025, ep13025, em13025, dsL]
  · norm_num [world13025, agent13025, scalar13025, tp13025, tm13025, ep13025, em13025, dsL]
  · norm_num [world13025, agent13025, scalar13025, tp13025, tm13025, ep13025, em13025, dsL]
  · norm_num [world13025, agent13025, scalar13025, tp13025, tm13025, ep13025, em13025, dsL]
  · norm_num [world13025, agent13025, scalar13025, tp13025, tm13025, ep13025, em13025, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13025, agent13025, tp13025, tm13025, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13025, agent13025, tp13025, tm13025, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13025, agent13025, scalar13025, tp13025, tm13025, ep13025, em13025, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13025, agent13025, tp13025, tm13025, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13025, agent13025, scalar13025, tp13025, tm13025, ep13025, em13025, dsL]

theorem tails13025 :
    exp (-((13025:ℝ)*ep13025)) ≤ scalar13025.upperTail ∧
    exp (-((13025:ℝ)*em13025)) ≤ scalar13025.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13025:ℝ)) (by norm_num [ep13025]) ?_)
      (show bp13025^8 ≤ scalar13025.upperTail by norm_num [bp13025, scalar13025])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13025, bp13025, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13025:ℝ)) (by norm_num [em13025]) ?_)
      (show bm13025^8 ≤ scalar13025.lowerTail by norm_num [bm13025, scalar13025])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13025, bm13025, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13025 :
    agent13025.root+dsL+scalar13025.worldRadius < √(1/100/aL) ∧
    2*(agent13025.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13025, agent13025, scalar13025, tp13025, tm13025, ep13025, em13025, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13025, agent13025, scalar13025, tp13025, tm13025, ep13025, em13025, dsL]

noncomputable def master13025 : MasterCertificate 13025 world13025 agent13025 :=
  master scalar13025 dsL tp13025 tm13025 ep13025 em13025
    (by norm_num [dsL]) (by norm_num [tp13025]) (by norm_num [tm13025])
    (by norm_num [ep13025]) (by norm_num [em13025])
    positive13025 negative13025 tails13025.1 tails13025.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13025.1 tailGuards13025.2

theorem preserves13025 : master13025.toScalarCertificate = scalar13025 := rfl

noncomputable def tp13026 : ℝ := (293108923 / 1250000000)
noncomputable def tm13026 : ℝ := (-((1225113971 / 2000000000)))
noncomputable def ep13026 : ℝ := (52262064248969647 / 100000000000000000000)
noncomputable def em13026 : ℝ := (10167022557292257 / 20000000000000000000)
noncomputable def bp13026 : ℝ := (21350303270783749087 / 50000000000000000000)
noncomputable def bm13026 : ℝ := (21852171122570173013 / 50000000000000000000)

theorem positive13026 :
    Eplus aL (agent13026.root+dsL) scalar13026.worldRadius world13026.frame
      agent13026.frame tp13026 ≤ -ep13026 := by
  apply positive_check (eT := (57840726018673550299 / 50000000000000000000)) (y := (38077730350938262563 / 100000000000000000000)) (u := (146342167024850949477 / 100000000000000000000))
  · norm_num [world13026, agent13026, scalar13026, tp13026, tm13026, ep13026, em13026, dsL]
  · norm_num [world13026, agent13026, scalar13026, tp13026, tm13026, ep13026, em13026, dsL]
  · norm_num [world13026, agent13026, scalar13026, tp13026, tm13026, ep13026, em13026, dsL]
  · norm_num [world13026, agent13026, scalar13026, tp13026, tm13026, ep13026, em13026, dsL]
  · norm_num [world13026, agent13026, scalar13026, tp13026, tm13026, ep13026, em13026, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13026, agent13026, tp13026, tm13026, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13026, agent13026, scalar13026, tp13026, tm13026, ep13026, em13026, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13026, agent13026, tp13026, tm13026, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13026, agent13026, scalar13026, tp13026, tm13026, ep13026, em13026, dsL]

theorem negative13026 :
    Eminus aL (agent13026.root+dsL) scalar13026.worldRadius world13026.frame
      agent13026.frame tm13026 ≤ -em13026 := by
  apply negative_check (lo := (68349363243975684761 / 100000000000000000000)) (hi := (34174681621987842381 / 50000000000000000000))
    (y := (-((8953658660205942641 / 12500000000000000000)))) (u := (2442800726124318991 / 5000000000000000000))
  · norm_num [world13026, agent13026, scalar13026, tp13026, tm13026, ep13026, em13026, dsL]
  · norm_num [world13026, agent13026, scalar13026, tp13026, tm13026, ep13026, em13026, dsL]
  · norm_num [world13026, agent13026, scalar13026, tp13026, tm13026, ep13026, em13026, dsL]
  · norm_num [world13026, agent13026, scalar13026, tp13026, tm13026, ep13026, em13026, dsL]
  · norm_num [world13026, agent13026, scalar13026, tp13026, tm13026, ep13026, em13026, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13026, agent13026, tp13026, tm13026, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13026, agent13026, tp13026, tm13026, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13026, agent13026, scalar13026, tp13026, tm13026, ep13026, em13026, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13026, agent13026, tp13026, tm13026, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13026, agent13026, scalar13026, tp13026, tm13026, ep13026, em13026, dsL]

theorem tails13026 :
    exp (-((13026:ℝ)*ep13026)) ≤ scalar13026.upperTail ∧
    exp (-((13026:ℝ)*em13026)) ≤ scalar13026.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13026:ℝ)) (by norm_num [ep13026]) ?_)
      (show bp13026^8 ≤ scalar13026.upperTail by norm_num [bp13026, scalar13026])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13026, bp13026, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13026:ℝ)) (by norm_num [em13026]) ?_)
      (show bm13026^8 ≤ scalar13026.lowerTail by norm_num [bm13026, scalar13026])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13026, bm13026, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13026 :
    agent13026.root+dsL+scalar13026.worldRadius < √(1/100/aL) ∧
    2*(agent13026.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13026, agent13026, scalar13026, tp13026, tm13026, ep13026, em13026, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13026, agent13026, scalar13026, tp13026, tm13026, ep13026, em13026, dsL]

noncomputable def master13026 : MasterCertificate 13026 world13026 agent13026 :=
  master scalar13026 dsL tp13026 tm13026 ep13026 em13026
    (by norm_num [dsL]) (by norm_num [tp13026]) (by norm_num [tm13026])
    (by norm_num [ep13026]) (by norm_num [em13026])
    positive13026 negative13026 tails13026.1 tails13026.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13026.1 tailGuards13026.2

theorem preserves13026 : master13026.toScalarCertificate = scalar13026 := rfl

noncomputable def tp13027 : ℝ := (293118289 / 1250000000)
noncomputable def tm13027 : ℝ := (-((6125729029 / 10000000000)))
noncomputable def ep13027 : ℝ := (52264318445046197 / 100000000000000000000)
noncomputable def em13027 : ℝ := (50837027870996421 / 100000000000000000000)
noncomputable def bp13027 : ℝ := (42696249835389812379 / 100000000000000000000)
noncomputable def bm13027 : ℝ := (21850101193969094377 / 50000000000000000000)

theorem positive13027 :
    Eplus aL (agent13027.root+dsL) scalar13027.worldRadius world13027.frame
      agent13027.frame tp13027 ≤ -ep13027 := by
  apply positive_check (eT := (57840816931533943543 / 50000000000000000000)) (y := (38078405796729129031 / 100000000000000000000)) (u := (146343155490196651637 / 100000000000000000000))
  · norm_num [world13027, agent13027, scalar13027, tp13027, tm13027, ep13027, em13027, dsL]
  · norm_num [world13027, agent13027, scalar13027, tp13027, tm13027, ep13027, em13027, dsL]
  · norm_num [world13027, agent13027, scalar13027, tp13027, tm13027, ep13027, em13027, dsL]
  · norm_num [world13027, agent13027, scalar13027, tp13027, tm13027, ep13027, em13027, dsL]
  · norm_num [world13027, agent13027, scalar13027, tp13027, tm13027, ep13027, em13027, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13027, agent13027, tp13027, tm13027, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13027, agent13027, scalar13027, tp13027, tm13027, ep13027, em13027, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13027, agent13027, tp13027, tm13027, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13027, agent13027, scalar13027, tp13027, tm13027, ep13027, em13027, dsL]

theorem negative13027 :
    Eminus aL (agent13027.root+dsL) scalar13027.worldRadius world13027.frame
      agent13027.frame tm13027 ≤ -em13027 := by
  apply negative_check (lo := (13669847568914336131 / 20000000000000000000)) (hi := (4271827365285730041 / 6250000000000000000))
    (y := (-((71629205570629697147 / 100000000000000000000)))) (u := (48856045649160425659 / 100000000000000000000))
  · norm_num [world13027, agent13027, scalar13027, tp13027, tm13027, ep13027, em13027, dsL]
  · norm_num [world13027, agent13027, scalar13027, tp13027, tm13027, ep13027, em13027, dsL]
  · norm_num [world13027, agent13027, scalar13027, tp13027, tm13027, ep13027, em13027, dsL]
  · norm_num [world13027, agent13027, scalar13027, tp13027, tm13027, ep13027, em13027, dsL]
  · norm_num [world13027, agent13027, scalar13027, tp13027, tm13027, ep13027, em13027, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13027, agent13027, tp13027, tm13027, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13027, agent13027, tp13027, tm13027, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13027, agent13027, scalar13027, tp13027, tm13027, ep13027, em13027, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13027, agent13027, tp13027, tm13027, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13027, agent13027, scalar13027, tp13027, tm13027, ep13027, em13027, dsL]

theorem tails13027 :
    exp (-((13027:ℝ)*ep13027)) ≤ scalar13027.upperTail ∧
    exp (-((13027:ℝ)*em13027)) ≤ scalar13027.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13027:ℝ)) (by norm_num [ep13027]) ?_)
      (show bp13027^8 ≤ scalar13027.upperTail by norm_num [bp13027, scalar13027])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13027, bp13027, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13027:ℝ)) (by norm_num [em13027]) ?_)
      (show bm13027^8 ≤ scalar13027.lowerTail by norm_num [bm13027, scalar13027])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13027, bm13027, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13027 :
    agent13027.root+dsL+scalar13027.worldRadius < √(1/100/aL) ∧
    2*(agent13027.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13027, agent13027, scalar13027, tp13027, tm13027, ep13027, em13027, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13027, agent13027, scalar13027, tp13027, tm13027, ep13027, em13027, dsL]

noncomputable def master13027 : MasterCertificate 13027 world13027 agent13027 :=
  master scalar13027 dsL tp13027 tm13027 ep13027 em13027
    (by norm_num [dsL]) (by norm_num [tp13027]) (by norm_num [tm13027])
    (by norm_num [ep13027]) (by norm_num [em13027])
    positive13027 negative13027 tails13027.1 tails13027.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13027.1 tailGuards13027.2

theorem preserves13027 : master13027.toScalarCertificate = scalar13027 := rfl

noncomputable def tp13028 : ℝ := (2345021173 / 10000000000)
noncomputable def tm13028 : ℝ := (-((6125888207 / 10000000000)))
noncomputable def ep13028 : ℝ := (52266572099593383 / 100000000000000000000)
noncomputable def em13028 : ℝ := (50838942466248513 / 100000000000000000000)
noncomputable def bp13028 : ℝ := (21345946854812439723 / 50000000000000000000)
noncomputable def bm13028 : ℝ := (21848031530922755147 / 50000000000000000000)

theorem positive13028 :
    Eplus aL (agent13028.root+dsL) scalar13028.worldRadius world13028.frame
      agent13028.frame tp13028 ≤ -ep13028 := by
  apply positive_check (eT := (115681815240311843319 / 100000000000000000000)) (y := (38079080396419125851 / 100000000000000000000)) (u := (146344142723999854411 / 100000000000000000000))
  · norm_num [world13028, agent13028, scalar13028, tp13028, tm13028, ep13028, em13028, dsL]
  · norm_num [world13028, agent13028, scalar13028, tp13028, tm13028, ep13028, em13028, dsL]
  · norm_num [world13028, agent13028, scalar13028, tp13028, tm13028, ep13028, em13028, dsL]
  · norm_num [world13028, agent13028, scalar13028, tp13028, tm13028, ep13028, em13028, dsL]
  · norm_num [world13028, agent13028, scalar13028, tp13028, tm13028, ep13028, em13028, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13028, agent13028, tp13028, tm13028, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13028, agent13028, scalar13028, tp13028, tm13028, ep13028, em13028, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13028, agent13028, tp13028, tm13028, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13028, agent13028, scalar13028, tp13028, tm13028, ep13028, em13028, dsL]

theorem negative13028 :
    Eminus aL (agent13028.root+dsL) scalar13028.worldRadius world13028.frame
      agent13028.frame tm13028 ≤ -em13028 := by
  apply negative_check (lo := (6834911237135535521 / 10000000000000000000)) (hi := (68349112371355355211 / 100000000000000000000))
    (y := (-((71629142908061330601 / 100000000000000000000)))) (u := (24428038131811511829 / 50000000000000000000))
  · norm_num [world13028, agent13028, scalar13028, tp13028, tm13028, ep13028, em13028, dsL]
  · norm_num [world13028, agent13028, scalar13028, tp13028, tm13028, ep13028, em13028, dsL]
  · norm_num [world13028, agent13028, scalar13028, tp13028, tm13028, ep13028, em13028, dsL]
  · norm_num [world13028, agent13028, scalar13028, tp13028, tm13028, ep13028, em13028, dsL]
  · norm_num [world13028, agent13028, scalar13028, tp13028, tm13028, ep13028, em13028, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13028, agent13028, tp13028, tm13028, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13028, agent13028, tp13028, tm13028, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13028, agent13028, scalar13028, tp13028, tm13028, ep13028, em13028, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13028, agent13028, tp13028, tm13028, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13028, agent13028, scalar13028, tp13028, tm13028, ep13028, em13028, dsL]

theorem tails13028 :
    exp (-((13028:ℝ)*ep13028)) ≤ scalar13028.upperTail ∧
    exp (-((13028:ℝ)*em13028)) ≤ scalar13028.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13028:ℝ)) (by norm_num [ep13028]) ?_)
      (show bp13028^8 ≤ scalar13028.upperTail by norm_num [bp13028, scalar13028])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13028, bp13028, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13028:ℝ)) (by norm_num [em13028]) ?_)
      (show bm13028^8 ≤ scalar13028.lowerTail by norm_num [bm13028, scalar13028])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13028, bm13028, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13028 :
    agent13028.root+dsL+scalar13028.worldRadius < √(1/100/aL) ∧
    2*(agent13028.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13028, agent13028, scalar13028, tp13028, tm13028, ep13028, em13028, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13028, agent13028, scalar13028, tp13028, tm13028, ep13028, em13028, dsL]

noncomputable def master13028 : MasterCertificate 13028 world13028 agent13028 :=
  master scalar13028 dsL tp13028 tm13028 ep13028 em13028
    (by norm_num [dsL]) (by norm_num [tp13028]) (by norm_num [tm13028])
    (by norm_num [ep13028]) (by norm_num [em13028])
    positive13028 negative13028 tails13028.1 tails13028.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13028.1 tailGuards13028.2

theorem preserves13028 : master13028.toScalarCertificate = scalar13028 := rfl

noncomputable def tp13029 : ℝ := (23450961 / 100000000)
noncomputable def tm13029 : ℝ := (-((3063023601 / 5000000000)))
noncomputable def ep13029 : ℝ := (5226882312693857 / 10000000000000000000)
noncomputable def em13029 : ℝ := (50840854617120213 / 100000000000000000000)
noncomputable def bp13029 : ℝ := (21343769807136810329 / 50000000000000000000)
noncomputable def bm13029 : ℝ := (21845962829034673373 / 50000000000000000000)

theorem positive13029 :
    Eplus aL (agent13029.root+dsL) scalar13029.worldRadius world13029.frame
      agent13029.frame tp13029 ≤ -ep13029 := by
  apply positive_check (eT := (115681997124829020229 / 100000000000000000000)) (y := (38079756718225797671 / 100000000000000000000)) (u := (29269026496939372739 / 20000000000000000000))
  · norm_num [world13029, agent13029, scalar13029, tp13029, tm13029, ep13029, em13029, dsL]
  · norm_num [world13029, agent13029, scalar13029, tp13029, tm13029, ep13029, em13029, dsL]
  · norm_num [world13029, agent13029, scalar13029, tp13029, tm13029, ep13029, em13029, dsL]
  · norm_num [world13029, agent13029, scalar13029, tp13029, tm13029, ep13029, em13029, dsL]
  · norm_num [world13029, agent13029, scalar13029, tp13029, tm13029, ep13029, em13029, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13029, agent13029, tp13029, tm13029, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13029, agent13029, scalar13029, tp13029, tm13029, ep13029, em13029, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13029, agent13029, tp13029, tm13029, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13029, agent13029, scalar13029, tp13029, tm13029, ep13029, em13029, dsL]

theorem negative13029 :
    Eminus aL (agent13029.root+dsL) scalar13029.worldRadius world13029.frame
      agent13029.frame tm13029 ≤ -em13029 := by
  apply negative_check (lo := (34174493809160744673 / 50000000000000000000)) (hi := (68348987618321489347 / 100000000000000000000))
    (y := (-((35814539430490875659 / 50000000000000000000)))) (u := (48856107554523087989 / 100000000000000000000))
  · norm_num [world13029, agent13029, scalar13029, tp13029, tm13029, ep13029, em13029, dsL]
  · norm_num [world13029, agent13029, scalar13029, tp13029, tm13029, ep13029, em13029, dsL]
  · norm_num [world13029, agent13029, scalar13029, tp13029, tm13029, ep13029, em13029, dsL]
  · norm_num [world13029, agent13029, scalar13029, tp13029, tm13029, ep13029, em13029, dsL]
  · norm_num [world13029, agent13029, scalar13029, tp13029, tm13029, ep13029, em13029, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13029, agent13029, tp13029, tm13029, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13029, agent13029, tp13029, tm13029, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13029, agent13029, scalar13029, tp13029, tm13029, ep13029, em13029, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13029, agent13029, tp13029, tm13029, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13029, agent13029, scalar13029, tp13029, tm13029, ep13029, em13029, dsL]

theorem tails13029 :
    exp (-((13029:ℝ)*ep13029)) ≤ scalar13029.upperTail ∧
    exp (-((13029:ℝ)*em13029)) ≤ scalar13029.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13029:ℝ)) (by norm_num [ep13029]) ?_)
      (show bp13029^8 ≤ scalar13029.upperTail by norm_num [bp13029, scalar13029])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13029, bp13029, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13029:ℝ)) (by norm_num [em13029]) ?_)
      (show bm13029^8 ≤ scalar13029.lowerTail by norm_num [bm13029, scalar13029])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13029, bm13029, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13029 :
    agent13029.root+dsL+scalar13029.worldRadius < √(1/100/aL) ∧
    2*(agent13029.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13029, agent13029, scalar13029, tp13029, tm13029, ep13029, em13029, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13029, agent13029, scalar13029, tp13029, tm13029, ep13029, em13029, dsL]

noncomputable def master13029 : MasterCertificate 13029 world13029 agent13029 :=
  master scalar13029 dsL tp13029 tm13029 ep13029 em13029
    (by norm_num [dsL]) (by norm_num [tp13029]) (by norm_num [tm13029])
    (by norm_num [ep13029]) (by norm_num [em13029])
    positive13029 negative13029 tails13029.1 tails13029.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13029.1 tailGuards13029.2

theorem preserves13029 : master13029.toScalarCertificate = scalar13029 := rfl

noncomputable def tp13030 : ℝ := (1172621229 / 5000000000)
noncomputable def tm13030 : ℝ := (-((1225284587 / 2000000000)))
noncomputable def ep13030 : ℝ := (52272426900957403 / 100000000000000000000)
noncomputable def em13030 : ℝ := (50844243536618649 / 100000000000000000000)
noncomputable def bp13030 : ℝ := (42682245300431799061 / 100000000000000000000)
noncomputable def bm13030 : ℝ := (5460842204148510271 / 12500000000000000000)

theorem positive13030 :
    Eplus aL (agent13030.root+dsL) scalar13030.worldRadius world13030.frame
      agent13030.frame tp13030 ≤ -ep13030 := by
  apply positive_check (eT := (11568269233946070399 / 10000000000000000000)) (y := (380797164725685627 / 1000000000000000000)) (u := (146345073587148315693 / 100000000000000000000))
  · norm_num [world13030, agent13030, scalar13030, tp13030, tm13030, ep13030, em13030, dsL]
  · norm_num [world13030, agent13030, scalar13030, tp13030, tm13030, ep13030, em13030, dsL]
  · norm_num [world13030, agent13030, scalar13030, tp13030, tm13030, ep13030, em13030, dsL]
  · norm_num [world13030, agent13030, scalar13030, tp13030, tm13030, ep13030, em13030, dsL]
  · norm_num [world13030, agent13030, scalar13030, tp13030, tm13030, ep13030, em13030, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13030, agent13030, tp13030, tm13030, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13030, agent13030, scalar13030, tp13030, tm13030, ep13030, em13030, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13030, agent13030, tp13030, tm13030, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13030, agent13030, scalar13030, tp13030, tm13030, ep13030, em13030, dsL]

theorem negative13030 :
    Eminus aL (agent13030.root+dsL) scalar13030.worldRadius world13030.frame
      agent13030.frame tm13030 ≤ -em13030 := by
  apply negative_check (lo := (13669588523432344457 / 20000000000000000000)) (hi := (34173971308580861143 / 50000000000000000000))
    (y := (-((7162714814420641509 / 10000000000000000000)))) (u := (1954282033467737749 / 4000000000000000000))
  · norm_num [world13030, agent13030, scalar13030, tp13030, tm13030, ep13030, em13030, dsL]
  · norm_num [world13030, agent13030, scalar13030, tp13030, tm13030, ep13030, em13030, dsL]
  · norm_num [world13030, agent13030, scalar13030, tp13030, tm13030, ep13030, em13030, dsL]
  · norm_num [world13030, agent13030, scalar13030, tp13030, tm13030, ep13030, em13030, dsL]
  · norm_num [world13030, agent13030, scalar13030, tp13030, tm13030, ep13030, em13030, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13030, agent13030, tp13030, tm13030, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13030, agent13030, tp13030, tm13030, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13030, agent13030, scalar13030, tp13030, tm13030, ep13030, em13030, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13030, agent13030, tp13030, tm13030, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13030, agent13030, scalar13030, tp13030, tm13030, ep13030, em13030, dsL]

theorem tails13030 :
    exp (-((13030:ℝ)*ep13030)) ≤ scalar13030.upperTail ∧
    exp (-((13030:ℝ)*em13030)) ≤ scalar13030.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13030:ℝ)) (by norm_num [ep13030]) ?_)
      (show bp13030^8 ≤ scalar13030.upperTail by norm_num [bp13030, scalar13030])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13030, bp13030, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13030:ℝ)) (by norm_num [em13030]) ?_)
      (show bm13030^8 ≤ scalar13030.lowerTail by norm_num [bm13030, scalar13030])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13030, bm13030, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13030 :
    agent13030.root+dsL+scalar13030.worldRadius < √(1/100/aL) ∧
    2*(agent13030.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13030, agent13030, scalar13030, tp13030, tm13030, ep13030, em13030, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13030, agent13030, scalar13030, tp13030, tm13030, ep13030, em13030, dsL]

noncomputable def master13030 : MasterCertificate 13030 world13030 agent13030 :=
  master scalar13030 dsL tp13030 tm13030 ep13030 em13030
    (by norm_num [dsL]) (by norm_num [tp13030]) (by norm_num [tm13030])
    (by norm_num [ep13030]) (by norm_num [em13030])
    positive13030 negative13030 tails13030.1 tails13030.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13030.1 tailGuards13030.2

theorem preserves13030 : master13030.toScalarCertificate = scalar13030 := rfl

noncomputable def tp13031 : ℝ := (2345317271 / 10000000000)
noncomputable def tm13031 : ℝ := (-((6126581873 / 10000000000)))
noncomputable def ep13031 : ℝ := (52274677151319107 / 100000000000000000000)
noncomputable def em13031 : ℝ := (6355769370236641 / 12500000000000000000)
noncomputable def bp13031 : ℝ := (10669473044183635647 / 25000000000000000000)
noncomputable def bm13031 : ℝ := (43682601130411912659 / 100000000000000000000)

theorem positive13031 :
    Eplus aL (agent13031.root+dsL) scalar13031.worldRadius world13031.frame
      agent13031.frame tp13031 ≤ -ep13031 := by
  apply positive_check (eT := (57841436730330905497 / 50000000000000000000)) (y := (761607823576455189 / 2000000000000000000)) (u := (146346060989843547143 / 100000000000000000000))
  · norm_num [world13031, agent13031, scalar13031, tp13031, tm13031, ep13031, em13031, dsL]
  · norm_num [world13031, agent13031, scalar13031, tp13031, tm13031, ep13031, em13031, dsL]
  · norm_num [world13031, agent13031, scalar13031, tp13031, tm13031, ep13031, em13031, dsL]
  · norm_num [world13031, agent13031, scalar13031, tp13031, tm13031, ep13031, em13031, dsL]
  · norm_num [world13031, agent13031, scalar13031, tp13031, tm13031, ep13031, em13031, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13031, agent13031, tp13031, tm13031, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13031, agent13031, scalar13031, tp13031, tm13031, ep13031, em13031, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13031, agent13031, tp13031, tm13031, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13031, agent13031, scalar13031, tp13031, tm13031, ep13031, em13031, dsL]

theorem negative13031 :
    Eminus aL (agent13031.root+dsL) scalar13031.worldRadius world13031.frame
      agent13031.frame tm13031 ≤ -em13031 := by
  apply negative_check (lo := (68347818013674943197 / 100000000000000000000)) (hi := (34173909006837471599 / 50000000000000000000))
    (y := (-((14325416932589218541 / 20000000000000000000)))) (u := (12214270462943728897 / 25000000000000000000))
  · norm_num [world13031, agent13031, scalar13031, tp13031, tm13031, ep13031, em13031, dsL]
  · norm_num [world13031, agent13031, scalar13031, tp13031, tm13031, ep13031, em13031, dsL]
  · norm_num [world13031, agent13031, scalar13031, tp13031, tm13031, ep13031, em13031, dsL]
  · norm_num [world13031, agent13031, scalar13031, tp13031, tm13031, ep13031, em13031, dsL]
  · norm_num [world13031, agent13031, scalar13031, tp13031, tm13031, ep13031, em13031, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13031, agent13031, tp13031, tm13031, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13031, agent13031, tp13031, tm13031, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13031, agent13031, scalar13031, tp13031, tm13031, ep13031, em13031, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13031, agent13031, tp13031, tm13031, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13031, agent13031, scalar13031, tp13031, tm13031, ep13031, em13031, dsL]

theorem tails13031 :
    exp (-((13031:ℝ)*ep13031)) ≤ scalar13031.upperTail ∧
    exp (-((13031:ℝ)*em13031)) ≤ scalar13031.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13031:ℝ)) (by norm_num [ep13031]) ?_)
      (show bp13031^8 ≤ scalar13031.upperTail by norm_num [bp13031, scalar13031])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13031, bp13031, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13031:ℝ)) (by norm_num [em13031]) ?_)
      (show bm13031^8 ≤ scalar13031.lowerTail by norm_num [bm13031, scalar13031])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13031, bm13031, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13031 :
    agent13031.root+dsL+scalar13031.worldRadius < √(1/100/aL) ∧
    2*(agent13031.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13031, agent13031, scalar13031, tp13031, tm13031, ep13031, em13031, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13031, agent13031, scalar13031, tp13031, tm13031, ep13031, em13031, dsL]

noncomputable def master13031 : MasterCertificate 13031 world13031 agent13031 :=
  master scalar13031 dsL tp13031 tm13031 ep13031 em13031
    (by norm_num [dsL]) (by norm_num [tp13031]) (by norm_num [tm13031])
    (by norm_num [ep13031]) (by norm_num [em13031])
    positive13031 negative13031 tails13031.1 tails13031.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13031.1 tailGuards13031.2

theorem preserves13031 : master13031.toScalarCertificate = scalar13031 := rfl

noncomputable def tp13032 : ℝ := (2345392009 / 10000000000)
noncomputable def tm13032 : ℝ := (-((191460647 / 312500000)))
noncomputable def ep13032 : ℝ := (10455385181032997 / 20000000000000000000)
noncomputable def em13032 : ℝ := (2542403250658457 / 5000000000000000000)
noncomputable def bp13032 : ℝ := (8534708059449798167 / 20000000000000000000)
noncomputable def bm13032 : ℝ := (170619006985206603 / 390625000000000000)

theorem positive13032 :
    Eplus aL (agent13032.root+dsL) scalar13032.worldRadius world13032.frame
      agent13032.frame tp13032 ≤ -ep13032 := by
  apply positive_check (eT := (1807547719936111293 / 1562500000000000000)) (y := (7616212999527952057 / 20000000000000000000)) (u := (2926940942009254639 / 2000000000000000000))
  · norm_num [world13032, agent13032, scalar13032, tp13032, tm13032, ep13032, em13032, dsL]
  · norm_num [world13032, agent13032, scalar13032, tp13032, tm13032, ep13032, em13032, dsL]
  · norm_num [world13032, agent13032, scalar13032, tp13032, tm13032, ep13032, em13032, dsL]
  · norm_num [world13032, agent13032, scalar13032, tp13032, tm13032, ep13032, em13032, dsL]
  · norm_num [world13032, agent13032, scalar13032, tp13032, tm13032, ep13032, em13032, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13032, agent13032, tp13032, tm13032, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13032, agent13032, scalar13032, tp13032, tm13032, ep13032, em13032, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13032, agent13032, tp13032, tm13032, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13032, agent13032, scalar13032, tp13032, tm13032, ep13032, em13032, dsL]

theorem negative13032 :
    Eminus aL (agent13032.root+dsL) scalar13032.worldRadius world13032.frame
      agent13032.frame tm13032 ≤ -em13032 := by
  apply negative_check (lo := (8543461725958818513 / 12500000000000000000)) (hi := (13669538761534109621 / 20000000000000000000))
    (y := (-((71627020907094797667 / 100000000000000000000)))) (u := (48857113001033297837 / 100000000000000000000))
  · norm_num [world13032, agent13032, scalar13032, tp13032, tm13032, ep13032, em13032, dsL]
  · norm_num [world13032, agent13032, scalar13032, tp13032, tm13032, ep13032, em13032, dsL]
  · norm_num [world13032, agent13032, scalar13032, tp13032, tm13032, ep13032, em13032, dsL]
  · norm_num [world13032, agent13032, scalar13032, tp13032, tm13032, ep13032, em13032, dsL]
  · norm_num [world13032, agent13032, scalar13032, tp13032, tm13032, ep13032, em13032, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13032, agent13032, tp13032, tm13032, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13032, agent13032, tp13032, tm13032, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13032, agent13032, scalar13032, tp13032, tm13032, ep13032, em13032, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13032, agent13032, tp13032, tm13032, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13032, agent13032, scalar13032, tp13032, tm13032, ep13032, em13032, dsL]

theorem tails13032 :
    exp (-((13032:ℝ)*ep13032)) ≤ scalar13032.upperTail ∧
    exp (-((13032:ℝ)*em13032)) ≤ scalar13032.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13032:ℝ)) (by norm_num [ep13032]) ?_)
      (show bp13032^8 ≤ scalar13032.upperTail by norm_num [bp13032, scalar13032])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13032, bp13032, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13032:ℝ)) (by norm_num [em13032]) ?_)
      (show bm13032^8 ≤ scalar13032.lowerTail by norm_num [bm13032, scalar13032])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13032, bm13032, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13032 :
    agent13032.root+dsL+scalar13032.worldRadius < √(1/100/aL) ∧
    2*(agent13032.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13032, agent13032, scalar13032, tp13032, tm13032, ep13032, em13032, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13032, agent13032, scalar13032, tp13032, tm13032, ep13032, em13032, dsL]

noncomputable def master13032 : MasterCertificate 13032 world13032 agent13032 :=
  master scalar13032 dsL tp13032 tm13032 ep13032 em13032
    (by norm_num [dsL]) (by norm_num [tp13032]) (by norm_num [tm13032])
    (by norm_num [ep13032]) (by norm_num [em13032])
    positive13032 negative13032 tails13032.1 tails13032.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13032.1 tailGuards13032.2

theorem preserves13032 : master13032.toScalarCertificate = scalar13032 := rfl

noncomputable def tp13033 : ℝ := (2345466723 / 10000000000)
noncomputable def tm13033 : ℝ := (-((612689943 / 1000000000)))
noncomputable def ep13033 : ℝ := (418233380073751 / 800000000000000000)
noncomputable def em13033 : ℝ := (6356246632812291 / 12500000000000000000)
noncomputable def bp13033 : ℝ := (10667297529009819187 / 25000000000000000000)
noncomputable def bm13033 : ℝ := (43674332053351783809 / 100000000000000000000)

theorem positive13033 :
    Eplus aL (agent13033.root+dsL) scalar13033.worldRadius world13033.frame
      agent13033.frame tp13033 ≤ -ep13033 := by
  apply positive_check (eT := (115683234551706751969 / 100000000000000000000)) (y := (380817389184012143 / 1000000000000000000)) (u := (36587008341730060083 / 25000000000000000000))
  · norm_num [world13033, agent13033, scalar13033, tp13033, tm13033, ep13033, em13033, dsL]
  · norm_num [world13033, agent13033, scalar13033, tp13033, tm13033, ep13033, em13033, dsL]
  · norm_num [world13033, agent13033, scalar13033, tp13033, tm13033, ep13033, em13033, dsL]
  · norm_num [world13033, agent13033, scalar13033, tp13033, tm13033, ep13033, em13033, dsL]
  · norm_num [world13033, agent13033, scalar13033, tp13033, tm13033, ep13033, em13033, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13033, agent13033, tp13033, tm13033, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13033, agent13033, scalar13033, tp13033, tm13033, ep13033, em13033, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13033, agent13033, tp13033, tm13033, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13033, agent13033, scalar13033, tp13033, tm13033, ep13033, em13033, dsL]

theorem negative13033 :
    Eminus aL (agent13033.root+dsL) scalar13033.worldRadius world13033.frame
      agent13033.frame tm13033 ≤ -em13033 := by
  apply negative_check (lo := (34173784995310129593 / 50000000000000000000)) (hi := (68347569990620259187 / 100000000000000000000))
    (y := (-((14325391328659706141 / 20000000000000000000)))) (u := (24428572199239473667 / 50000000000000000000))
  · norm_num [world13033, agent13033, scalar13033, tp13033, tm13033, ep13033, em13033, dsL]
  · norm_num [world13033, agent13033, scalar13033, tp13033, tm13033, ep13033, em13033, dsL]
  · norm_num [world13033, agent13033, scalar13033, tp13033, tm13033, ep13033, em13033, dsL]
  · norm_num [world13033, agent13033, scalar13033, tp13033, tm13033, ep13033, em13033, dsL]
  · norm_num [world13033, agent13033, scalar13033, tp13033, tm13033, ep13033, em13033, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13033, agent13033, tp13033, tm13033, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13033, agent13033, tp13033, tm13033, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13033, agent13033, scalar13033, tp13033, tm13033, ep13033, em13033, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13033, agent13033, tp13033, tm13033, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13033, agent13033, scalar13033, tp13033, tm13033, ep13033, em13033, dsL]

theorem tails13033 :
    exp (-((13033:ℝ)*ep13033)) ≤ scalar13033.upperTail ∧
    exp (-((13033:ℝ)*em13033)) ≤ scalar13033.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13033:ℝ)) (by norm_num [ep13033]) ?_)
      (show bp13033^8 ≤ scalar13033.upperTail by norm_num [bp13033, scalar13033])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13033, bp13033, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13033:ℝ)) (by norm_num [em13033]) ?_)
      (show bm13033^8 ≤ scalar13033.lowerTail by norm_num [bm13033, scalar13033])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13033, bm13033, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13033 :
    agent13033.root+dsL+scalar13033.worldRadius < √(1/100/aL) ∧
    2*(agent13033.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13033, agent13033, scalar13033, tp13033, tm13033, ep13033, em13033, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13033, agent13033, scalar13033, tp13033, tm13033, ep13033, em13033, dsL]

noncomputable def master13033 : MasterCertificate 13033 world13033 agent13033 :=
  master scalar13033 dsL tp13033 tm13033 ep13033 em13033
    (by norm_num [dsL]) (by norm_num [tp13033]) (by norm_num [tm13033])
    (by norm_num [ep13033]) (by norm_num [em13033])
    positive13033 negative13033 tails13033.1 tails13033.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13033.1 tailGuards13033.2

theorem preserves13033 : master13033.toScalarCertificate = scalar13033 := rfl

noncomputable def tp13034 : ℝ := (1172770721 / 5000000000)
noncomputable def tm13034 : ℝ := (-((153176451 / 250000000)))
noncomputable def ep13034 : ℝ := (653517737723297 / 1250000000000000000)
noncomputable def em13034 : ℝ := (25425940515128067 / 50000000000000000000)
noncomputable def bp13034 : ℝ := (42664840204984069883 / 100000000000000000000)
noncomputable def bm13034 : ℝ := (21835099279716670677 / 50000000000000000000)

theorem positive13034 :
    Eplus aL (agent13034.root+dsL) scalar13034.worldRadius world13034.frame
      agent13034.frame tp13034 ≤ -ep13034 := by
  apply positive_check (eT := (28920853774109995291 / 25000000000000000000)) (y := (9520603274364567037 / 25000000000000000000)) (u := (36587255004509376037 / 25000000000000000000))
  · norm_num [world13034, agent13034, scalar13034, tp13034, tm13034, ep13034, em13034, dsL]
  · norm_num [world13034, agent13034, scalar13034, tp13034, tm13034, ep13034, em13034, dsL]
  · norm_num [world13034, agent13034, scalar13034, tp13034, tm13034, ep13034, em13034, dsL]
  · norm_num [world13034, agent13034, scalar13034, tp13034, tm13034, ep13034, em13034, dsL]
  · norm_num [world13034, agent13034, scalar13034, tp13034, tm13034, ep13034, em13034, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13034, agent13034, tp13034, tm13034, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13034, agent13034, scalar13034, tp13034, tm13034, ep13034, em13034, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13034, agent13034, tp13034, tm13034, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13034, agent13034, scalar13034, tp13034, tm13034, ep13034, em13034, dsL]

theorem negative13034 :
    Eminus aL (agent13034.root+dsL) scalar13034.worldRadius world13034.frame
      agent13034.frame tm13034 ≤ -em13034 := by
  apply negative_check (lo := (13669489321836892423 / 20000000000000000000)) (hi := (17086861652296115529 / 25000000000000000000))
    (y := (-((71626891990570043439 / 100000000000000000000)))) (u := (48857175985966072999 / 100000000000000000000))
  · norm_num [world13034, agent13034, scalar13034, tp13034, tm13034, ep13034, em13034, dsL]
  · norm_num [world13034, agent13034, scalar13034, tp13034, tm13034, ep13034, em13034, dsL]
  · norm_num [world13034, agent13034, scalar13034, tp13034, tm13034, ep13034, em13034, dsL]
  · norm_num [world13034, agent13034, scalar13034, tp13034, tm13034, ep13034, em13034, dsL]
  · norm_num [world13034, agent13034, scalar13034, tp13034, tm13034, ep13034, em13034, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13034, agent13034, tp13034, tm13034, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13034, agent13034, tp13034, tm13034, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13034, agent13034, scalar13034, tp13034, tm13034, ep13034, em13034, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13034, agent13034, tp13034, tm13034, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13034, agent13034, scalar13034, tp13034, tm13034, ep13034, em13034, dsL]

theorem tails13034 :
    exp (-((13034:ℝ)*ep13034)) ≤ scalar13034.upperTail ∧
    exp (-((13034:ℝ)*em13034)) ≤ scalar13034.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13034:ℝ)) (by norm_num [ep13034]) ?_)
      (show bp13034^8 ≤ scalar13034.upperTail by norm_num [bp13034, scalar13034])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13034, bp13034, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13034:ℝ)) (by norm_num [em13034]) ?_)
      (show bm13034^8 ≤ scalar13034.lowerTail by norm_num [bm13034, scalar13034])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13034, bm13034, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13034 :
    agent13034.root+dsL+scalar13034.worldRadius < √(1/100/aL) ∧
    2*(agent13034.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13034, agent13034, scalar13034, tp13034, tm13034, ep13034, em13034, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13034, agent13034, scalar13034, tp13034, tm13034, ep13034, em13034, dsL]

noncomputable def master13034 : MasterCertificate 13034 world13034 agent13034 :=
  master scalar13034 dsL tp13034 tm13034 ep13034 em13034
    (by norm_num [dsL]) (by norm_num [tp13034]) (by norm_num [tm13034])
    (by norm_num [ep13034]) (by norm_num [em13034])
    positive13034 negative13034 tails13034.1 tails13034.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13034.1 tailGuards13034.2

theorem preserves13034 : master13034.toScalarCertificate = scalar13034 := rfl

noncomputable def tp13035 : ℝ := (469123217 / 2000000000)
noncomputable def tm13035 : ℝ := (-((1531804187 / 2500000000)))
noncomputable def ep13035 : ℝ := (26141832309953273 / 50000000000000000000)
noncomputable def em13035 : ℝ := (25426894063198877 / 50000000000000000000)
noncomputable def bp13035 : ℝ := (42660491127966240751 / 100000000000000000000)
noncomputable def bm13035 : ℝ := (10916516467145191381 / 25000000000000000000)

theorem positive13035 :
    Eplus aL (agent13035.root+dsL) scalar13035.worldRadius world13035.frame
      agent13035.frame tp13035 ≤ -ep13035 := by
  apply positive_check (eT := (57841797564028198141 / 50000000000000000000)) (y := (19041543186628968553 / 50000000000000000000)) (u := (14635000535388934847 / 10000000000000000000))
  · norm_num [world13035, agent13035, scalar13035, tp13035, tm13035, ep13035, em13035, dsL]
  · norm_num [world13035, agent13035, scalar13035, tp13035, tm13035, ep13035, em13035, dsL]
  · norm_num [world13035, agent13035, scalar13035, tp13035, tm13035, ep13035, em13035, dsL]
  · norm_num [world13035, agent13035, scalar13035, tp13035, tm13035, ep13035, em13035, dsL]
  · norm_num [world13035, agent13035, scalar13035, tp13035, tm13035, ep13035, em13035, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13035, agent13035, tp13035, tm13035, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13035, agent13035, scalar13035, tp13035, tm13035, ep13035, em13035, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13035, agent13035, tp13035, tm13035, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13035, agent13035, scalar13035, tp13035, tm13035, ep13035, em13035, dsL]

theorem negative13035 :
    Eminus aL (agent13035.root+dsL) scalar13035.worldRadius world13035.frame
      agent13035.frame tm13035 ≤ -em13035 := by
  apply negative_check (lo := (68347322754950308847 / 100000000000000000000)) (hi := (4271707672184394303 / 6250000000000000000))
    (y := (-((3581341451916600701 / 5000000000000000000)))) (u := (977144134853229503 / 2000000000000000000))
  · norm_num [world13035, agent13035, scalar13035, tp13035, tm13035, ep13035, em13035, dsL]
  · norm_num [world13035, agent13035, scalar13035, tp13035, tm13035, ep13035, em13035, dsL]
  · norm_num [world13035, agent13035, scalar13035, tp13035, tm13035, ep13035, em13035, dsL]
  · norm_num [world13035, agent13035, scalar13035, tp13035, tm13035, ep13035, em13035, dsL]
  · norm_num [world13035, agent13035, scalar13035, tp13035, tm13035, ep13035, em13035, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13035, agent13035, tp13035, tm13035, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13035, agent13035, tp13035, tm13035, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13035, agent13035, scalar13035, tp13035, tm13035, ep13035, em13035, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13035, agent13035, tp13035, tm13035, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13035, agent13035, scalar13035, tp13035, tm13035, ep13035, em13035, dsL]

theorem tails13035 :
    exp (-((13035:ℝ)*ep13035)) ≤ scalar13035.upperTail ∧
    exp (-((13035:ℝ)*em13035)) ≤ scalar13035.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13035:ℝ)) (by norm_num [ep13035]) ?_)
      (show bp13035^8 ≤ scalar13035.upperTail by norm_num [bp13035, scalar13035])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13035, bp13035, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13035:ℝ)) (by norm_num [em13035]) ?_)
      (show bm13035^8 ≤ scalar13035.lowerTail by norm_num [bm13035, scalar13035])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13035, bm13035, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13035 :
    agent13035.root+dsL+scalar13035.worldRadius < √(1/100/aL) ∧
    2*(agent13035.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13035, agent13035, scalar13035, tp13035, tm13035, ep13035, em13035, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13035, agent13035, scalar13035, tp13035, tm13035, ep13035, em13035, dsL]

noncomputable def master13035 : MasterCertificate 13035 world13035 agent13035 :=
  master scalar13035 dsL tp13035 tm13035 ep13035 em13035
    (by norm_num [dsL]) (by norm_num [tp13035]) (by norm_num [tm13035])
    (by norm_num [ep13035]) (by norm_num [em13035])
    positive13035 negative13035 tails13035.1 tails13035.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13035.1 tailGuards13035.2

theorem preserves13035 : master13035.toScalarCertificate = scalar13035 := rfl

noncomputable def tp13036 : ℝ := (2345690683 / 10000000000)
noncomputable def tm13036 : ℝ := (-((6127375099 / 10000000000)))
noncomputable def ep13036 : ℝ := (6535738430719079 / 12500000000000000000)
noncomputable def em13036 : ℝ := (50855692679061033 / 100000000000000000000)
noncomputable def bp13036 : ℝ := (2132807209224372441 / 5000000000000000000)
noncomputable def bm13036 : ℝ := (43661935170264628993 / 100000000000000000000)

theorem positive13036 :
    Eplus aL (agent13036.root+dsL) scalar13036.worldRadius world13036.frame
      agent13036.frame tp13036 ≤ -ep13036 := by
  apply positive_check (eT := (115683774869358369377 / 100000000000000000000)) (y := (19041879640221099213 / 50000000000000000000)) (u := (18293873769612867877 / 12500000000000000000))
  · norm_num [world13036, agent13036, scalar13036, tp13036, tm13036, ep13036, em13036, dsL]
  · norm_num [world13036, agent13036, scalar13036, tp13036, tm13036, ep13036, em13036, dsL]
  · norm_num [world13036, agent13036, scalar13036, tp13036, tm13036, ep13036, em13036, dsL]
  · norm_num [world13036, agent13036, scalar13036, tp13036, tm13036, ep13036, em13036, dsL]
  · norm_num [world13036, agent13036, scalar13036, tp13036, tm13036, ep13036, em13036, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13036, agent13036, tp13036, tm13036, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13036, agent13036, scalar13036, tp13036, tm13036, ep13036, em13036, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13036, agent13036, tp13036, tm13036, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13036, agent13036, scalar13036, tp13036, tm13036, ep13036, em13036, dsL]

theorem negative13036 :
    Eminus aL (agent13036.root+dsL) scalar13036.worldRadius world13036.frame
      agent13036.frame tm13036 ≤ -em13036 := by
  apply negative_check (lo := (68347200359384963843 / 100000000000000000000)) (hi := (17086800089846240961 / 25000000000000000000))
    (y := (-((17906690684872426481 / 25000000000000000000)))) (u := (48857239134434667291 / 100000000000000000000))
  · norm_num [world13036, agent13036, scalar13036, tp13036, tm13036, ep13036, em13036, dsL]
  · norm_num [world13036, agent13036, scalar13036, tp13036, tm13036, ep13036, em13036, dsL]
  · norm_num [world13036, agent13036, scalar13036, tp13036, tm13036, ep13036, em13036, dsL]
  · norm_num [world13036, agent13036, scalar13036, tp13036, tm13036, ep13036, em13036, dsL]
  · norm_num [world13036, agent13036, scalar13036, tp13036, tm13036, ep13036, em13036, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13036, agent13036, tp13036, tm13036, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13036, agent13036, tp13036, tm13036, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13036, agent13036, scalar13036, tp13036, tm13036, ep13036, em13036, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13036, agent13036, tp13036, tm13036, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13036, agent13036, scalar13036, tp13036, tm13036, ep13036, em13036, dsL]

theorem tails13036 :
    exp (-((13036:ℝ)*ep13036)) ≤ scalar13036.upperTail ∧
    exp (-((13036:ℝ)*em13036)) ≤ scalar13036.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13036:ℝ)) (by norm_num [ep13036]) ?_)
      (show bp13036^8 ≤ scalar13036.upperTail by norm_num [bp13036, scalar13036])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13036, bp13036, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13036:ℝ)) (by norm_num [em13036]) ?_)
      (show bm13036^8 ≤ scalar13036.lowerTail by norm_num [bm13036, scalar13036])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13036, bm13036, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13036 :
    agent13036.root+dsL+scalar13036.worldRadius < √(1/100/aL) ∧
    2*(agent13036.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13036, agent13036, scalar13036, tp13036, tm13036, ep13036, em13036, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13036, agent13036, scalar13036, tp13036, tm13036, ep13036, em13036, dsL]

noncomputable def master13036 : MasterCertificate 13036 world13036 agent13036 :=
  master scalar13036 dsL tp13036 tm13036 ep13036 em13036
    (by norm_num [dsL]) (by norm_num [tp13036]) (by norm_num [tm13036])
    (by norm_num [ep13036]) (by norm_num [em13036])
    positive13036 negative13036 tails13036.1 tails13036.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13036.1 tailGuards13036.2

theorem preserves13036 : master13036.toScalarCertificate = scalar13036 := rfl

noncomputable def tp13037 : ℝ := (1172882621 / 5000000000)
noncomputable def tm13037 : ℝ := (-((765941683 / 1250000000)))
noncomputable def ep13037 : ℝ := (26144075327040169 / 50000000000000000000)
noncomputable def em13037 : ℝ := (50857597593046957 / 100000000000000000000)
noncomputable def bp13037 : ℝ := (10662949294736277989 / 25000000000000000000)
noncomputable def bm13037 : ℝ := (5457225549720558421 / 12500000000000000000)

theorem positive13037 :
    Eplus aL (agent13037.root+dsL) scalar13037.worldRadius world13037.frame
      agent13037.frame tp13037 ≤ -ep13037 := by
  apply positive_check (eT := (14460494295428217987 / 12500000000000000000)) (y := (38084431628567987929 / 100000000000000000000)) (u := (146351974148350257653 / 100000000000000000000))
  · norm_num [world13037, agent13037, scalar13037, tp13037, tm13037, ep13037, em13037, dsL]
  · norm_num [world13037, agent13037, scalar13037, tp13037, tm13037, ep13037, em13037, dsL]
  · norm_num [world13037, agent13037, scalar13037, tp13037, tm13037, ep13037, em13037, dsL]
  · norm_num [world13037, agent13037, scalar13037, tp13037, tm13037, ep13037, em13037, dsL]
  · norm_num [world13037, agent13037, scalar13037, tp13037, tm13037, ep13037, em13037, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13037, agent13037, tp13037, tm13037, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13037, agent13037, scalar13037, tp13037, tm13037, ep13037, em13037, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13037, agent13037, tp13037, tm13037, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13037, agent13037, scalar13037, tp13037, tm13037, ep13037, em13037, dsL]

theorem negative13037 :
    Eminus aL (agent13037.root+dsL) scalar13037.worldRadius world13037.frame
      agent13037.frame tm13037 ≤ -em13037 := by
  apply negative_check (lo := (68347077847593122789 / 100000000000000000000)) (hi := (6834707784759312279 / 10000000000000000000))
    (y := (-((71626697427739870379 / 100000000000000000000)))) (u := (24428635521981443831 / 50000000000000000000))
  · norm_num [world13037, agent13037, scalar13037, tp13037, tm13037, ep13037, em13037, dsL]
  · norm_num [world13037, agent13037, scalar13037, tp13037, tm13037, ep13037, em13037, dsL]
  · norm_num [world13037, agent13037, scalar13037, tp13037, tm13037, ep13037, em13037, dsL]
  · norm_num [world13037, agent13037, scalar13037, tp13037, tm13037, ep13037, em13037, dsL]
  · norm_num [world13037, agent13037, scalar13037, tp13037, tm13037, ep13037, em13037, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13037, agent13037, tp13037, tm13037, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13037, agent13037, tp13037, tm13037, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13037, agent13037, scalar13037, tp13037, tm13037, ep13037, em13037, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13037, agent13037, tp13037, tm13037, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13037, agent13037, scalar13037, tp13037, tm13037, ep13037, em13037, dsL]

theorem tails13037 :
    exp (-((13037:ℝ)*ep13037)) ≤ scalar13037.upperTail ∧
    exp (-((13037:ℝ)*em13037)) ≤ scalar13037.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13037:ℝ)) (by norm_num [ep13037]) ?_)
      (show bp13037^8 ≤ scalar13037.upperTail by norm_num [bp13037, scalar13037])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13037, bp13037, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13037:ℝ)) (by norm_num [em13037]) ?_)
      (show bm13037^8 ≤ scalar13037.lowerTail by norm_num [bm13037, scalar13037])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13037, bm13037, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13037 :
    agent13037.root+dsL+scalar13037.worldRadius < √(1/100/aL) ∧
    2*(agent13037.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13037, agent13037, scalar13037, tp13037, tm13037, ep13037, em13037, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13037, agent13037, scalar13037, tp13037, tm13037, ep13037, em13037, dsL]

noncomputable def master13037 : MasterCertificate 13037 world13037 agent13037 :=
  master scalar13037 dsL tp13037 tm13037 ep13037 em13037
    (by norm_num [dsL]) (by norm_num [tp13037]) (by norm_num [tm13037])
    (by norm_num [ep13037]) (by norm_num [em13037])
    positive13037 negative13037 tails13037.1 tails13037.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13037.1 tailGuards13037.2

theorem preserves13037 : master13037.toScalarCertificate = scalar13037 := rfl

noncomputable def tp13038 : ℝ := (2345839791 / 10000000000)
noncomputable def tm13038 : ℝ := (-((3063845887 / 5000000000)))
noncomputable def ep13038 : ℝ := (52290392046317719 / 100000000000000000000)
noncomputable def em13038 : ℝ := (50859500797589977 / 100000000000000000000)
noncomputable def bp13038 : ℝ := (42647451639497780297 / 100000000000000000000)
noncomputable def bm13038 : ℝ := (8730735004870698183 / 20000000000000000000)

theorem positive13038 :
    Eplus aL (agent13038.root+dsL) scalar13038.worldRadius world13038.frame
      agent13038.frame tp13038 ≤ -ep13038 := by
  apply positive_check (eT := (11568413381866692783 / 10000000000000000000)) (y := (9521276106328859147 / 25000000000000000000)) (u := (73176479401492256559 / 50000000000000000000))
  · norm_num [world13038, agent13038, scalar13038, tp13038, tm13038, ep13038, em13038, dsL]
  · norm_num [world13038, agent13038, scalar13038, tp13038, tm13038, ep13038, em13038, dsL]
  · norm_num [world13038, agent13038, scalar13038, tp13038, tm13038, ep13038, em13038, dsL]
  · norm_num [world13038, agent13038, scalar13038, tp13038, tm13038, ep13038, em13038, dsL]
  · norm_num [world13038, agent13038, scalar13038, tp13038, tm13038, ep13038, em13038, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13038, agent13038, tp13038, tm13038, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13038, agent13038, scalar13038, tp13038, tm13038, ep13038, em13038, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13038, agent13038, tp13038, tm13038, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13038, agent13038, scalar13038, tp13038, tm13038, ep13038, em13038, dsL]

theorem negative13038 :
    Eminus aL (agent13038.root+dsL) scalar13038.worldRadius world13038.frame
      agent13038.frame tm13038 ≤ -em13038 := by
  apply negative_check (lo := (34173477756212013649 / 50000000000000000000)) (hi := (68346955512424027299 / 100000000000000000000))
    (y := (-((71626632501516419417 / 100000000000000000000)))) (u := (381697677852766839 / 781250000000000000))
  · norm_num [world13038, agent13038, scalar13038, tp13038, tm13038, ep13038, em13038, dsL]
  · norm_num [world13038, agent13038, scalar13038, tp13038, tm13038, ep13038, em13038, dsL]
  · norm_num [world13038, agent13038, scalar13038, tp13038, tm13038, ep13038, em13038, dsL]
  · norm_num [world13038, agent13038, scalar13038, tp13038, tm13038, ep13038, em13038, dsL]
  · norm_num [world13038, agent13038, scalar13038, tp13038, tm13038, ep13038, em13038, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13038, agent13038, tp13038, tm13038, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13038, agent13038, tp13038, tm13038, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13038, agent13038, scalar13038, tp13038, tm13038, ep13038, em13038, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13038, agent13038, tp13038, tm13038, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13038, agent13038, scalar13038, tp13038, tm13038, ep13038, em13038, dsL]

theorem tails13038 :
    exp (-((13038:ℝ)*ep13038)) ≤ scalar13038.upperTail ∧
    exp (-((13038:ℝ)*em13038)) ≤ scalar13038.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13038:ℝ)) (by norm_num [ep13038]) ?_)
      (show bp13038^8 ≤ scalar13038.upperTail by norm_num [bp13038, scalar13038])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13038, bp13038, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13038:ℝ)) (by norm_num [em13038]) ?_)
      (show bm13038^8 ≤ scalar13038.lowerTail by norm_num [bm13038, scalar13038])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13038, bm13038, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13038 :
    agent13038.root+dsL+scalar13038.worldRadius < √(1/100/aL) ∧
    2*(agent13038.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13038, agent13038, scalar13038, tp13038, tm13038, ep13038, em13038, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13038, agent13038, scalar13038, tp13038, tm13038, ep13038, em13038, dsL]

noncomputable def master13038 : MasterCertificate 13038 world13038 agent13038 :=
  master scalar13038 dsL tp13038 tm13038 ep13038 em13038
    (by norm_num [dsL]) (by norm_num [tp13038]) (by norm_num [tm13038])
    (by norm_num [ep13038]) (by norm_num [em13038])
    positive13038 negative13038 tails13038.1 tails13038.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13038.1 tailGuards13038.2

theorem preserves13038 : master13038.toScalarCertificate = scalar13038 := rfl

noncomputable def tp13039 : ℝ := (2345914307 / 10000000000)
noncomputable def tm13039 : ℝ := (-((6127850137 / 10000000000)))
noncomputable def ep13039 : ℝ := (2091705313174531 / 4000000000000000000)
noncomputable def em13039 : ℝ := (50861403439143301 / 100000000000000000000)
noncomputable def bp13039 : ℝ := (10660776681812034799 / 25000000000000000000)
noncomputable def bm13039 : ℝ := (21824773117181865771 / 50000000000000000000)

theorem positive13039 :
    Eplus aL (agent13039.root+dsL) scalar13039.worldRadius world13039.frame
      agent13039.frame tp13039 ≤ -ep13039 := by
  apply positive_check (eT := (115684313069789993713 / 100000000000000000000)) (y := (38085776764128763457 / 100000000000000000000)) (u := (18294242849254858881 / 12500000000000000000))
  · norm_num [world13039, agent13039, scalar13039, tp13039, tm13039, ep13039, em13039, dsL]
  · norm_num [world13039, agent13039, scalar13039, tp13039, tm13039, ep13039, em13039, dsL]
  · norm_num [world13039, agent13039, scalar13039, tp13039, tm13039, ep13039, em13039, dsL]
  · norm_num [world13039, agent13039, scalar13039, tp13039, tm13039, ep13039, em13039, dsL]
  · norm_num [world13039, agent13039, scalar13039, tp13039, tm13039, ep13039, em13039, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13039, agent13039, tp13039, tm13039, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13039, agent13039, scalar13039, tp13039, tm13039, ep13039, em13039, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13039, agent13039, tp13039, tm13039, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13039, agent13039, scalar13039, tp13039, tm13039, ep13039, em13039, dsL]

theorem negative13039 :
    Eminus aL (agent13039.root+dsL) scalar13039.worldRadius world13039.frame
      agent13039.frame tm13039 ≤ -em13039 := by
  apply negative_check (lo := (68346832895507804333 / 100000000000000000000)) (hi := (34173416447753902167 / 50000000000000000000))
    (y := (-((71626568269869398807 / 100000000000000000000)))) (u := (24428667073507244919 / 50000000000000000000))
  · norm_num [world13039, agent13039, scalar13039, tp13039, tm13039, ep13039, em13039, dsL]
  · norm_num [world13039, agent13039, scalar13039, tp13039, tm13039, ep13039, em13039, dsL]
  · norm_num [world13039, agent13039, scalar13039, tp13039, tm13039, ep13039, em13039, dsL]
  · norm_num [world13039, agent13039, scalar13039, tp13039, tm13039, ep13039, em13039, dsL]
  · norm_num [world13039, agent13039, scalar13039, tp13039, tm13039, ep13039, em13039, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13039, agent13039, tp13039, tm13039, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13039, agent13039, tp13039, tm13039, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13039, agent13039, scalar13039, tp13039, tm13039, ep13039, em13039, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13039, agent13039, tp13039, tm13039, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13039, agent13039, scalar13039, tp13039, tm13039, ep13039, em13039, dsL]

theorem tails13039 :
    exp (-((13039:ℝ)*ep13039)) ≤ scalar13039.upperTail ∧
    exp (-((13039:ℝ)*em13039)) ≤ scalar13039.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13039:ℝ)) (by norm_num [ep13039]) ?_)
      (show bp13039^8 ≤ scalar13039.upperTail by norm_num [bp13039, scalar13039])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13039, bp13039, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13039:ℝ)) (by norm_num [em13039]) ?_)
      (show bm13039^8 ≤ scalar13039.lowerTail by norm_num [bm13039, scalar13039])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13039, bm13039, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13039 :
    agent13039.root+dsL+scalar13039.worldRadius < √(1/100/aL) ∧
    2*(agent13039.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13039, agent13039, scalar13039, tp13039, tm13039, ep13039, em13039, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13039, agent13039, scalar13039, tp13039, tm13039, ep13039, em13039, dsL]

noncomputable def master13039 : MasterCertificate 13039 world13039 agent13039 :=
  master scalar13039 dsL tp13039 tm13039 ep13039 em13039
    (by norm_num [dsL]) (by norm_num [tp13039]) (by norm_num [tm13039])
    (by norm_num [ep13039]) (by norm_num [em13039])
    positive13039 negative13039 tails13039.1 tails13039.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13039.1 tailGuards13039.2

theorem preserves13039 : master13039.toScalarCertificate = scalar13039 := rfl

noncomputable def tp13040 : ℝ := (2346060253 / 10000000000)
noncomputable def tm13040 : ℝ := (-((766028079 / 1250000000)))
noncomputable def ep13040 : ℝ := (10459244493193361 / 20000000000000000000)
noncomputable def em13040 : ℝ := (7947621718541 / 15625000000000000)
noncomputable def bp13040 : ℝ := (42637824559934794689 / 100000000000000000000)
noncomputable def bm13040 : ℝ := (43644369776100244033 / 100000000000000000000)

theorem positive13040 :
    Eplus aL (agent13040.root+dsL) scalar13040.worldRadius world13040.frame
      agent13040.frame tp13040 ≤ -ep13040 := by
  apply positive_check (eT := (115685005545672001891 / 100000000000000000000)) (y := (38085734661765613301 / 100000000000000000000)) (u := (18294235146947920343 / 12500000000000000000))
  · norm_num [world13040, agent13040, scalar13040, tp13040, tm13040, ep13040, em13040, dsL]
  · norm_num [world13040, agent13040, scalar13040, tp13040, tm13040, ep13040, em13040, dsL]
  · norm_num [world13040, agent13040, scalar13040, tp13040, tm13040, ep13040, em13040, dsL]
  · norm_num [world13040, agent13040, scalar13040, tp13040, tm13040, ep13040, em13040, dsL]
  · norm_num [world13040, agent13040, scalar13040, tp13040, tm13040, ep13040, em13040, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13040, agent13040, tp13040, tm13040, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13040, agent13040, scalar13040, tp13040, tm13040, ep13040, em13040, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13040, agent13040, tp13040, tm13040, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13040, agent13040, scalar13040, tp13040, tm13040, ep13040, em13040, dsL]

theorem negative13040 :
    Eminus aL (agent13040.root+dsL) scalar13040.worldRadius world13040.frame
      agent13040.frame tm13040 ≤ -em13040 := by
  apply negative_check (lo := (17086448206533772761 / 25000000000000000000)) (hi := (13669158565227018209 / 20000000000000000000))
    (y := (-((4476539695282757073 / 6250000000000000000)))) (u := (24429139319712279809 / 50000000000000000000))
  · norm_num [world13040, agent13040, scalar13040, tp13040, tm13040, ep13040, em13040, dsL]
  · norm_num [world13040, agent13040, scalar13040, tp13040, tm13040, ep13040, em13040, dsL]
  · norm_num [world13040, agent13040, scalar13040, tp13040, tm13040, ep13040, em13040, dsL]
  · norm_num [world13040, agent13040, scalar13040, tp13040, tm13040, ep13040, em13040, dsL]
  · norm_num [world13040, agent13040, scalar13040, tp13040, tm13040, ep13040, em13040, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13040, agent13040, tp13040, tm13040, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13040, agent13040, tp13040, tm13040, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13040, agent13040, scalar13040, tp13040, tm13040, ep13040, em13040, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13040, agent13040, tp13040, tm13040, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13040, agent13040, scalar13040, tp13040, tm13040, ep13040, em13040, dsL]

theorem tails13040 :
    exp (-((13040:ℝ)*ep13040)) ≤ scalar13040.upperTail ∧
    exp (-((13040:ℝ)*em13040)) ≤ scalar13040.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13040:ℝ)) (by norm_num [ep13040]) ?_)
      (show bp13040^8 ≤ scalar13040.upperTail by norm_num [bp13040, scalar13040])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13040, bp13040, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13040:ℝ)) (by norm_num [em13040]) ?_)
      (show bm13040^8 ≤ scalar13040.lowerTail by norm_num [bm13040, scalar13040])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13040, bm13040, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13040 :
    agent13040.root+dsL+scalar13040.worldRadius < √(1/100/aL) ∧
    2*(agent13040.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13040, agent13040, scalar13040, tp13040, tm13040, ep13040, em13040, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13040, agent13040, scalar13040, tp13040, tm13040, ep13040, em13040, dsL]

noncomputable def master13040 : MasterCertificate 13040 world13040 agent13040 :=
  master scalar13040 dsL tp13040 tm13040 ep13040 em13040
    (by norm_num [dsL]) (by norm_num [tp13040]) (by norm_num [tm13040])
    (by norm_num [ep13040]) (by norm_num [em13040])
    positive13040 negative13040 tails13040.1 tails13040.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13040.1 tailGuards13040.2

theorem preserves13040 : master13040.toScalarCertificate = scalar13040 := rfl

noncomputable def tp13041 : ℝ := (586533671 / 2500000000)
noncomputable def tm13041 : ℝ := (-((6128382769 / 10000000000)))
noncomputable def ep13041 : ℝ := (26149230324246993 / 50000000000000000000)
noncomputable def em13041 : ℝ := (25433339617733497 / 50000000000000000000)
noncomputable def bp13041 : ℝ := (42633481886250675031 / 100000000000000000000)
noncomputable def bm13041 : ℝ := (21820121540707436313 / 50000000000000000000)

theorem positive13041 :
    Eplus aL (agent13041.root+dsL) scalar13041.worldRadius world13041.frame
      agent13041.frame tp13041 ≤ -ep13041 := by
  apply positive_check (eT := (57842592121044187249 / 50000000000000000000)) (y := (38086406290758137967 / 100000000000000000000)) (u := (146354864133981936161 / 100000000000000000000))
  · norm_num [world13041, agent13041, scalar13041, tp13041, tm13041, ep13041, em13041, dsL]
  · norm_num [world13041, agent13041, scalar13041, tp13041, tm13041, ep13041, em13041, dsL]
  · norm_num [world13041, agent13041, scalar13041, tp13041, tm13041, ep13041, em13041, dsL]
  · norm_num [world13041, agent13041, scalar13041, tp13041, tm13041, ep13041, em13041, dsL]
  · norm_num [world13041, agent13041, scalar13041, tp13041, tm13041, ep13041, em13041, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13041, agent13041, tp13041, tm13041, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13041, agent13041, scalar13041, tp13041, tm13041, ep13041, em13041, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13041, agent13041, tp13041, tm13041, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13041, agent13041, scalar13041, tp13041, tm13041, ep13041, em13041, dsL]

theorem negative13041 :
    Eminus aL (agent13041.root+dsL) scalar13041.worldRadius world13041.frame
      agent13041.frame tm13041 ≤ -em13041 := by
  apply negative_check (lo := (17086417768976274373 / 25000000000000000000)) (hi := (68345671075905097493 / 100000000000000000000))
    (y := (-((71624570142451078139 / 100000000000000000000)))) (u := (3053644399284824023 / 6250000000000000000))
  · norm_num [world13041, agent13041, scalar13041, tp13041, tm13041, ep13041, em13041, dsL]
  · norm_num [world13041, agent13041, scalar13041, tp13041, tm13041, ep13041, em13041, dsL]
  · norm_num [world13041, agent13041, scalar13041, tp13041, tm13041, ep13041, em13041, dsL]
  · norm_num [world13041, agent13041, scalar13041, tp13041, tm13041, ep13041, em13041, dsL]
  · norm_num [world13041, agent13041, scalar13041, tp13041, tm13041, ep13041, em13041, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13041, agent13041, tp13041, tm13041, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13041, agent13041, tp13041, tm13041, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13041, agent13041, scalar13041, tp13041, tm13041, ep13041, em13041, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13041, agent13041, tp13041, tm13041, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13041, agent13041, scalar13041, tp13041, tm13041, ep13041, em13041, dsL]

theorem tails13041 :
    exp (-((13041:ℝ)*ep13041)) ≤ scalar13041.upperTail ∧
    exp (-((13041:ℝ)*em13041)) ≤ scalar13041.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13041:ℝ)) (by norm_num [ep13041]) ?_)
      (show bp13041^8 ≤ scalar13041.upperTail by norm_num [bp13041, scalar13041])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13041, bp13041, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13041:ℝ)) (by norm_num [em13041]) ?_)
      (show bm13041^8 ≤ scalar13041.lowerTail by norm_num [bm13041, scalar13041])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13041, bm13041, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13041 :
    agent13041.root+dsL+scalar13041.worldRadius < √(1/100/aL) ∧
    2*(agent13041.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13041, agent13041, scalar13041, tp13041, tm13041, ep13041, em13041, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13041, agent13041, scalar13041, tp13041, tm13041, ep13041, em13041, dsL]

noncomputable def master13041 : MasterCertificate 13041 world13041 agent13041 :=
  master scalar13041 dsL tp13041 tm13041 ep13041 em13041
    (by norm_num [dsL]) (by norm_num [tp13041]) (by norm_num [tm13041])
    (by norm_num [ep13041]) (by norm_num [em13041])
    positive13041 negative13041 tails13041.1 tails13041.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13041.1 tailGuards13041.2

theorem preserves13041 : master13041.toScalarCertificate = scalar13041 := rfl

noncomputable def tp13042 : ℝ := (1173104541 / 5000000000)
noncomputable def tm13042 : ℝ := (-((6128540739 / 10000000000)))
noncomputable def ep13042 : ℝ := (26150348890273373 / 50000000000000000000)
noncomputable def em13042 : ℝ := (50868578505992243 / 100000000000000000000)
noncomputable def bp13042 : ℝ := (42629140146378861251 / 100000000000000000000)
noncomputable def bm13042 : ℝ := (43636117257012068417 / 100000000000000000000)

theorem positive13042 :
    Eplus aL (agent13042.root+dsL) scalar13042.worldRadius world13042.frame
      agent13042.frame tp13042 ≤ -ep13042 := by
  apply positive_check (eT := (72303351709014767 / 62500000000000000)) (y := (19043538806434330789 / 50000000000000000000)) (u := (36588961662460653447 / 25000000000000000000))
  · norm_num [world13042, agent13042, scalar13042, tp13042, tm13042, ep13042, em13042, dsL]
  · norm_num [world13042, agent13042, scalar13042, tp13042, tm13042, ep13042, em13042, dsL]
  · norm_num [world13042, agent13042, scalar13042, tp13042, tm13042, ep13042, em13042, dsL]
  · norm_num [world13042, agent13042, scalar13042, tp13042, tm13042, ep13042, em13042, dsL]
  · norm_num [world13042, agent13042, scalar13042, tp13042, tm13042, ep13042, em13042, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13042, agent13042, tp13042, tm13042, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13042, agent13042, scalar13042, tp13042, tm13042, ep13042, em13042, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13042, agent13042, tp13042, tm13042, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13042, agent13042, scalar13042, tp13042, tm13042, ep13042, em13042, dsL]

theorem negative13042 :
    Eminus aL (agent13042.root+dsL) scalar13042.worldRadius world13042.frame
      agent13042.frame tm13042 ≤ -em13042 := by
  apply negative_check (lo := (68345549977698188877 / 100000000000000000000)) (hi := (34172774988849094439 / 50000000000000000000))
    (y := (-((716245040245485429 / 1000000000000000000)))) (u := (24429171346328953417 / 50000000000000000000))
  · norm_num [world13042, agent13042, scalar13042, tp13042, tm13042, ep13042, em13042, dsL]
  · norm_num [world13042, agent13042, scalar13042, tp13042, tm13042, ep13042, em13042, dsL]
  · norm_num [world13042, agent13042, scalar13042, tp13042, tm13042, ep13042, em13042, dsL]
  · norm_num [world13042, agent13042, scalar13042, tp13042, tm13042, ep13042, em13042, dsL]
  · norm_num [world13042, agent13042, scalar13042, tp13042, tm13042, ep13042, em13042, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13042, agent13042, tp13042, tm13042, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13042, agent13042, tp13042, tm13042, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13042, agent13042, scalar13042, tp13042, tm13042, ep13042, em13042, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13042, agent13042, tp13042, tm13042, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13042, agent13042, scalar13042, tp13042, tm13042, ep13042, em13042, dsL]

theorem tails13042 :
    exp (-((13042:ℝ)*ep13042)) ≤ scalar13042.upperTail ∧
    exp (-((13042:ℝ)*em13042)) ≤ scalar13042.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13042:ℝ)) (by norm_num [ep13042]) ?_)
      (show bp13042^8 ≤ scalar13042.upperTail by norm_num [bp13042, scalar13042])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13042, bp13042, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13042:ℝ)) (by norm_num [em13042]) ?_)
      (show bm13042^8 ≤ scalar13042.lowerTail by norm_num [bm13042, scalar13042])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13042, bm13042, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13042 :
    agent13042.root+dsL+scalar13042.worldRadius < √(1/100/aL) ∧
    2*(agent13042.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13042, agent13042, scalar13042, tp13042, tm13042, ep13042, em13042, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13042, agent13042, scalar13042, tp13042, tm13042, ep13042, em13042, dsL]

noncomputable def master13042 : MasterCertificate 13042 world13042 agent13042 :=
  master scalar13042 dsL tp13042 tm13042 ep13042 em13042
    (by norm_num [dsL]) (by norm_num [tp13042]) (by norm_num [tm13042])
    (by norm_num [ep13042]) (by norm_num [em13042])
    positive13042 negative13042 tails13042.1 tails13042.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13042.1 tailGuards13042.2

theorem preserves13042 : master13042.toScalarCertificate = scalar13042 := rfl

noncomputable def tp13043 : ℝ := (2346283431 / 10000000000)
noncomputable def tm13043 : ℝ := (-((3064349309 / 5000000000)))
noncomputable def ep13043 : ℝ := (1634466673056893 / 3125000000000000000)
noncomputable def em13043 : ℝ := (10174095294118453 / 20000000000000000000)
noncomputable def bp13043 : ℝ := (4262479956566554821 / 10000000000000000000)
noncomputable def bm13043 : ℝ := (43631992544489099787 / 100000000000000000000)

theorem positive13043 :
    Eplus aL (agent13043.root+dsL) scalar13043.worldRadius world13043.frame
      agent13043.frame tp13043 ≤ -ep13043 := by
  apply positive_check (eT := (115685540907750944559 / 100000000000000000000)) (y := (38087748551394082513 / 100000000000000000000)) (u := (14635682861089616739 / 10000000000000000000))
  · norm_num [world13043, agent13043, scalar13043, tp13043, tm13043, ep13043, em13043, dsL]
  · norm_num [world13043, agent13043, scalar13043, tp13043, tm13043, ep13043, em13043, dsL]
  · norm_num [world13043, agent13043, scalar13043, tp13043, tm13043, ep13043, em13043, dsL]
  · norm_num [world13043, agent13043, scalar13043, tp13043, tm13043, ep13043, em13043, dsL]
  · norm_num [world13043, agent13043, scalar13043, tp13043, tm13043, ep13043, em13043, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13043, agent13043, tp13043, tm13043, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13043, agent13043, scalar13043, tp13043, tm13043, ep13043, em13043, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13043, agent13043, tp13043, tm13043, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13043, agent13043, scalar13043, tp13043, tm13043, ep13043, em13043, dsL]

theorem negative13043 :
    Eminus aL (agent13043.root+dsL) scalar13043.worldRadius world13043.frame
      agent13043.frame tm13043 ≤ -em13043 := by
  apply negative_check (lo := (68345429208893489013 / 100000000000000000000)) (hi := (34172714604446744507 / 50000000000000000000))
    (y := (-((71624437662192910369 / 100000000000000000000)))) (u := (24429187558107899607 / 50000000000000000000))
  · norm_num [world13043, agent13043, scalar13043, tp13043, tm13043, ep13043, em13043, dsL]
  · norm_num [world13043, agent13043, scalar13043, tp13043, tm13043, ep13043, em13043, dsL]
  · norm_num [world13043, agent13043, scalar13043, tp13043, tm13043, ep13043, em13043, dsL]
  · norm_num [world13043, agent13043, scalar13043, tp13043, tm13043, ep13043, em13043, dsL]
  · norm_num [world13043, agent13043, scalar13043, tp13043, tm13043, ep13043, em13043, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13043, agent13043, tp13043, tm13043, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13043, agent13043, tp13043, tm13043, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13043, agent13043, scalar13043, tp13043, tm13043, ep13043, em13043, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13043, agent13043, tp13043, tm13043, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13043, agent13043, scalar13043, tp13043, tm13043, ep13043, em13043, dsL]

theorem tails13043 :
    exp (-((13043:ℝ)*ep13043)) ≤ scalar13043.upperTail ∧
    exp (-((13043:ℝ)*em13043)) ≤ scalar13043.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13043:ℝ)) (by norm_num [ep13043]) ?_)
      (show bp13043^8 ≤ scalar13043.upperTail by norm_num [bp13043, scalar13043])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13043, bp13043, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13043:ℝ)) (by norm_num [em13043]) ?_)
      (show bm13043^8 ≤ scalar13043.lowerTail by norm_num [bm13043, scalar13043])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13043, bm13043, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13043 :
    agent13043.root+dsL+scalar13043.worldRadius < √(1/100/aL) ∧
    2*(agent13043.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13043, agent13043, scalar13043, tp13043, tm13043, ep13043, em13043, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13043, agent13043, scalar13043, tp13043, tm13043, ep13043, em13043, dsL]

noncomputable def master13043 : MasterCertificate 13043 world13043 agent13043 :=
  master scalar13043 dsL tp13043 tm13043 ep13043 em13043
    (by norm_num [dsL]) (by norm_num [tp13043]) (by norm_num [tm13043])
    (by norm_num [ep13043]) (by norm_num [em13043])
    positive13043 negative13043 tails13043.1 tails13043.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13043.1 tailGuards13043.2

theorem preserves13043 : master13043.toScalarCertificate = scalar13043 := rfl

noncomputable def tp13044 : ℝ := (2346357763 / 10000000000)
noncomputable def tm13044 : ℝ := (-((612885643 / 1000000000)))
noncomputable def ep13044 : ℝ := (13076291989173693 / 25000000000000000000)
noncomputable def em13044 : ℝ := (10174474644763541 / 20000000000000000000)
noncomputable def bp13044 : ℝ := (10655115029696368427 / 25000000000000000000)
noncomputable def bm13044 : ℝ := (10906967219139806641 / 25000000000000000000)

theorem positive13044 :
    Eplus aL (agent13044.root+dsL) scalar13044.worldRadius world13044.frame
      agent13044.frame tp13044 ≤ -ep13044 := by
  apply positive_check (eT := (28921429747989269287 / 25000000000000000000)) (y := (19044209730506043347 / 50000000000000000000)) (u := (146357810536229835857 / 100000000000000000000))
  · norm_num [world13044, agent13044, scalar13044, tp13044, tm13044, ep13044, em13044, dsL]
  · norm_num [world13044, agent13044, scalar13044, tp13044, tm13044, ep13044, em13044, dsL]
  · norm_num [world13044, agent13044, scalar13044, tp13044, tm13044, ep13044, em13044, dsL]
  · norm_num [world13044, agent13044, scalar13044, tp13044, tm13044, ep13044, em13044, dsL]
  · norm_num [world13044, agent13044, scalar13044, tp13044, tm13044, ep13044, em13044, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13044, agent13044, tp13044, tm13044, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13044, agent13044, scalar13044, tp13044, tm13044, ep13044, em13044, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13044, agent13044, tp13044, tm13044, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13044, agent13044, scalar13044, tp13044, tm13044, ep13044, em13044, dsL]

theorem negative13044 :
    Eminus aL (agent13044.root+dsL) scalar13044.worldRadius world13044.frame
      agent13044.frame tm13044 ≤ -em13044 := by
  apply negative_check (lo := (2733812346705579571 / 4000000000000000000)) (hi := (17086327166909872319 / 25000000000000000000))
    (y := (-((71624371120928677373 / 100000000000000000000)))) (u := (24429203813603550927 / 50000000000000000000))
  · norm_num [world13044, agent13044, scalar13044, tp13044, tm13044, ep13044, em13044, dsL]
  · norm_num [world13044, agent13044, scalar13044, tp13044, tm13044, ep13044, em13044, dsL]
  · norm_num [world13044, agent13044, scalar13044, tp13044, tm13044, ep13044, em13044, dsL]
  · norm_num [world13044, agent13044, scalar13044, tp13044, tm13044, ep13044, em13044, dsL]
  · norm_num [world13044, agent13044, scalar13044, tp13044, tm13044, ep13044, em13044, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13044, agent13044, tp13044, tm13044, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13044, agent13044, tp13044, tm13044, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13044, agent13044, scalar13044, tp13044, tm13044, ep13044, em13044, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13044, agent13044, tp13044, tm13044, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13044, agent13044, scalar13044, tp13044, tm13044, ep13044, em13044, dsL]

theorem tails13044 :
    exp (-((13044:ℝ)*ep13044)) ≤ scalar13044.upperTail ∧
    exp (-((13044:ℝ)*em13044)) ≤ scalar13044.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13044:ℝ)) (by norm_num [ep13044]) ?_)
      (show bp13044^8 ≤ scalar13044.upperTail by norm_num [bp13044, scalar13044])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13044, bp13044, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13044:ℝ)) (by norm_num [em13044]) ?_)
      (show bm13044^8 ≤ scalar13044.lowerTail by norm_num [bm13044, scalar13044])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13044, bm13044, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13044 :
    agent13044.root+dsL+scalar13044.worldRadius < √(1/100/aL) ∧
    2*(agent13044.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13044, agent13044, scalar13044, tp13044, tm13044, ep13044, em13044, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13044, agent13044, scalar13044, tp13044, tm13044, ep13044, em13044, dsL]

noncomputable def master13044 : MasterCertificate 13044 world13044 agent13044 :=
  master scalar13044 dsL tp13044 tm13044 ep13044 em13044
    (by norm_num [dsL]) (by norm_num [tp13044]) (by norm_num [tm13044])
    (by norm_num [ep13044]) (by norm_num [em13044])
    positive13044 negative13044 tails13044.1 tails13044.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13044.1 tailGuards13044.2

theorem preserves13044 : master13044.toScalarCertificate = scalar13044 := rfl

noncomputable def tp13045 : ℝ := (2346432029 / 10000000000)
noncomputable def tm13045 : ℝ := (-((6129014149 / 10000000000)))
noncomputable def ep13045 : ℝ := (52307401181215153 / 100000000000000000000)
noncomputable def em13045 : ℝ := (12718567215176189 / 25000000000000000000)
noncomputable def bp13045 : ℝ := (42616121705597462637 / 100000000000000000000)
noncomputable def bm13045 : ℝ := (43623746185595115313 / 100000000000000000000)

theorem positive13045 :
    Eplus aL (agent13045.root+dsL) scalar13045.worldRadius world13045.frame
      agent13045.frame tp13045 ≤ -ep13045 := by
  apply positive_check (eT := (57842948317509321513 / 50000000000000000000)) (y := (1904454482000568111 / 5000000000000000000)) (u := (146358791398826613029 / 100000000000000000000))
  · norm_num [world13045, agent13045, scalar13045, tp13045, tm13045, ep13045, em13045, dsL]
  · norm_num [world13045, agent13045, scalar13045, tp13045, tm13045, ep13045, em13045, dsL]
  · norm_num [world13045, agent13045, scalar13045, tp13045, tm13045, ep13045, em13045, dsL]
  · norm_num [world13045, agent13045, scalar13045, tp13045, tm13045, ep13045, em13045, dsL]
  · norm_num [world13045, agent13045, scalar13045, tp13045, tm13045, ep13045, em13045, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13045, agent13045, tp13045, tm13045, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13045, agent13045, scalar13045, tp13045, tm13045, ep13045, em13045, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13045, agent13045, tp13045, tm13045, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13045, agent13045, scalar13045, tp13045, tm13045, ep13045, em13045, dsL]

theorem negative13045 :
    Eminus aL (agent13045.root+dsL) scalar13045.worldRadius world13045.frame
      agent13045.frame tm13045 ≤ -em13045 := by
  apply negative_check (lo := (13669037692859742653 / 20000000000000000000)) (hi := (34172594232149356633 / 50000000000000000000))
    (y := (-((35812152220121502219 / 50000000000000000000)))) (u := (48858440206339178547 / 100000000000000000000))
  · norm_num [world13045, agent13045, scalar13045, tp13045, tm13045, ep13045, em13045, dsL]
  · norm_num [world13045, agent13045, scalar13045, tp13045, tm13045, ep13045, em13045, dsL]
  · norm_num [world13045, agent13045, scalar13045, tp13045, tm13045, ep13045, em13045, dsL]
  · norm_num [world13045, agent13045, scalar13045, tp13045, tm13045, ep13045, em13045, dsL]
  · norm_num [world13045, agent13045, scalar13045, tp13045, tm13045, ep13045, em13045, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13045, agent13045, tp13045, tm13045, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13045, agent13045, tp13045, tm13045, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13045, agent13045, scalar13045, tp13045, tm13045, ep13045, em13045, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13045, agent13045, tp13045, tm13045, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13045, agent13045, scalar13045, tp13045, tm13045, ep13045, em13045, dsL]

theorem tails13045 :
    exp (-((13045:ℝ)*ep13045)) ≤ scalar13045.upperTail ∧
    exp (-((13045:ℝ)*em13045)) ≤ scalar13045.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13045:ℝ)) (by norm_num [ep13045]) ?_)
      (show bp13045^8 ≤ scalar13045.upperTail by norm_num [bp13045, scalar13045])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13045, bp13045, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13045:ℝ)) (by norm_num [em13045]) ?_)
      (show bm13045^8 ≤ scalar13045.lowerTail by norm_num [bm13045, scalar13045])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13045, bm13045, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13045 :
    agent13045.root+dsL+scalar13045.worldRadius < √(1/100/aL) ∧
    2*(agent13045.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13045, agent13045, scalar13045, tp13045, tm13045, ep13045, em13045, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13045, agent13045, scalar13045, tp13045, tm13045, ep13045, em13045, dsL]

noncomputable def master13045 : MasterCertificate 13045 world13045 agent13045 :=
  master scalar13045 dsL tp13045 tm13045 ep13045 em13045
    (by norm_num [dsL]) (by norm_num [tp13045]) (by norm_num [tm13045])
    (by norm_num [ep13045]) (by norm_num [em13045])
    positive13045 negative13045 tails13045.1 tails13045.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13045.1 tailGuards13045.2

theorem preserves13045 : master13045.toScalarCertificate = scalar13045 := rfl

noncomputable def tp13046 : ℝ := (586626577 / 2500000000)
noncomputable def tm13046 : ℝ := (-((6129171651 / 10000000000)))
noncomputable def ep13046 : ℝ := (26154816826374403 / 50000000000000000000)
noncomputable def em13046 : ℝ := (50876163784722359 / 100000000000000000000)
noncomputable def bp13046 : ℝ := (42611784019364322437 / 100000000000000000000)
noncomputable def bm13046 : ℝ := (43619624184577699253 / 100000000000000000000)

theorem positive13046 :
    Eplus aL (agent13046.root+dsL) scalar13046.worldRadius world13046.frame
      agent13046.frame tp13046 ≤ -ep13046 := by
  apply positive_check (eT := (115686074404509340701 / 100000000000000000000)) (y := (1190305009846479461 / 3125000000000000000)) (u := (29271954598810736977 / 20000000000000000000))
  · norm_num [world13046, agent13046, scalar13046, tp13046, tm13046, ep13046, em13046, dsL]
  · norm_num [world13046, agent13046, scalar13046, tp13046, tm13046, ep13046, em13046, dsL]
  · norm_num [world13046, agent13046, scalar13046, tp13046, tm13046, ep13046, em13046, dsL]
  · norm_num [world13046, agent13046, scalar13046, tp13046, tm13046, ep13046, em13046, dsL]
  · norm_num [world13046, agent13046, scalar13046, tp13046, tm13046, ep13046, em13046, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13046, agent13046, tp13046, tm13046, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13046, agent13046, scalar13046, tp13046, tm13046, ep13046, em13046, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13046, agent13046, tp13046, tm13046, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13046, agent13046, scalar13046, tp13046, tm13046, ep13046, em13046, dsL]

theorem negative13046 :
    Eminus aL (agent13046.root+dsL) scalar13046.worldRadius world13046.frame
      agent13046.frame tm13046 ≤ -em13046 := by
  apply negative_check (lo := (68345069125051523867 / 100000000000000000000)) (hi := (17086267281262880967 / 25000000000000000000))
    (y := (-((71624236146051763093 / 100000000000000000000)))) (u := (48858473573827164629 / 100000000000000000000))
  · norm_num [world13046, agent13046, scalar13046, tp13046, tm13046, ep13046, em13046, dsL]
  · norm_num [world13046, agent13046, scalar13046, tp13046, tm13046, ep13046, em13046, dsL]
  · norm_num [world13046, agent13046, scalar13046, tp13046, tm13046, ep13046, em13046, dsL]
  · norm_num [world13046, agent13046, scalar13046, tp13046, tm13046, ep13046, em13046, dsL]
  · norm_num [world13046, agent13046, scalar13046, tp13046, tm13046, ep13046, em13046, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13046, agent13046, tp13046, tm13046, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13046, agent13046, tp13046, tm13046, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13046, agent13046, scalar13046, tp13046, tm13046, ep13046, em13046, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13046, agent13046, tp13046, tm13046, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13046, agent13046, scalar13046, tp13046, tm13046, ep13046, em13046, dsL]

theorem tails13046 :
    exp (-((13046:ℝ)*ep13046)) ≤ scalar13046.upperTail ∧
    exp (-((13046:ℝ)*em13046)) ≤ scalar13046.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13046:ℝ)) (by norm_num [ep13046]) ?_)
      (show bp13046^8 ≤ scalar13046.upperTail by norm_num [bp13046, scalar13046])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13046, bp13046, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13046:ℝ)) (by norm_num [em13046]) ?_)
      (show bm13046^8 ≤ scalar13046.lowerTail by norm_num [bm13046, scalar13046])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13046, bm13046, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13046 :
    agent13046.root+dsL+scalar13046.worldRadius < √(1/100/aL) ∧
    2*(agent13046.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13046, agent13046, scalar13046, tp13046, tm13046, ep13046, em13046, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13046, agent13046, scalar13046, tp13046, tm13046, ep13046, em13046, dsL]

noncomputable def master13046 : MasterCertificate 13046 world13046 agent13046 :=
  master scalar13046 dsL tp13046 tm13046 ep13046 em13046
    (by norm_num [dsL]) (by norm_num [tp13046]) (by norm_num [tm13046])
    (by norm_num [ep13046]) (by norm_num [em13046])
    positive13046 negative13046 tails13046.1 tails13046.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13046.1 tailGuards13046.2

theorem preserves13046 : master13046.toScalarCertificate = scalar13046 := rfl

noncomputable def tp13047 : ℝ := (2346580569 / 10000000000)
noncomputable def tm13047 : ℝ := (-((6129329313 / 10000000000)))
noncomputable def ep13047 : ℝ := (2092474591437013 / 4000000000000000000)
noncomputable def em13047 : ℝ := (6359757187187197 / 12500000000000000000)
noncomputable def bp13047 : ℝ := (2130372373341653837 / 5000000000000000000)
noncomputable def bm13047 : ℝ := (43615503228001430457 / 100000000000000000000)

theorem positive13047 :
    Eplus aL (agent13047.root+dsL) scalar13047.worldRadius world13047.frame
      agent13047.frame tp13047 ≤ -ep13047 := by
  apply positive_check (eT := (14460781509713900591 / 12500000000000000000)) (y := (4761303867933507801 / 12500000000000000000)) (u := (146360754527520557191 / 100000000000000000000))
  · norm_num [world13047, agent13047, scalar13047, tp13047, tm13047, ep13047, em13047, dsL]
  · norm_num [world13047, agent13047, scalar13047, tp13047, tm13047, ep13047, em13047, dsL]
  · norm_num [world13047, agent13047, scalar13047, tp13047, tm13047, ep13047, em13047, dsL]
  · norm_num [world13047, agent13047, scalar13047, tp13047, tm13047, ep13047, em13047, dsL]
  · norm_num [world13047, agent13047, scalar13047, tp13047, tm13047, ep13047, em13047, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13047, agent13047, tp13047, tm13047, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13047, agent13047, scalar13047, tp13047, tm13047, ep13047, em13047, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13047, agent13047, tp13047, tm13047, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13047, agent13047, scalar13047, tp13047, tm13047, ep13047, em13047, dsL]

theorem negative13047 :
    Eminus aL (agent13047.root+dsL) scalar13047.worldRadius world13047.frame
      agent13047.frame tm13047 ≤ -em13047 := by
  apply negative_check (lo := (6834494904992010133 / 10000000000000000000)) (hi := (68344949049920101331 / 100000000000000000000))
    (y := (-((71624169852140161863 / 100000000000000000000)))) (u := (24429252982015590869 / 50000000000000000000))
  · norm_num [world13047, agent13047, scalar13047, tp13047, tm13047, ep13047, em13047, dsL]
  · norm_num [world13047, agent13047, scalar13047, tp13047, tm13047, ep13047, em13047, dsL]
  · norm_num [world13047, agent13047, scalar13047, tp13047, tm13047, ep13047, em13047, dsL]
  · norm_num [world13047, agent13047, scalar13047, tp13047, tm13047, ep13047, em13047, dsL]
  · norm_num [world13047, agent13047, scalar13047, tp13047, tm13047, ep13047, em13047, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13047, agent13047, tp13047, tm13047, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13047, agent13047, tp13047, tm13047, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13047, agent13047, scalar13047, tp13047, tm13047, ep13047, em13047, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13047, agent13047, tp13047, tm13047, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13047, agent13047, scalar13047, tp13047, tm13047, ep13047, em13047, dsL]

theorem tails13047 :
    exp (-((13047:ℝ)*ep13047)) ≤ scalar13047.upperTail ∧
    exp (-((13047:ℝ)*em13047)) ≤ scalar13047.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13047:ℝ)) (by norm_num [ep13047]) ?_)
      (show bp13047^8 ≤ scalar13047.upperTail by norm_num [bp13047, scalar13047])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13047, bp13047, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13047:ℝ)) (by norm_num [em13047]) ?_)
      (show bm13047^8 ≤ scalar13047.lowerTail by norm_num [bm13047, scalar13047])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13047, bm13047, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13047 :
    agent13047.root+dsL+scalar13047.worldRadius < √(1/100/aL) ∧
    2*(agent13047.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13047, agent13047, scalar13047, tp13047, tm13047, ep13047, em13047, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13047, agent13047, scalar13047, tp13047, tm13047, ep13047, em13047, dsL]

noncomputable def master13047 : MasterCertificate 13047 world13047 agent13047 :=
  master scalar13047 dsL tp13047 tm13047 ep13047 em13047
    (by norm_num [dsL]) (by norm_num [tp13047]) (by norm_num [tm13047])
    (by norm_num [ep13047]) (by norm_num [em13047])
    positive13047 negative13047 tails13047.1 tails13047.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13047.1 tailGuards13047.2

theorem preserves13047 : master13047.toScalarCertificate = scalar13047 := rfl

noncomputable def tp13048 : ℝ := (1173327379 / 5000000000)
noncomputable def tm13048 : ℝ := (-((6129486743 / 10000000000)))
noncomputable def ep13048 : ℝ := (40870386880767 / 78125000000000000)
noncomputable def em13048 : ℝ := (6359993817610381 / 12500000000000000000)
noncomputable def bp13048 : ℝ := (10650777903134571937 / 25000000000000000000)
noncomputable def bm13048 : ℝ := (43611382930421283859 / 100000000000000000000)

theorem positive13048 :
    Eplus aL (agent13048.root+dsL) scalar13048.worldRadius world13048.frame
      agent13048.frame tp13048 ≤ -ep13048 := by
  apply positive_check (eT := (57843214633352386069 / 50000000000000000000)) (y := (38091100686962245111 / 100000000000000000000)) (u := (146361734772434601581 / 100000000000000000000))
  · norm_num [world13048, agent13048, scalar13048, tp13048, tm13048, ep13048, em13048, dsL]
  · norm_num [world13048, agent13048, scalar13048, tp13048, tm13048, ep13048, em13048, dsL]
  · norm_num [world13048, agent13048, scalar13048, tp13048, tm13048, ep13048, em13048, dsL]
  · norm_num [world13048, agent13048, scalar13048, tp13048, tm13048, ep13048, em13048, dsL]
  · norm_num [world13048, agent13048, scalar13048, tp13048, tm13048, ep13048, em13048, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13048, agent13048, tp13048, tm13048, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13048, agent13048, scalar13048, tp13048, tm13048, ep13048, em13048, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13048, agent13048, tp13048, tm13048, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13048, agent13048, scalar13048, tp13048, tm13048, ep13048, em13048, dsL]

theorem negative13048 :
    Eminus aL (agent13048.root+dsL) scalar13048.worldRadius world13048.frame
      agent13048.frame tm13048 ≤ -em13048 := by
  apply negative_check (lo := (68344829902557366527 / 100000000000000000000)) (hi := (266971991806864713 / 390625000000000000))
    (y := (-((35812051105653478411 / 50000000000000000000)))) (u := (24429269506171442209 / 50000000000000000000))
  · norm_num [world13048, agent13048, scalar13048, tp13048, tm13048, ep13048, em13048, dsL]
  · norm_num [world13048, agent13048, scalar13048, tp13048, tm13048, ep13048, em13048, dsL]
  · norm_num [world13048, agent13048, scalar13048, tp13048, tm13048, ep13048, em13048, dsL]
  · norm_num [world13048, agent13048, scalar13048, tp13048, tm13048, ep13048, em13048, dsL]
  · norm_num [world13048, agent13048, scalar13048, tp13048, tm13048, ep13048, em13048, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13048, agent13048, tp13048, tm13048, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13048, agent13048, tp13048, tm13048, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13048, agent13048, scalar13048, tp13048, tm13048, ep13048, em13048, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13048, agent13048, tp13048, tm13048, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13048, agent13048, scalar13048, tp13048, tm13048, ep13048, em13048, dsL]

theorem tails13048 :
    exp (-((13048:ℝ)*ep13048)) ≤ scalar13048.upperTail ∧
    exp (-((13048:ℝ)*em13048)) ≤ scalar13048.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13048:ℝ)) (by norm_num [ep13048]) ?_)
      (show bp13048^8 ≤ scalar13048.upperTail by norm_num [bp13048, scalar13048])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13048, bp13048, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13048:ℝ)) (by norm_num [em13048]) ?_)
      (show bm13048^8 ≤ scalar13048.lowerTail by norm_num [bm13048, scalar13048])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13048, bm13048, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13048 :
    agent13048.root+dsL+scalar13048.worldRadius < √(1/100/aL) ∧
    2*(agent13048.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13048, agent13048, scalar13048, tp13048, tm13048, ep13048, em13048, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13048, agent13048, scalar13048, tp13048, tm13048, ep13048, em13048, dsL]

noncomputable def master13048 : MasterCertificate 13048 world13048 agent13048 :=
  master scalar13048 dsL tp13048 tm13048 ep13048 em13048
    (by norm_num [dsL]) (by norm_num [tp13048]) (by norm_num [tm13048])
    (by norm_num [ep13048]) (by norm_num [em13048])
    positive13048 negative13048 tails13048.1 tails13048.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13048.1 tailGuards13048.2

theorem preserves13048 : master13048.toScalarCertificate = scalar13048 := rfl

noncomputable def tp13049 : ℝ := (2346728891 / 10000000000)
noncomputable def tm13049 : ℝ := (-((3064822071 / 5000000000)))
noncomputable def ep13049 : ℝ := (26158162127071239 / 50000000000000000000)
noncomputable def em13049 : ℝ := (50881842278571277 / 100000000000000000000)
noncomputable def bp13049 : ℝ := (8519755383426365337 / 20000000000000000000)
noncomputable def bm13049 : ℝ := (43607263744432024767 / 100000000000000000000)

theorem positive13049 :
    Eplus aL (agent13049.root+dsL) scalar13049.worldRadius world13049.frame
      agent13049.frame tp13049 ≤ -ep13049 := by
  apply positive_check (eT := (11568660608645845831 / 10000000000000000000)) (y := (19045884962090149229 / 50000000000000000000)) (u := (146362714282914307927 / 100000000000000000000))
  · norm_num [world13049, agent13049, scalar13049, tp13049, tm13049, ep13049, em13049, dsL]
  · norm_num [world13049, agent13049, scalar13049, tp13049, tm13049, ep13049, em13049, dsL]
  · norm_num [world13049, agent13049, scalar13049, tp13049, tm13049, ep13049, em13049, dsL]
  · norm_num [world13049, agent13049, scalar13049, tp13049, tm13049, ep13049, em13049, dsL]
  · norm_num [world13049, agent13049, scalar13049, tp13049, tm13049, ep13049, em13049, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13049, agent13049, tp13049, tm13049, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13049, agent13049, scalar13049, tp13049, tm13049, ep13049, em13049, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13049, agent13049, tp13049, tm13049, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world13049, agent13049, scalar13049, tp13049, tm13049, ep13049, em13049, dsL]

theorem negative13049 :
    Eminus aL (agent13049.root+dsL) scalar13049.worldRadius world13049.frame
      agent13049.frame tm13049 ≤ -em13049 := by
  apply negative_check (lo := (68344710829904651957 / 100000000000000000000)) (hi := (34172355414952325979 / 50000000000000000000))
    (y := (-((71624034900951863813 / 100000000000000000000)))) (u := (9771714379842011003 / 20000000000000000000))
  · norm_num [world13049, agent13049, scalar13049, tp13049, tm13049, ep13049, em13049, dsL]
  · norm_num [world13049, agent13049, scalar13049, tp13049, tm13049, ep13049, em13049, dsL]
  · norm_num [world13049, agent13049, scalar13049, tp13049, tm13049, ep13049, em13049, dsL]
  · norm_num [world13049, agent13049, scalar13049, tp13049, tm13049, ep13049, em13049, dsL]
  · norm_num [world13049, agent13049, scalar13049, tp13049, tm13049, ep13049, em13049, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world13049, agent13049, tp13049, tm13049, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13049, agent13049, tp13049, tm13049, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13049, agent13049, scalar13049, tp13049, tm13049, ep13049, em13049, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world13049, agent13049, tp13049, tm13049, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world13049, agent13049, scalar13049, tp13049, tm13049, ep13049, em13049, dsL]

theorem tails13049 :
    exp (-((13049:ℝ)*ep13049)) ≤ scalar13049.upperTail ∧
    exp (-((13049:ℝ)*em13049)) ≤ scalar13049.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (13049:ℝ)) (by norm_num [ep13049]) ?_)
      (show bp13049^8 ≤ scalar13049.upperTail by norm_num [bp13049, scalar13049])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep13049, bp13049, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (13049:ℝ)) (by norm_num [em13049]) ?_)
      (show bm13049^8 ≤ scalar13049.lowerTail by norm_num [bm13049, scalar13049])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em13049, bm13049, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards13049 :
    agent13049.root+dsL+scalar13049.worldRadius < √(1/100/aL) ∧
    2*(agent13049.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world13049, agent13049, scalar13049, tp13049, tm13049, ep13049, em13049, dsL]
  · apply le_trans _ x0_lo
    norm_num [world13049, agent13049, scalar13049, tp13049, tm13049, ep13049, em13049, dsL]

noncomputable def master13049 : MasterCertificate 13049 world13049 agent13049 :=
  master scalar13049 dsL tp13049 tm13049 ep13049 em13049
    (by norm_num [dsL]) (by norm_num [tp13049]) (by norm_num [tm13049])
    (by norm_num [ep13049]) (by norm_num [em13049])
    positive13049 negative13049 tails13049.1 tails13049.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards13049.1 tailGuards13049.2

theorem preserves13049 : master13049.toScalarCertificate = scalar13049 := rfl

end BstLean.Part268
