import BstLean.Part261Checker
import BstLean.Part259Data0

namespace BstLean.Part261
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part259

noncomputable def tp12226 : ℝ := (2301326739 / 10000000000)
noncomputable def tm12226 : ℝ := (-((6055932101 / 10000000000)))
noncomputable def ep12226 : ℝ := (6324489954853679 / 12500000000000000000)
noncomputable def em12226 : ℝ := (9904680850898537 / 20000000000000000000)
noncomputable def bp12226 : ℝ := (46151896026726632639 / 100000000000000000000)
noncomputable def bm12226 : ℝ := (23457296078430142739 / 50000000000000000000)

theorem positive12226 :
    Eplus aL (agent12226.root+dsL) scalar12226.worldRadius world12226.frame
      agent12226.frame tp12226 ≤ -ep12226 := by
  apply positive_check (eT := (28916804150335961127 / 25000000000000000000)) (y := (37149208150503481987 / 100000000000000000000)) (u := (144989636505889415789 / 100000000000000000000))
  · norm_num [world12226, agent12226, scalar12226, tp12226, tm12226, ep12226, em12226, dsL]
  · norm_num [world12226, agent12226, scalar12226, tp12226, tm12226, ep12226, em12226, dsL]
  · norm_num [world12226, agent12226, scalar12226, tp12226, tm12226, ep12226, em12226, dsL]
  · norm_num [world12226, agent12226, scalar12226, tp12226, tm12226, ep12226, em12226, dsL]
  · norm_num [world12226, agent12226, scalar12226, tp12226, tm12226, ep12226, em12226, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12226, agent12226, tp12226, tm12226, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12226, agent12226, scalar12226, tp12226, tm12226, ep12226, em12226, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12226, agent12226, tp12226, tm12226, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12226, agent12226, scalar12226, tp12226, tm12226, ep12226, em12226, dsL]

theorem negative12226 :
    Eminus aL (agent12226.root+dsL) scalar12226.worldRadius world12226.frame
      agent12226.frame tm12226 ≤ -em12226 := by
  apply negative_check (lo := (13636169280809885173 / 20000000000000000000)) (hi := (34090423202024712933 / 50000000000000000000))
    (y := (-((70849171948164973489 / 100000000000000000000)))) (u := (12309657358259930971 / 25000000000000000000))
  · norm_num [world12226, agent12226, scalar12226, tp12226, tm12226, ep12226, em12226, dsL]
  · norm_num [world12226, agent12226, scalar12226, tp12226, tm12226, ep12226, em12226, dsL]
  · norm_num [world12226, agent12226, scalar12226, tp12226, tm12226, ep12226, em12226, dsL]
  · norm_num [world12226, agent12226, scalar12226, tp12226, tm12226, ep12226, em12226, dsL]
  · norm_num [world12226, agent12226, scalar12226, tp12226, tm12226, ep12226, em12226, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12226, agent12226, tp12226, tm12226, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12226, agent12226, tp12226, tm12226, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12226, agent12226, scalar12226, tp12226, tm12226, ep12226, em12226, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12226, agent12226, tp12226, tm12226, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12226, agent12226, scalar12226, tp12226, tm12226, ep12226, em12226, dsL]

theorem tails12226 :
    exp (-((12226:ℝ)*ep12226)) ≤ scalar12226.upperTail ∧
    exp (-((12226:ℝ)*em12226)) ≤ scalar12226.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12226:ℝ)) (by norm_num [ep12226]) ?_)
      (show bp12226^8 ≤ scalar12226.upperTail by norm_num [bp12226, scalar12226])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12226, bp12226, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12226:ℝ)) (by norm_num [em12226]) ?_)
      (show bm12226^8 ≤ scalar12226.lowerTail by norm_num [bm12226, scalar12226])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12226, bm12226, Finset.sum_range_succ, Nat.factorial]

theorem guards12226 :
    agent12226.root+dsL+scalar12226.worldRadius < √(1/100/aL) ∧
    2*(agent12226.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12226, agent12226, scalar12226, tp12226, tm12226, ep12226, em12226, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12226, agent12226, scalar12226, tp12226, tm12226, ep12226, em12226, dsL]

noncomputable def master12226 : MasterCertificate 12226 world12226 agent12226 :=
  master scalar12226 dsL tp12226 tm12226 ep12226 em12226
    (by norm_num [dsL]) (by norm_num [tp12226]) (by norm_num [tm12226])
    (by norm_num [ep12226]) (by norm_num [em12226])
    positive12226 negative12226 tails12226.1 tails12226.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12226.1 guards12226.2

theorem preserves12226 : master12226.toScalarCertificate = scalar12226 := rfl

end BstLean.Part261
