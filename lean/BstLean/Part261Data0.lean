import BstLean.Part261Checker
import BstLean.Part259Data0
import BstLean.Part259Data1
import BstLean.Part259Data2
import BstLean.Part259Data3
import BstLean.Part259Data4
import BstLean.Part261Pilot

namespace BstLean.Part261
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part259

noncomputable def tp12225 : ℝ := (2301223133 / 10000000000)
noncomputable def tm12225 : ℝ := (-((3027850811 / 5000000000)))
noncomputable def ep12225 : ℝ := (6324096239586171 / 12500000000000000000)
noncomputable def em12225 : ℝ := (12380161364593073 / 25000000000000000000)
noncomputable def bp12225 : ℝ := (9231407310767243767 / 20000000000000000000)
noncomputable def bm12225 : ℝ := (23459737221133569597 / 50000000000000000000)

theorem positive12225 :
    Eplus aL (agent12225.root+dsL) scalar12225.worldRadius world12225.frame
      agent12225.frame tp12225 ≤ -ep12225 := by
  apply positive_check (eT := (14458357127445856167 / 12500000000000000000)) (y := (37148347178102526923 / 100000000000000000000)) (u := (9061774261906793011 / 6250000000000000000))
  · norm_num [world12225, agent12225, scalar12225, tp12225, tm12225, ep12225, em12225, dsL]
  · norm_num [world12225, agent12225, scalar12225, tp12225, tm12225, ep12225, em12225, dsL]
  · norm_num [world12225, agent12225, scalar12225, tp12225, tm12225, ep12225, em12225, dsL]
  · norm_num [world12225, agent12225, scalar12225, tp12225, tm12225, ep12225, em12225, dsL]
  · norm_num [world12225, agent12225, scalar12225, tp12225, tm12225, ep12225, em12225, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12225, agent12225, tp12225, tm12225, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12225, agent12225, scalar12225, tp12225, tm12225, ep12225, em12225, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12225, agent12225, tp12225, tm12225, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12225, agent12225, scalar12225, tp12225, tm12225, ep12225, em12225, dsL]

theorem negative12225 :
    Eminus aL (agent12225.root+dsL) scalar12225.worldRadius world12225.frame
      agent12225.frame tm12225 ≤ -em12225 := by
  apply negative_check (lo := (4261326398225556569 / 6250000000000000000)) (hi := (13636244474321781021 / 20000000000000000000))
    (y := (-((14169815376307522121 / 20000000000000000000)))) (u := (49238676242566335699 / 100000000000000000000))
  · norm_num [world12225, agent12225, scalar12225, tp12225, tm12225, ep12225, em12225, dsL]
  · norm_num [world12225, agent12225, scalar12225, tp12225, tm12225, ep12225, em12225, dsL]
  · norm_num [world12225, agent12225, scalar12225, tp12225, tm12225, ep12225, em12225, dsL]
  · norm_num [world12225, agent12225, scalar12225, tp12225, tm12225, ep12225, em12225, dsL]
  · norm_num [world12225, agent12225, scalar12225, tp12225, tm12225, ep12225, em12225, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12225, agent12225, tp12225, tm12225, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12225, agent12225, tp12225, tm12225, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12225, agent12225, scalar12225, tp12225, tm12225, ep12225, em12225, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12225, agent12225, tp12225, tm12225, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12225, agent12225, scalar12225, tp12225, tm12225, ep12225, em12225, dsL]

theorem tails12225 :
    exp (-((12225:ℝ)*ep12225)) ≤ scalar12225.upperTail ∧
    exp (-((12225:ℝ)*em12225)) ≤ scalar12225.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12225:ℝ)) (by norm_num [ep12225]) ?_)
      (show bp12225^8 ≤ scalar12225.upperTail by norm_num [bp12225, scalar12225])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12225, bp12225, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12225:ℝ)) (by norm_num [em12225]) ?_)
      (show bm12225^8 ≤ scalar12225.lowerTail by norm_num [bm12225, scalar12225])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12225, bm12225, Finset.sum_range_succ, Nat.factorial]

theorem guards12225 :
    agent12225.root+dsL+scalar12225.worldRadius < √(1/100/aL) ∧
    2*(agent12225.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12225, agent12225, scalar12225, tp12225, tm12225, ep12225, em12225, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12225, agent12225, scalar12225, tp12225, tm12225, ep12225, em12225, dsL]

noncomputable def master12225 : MasterCertificate 12225 world12225 agent12225 :=
  master scalar12225 dsL tp12225 tm12225 ep12225 em12225
    (by norm_num [dsL]) (by norm_num [tp12225]) (by norm_num [tm12225])
    (by norm_num [ep12225]) (by norm_num [em12225])
    positive12225 negative12225 tails12225.1 tails12225.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12225.1 guards12225.2

theorem preserves12225 : master12225.toScalarCertificate = scalar12225 := rfl

noncomputable def tp12227 : ℝ := (287678791 / 1250000000)
noncomputable def tm12227 : ℝ := (-((378510169 / 625000000)))
noncomputable def ep12227 : ℝ := (25299533779374219 / 50000000000000000000)
noncomputable def em12227 : ℝ := (12381540349067759 / 25000000000000000000)
noncomputable def bp12227 : ℝ := (46146756979844282061 / 100000000000000000000)
noncomputable def bm12227 : ℝ := (23454855621021514139 / 50000000000000000000)

theorem positive12227 :
    Eplus aL (agent12227.root+dsL) scalar12227.worldRadius world12227.frame
      agent12227.frame tp12227 ≤ -ep12227 := by
  apply positive_check (eT := (115667576090988679371 / 100000000000000000000)) (y := (7430013856573092469 / 20000000000000000000)) (u := (144990885063946746719 / 100000000000000000000))
  · norm_num [world12227, agent12227, scalar12227, tp12227, tm12227, ep12227, em12227, dsL]
  · norm_num [world12227, agent12227, scalar12227, tp12227, tm12227, ep12227, em12227, dsL]
  · norm_num [world12227, agent12227, scalar12227, tp12227, tm12227, ep12227, em12227, dsL]
  · norm_num [world12227, agent12227, scalar12227, tp12227, tm12227, ep12227, em12227, dsL]
  · norm_num [world12227, agent12227, scalar12227, tp12227, tm12227, ep12227, em12227, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12227, agent12227, tp12227, tm12227, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12227, agent12227, scalar12227, tp12227, tm12227, ep12227, em12227, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12227, agent12227, tp12227, tm12227, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12227, agent12227, scalar12227, tp12227, tm12227, ep12227, em12227, dsL]

theorem negative12227 :
    Eminus aL (agent12227.root+dsL) scalar12227.worldRadius world12227.frame
      agent12227.frame tm12227 ≤ -em12227 := by
  apply negative_check (lo := (13636093969404745413 / 20000000000000000000)) (hi := (34090234923511863533 / 50000000000000000000))
    (y := (-((35424634517683859069 / 50000000000000000000)))) (u := (12309645407163735879 / 25000000000000000000))
  · norm_num [world12227, agent12227, scalar12227, tp12227, tm12227, ep12227, em12227, dsL]
  · norm_num [world12227, agent12227, scalar12227, tp12227, tm12227, ep12227, em12227, dsL]
  · norm_num [world12227, agent12227, scalar12227, tp12227, tm12227, ep12227, em12227, dsL]
  · norm_num [world12227, agent12227, scalar12227, tp12227, tm12227, ep12227, em12227, dsL]
  · norm_num [world12227, agent12227, scalar12227, tp12227, tm12227, ep12227, em12227, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12227, agent12227, tp12227, tm12227, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12227, agent12227, tp12227, tm12227, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12227, agent12227, scalar12227, tp12227, tm12227, ep12227, em12227, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12227, agent12227, tp12227, tm12227, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12227, agent12227, scalar12227, tp12227, tm12227, ep12227, em12227, dsL]

theorem tails12227 :
    exp (-((12227:ℝ)*ep12227)) ≤ scalar12227.upperTail ∧
    exp (-((12227:ℝ)*em12227)) ≤ scalar12227.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12227:ℝ)) (by norm_num [ep12227]) ?_)
      (show bp12227^8 ≤ scalar12227.upperTail by norm_num [bp12227, scalar12227])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12227, bp12227, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12227:ℝ)) (by norm_num [em12227]) ?_)
      (show bm12227^8 ≤ scalar12227.lowerTail by norm_num [bm12227, scalar12227])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12227, bm12227, Finset.sum_range_succ, Nat.factorial]

theorem guards12227 :
    agent12227.root+dsL+scalar12227.worldRadius < √(1/100/aL) ∧
    2*(agent12227.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12227, agent12227, scalar12227, tp12227, tm12227, ep12227, em12227, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12227, agent12227, scalar12227, tp12227, tm12227, ep12227, em12227, dsL]

noncomputable def master12227 : MasterCertificate 12227 world12227 agent12227 :=
  master scalar12227 dsL tp12227 tm12227 ep12227 em12227
    (by norm_num [dsL]) (by norm_num [tp12227]) (by norm_num [tm12227])
    (by norm_num [ep12227]) (by norm_num [em12227])
    positive12227 negative12227 tails12227.1 tails12227.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12227.1 guards12227.2

theorem preserves12227 : master12227.toScalarCertificate = scalar12227 := rfl

noncomputable def tp12228 : ℝ := (575383473 / 2500000000)
noncomputable def tm12228 : ℝ := (-((3028196517 / 5000000000)))
noncomputable def ep12228 : ℝ := (12650553610614219 / 25000000000000000000)
noncomputable def em12228 : ℝ := (49528917613992533 / 100000000000000000000)
noncomputable def bp12228 : ℝ := (922832377457724819 / 2000000000000000000)
noncomputable def bm12228 : ℝ := (2931551948388334817 / 6250000000000000000)

theorem positive12228 :
    Eplus aL (agent12228.root+dsL) scalar12228.worldRadius world12228.frame
      agent12228.frame tp12228 ≤ -ep12228 := by
  apply positive_check (eT := (57833967714959027583 / 50000000000000000000)) (y := (7430185977429004963 / 20000000000000000000)) (u := (144992132867077898419 / 100000000000000000000))
  · norm_num [world12228, agent12228, scalar12228, tp12228, tm12228, ep12228, em12228, dsL]
  · norm_num [world12228, agent12228, scalar12228, tp12228, tm12228, ep12228, em12228, dsL]
  · norm_num [world12228, agent12228, scalar12228, tp12228, tm12228, ep12228, em12228, dsL]
  · norm_num [world12228, agent12228, scalar12228, tp12228, tm12228, ep12228, em12228, dsL]
  · norm_num [world12228, agent12228, scalar12228, tp12228, tm12228, ep12228, em12228, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12228, agent12228, tp12228, tm12228, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12228, agent12228, scalar12228, tp12228, tm12228, ep12228, em12228, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12228, agent12228, tp12228, tm12228, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12228, agent12228, scalar12228, tp12228, tm12228, ep12228, em12228, dsL]

theorem negative12228 :
    Eminus aL (agent12228.root+dsL) scalar12228.worldRadius world12228.frame
      agent12228.frame tm12228 ≤ -em12228 := by
  apply negative_check (lo := (68180094412490307277 / 100000000000000000000)) (hi := (34090047206245153639 / 50000000000000000000))
    (y := (-((70849363068460418617 / 100000000000000000000)))) (u := (1230963383202890129 / 2500000000000000000))
  · norm_num [world12228, agent12228, scalar12228, tp12228, tm12228, ep12228, em12228, dsL]
  · norm_num [world12228, agent12228, scalar12228, tp12228, tm12228, ep12228, em12228, dsL]
  · norm_num [world12228, agent12228, scalar12228, tp12228, tm12228, ep12228, em12228, dsL]
  · norm_num [world12228, agent12228, scalar12228, tp12228, tm12228, ep12228, em12228, dsL]
  · norm_num [world12228, agent12228, scalar12228, tp12228, tm12228, ep12228, em12228, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12228, agent12228, tp12228, tm12228, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12228, agent12228, tp12228, tm12228, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12228, agent12228, scalar12228, tp12228, tm12228, ep12228, em12228, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12228, agent12228, tp12228, tm12228, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12228, agent12228, scalar12228, tp12228, tm12228, ep12228, em12228, dsL]

theorem tails12228 :
    exp (-((12228:ℝ)*ep12228)) ≤ scalar12228.upperTail ∧
    exp (-((12228:ℝ)*em12228)) ≤ scalar12228.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12228:ℝ)) (by norm_num [ep12228]) ?_)
      (show bp12228^8 ≤ scalar12228.upperTail by norm_num [bp12228, scalar12228])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12228, bp12228, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12228:ℝ)) (by norm_num [em12228]) ?_)
      (show bm12228^8 ≤ scalar12228.lowerTail by norm_num [bm12228, scalar12228])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12228, bm12228, Finset.sum_range_succ, Nat.factorial]

theorem guards12228 :
    agent12228.root+dsL+scalar12228.worldRadius < √(1/100/aL) ∧
    2*(agent12228.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12228, agent12228, scalar12228, tp12228, tm12228, ep12228, em12228, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12228, agent12228, scalar12228, tp12228, tm12228, ep12228, em12228, dsL]

noncomputable def master12228 : MasterCertificate 12228 world12228 agent12228 :=
  master scalar12228 dsL tp12228 tm12228 ep12228 em12228
    (by norm_num [dsL]) (by norm_num [tp12228]) (by norm_num [tm12228])
    (by norm_num [ep12228]) (by norm_num [em12228])
    positive12228 negative12228 tails12228.1 tails12228.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12228.1 guards12228.2

theorem preserves12228 : master12228.toScalarCertificate = scalar12228 := rfl

noncomputable def tp12229 : ℝ := (575409421 / 2500000000)
noncomputable def tm12229 : ℝ := (-((47317377 / 78125000)))
noncomputable def ep12229 : ℝ := (5060536553718127 / 10000000000000000000)
noncomputable def em12229 : ℝ := (49531678640222751 / 100000000000000000000)
noncomputable def bp12229 : ℝ := (46136478005218986053 / 100000000000000000000)
noncomputable def bm12229 : ℝ := (11724986960889800193 / 25000000000000000000)

theorem positive12229 :
    Eplus aL (agent12229.root+dsL) scalar12229.worldRadius world12229.frame
      agent12229.frame tp12229 ≤ -ep12229 := by
  apply positive_check (eT := (14458537058606258529 / 12500000000000000000)) (y := (37151787006634316977 / 100000000000000000000)) (u := (144993375628232608953 / 100000000000000000000))
  · norm_num [world12229, agent12229, scalar12229, tp12229, tm12229, ep12229, em12229, dsL]
  · norm_num [world12229, agent12229, scalar12229, tp12229, tm12229, ep12229, em12229, dsL]
  · norm_num [world12229, agent12229, scalar12229, tp12229, tm12229, ep12229, em12229, dsL]
  · norm_num [world12229, agent12229, scalar12229, tp12229, tm12229, ep12229, em12229, dsL]
  · norm_num [world12229, agent12229, scalar12229, tp12229, tm12229, ep12229, em12229, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12229, agent12229, tp12229, tm12229, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12229, agent12229, scalar12229, tp12229, tm12229, ep12229, em12229, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12229, agent12229, tp12229, tm12229, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12229, agent12229, scalar12229, tp12229, tm12229, ep12229, em12229, dsL]

theorem negative12229 :
    Eminus aL (agent12229.root+dsL) scalar12229.worldRadius world12229.frame
      agent12229.frame tm12229 ≤ -em12229 := by
  apply negative_check (lo := (68179715077151963013 / 100000000000000000000)) (hi := (34089857538575981507 / 50000000000000000000))
    (y := (-((1416989011359987291 / 2000000000000000000)))) (u := (49238492244643058251 / 100000000000000000000))
  · norm_num [world12229, agent12229, scalar12229, tp12229, tm12229, ep12229, em12229, dsL]
  · norm_num [world12229, agent12229, scalar12229, tp12229, tm12229, ep12229, em12229, dsL]
  · norm_num [world12229, agent12229, scalar12229, tp12229, tm12229, ep12229, em12229, dsL]
  · norm_num [world12229, agent12229, scalar12229, tp12229, tm12229, ep12229, em12229, dsL]
  · norm_num [world12229, agent12229, scalar12229, tp12229, tm12229, ep12229, em12229, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12229, agent12229, tp12229, tm12229, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12229, agent12229, tp12229, tm12229, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12229, agent12229, scalar12229, tp12229, tm12229, ep12229, em12229, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12229, agent12229, tp12229, tm12229, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12229, agent12229, scalar12229, tp12229, tm12229, ep12229, em12229, dsL]

theorem tails12229 :
    exp (-((12229:ℝ)*ep12229)) ≤ scalar12229.upperTail ∧
    exp (-((12229:ℝ)*em12229)) ≤ scalar12229.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12229:ℝ)) (by norm_num [ep12229]) ?_)
      (show bp12229^8 ≤ scalar12229.upperTail by norm_num [bp12229, scalar12229])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12229, bp12229, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12229:ℝ)) (by norm_num [em12229]) ?_)
      (show bm12229^8 ≤ scalar12229.lowerTail by norm_num [bm12229, scalar12229])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12229, bm12229, Finset.sum_range_succ, Nat.factorial]

theorem guards12229 :
    agent12229.root+dsL+scalar12229.worldRadius < √(1/100/aL) ∧
    2*(agent12229.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12229, agent12229, scalar12229, tp12229, tm12229, ep12229, em12229, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12229, agent12229, scalar12229, tp12229, tm12229, ep12229, em12229, dsL]

noncomputable def master12229 : MasterCertificate 12229 world12229 agent12229 :=
  master scalar12229 dsL tp12229 tm12229 ep12229 em12229
    (by norm_num [dsL]) (by norm_num [tp12229]) (by norm_num [tm12229])
    (by norm_num [ep12229]) (by norm_num [em12229])
    positive12229 negative12229 tails12229.1 tails12229.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12229.1 guards12229.2

theorem preserves12229 : master12229.toScalarCertificate = scalar12229 := rfl

noncomputable def tp12230 : ℝ := (1150870717 / 5000000000)
noncomputable def tm12230 : ℝ := (-((3028427599 / 5000000000)))
noncomputable def ep12230 : ℝ := (50608515307781119 / 100000000000000000000)
noncomputable def em12230 : ℝ := (24767219224232241 / 50000000000000000000)
noncomputable def bp12230 : ℝ := (9226267656145394677 / 20000000000000000000)
noncomputable def bm12230 : ℝ := (46895065570805554623 / 100000000000000000000)

theorem positive12230 :
    Eplus aL (agent12230.root+dsL) scalar12230.worldRadius world12230.frame
      agent12230.frame tp12230 ≤ -ep12230 := by
  apply positive_check (eT := (7229291077040897171 / 6250000000000000000)) (y := (37152643702884708449 / 100000000000000000000)) (u := (72497308893182842761 / 50000000000000000000))
  · norm_num [world12230, agent12230, scalar12230, tp12230, tm12230, ep12230, em12230, dsL]
  · norm_num [world12230, agent12230, scalar12230, tp12230, tm12230, ep12230, em12230, dsL]
  · norm_num [world12230, agent12230, scalar12230, tp12230, tm12230, ep12230, em12230, dsL]
  · norm_num [world12230, agent12230, scalar12230, tp12230, tm12230, ep12230, em12230, dsL]
  · norm_num [world12230, agent12230, scalar12230, tp12230, tm12230, ep12230, em12230, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12230, agent12230, tp12230, tm12230, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12230, agent12230, scalar12230, tp12230, tm12230, ep12230, em12230, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12230, agent12230, tp12230, tm12230, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12230, agent12230, scalar12230, tp12230, tm12230, ep12230, em12230, dsL]

theorem negative12230 :
    Eminus aL (agent12230.root+dsL) scalar12230.worldRadius world12230.frame
      agent12230.frame tm12230 ≤ -em12230 := by
  apply negative_check (lo := (68179336894593504533 / 100000000000000000000)) (hi := (34089668447296752267 / 50000000000000000000))
    (y := (-((2214047997690582317 / 3125000000000000000)))) (u := (6154806276952488351 / 12500000000000000000))
  · norm_num [world12230, agent12230, scalar12230, tp12230, tm12230, ep12230, em12230, dsL]
  · norm_num [world12230, agent12230, scalar12230, tp12230, tm12230, ep12230, em12230, dsL]
  · norm_num [world12230, agent12230, scalar12230, tp12230, tm12230, ep12230, em12230, dsL]
  · norm_num [world12230, agent12230, scalar12230, tp12230, tm12230, ep12230, em12230, dsL]
  · norm_num [world12230, agent12230, scalar12230, tp12230, tm12230, ep12230, em12230, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12230, agent12230, tp12230, tm12230, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12230, agent12230, tp12230, tm12230, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12230, agent12230, scalar12230, tp12230, tm12230, ep12230, em12230, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12230, agent12230, tp12230, tm12230, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12230, agent12230, scalar12230, tp12230, tm12230, ep12230, em12230, dsL]

theorem tails12230 :
    exp (-((12230:ℝ)*ep12230)) ≤ scalar12230.upperTail ∧
    exp (-((12230:ℝ)*em12230)) ≤ scalar12230.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12230:ℝ)) (by norm_num [ep12230]) ?_)
      (show bp12230^8 ≤ scalar12230.upperTail by norm_num [bp12230, scalar12230])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12230, bp12230, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12230:ℝ)) (by norm_num [em12230]) ?_)
      (show bm12230^8 ≤ scalar12230.lowerTail by norm_num [bm12230, scalar12230])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12230, bm12230, Finset.sum_range_succ, Nat.factorial]

theorem guards12230 :
    agent12230.root+dsL+scalar12230.worldRadius < √(1/100/aL) ∧
    2*(agent12230.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12230, agent12230, scalar12230, tp12230, tm12230, ep12230, em12230, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12230, agent12230, scalar12230, tp12230, tm12230, ep12230, em12230, dsL]

noncomputable def master12230 : MasterCertificate 12230 world12230 agent12230 :=
  master scalar12230 dsL tp12230 tm12230 ep12230 em12230
    (by norm_num [dsL]) (by norm_num [tp12230]) (by norm_num [tm12230])
    (by norm_num [ep12230]) (by norm_num [em12230])
    positive12230 negative12230 tails12230.1 tails12230.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12230.1 guards12230.2

theorem preserves12230 : master12230.toScalarCertificate = scalar12230 := rfl

noncomputable def tp12231 : ℝ := (35966331 / 156250000)
noncomputable def tm12231 : ℝ := (-((6057086339 / 10000000000)))
noncomputable def ep12231 : ℝ := (2530583173977993 / 5000000000000000000)
noncomputable def em12231 : ℝ := (49537196750029563 / 100000000000000000000)
noncomputable def bp12231 : ℝ := (11531549973276021811 / 25000000000000000000)
noncomputable def bm12231 : ℝ := (187560738251601497 / 400000000000000000)

theorem positive12231 :
    Eplus aL (agent12231.root+dsL) scalar12231.worldRadius world12231.frame
      agent12231.frame tp12231 ≤ -ep12231 := by
  apply positive_check (eT := (4626760721143967303 / 4000000000000000000)) (y := (7430700200748877007 / 20000000000000000000)) (u := (72497930415899382397 / 50000000000000000000))
  · norm_num [world12231, agent12231, scalar12231, tp12231, tm12231, ep12231, em12231, dsL]
  · norm_num [world12231, agent12231, scalar12231, tp12231, tm12231, ep12231, em12231, dsL]
  · norm_num [world12231, agent12231, scalar12231, tp12231, tm12231, ep12231, em12231, dsL]
  · norm_num [world12231, agent12231, scalar12231, tp12231, tm12231, ep12231, em12231, dsL]
  · norm_num [world12231, agent12231, scalar12231, tp12231, tm12231, ep12231, em12231, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12231, agent12231, tp12231, tm12231, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12231, agent12231, scalar12231, tp12231, tm12231, ep12231, em12231, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12231, agent12231, tp12231, tm12231, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12231, agent12231, scalar12231, tp12231, tm12231, ep12231, em12231, dsL]

theorem negative12231 :
    Eminus aL (agent12231.root+dsL) scalar12231.worldRadius world12231.frame
      agent12231.frame tm12231 ≤ -em12231 := by
  apply negative_check (lo := (34089478899734291521 / 50000000000000000000)) (hi := (68178957799468583043 / 100000000000000000000))
    (y := (-((2214050759750669131 / 3125000000000000000)))) (u := (49238406695780554831 / 100000000000000000000))
  · norm_num [world12231, agent12231, scalar12231, tp12231, tm12231, ep12231, em12231, dsL]
  · norm_num [world12231, agent12231, scalar12231, tp12231, tm12231, ep12231, em12231, dsL]
  · norm_num [world12231, agent12231, scalar12231, tp12231, tm12231, ep12231, em12231, dsL]
  · norm_num [world12231, agent12231, scalar12231, tp12231, tm12231, ep12231, em12231, dsL]
  · norm_num [world12231, agent12231, scalar12231, tp12231, tm12231, ep12231, em12231, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12231, agent12231, tp12231, tm12231, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12231, agent12231, tp12231, tm12231, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12231, agent12231, scalar12231, tp12231, tm12231, ep12231, em12231, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12231, agent12231, tp12231, tm12231, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12231, agent12231, scalar12231, tp12231, tm12231, ep12231, em12231, dsL]

theorem tails12231 :
    exp (-((12231:ℝ)*ep12231)) ≤ scalar12231.upperTail ∧
    exp (-((12231:ℝ)*em12231)) ≤ scalar12231.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12231:ℝ)) (by norm_num [ep12231]) ?_)
      (show bp12231^8 ≤ scalar12231.upperTail by norm_num [bp12231, scalar12231])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12231, bp12231, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12231:ℝ)) (by norm_num [em12231]) ?_)
      (show bm12231^8 ≤ scalar12231.lowerTail by norm_num [bm12231, scalar12231])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12231, bm12231, Finset.sum_range_succ, Nat.factorial]

theorem guards12231 :
    agent12231.root+dsL+scalar12231.worldRadius < √(1/100/aL) ∧
    2*(agent12231.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12231, agent12231, scalar12231, tp12231, tm12231, ep12231, em12231, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12231, agent12231, scalar12231, tp12231, tm12231, ep12231, em12231, dsL]

noncomputable def master12231 : MasterCertificate 12231 world12231 agent12231 :=
  master scalar12231 dsL tp12231 tm12231 ep12231 em12231
    (by norm_num [dsL]) (by norm_num [tp12231]) (by norm_num [tm12231])
    (by norm_num [ep12231]) (by norm_num [em12231])
    positive12231 negative12231 tails12231.1 tails12231.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12231.1 guards12231.2

theorem preserves12231 : master12231.toScalarCertificate = scalar12231 := rfl

noncomputable def tp12232 : ℝ := (575487207 / 2500000000)
noncomputable def tm12232 : ℝ := (-((1514329257 / 2500000000)))
noncomputable def ep12232 : ℝ := (12653702582944667 / 25000000000000000000)
noncomputable def em12232 : ℝ := (49539953837598669 / 100000000000000000000)
noncomputable def bp12232 : ℝ := (46121062645375188441 / 100000000000000000000)
noncomputable def bm12232 : ℝ := (46885304610003562757 / 100000000000000000000)

theorem positive12232 :
    Eplus aL (agent12232.root+dsL) scalar12232.worldRadius world12232.frame
      agent12232.frame tp12232 ≤ -ep12232 := by
  apply positive_check (eT := (23133875616261697383 / 20000000000000000000)) (y := (18577178385552397459 / 50000000000000000000)) (u := (144997101664359021117 / 100000000000000000000))
  · norm_num [world12232, agent12232, scalar12232, tp12232, tm12232, ep12232, em12232, dsL]
  · norm_num [world12232, agent12232, scalar12232, tp12232, tm12232, ep12232, em12232, dsL]
  · norm_num [world12232, agent12232, scalar12232, tp12232, tm12232, ep12232, em12232, dsL]
  · norm_num [world12232, agent12232, scalar12232, tp12232, tm12232, ep12232, em12232, dsL]
  · norm_num [world12232, agent12232, scalar12232, tp12232, tm12232, ep12232, em12232, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12232, agent12232, tp12232, tm12232, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12232, agent12232, scalar12232, tp12232, tm12232, ep12232, em12232, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12232, agent12232, tp12232, tm12232, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12232, agent12232, scalar12232, tp12232, tm12232, ep12232, em12232, dsL]

theorem negative12232 :
    Eminus aL (agent12232.root+dsL) scalar12232.worldRadius world12232.frame
      agent12232.frame tm12232 ≤ -em12232 := by
  apply negative_check (lo := (4261161287412574477 / 6250000000000000000)) (hi := (68178580598601191633 / 100000000000000000000))
    (y := (-((14169941781006348307 / 20000000000000000000)))) (u := (49238365043547710107 / 100000000000000000000))
  · norm_num [world12232, agent12232, scalar12232, tp12232, tm12232, ep12232, em12232, dsL]
  · norm_num [world12232, agent12232, scalar12232, tp12232, tm12232, ep12232, em12232, dsL]
  · norm_num [world12232, agent12232, scalar12232, tp12232, tm12232, ep12232, em12232, dsL]
  · norm_num [world12232, agent12232, scalar12232, tp12232, tm12232, ep12232, em12232, dsL]
  · norm_num [world12232, agent12232, scalar12232, tp12232, tm12232, ep12232, em12232, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12232, agent12232, tp12232, tm12232, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12232, agent12232, tp12232, tm12232, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12232, agent12232, scalar12232, tp12232, tm12232, ep12232, em12232, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12232, agent12232, tp12232, tm12232, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12232, agent12232, scalar12232, tp12232, tm12232, ep12232, em12232, dsL]

theorem tails12232 :
    exp (-((12232:ℝ)*ep12232)) ≤ scalar12232.upperTail ∧
    exp (-((12232:ℝ)*em12232)) ≤ scalar12232.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12232:ℝ)) (by norm_num [ep12232]) ?_)
      (show bp12232^8 ≤ scalar12232.upperTail by norm_num [bp12232, scalar12232])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12232, bp12232, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12232:ℝ)) (by norm_num [em12232]) ?_)
      (show bm12232^8 ≤ scalar12232.lowerTail by norm_num [bm12232, scalar12232])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12232, bm12232, Finset.sum_range_succ, Nat.factorial]

theorem guards12232 :
    agent12232.root+dsL+scalar12232.worldRadius < √(1/100/aL) ∧
    2*(agent12232.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12232, agent12232, scalar12232, tp12232, tm12232, ep12232, em12232, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12232, agent12232, scalar12232, tp12232, tm12232, ep12232, em12232, dsL]

noncomputable def master12232 : MasterCertificate 12232 world12232 agent12232 :=
  master scalar12232 dsL tp12232 tm12232 ep12232 em12232
    (by norm_num [dsL]) (by norm_num [tp12232]) (by norm_num [tm12232])
    (by norm_num [ep12232]) (by norm_num [em12232])
    positive12232 negative12232 tails12232.1 tails12232.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12232.1 guards12232.2

theorem preserves12232 : master12232.toScalarCertificate = scalar12232 := rfl

noncomputable def tp12233 : ℝ := (575513113 / 2500000000)
noncomputable def tm12233 : ℝ := (-((6057547861 / 10000000000)))
noncomputable def ep12233 : ℝ := (25308977560662107 / 50000000000000000000)
noncomputable def em12233 : ℝ := (49542708988595417 / 100000000000000000000)
noncomputable def bp12233 : ℝ := (11528981765384110637 / 25000000000000000000)
noncomputable def bm12233 : ℝ := (46880426230091222813 / 100000000000000000000)

theorem positive12233 :
    Eplus aL (agent12233.root+dsL) scalar12233.worldRadius world12233.frame
      agent12233.frame tp12233 ≤ -ep12233 := by
  apply positive_check (eT := (57834869009934746661 / 50000000000000000000)) (y := (18577606421926118277 / 50000000000000000000)) (u := (1159986743602752783 / 800000000000000000))
  · norm_num [world12233, agent12233, scalar12233, tp12233, tm12233, ep12233, em12233, dsL]
  · norm_num [world12233, agent12233, scalar12233, tp12233, tm12233, ep12233, em12233, dsL]
  · norm_num [world12233, agent12233, scalar12233, tp12233, tm12233, ep12233, em12233, dsL]
  · norm_num [world12233, agent12233, scalar12233, tp12233, tm12233, ep12233, em12233, dsL]
  · norm_num [world12233, agent12233, scalar12233, tp12233, tm12233, ep12233, em12233, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12233, agent12233, tp12233, tm12233, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12233, agent12233, scalar12233, tp12233, tm12233, ep12233, em12233, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12233, agent12233, tp12233, tm12233, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12233, agent12233, scalar12233, tp12233, tm12233, ep12233, em12233, dsL]

theorem negative12233 :
    Eminus aL (agent12233.root+dsL) scalar12233.worldRadius world12233.frame
      agent12233.frame tm12233 ≤ -em12233 := by
  apply negative_check (lo := (17044550680582705913 / 25000000000000000000)) (hi := (68178202722330823653 / 100000000000000000000))
    (y := (-((35424897935043319373 / 50000000000000000000)))) (u := (1538697569481098087 / 3125000000000000000))
  · norm_num [world12233, agent12233, scalar12233, tp12233, tm12233, ep12233, em12233, dsL]
  · norm_num [world12233, agent12233, scalar12233, tp12233, tm12233, ep12233, em12233, dsL]
  · norm_num [world12233, agent12233, scalar12233, tp12233, tm12233, ep12233, em12233, dsL]
  · norm_num [world12233, agent12233, scalar12233, tp12233, tm12233, ep12233, em12233, dsL]
  · norm_num [world12233, agent12233, scalar12233, tp12233, tm12233, ep12233, em12233, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12233, agent12233, tp12233, tm12233, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12233, agent12233, tp12233, tm12233, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12233, agent12233, scalar12233, tp12233, tm12233, ep12233, em12233, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12233, agent12233, tp12233, tm12233, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12233, agent12233, scalar12233, tp12233, tm12233, ep12233, em12233, dsL]

theorem tails12233 :
    exp (-((12233:ℝ)*ep12233)) ≤ scalar12233.upperTail ∧
    exp (-((12233:ℝ)*em12233)) ≤ scalar12233.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12233:ℝ)) (by norm_num [ep12233]) ?_)
      (show bp12233^8 ≤ scalar12233.upperTail by norm_num [bp12233, scalar12233])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12233, bp12233, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12233:ℝ)) (by norm_num [em12233]) ?_)
      (show bm12233^8 ≤ scalar12233.lowerTail by norm_num [bm12233, scalar12233])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12233, bm12233, Finset.sum_range_succ, Nat.factorial]

theorem guards12233 :
    agent12233.root+dsL+scalar12233.worldRadius < √(1/100/aL) ∧
    2*(agent12233.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12233, agent12233, scalar12233, tp12233, tm12233, ep12233, em12233, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12233, agent12233, scalar12233, tp12233, tm12233, ep12233, em12233, dsL]

noncomputable def master12233 : MasterCertificate 12233 world12233 agent12233 :=
  master scalar12233 dsL tp12233 tm12233 ep12233 em12233
    (by norm_num [dsL]) (by norm_num [tp12233]) (by norm_num [tm12233])
    (by norm_num [ep12233]) (by norm_num [em12233])
    positive12233 negative12233 tails12233.1 tails12233.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12233.1 guards12233.2

theorem preserves12233 : master12233.toScalarCertificate = scalar12233 := rfl

noncomputable def tp12234 : ℝ := (2302156017 / 10000000000)
noncomputable def tm12234 : ℝ := (-((1514444629 / 2500000000)))
noncomputable def ep12234 : ℝ := (632763738188539 / 1250000000000000000)
noncomputable def em12234 : ℝ := (193536966232789 / 390625000000000000)
noncomputable def bp12234 : ℝ := (46110792290480846363 / 100000000000000000000)
noncomputable def bm12234 : ℝ := (23437774298451087633 / 50000000000000000000)

theorem positive12234 :
    Eplus aL (agent12234.root+dsL) scalar12234.worldRadius world12234.frame
      agent12234.frame tp12234 ≤ -ep12234 := by
  apply positive_check (eT := (28917524389748817127 / 25000000000000000000)) (y := (37156068150078926127 / 100000000000000000000)) (u := (28999916627100726351 / 20000000000000000000))
  · norm_num [world12234, agent12234, scalar12234, tp12234, tm12234, ep12234, em12234, dsL]
  · norm_num [world12234, agent12234, scalar12234, tp12234, tm12234, ep12234, em12234, dsL]
  · norm_num [world12234, agent12234, scalar12234, tp12234, tm12234, ep12234, em12234, dsL]
  · norm_num [world12234, agent12234, scalar12234, tp12234, tm12234, ep12234, em12234, dsL]
  · norm_num [world12234, agent12234, scalar12234, tp12234, tm12234, ep12234, em12234, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12234, agent12234, tp12234, tm12234, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12234, agent12234, scalar12234, tp12234, tm12234, ep12234, em12234, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12234, agent12234, tp12234, tm12234, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12234, agent12234, scalar12234, tp12234, tm12234, ep12234, em12234, dsL]

theorem negative12234 :
    Eminus aL (agent12234.root+dsL) scalar12234.worldRadius world12234.frame
      agent12234.frame tm12234 ≤ -em12234 := by
  apply negative_check (lo := (4261114097434465219 / 6250000000000000000)) (hi := (13635565111790288701 / 20000000000000000000))
    (y := (-((70849881799069056807 / 100000000000000000000)))) (u := (49238279913424070761 / 100000000000000000000))
  · norm_num [world12234, agent12234, scalar12234, tp12234, tm12234, ep12234, em12234, dsL]
  · norm_num [world12234, agent12234, scalar12234, tp12234, tm12234, ep12234, em12234, dsL]
  · norm_num [world12234, agent12234, scalar12234, tp12234, tm12234, ep12234, em12234, dsL]
  · norm_num [world12234, agent12234, scalar12234, tp12234, tm12234, ep12234, em12234, dsL]
  · norm_num [world12234, agent12234, scalar12234, tp12234, tm12234, ep12234, em12234, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12234, agent12234, tp12234, tm12234, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12234, agent12234, tp12234, tm12234, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12234, agent12234, scalar12234, tp12234, tm12234, ep12234, em12234, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12234, agent12234, tp12234, tm12234, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12234, agent12234, scalar12234, tp12234, tm12234, ep12234, em12234, dsL]

theorem tails12234 :
    exp (-((12234:ℝ)*ep12234)) ≤ scalar12234.upperTail ∧
    exp (-((12234:ℝ)*em12234)) ≤ scalar12234.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12234:ℝ)) (by norm_num [ep12234]) ?_)
      (show bp12234^8 ≤ scalar12234.upperTail by norm_num [bp12234, scalar12234])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12234, bp12234, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12234:ℝ)) (by norm_num [em12234]) ?_)
      (show bm12234^8 ≤ scalar12234.lowerTail by norm_num [bm12234, scalar12234])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12234, bm12234, Finset.sum_range_succ, Nat.factorial]

theorem guards12234 :
    agent12234.root+dsL+scalar12234.worldRadius < √(1/100/aL) ∧
    2*(agent12234.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12234, agent12234, scalar12234, tp12234, tm12234, ep12234, em12234, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12234, agent12234, scalar12234, tp12234, tm12234, ep12234, em12234, dsL]

noncomputable def master12234 : MasterCertificate 12234 world12234 agent12234 :=
  master scalar12234 dsL tp12234 tm12234 ep12234 em12234
    (by norm_num [dsL]) (by norm_num [tp12234]) (by norm_num [tm12234])
    (by norm_num [ep12234]) (by norm_num [em12234])
    positive12234 negative12234 tails12234.1 tails12234.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12234.1 guards12234.2

theorem preserves12234 : master12234.toScalarCertificate = scalar12234 := rfl

noncomputable def tp12235 : ℝ := (575564889 / 2500000000)
noncomputable def tm12235 : ℝ := (-((1514502201 / 2500000000)))
noncomputable def ep12235 : ℝ := (25312120535152159 / 50000000000000000000)
noncomputable def em12235 : ℝ := (12387053984068131 / 25000000000000000000)
noncomputable def bp12235 : ℝ := (23052829540794092623 / 50000000000000000000)
noncomputable def bm12235 : ℝ := (46870672428939470307 / 100000000000000000000)

theorem positive12235 :
    Eplus aL (agent12235.root+dsL) scalar12235.worldRadius world12235.frame
      agent12235.frame tp12235 ≤ -ep12235 := by
  apply positive_check (eT := (115670456940110453043 / 100000000000000000000)) (y := (18578461753826169349 / 50000000000000000000)) (u := (145000823405723763009 / 100000000000000000000))
  · norm_num [world12235, agent12235, scalar12235, tp12235, tm12235, ep12235, em12235, dsL]
  · norm_num [world12235, agent12235, scalar12235, tp12235, tm12235, ep12235, em12235, dsL]
  · norm_num [world12235, agent12235, scalar12235, tp12235, tm12235, ep12235, em12235, dsL]
  · norm_num [world12235, agent12235, scalar12235, tp12235, tm12235, ep12235, em12235, dsL]
  · norm_num [world12235, agent12235, scalar12235, tp12235, tm12235, ep12235, em12235, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12235, agent12235, tp12235, tm12235, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12235, agent12235, scalar12235, tp12235, tm12235, ep12235, em12235, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12235, agent12235, tp12235, tm12235, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12235, agent12235, scalar12235, tp12235, tm12235, ep12235, em12235, dsL]

theorem negative12235 :
    Eminus aL (agent12235.root+dsL) scalar12235.worldRadius world12235.frame
      agent12235.frame tm12235 ≤ -em12235 := by
  apply negative_check (lo := (68177449923114181313 / 100000000000000000000)) (hi := (34088724961557090657 / 50000000000000000000))
    (y := (-((35424982454616445557 / 50000000000000000000)))) (u := (49238238991425970691 / 100000000000000000000))
  · norm_num [world12235, agent12235, scalar12235, tp12235, tm12235, ep12235, em12235, dsL]
  · norm_num [world12235, agent12235, scalar12235, tp12235, tm12235, ep12235, em12235, dsL]
  · norm_num [world12235, agent12235, scalar12235, tp12235, tm12235, ep12235, em12235, dsL]
  · norm_num [world12235, agent12235, scalar12235, tp12235, tm12235, ep12235, em12235, dsL]
  · norm_num [world12235, agent12235, scalar12235, tp12235, tm12235, ep12235, em12235, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12235, agent12235, tp12235, tm12235, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12235, agent12235, tp12235, tm12235, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12235, agent12235, scalar12235, tp12235, tm12235, ep12235, em12235, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12235, agent12235, tp12235, tm12235, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12235, agent12235, scalar12235, tp12235, tm12235, ep12235, em12235, dsL]

theorem tails12235 :
    exp (-((12235:ℝ)*ep12235)) ≤ scalar12235.upperTail ∧
    exp (-((12235:ℝ)*em12235)) ≤ scalar12235.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12235:ℝ)) (by norm_num [ep12235]) ?_)
      (show bp12235^8 ≤ scalar12235.upperTail by norm_num [bp12235, scalar12235])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12235, bp12235, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12235:ℝ)) (by norm_num [em12235]) ?_)
      (show bm12235^8 ≤ scalar12235.lowerTail by norm_num [bm12235, scalar12235])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12235, bm12235, Finset.sum_range_succ, Nat.factorial]

theorem guards12235 :
    agent12235.root+dsL+scalar12235.worldRadius < √(1/100/aL) ∧
    2*(agent12235.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12235, agent12235, scalar12235, tp12235, tm12235, ep12235, em12235, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12235, agent12235, scalar12235, tp12235, tm12235, ep12235, em12235, dsL]

noncomputable def master12235 : MasterCertificate 12235 world12235 agent12235 :=
  master scalar12235 dsL tp12235 tm12235 ep12235 em12235
    (by norm_num [dsL]) (by norm_num [tp12235]) (by norm_num [tm12235])
    (by norm_num [ep12235]) (by norm_num [em12235])
    positive12235 negative12235 tails12235.1 tails12235.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12235.1 guards12235.2

theorem preserves12235 : master12235.toScalarCertificate = scalar12235 := rfl

noncomputable def tp12236 : ℝ := (2302363001 / 10000000000)
noncomputable def tm12236 : ℝ := (-((6058239211 / 10000000000)))
noncomputable def ep12236 : ℝ := (25313690873664163 / 50000000000000000000)
noncomputable def em12236 : ℝ := (24775483646587967 / 50000000000000000000)
noncomputable def bp12236 : ℝ := (5762565878199150893 / 12500000000000000000)
noncomputable def bm12236 : ℝ := (2929112332682888867 / 6250000000000000000)

theorem positive12236 :
    Eplus aL (agent12236.root+dsL) scalar12236.worldRadius world12236.frame
      agent12236.frame tp12236 ≤ -ep12236 := by
  apply positive_check (eT := (1156708156658673801 / 1000000000000000000)) (y := (11611805512578963 / 31250000000000000)) (u := (145002061910316465149 / 100000000000000000000))
  · norm_num [world12236, agent12236, scalar12236, tp12236, tm12236, ep12236, em12236, dsL]
  · norm_num [world12236, agent12236, scalar12236, tp12236, tm12236, ep12236, em12236, dsL]
  · norm_num [world12236, agent12236, scalar12236, tp12236, tm12236, ep12236, em12236, dsL]
  · norm_num [world12236, agent12236, scalar12236, tp12236, tm12236, ep12236, em12236, dsL]
  · norm_num [world12236, agent12236, scalar12236, tp12236, tm12236, ep12236, em12236, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12236, agent12236, tp12236, tm12236, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12236, agent12236, scalar12236, tp12236, tm12236, ep12236, em12236, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12236, agent12236, tp12236, tm12236, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12236, agent12236, scalar12236, tp12236, tm12236, ep12236, em12236, dsL]

theorem negative12236 :
    Eminus aL (agent12236.root+dsL) scalar12236.worldRadius world12236.frame
      agent12236.frame tm12236 ≤ -em12236 := by
  apply negative_check (lo := (6817707371964804099 / 10000000000000000000)) (hi := (68177073719648040991 / 100000000000000000000))
    (y := (-((70850050115739038243 / 100000000000000000000)))) (u := (24619098518630355783 / 50000000000000000000))
  · norm_num [world12236, agent12236, scalar12236, tp12236, tm12236, ep12236, em12236, dsL]
  · norm_num [world12236, agent12236, scalar12236, tp12236, tm12236, ep12236, em12236, dsL]
  · norm_num [world12236, agent12236, scalar12236, tp12236, tm12236, ep12236, em12236, dsL]
  · norm_num [world12236, agent12236, scalar12236, tp12236, tm12236, ep12236, em12236, dsL]
  · norm_num [world12236, agent12236, scalar12236, tp12236, tm12236, ep12236, em12236, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12236, agent12236, tp12236, tm12236, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12236, agent12236, tp12236, tm12236, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12236, agent12236, scalar12236, tp12236, tm12236, ep12236, em12236, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12236, agent12236, tp12236, tm12236, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12236, agent12236, scalar12236, tp12236, tm12236, ep12236, em12236, dsL]

theorem tails12236 :
    exp (-((12236:ℝ)*ep12236)) ≤ scalar12236.upperTail ∧
    exp (-((12236:ℝ)*em12236)) ≤ scalar12236.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12236:ℝ)) (by norm_num [ep12236]) ?_)
      (show bp12236^8 ≤ scalar12236.upperTail by norm_num [bp12236, scalar12236])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12236, bp12236, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12236:ℝ)) (by norm_num [em12236]) ?_)
      (show bm12236^8 ≤ scalar12236.lowerTail by norm_num [bm12236, scalar12236])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12236, bm12236, Finset.sum_range_succ, Nat.factorial]

theorem guards12236 :
    agent12236.root+dsL+scalar12236.worldRadius < √(1/100/aL) ∧
    2*(agent12236.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12236, agent12236, scalar12236, tp12236, tm12236, ep12236, em12236, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12236, agent12236, scalar12236, tp12236, tm12236, ep12236, em12236, dsL]

noncomputable def master12236 : MasterCertificate 12236 world12236 agent12236 :=
  master scalar12236 dsL tp12236 tm12236 ep12236 em12236
    (by norm_num [dsL]) (by norm_num [tp12236]) (by norm_num [tm12236])
    (by norm_num [ep12236]) (by norm_num [em12236])
    positive12236 negative12236 tails12236.1 tails12236.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12236.1 guards12236.2

theorem preserves12236 : master12236.toScalarCertificate = scalar12236 := rfl

noncomputable def tp12237 : ℝ := (1151233223 / 5000000000)
noncomputable def tm12237 : ℝ := (-((6058469487 / 10000000000)))
noncomputable def ep12237 : ℝ := (50630520988119853 / 100000000000000000000)
noncomputable def em12237 : ℝ := (1982148692144827 / 4000000000000000000)
noncomputable def bp12237 : ℝ := (46095396191592829193 / 100000000000000000000)
noncomputable def bm12237 : ℝ := (11715230841697686571 / 25000000000000000000)

theorem positive12237 :
    Eplus aL (agent12237.root+dsL) scalar12237.worldRadius world12237.frame
      agent12237.frame tp12237 ≤ -ep12237 := by
  apply positive_check (eT := (115671174423779191913 / 100000000000000000000)) (y := (18579316063025904621 / 50000000000000000000)) (u := (145003300937637579789 / 100000000000000000000))
  · norm_num [world12237, agent12237, scalar12237, tp12237, tm12237, ep12237, em12237, dsL]
  · norm_num [world12237, agent12237, scalar12237, tp12237, tm12237, ep12237, em12237, dsL]
  · norm_num [world12237, agent12237, scalar12237, tp12237, tm12237, ep12237, em12237, dsL]
  · norm_num [world12237, agent12237, scalar12237, tp12237, tm12237, ep12237, em12237, dsL]
  · norm_num [world12237, agent12237, scalar12237, tp12237, tm12237, ep12237, em12237, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12237, agent12237, tp12237, tm12237, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12237, agent12237, scalar12237, tp12237, tm12237, ep12237, em12237, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12237, agent12237, tp12237, tm12237, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12237, agent12237, scalar12237, tp12237, tm12237, ep12237, em12237, dsL]

theorem negative12237 :
    Eminus aL (agent12237.root+dsL) scalar12237.worldRadius world12237.frame
      agent12237.frame tm12237 ≤ -em12237 := by
  apply negative_check (lo := (68176698026304212281 / 100000000000000000000)) (hi := (34088349013152106141 / 50000000000000000000))
    (y := (-((8856266810735257267 / 12500000000000000000)))) (u := (3077384718433810967 / 6250000000000000000))
  · norm_num [world12237, agent12237, scalar12237, tp12237, tm12237, ep12237, em12237, dsL]
  · norm_num [world12237, agent12237, scalar12237, tp12237, tm12237, ep12237, em12237, dsL]
  · norm_num [world12237, agent12237, scalar12237, tp12237, tm12237, ep12237, em12237, dsL]
  · norm_num [world12237, agent12237, scalar12237, tp12237, tm12237, ep12237, em12237, dsL]
  · norm_num [world12237, agent12237, scalar12237, tp12237, tm12237, ep12237, em12237, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12237, agent12237, tp12237, tm12237, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12237, agent12237, tp12237, tm12237, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12237, agent12237, scalar12237, tp12237, tm12237, ep12237, em12237, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12237, agent12237, tp12237, tm12237, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12237, agent12237, scalar12237, tp12237, tm12237, ep12237, em12237, dsL]

theorem tails12237 :
    exp (-((12237:ℝ)*ep12237)) ≤ scalar12237.upperTail ∧
    exp (-((12237:ℝ)*em12237)) ≤ scalar12237.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12237:ℝ)) (by norm_num [ep12237]) ?_)
      (show bp12237^8 ≤ scalar12237.upperTail by norm_num [bp12237, scalar12237])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12237, bp12237, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12237:ℝ)) (by norm_num [em12237]) ?_)
      (show bm12237^8 ≤ scalar12237.lowerTail by norm_num [bm12237, scalar12237])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12237, bm12237, Finset.sum_range_succ, Nat.factorial]

theorem guards12237 :
    agent12237.root+dsL+scalar12237.worldRadius < √(1/100/aL) ∧
    2*(agent12237.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12237, agent12237, scalar12237, tp12237, tm12237, ep12237, em12237, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12237, agent12237, scalar12237, tp12237, tm12237, ep12237, em12237, dsL]

noncomputable def master12237 : MasterCertificate 12237 world12237 agent12237 :=
  master scalar12237 dsL tp12237 tm12237 ep12237 em12237
    (by norm_num [dsL]) (by norm_num [tp12237]) (by norm_num [tm12237])
    (by norm_num [ep12237]) (by norm_num [em12237])
    positive12237 negative12237 tails12237.1 tails12237.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12237.1 guards12237.2

theorem preserves12237 : master12237.toScalarCertificate = scalar12237 := rfl

noncomputable def tp12238 : ℝ := (2302569817 / 10000000000)
noncomputable def tm12238 : ℝ := (-((6058699837 / 10000000000)))
noncomputable def ep12238 : ℝ := (10126731726895191 / 20000000000000000000)
noncomputable def em12238 : ℝ := (6194558226429349 / 12500000000000000000)
noncomputable def bp12238 : ℝ := (46090266691097918789 / 100000000000000000000)
noncomputable def bm12238 : ℝ := (11714012668114334449 / 25000000000000000000)

theorem positive12238 :
    Eplus aL (agent12238.root+dsL) scalar12238.worldRadius world12238.frame
      agent12238.frame tp12238 ≤ -ep12238 := by
  apply positive_check (eT := (11567153267265222069 / 10000000000000000000)) (y := (7431897186434350323 / 20000000000000000000)) (u := (14500453898998037961 / 10000000000000000000))
  · norm_num [world12238, agent12238, scalar12238, tp12238, tm12238, ep12238, em12238, dsL]
  · norm_num [world12238, agent12238, scalar12238, tp12238, tm12238, ep12238, em12238, dsL]
  · norm_num [world12238, agent12238, scalar12238, tp12238, tm12238, ep12238, em12238, dsL]
  · norm_num [world12238, agent12238, scalar12238, tp12238, tm12238, ep12238, em12238, dsL]
  · norm_num [world12238, agent12238, scalar12238, tp12238, tm12238, ep12238, em12238, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12238, agent12238, tp12238, tm12238, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12238, agent12238, scalar12238, tp12238, tm12238, ep12238, em12238, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12238, agent12238, tp12238, tm12238, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12238, agent12238, scalar12238, tp12238, tm12238, ep12238, em12238, dsL]

theorem negative12238 :
    Eminus aL (agent12238.root+dsL) scalar12238.worldRadius world12238.frame
      agent12238.frame tm12238 ≤ -em12238 := by
  apply negative_check (lo := (13635264391870785057 / 20000000000000000000)) (hi := (34088160979676962643 / 50000000000000000000))
    (y := (-((17712555170376498817 / 25000000000000000000)))) (u := (12309528263455980667 / 25000000000000000000))
  · norm_num [world12238, agent12238, scalar12238, tp12238, tm12238, ep12238, em12238, dsL]
  · norm_num [world12238, agent12238, scalar12238, tp12238, tm12238, ep12238, em12238, dsL]
  · norm_num [world12238, agent12238, scalar12238, tp12238, tm12238, ep12238, em12238, dsL]
  · norm_num [world12238, agent12238, scalar12238, tp12238, tm12238, ep12238, em12238, dsL]
  · norm_num [world12238, agent12238, scalar12238, tp12238, tm12238, ep12238, em12238, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12238, agent12238, tp12238, tm12238, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12238, agent12238, tp12238, tm12238, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12238, agent12238, scalar12238, tp12238, tm12238, ep12238, em12238, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12238, agent12238, tp12238, tm12238, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12238, agent12238, scalar12238, tp12238, tm12238, ep12238, em12238, dsL]

theorem tails12238 :
    exp (-((12238:ℝ)*ep12238)) ≤ scalar12238.upperTail ∧
    exp (-((12238:ℝ)*em12238)) ≤ scalar12238.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12238:ℝ)) (by norm_num [ep12238]) ?_)
      (show bp12238^8 ≤ scalar12238.upperTail by norm_num [bp12238, scalar12238])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12238, bp12238, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12238:ℝ)) (by norm_num [em12238]) ?_)
      (show bm12238^8 ≤ scalar12238.lowerTail by norm_num [bm12238, scalar12238])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12238, bm12238, Finset.sum_range_succ, Nat.factorial]

theorem guards12238 :
    agent12238.root+dsL+scalar12238.worldRadius < √(1/100/aL) ∧
    2*(agent12238.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12238, agent12238, scalar12238, tp12238, tm12238, ep12238, em12238, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12238, agent12238, scalar12238, tp12238, tm12238, ep12238, em12238, dsL]

noncomputable def master12238 : MasterCertificate 12238 world12238 agent12238 :=
  master scalar12238 dsL tp12238 tm12238 ep12238 em12238
    (by norm_num [dsL]) (by norm_num [tp12238]) (by norm_num [tm12238])
    (by norm_num [ep12238]) (by norm_num [em12238])
    positive12238 negative12238 tails12238.1 tails12238.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12238.1 guards12238.2

theorem preserves12238 : master12238.toScalarCertificate = scalar12238 := rfl

noncomputable def tp12239 : ℝ := (2302673179 / 10000000000)
noncomputable def tm12239 : ℝ := (-((6058929763 / 10000000000)))
noncomputable def ep12239 : ℝ := (25318397480554043 / 50000000000000000000)
noncomputable def em12239 : ℝ := (49559213105403289 / 100000000000000000000)
noncomputable def bp12239 : ℝ := (46085138330381989329 / 100000000000000000000)
noncomputable def bm12239 : ℝ := (46851179032910955081 / 100000000000000000000)

theorem positive12239 :
    Eplus aL (agent12239.root+dsL) scalar12239.worldRadius world12239.frame
      agent12239.frame tp12239 ≤ -ep12239 := by
  apply positive_check (eT := (57835945443910197739 / 50000000000000000000)) (y := (9290084971545738943 / 25000000000000000000)) (u := (145005777267344664729 / 100000000000000000000))
  · norm_num [world12239, agent12239, scalar12239, tp12239, tm12239, ep12239, em12239, dsL]
  · norm_num [world12239, agent12239, scalar12239, tp12239, tm12239, ep12239, em12239, dsL]
  · norm_num [world12239, agent12239, scalar12239, tp12239, tm12239, ep12239, em12239, dsL]
  · norm_num [world12239, agent12239, scalar12239, tp12239, tm12239, ep12239, em12239, dsL]
  · norm_num [world12239, agent12239, scalar12239, tp12239, tm12239, ep12239, em12239, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12239, agent12239, tp12239, tm12239, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12239, agent12239, scalar12239, tp12239, tm12239, ep12239, em12239, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12239, agent12239, tp12239, tm12239, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12239, agent12239, scalar12239, tp12239, tm12239, ep12239, em12239, dsL]

theorem negative12239 :
    Eminus aL (agent12239.root+dsL) scalar12239.worldRadius world12239.frame
      agent12239.frame tm12239 ≤ -em12239 := by
  apply negative_check (lo := (4260996729096468387 / 6250000000000000000)) (hi := (68175947665543494193 / 100000000000000000000))
    (y := (-((35425151676054165543 / 50000000000000000000)))) (u := (24619036174198053997 / 50000000000000000000))
  · norm_num [world12239, agent12239, scalar12239, tp12239, tm12239, ep12239, em12239, dsL]
  · norm_num [world12239, agent12239, scalar12239, tp12239, tm12239, ep12239, em12239, dsL]
  · norm_num [world12239, agent12239, scalar12239, tp12239, tm12239, ep12239, em12239, dsL]
  · norm_num [world12239, agent12239, scalar12239, tp12239, tm12239, ep12239, em12239, dsL]
  · norm_num [world12239, agent12239, scalar12239, tp12239, tm12239, ep12239, em12239, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12239, agent12239, tp12239, tm12239, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12239, agent12239, tp12239, tm12239, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12239, agent12239, scalar12239, tp12239, tm12239, ep12239, em12239, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12239, agent12239, tp12239, tm12239, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12239, agent12239, scalar12239, tp12239, tm12239, ep12239, em12239, dsL]

theorem tails12239 :
    exp (-((12239:ℝ)*ep12239)) ≤ scalar12239.upperTail ∧
    exp (-((12239:ℝ)*em12239)) ≤ scalar12239.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12239:ℝ)) (by norm_num [ep12239]) ?_)
      (show bp12239^8 ≤ scalar12239.upperTail by norm_num [bp12239, scalar12239])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12239, bp12239, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12239:ℝ)) (by norm_num [em12239]) ?_)
      (show bm12239^8 ≤ scalar12239.lowerTail by norm_num [bm12239, scalar12239])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12239, bm12239, Finset.sum_range_succ, Nat.factorial]

theorem guards12239 :
    agent12239.root+dsL+scalar12239.worldRadius < √(1/100/aL) ∧
    2*(agent12239.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12239, agent12239, scalar12239, tp12239, tm12239, ep12239, em12239, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12239, agent12239, scalar12239, tp12239, tm12239, ep12239, em12239, dsL]

noncomputable def master12239 : MasterCertificate 12239 world12239 agent12239 :=
  master scalar12239 dsL tp12239 tm12239 ep12239 em12239
    (by norm_num [dsL]) (by norm_num [tp12239]) (by norm_num [tm12239])
    (by norm_num [ep12239]) (by norm_num [em12239])
    positive12239 negative12239 tails12239.1 tails12239.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12239.1 guards12239.2

theorem preserves12239 : master12239.toScalarCertificate = scalar12239 := rfl

noncomputable def tp12240 : ℝ := (1151388233 / 5000000000)
noncomputable def tm12240 : ℝ := (-((6059159709 / 10000000000)))
noncomputable def ep12240 : ℝ := (25319964686771487 / 50000000000000000000)
noncomputable def em12240 : ℝ := (24780979308480359 / 50000000000000000000)
noncomputable def bp12240 : ℝ := (5760001441067209129 / 12500000000000000000)
noncomputable def bm12240 : ℝ := (9369261771131927161 / 20000000000000000000)

theorem positive12240 :
    Eplus aL (agent12240.root+dsL) scalar12240.worldRadius world12240.frame
      agent12240.frame tp12240 ≤ -ep12240 := by
  apply positive_check (eT := (57836124293337797153 / 50000000000000000000)) (y := (37161193041181955291 / 100000000000000000000)) (u := (145007014396659566981 / 100000000000000000000))
  · norm_num [world12240, agent12240, scalar12240, tp12240, tm12240, ep12240, em12240, dsL]
  · norm_num [world12240, agent12240, scalar12240, tp12240, tm12240, ep12240, em12240, dsL]
  · norm_num [world12240, agent12240, scalar12240, tp12240, tm12240, ep12240, em12240, dsL]
  · norm_num [world12240, agent12240, scalar12240, tp12240, tm12240, ep12240, em12240, dsL]
  · norm_num [world12240, agent12240, scalar12240, tp12240, tm12240, ep12240, em12240, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12240, agent12240, tp12240, tm12240, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12240, agent12240, scalar12240, tp12240, tm12240, ep12240, em12240, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12240, agent12240, tp12240, tm12240, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12240, agent12240, scalar12240, tp12240, tm12240, ep12240, em12240, dsL]

theorem negative12240 :
    Eminus aL (agent12240.root+dsL) scalar12240.worldRadius world12240.frame
      agent12240.frame tm12240 ≤ -em12240 := by
  apply negative_check (lo := (17043893307708634181 / 25000000000000000000)) (hi := (2727022929233381469 / 4000000000000000000))
    (y := (-((70850386916946047179 / 100000000000000000000)))) (u := (24619015601349023597 / 50000000000000000000))
  · norm_num [world12240, agent12240, scalar12240, tp12240, tm12240, ep12240, em12240, dsL]
  · norm_num [world12240, agent12240, scalar12240, tp12240, tm12240, ep12240, em12240, dsL]
  · norm_num [world12240, agent12240, scalar12240, tp12240, tm12240, ep12240, em12240, dsL]
  · norm_num [world12240, agent12240, scalar12240, tp12240, tm12240, ep12240, em12240, dsL]
  · norm_num [world12240, agent12240, scalar12240, tp12240, tm12240, ep12240, em12240, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12240, agent12240, tp12240, tm12240, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12240, agent12240, tp12240, tm12240, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12240, agent12240, scalar12240, tp12240, tm12240, ep12240, em12240, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12240, agent12240, tp12240, tm12240, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12240, agent12240, scalar12240, tp12240, tm12240, ep12240, em12240, dsL]

theorem tails12240 :
    exp (-((12240:ℝ)*ep12240)) ≤ scalar12240.upperTail ∧
    exp (-((12240:ℝ)*em12240)) ≤ scalar12240.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12240:ℝ)) (by norm_num [ep12240]) ?_)
      (show bp12240^8 ≤ scalar12240.upperTail by norm_num [bp12240, scalar12240])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12240, bp12240, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12240:ℝ)) (by norm_num [em12240]) ?_)
      (show bm12240^8 ≤ scalar12240.lowerTail by norm_num [bm12240, scalar12240])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12240, bm12240, Finset.sum_range_succ, Nat.factorial]

theorem guards12240 :
    agent12240.root+dsL+scalar12240.worldRadius < √(1/100/aL) ∧
    2*(agent12240.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12240, agent12240, scalar12240, tp12240, tm12240, ep12240, em12240, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12240, agent12240, scalar12240, tp12240, tm12240, ep12240, em12240, dsL]

noncomputable def master12240 : MasterCertificate 12240 world12240 agent12240 :=
  master scalar12240 dsL tp12240 tm12240 ep12240 em12240
    (by norm_num [dsL]) (by norm_num [tp12240]) (by norm_num [tm12240])
    (by norm_num [ep12240]) (by norm_num [em12240])
    positive12240 negative12240 tails12240.1 tails12240.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12240.1 guards12240.2

theorem preserves12240 : master12240.toScalarCertificate = scalar12240 := rfl

noncomputable def tp12241 : ℝ := (28785997 / 125000000)
noncomputable def tm12241 : ℝ := (-((3029694761 / 5000000000)))
noncomputable def ep12241 : ℝ := (50643063263684933 / 100000000000000000000)
noncomputable def em12241 : ℝ := (49564703636451727 / 100000000000000000000)
noncomputable def bp12241 : ℝ := (1842995412168207921 / 4000000000000000000)
noncomputable def bm12241 : ℝ := (936828784316673973 / 2000000000000000000)

theorem positive12241 :
    Eplus aL (agent12241.root+dsL) scalar12241.worldRadius world12241.frame
      agent12241.frame tp12241 ≤ -ep12241 := by
  apply positive_check (eT := (57836303184454348341 / 50000000000000000000)) (y := (37162046675106278317 / 100000000000000000000)) (u := (72504126115505192149 / 50000000000000000000))
  · norm_num [world12241, agent12241, scalar12241, tp12241, tm12241, ep12241, em12241, dsL]
  · norm_num [world12241, agent12241, scalar12241, tp12241, tm12241, ep12241, em12241, dsL]
  · norm_num [world12241, agent12241, scalar12241, tp12241, tm12241, ep12241, em12241, dsL]
  · norm_num [world12241, agent12241, scalar12241, tp12241, tm12241, ep12241, em12241, dsL]
  · norm_num [world12241, agent12241, scalar12241, tp12241, tm12241, ep12241, em12241, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12241, agent12241, tp12241, tm12241, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12241, agent12241, scalar12241, tp12241, tm12241, ep12241, em12241, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12241, agent12241, tp12241, tm12241, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12241, agent12241, scalar12241, tp12241, tm12241, ep12241, em12241, dsL]

theorem negative12241 :
    Eminus aL (agent12241.root+dsL) scalar12241.worldRadius world12241.frame
      agent12241.frame tm12241 ≤ -em12241 := by
  apply negative_check (lo := (8521899914340737159 / 12500000000000000000)) (hi := (68175199314725897273 / 100000000000000000000))
    (y := (-((2834018811546293759 / 4000000000000000000)))) (u := (49237990152125936939 / 100000000000000000000))
  · norm_num [world12241, agent12241, scalar12241, tp12241, tm12241, ep12241, em12241, dsL]
  · norm_num [world12241, agent12241, scalar12241, tp12241, tm12241, ep12241, em12241, dsL]
  · norm_num [world12241, agent12241, scalar12241, tp12241, tm12241, ep12241, em12241, dsL]
  · norm_num [world12241, agent12241, scalar12241, tp12241, tm12241, ep12241, em12241, dsL]
  · norm_num [world12241, agent12241, scalar12241, tp12241, tm12241, ep12241, em12241, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12241, agent12241, tp12241, tm12241, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12241, agent12241, tp12241, tm12241, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12241, agent12241, scalar12241, tp12241, tm12241, ep12241, em12241, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12241, agent12241, tp12241, tm12241, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12241, agent12241, scalar12241, tp12241, tm12241, ep12241, em12241, dsL]

theorem tails12241 :
    exp (-((12241:ℝ)*ep12241)) ≤ scalar12241.upperTail ∧
    exp (-((12241:ℝ)*em12241)) ≤ scalar12241.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12241:ℝ)) (by norm_num [ep12241]) ?_)
      (show bp12241^8 ≤ scalar12241.upperTail by norm_num [bp12241, scalar12241])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12241, bp12241, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12241:ℝ)) (by norm_num [em12241]) ?_)
      (show bm12241^8 ≤ scalar12241.lowerTail by norm_num [bm12241, scalar12241])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12241, bm12241, Finset.sum_range_succ, Nat.factorial]

theorem guards12241 :
    agent12241.root+dsL+scalar12241.worldRadius < √(1/100/aL) ∧
    2*(agent12241.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12241, agent12241, scalar12241, tp12241, tm12241, ep12241, em12241, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12241, agent12241, scalar12241, tp12241, tm12241, ep12241, em12241, dsL]

noncomputable def master12241 : MasterCertificate 12241 world12241 agent12241 :=
  master scalar12241 dsL tp12241 tm12241 ep12241 em12241
    (by norm_num [dsL]) (by norm_num [tp12241]) (by norm_num [tm12241])
    (by norm_num [ep12241]) (by norm_num [em12241])
    positive12241 negative12241 tails12241.1 tails12241.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12241.1 guards12241.2

theorem preserves12241 : master12241.toScalarCertificate = scalar12241 := rfl

noncomputable def tp12242 : ℝ := (2302982903 / 10000000000)
noncomputable def tm12242 : ℝ := (-((6059619223 / 10000000000)))
noncomputable def ep12242 : ℝ := (10129238953270801 / 20000000000000000000)
noncomputable def em12242 : ℝ := (49567446435541199 / 100000000000000000000)
noncomputable def bp12242 : ℝ := (23034880486164098723 / 50000000000000000000)
noncomputable def bm12242 : ℝ := (2341828567609186633 / 5000000000000000000)

theorem positive12242 :
    Eplus aL (agent12242.root+dsL) scalar12242.worldRadius world12242.frame
      agent12242.frame tp12242 ≤ -ep12242 := by
  apply positive_check (eT := (14459120384878241167 / 12500000000000000000)) (y := (18581449119915484923 / 50000000000000000000)) (u := (18126185884424002177 / 12500000000000000000))
  · norm_num [world12242, agent12242, scalar12242, tp12242, tm12242, ep12242, em12242, dsL]
  · norm_num [world12242, agent12242, scalar12242, tp12242, tm12242, ep12242, em12242, dsL]
  · norm_num [world12242, agent12242, scalar12242, tp12242, tm12242, ep12242, em12242, dsL]
  · norm_num [world12242, agent12242, scalar12242, tp12242, tm12242, ep12242, em12242, dsL]
  · norm_num [world12242, agent12242, scalar12242, tp12242, tm12242, ep12242, em12242, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12242, agent12242, tp12242, tm12242, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12242, agent12242, scalar12242, tp12242, tm12242, ep12242, em12242, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12242, agent12242, tp12242, tm12242, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12242, agent12242, scalar12242, tp12242, tm12242, ep12242, em12242, dsL]

theorem negative12242 :
    Eminus aL (agent12242.root+dsL) scalar12242.worldRadius world12242.frame
      agent12242.frame tm12242 ≤ -em12242 := by
  apply negative_check (lo := (13634965165345539779 / 20000000000000000000)) (hi := (4260926614170481181 / 6250000000000000000))
    (y := (-((14170110632034648561 / 20000000000000000000)))) (u := (49237949347874007309 / 100000000000000000000))
  · norm_num [world12242, agent12242, scalar12242, tp12242, tm12242, ep12242, em12242, dsL]
  · norm_num [world12242, agent12242, scalar12242, tp12242, tm12242, ep12242, em12242, dsL]
  · norm_num [world12242, agent12242, scalar12242, tp12242, tm12242, ep12242, em12242, dsL]
  · norm_num [world12242, agent12242, scalar12242, tp12242, tm12242, ep12242, em12242, dsL]
  · norm_num [world12242, agent12242, scalar12242, tp12242, tm12242, ep12242, em12242, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12242, agent12242, tp12242, tm12242, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12242, agent12242, tp12242, tm12242, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12242, agent12242, scalar12242, tp12242, tm12242, ep12242, em12242, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12242, agent12242, tp12242, tm12242, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12242, agent12242, scalar12242, tp12242, tm12242, ep12242, em12242, dsL]

theorem tails12242 :
    exp (-((12242:ℝ)*ep12242)) ≤ scalar12242.upperTail ∧
    exp (-((12242:ℝ)*em12242)) ≤ scalar12242.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12242:ℝ)) (by norm_num [ep12242]) ?_)
      (show bp12242^8 ≤ scalar12242.upperTail by norm_num [bp12242, scalar12242])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12242, bp12242, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12242:ℝ)) (by norm_num [em12242]) ?_)
      (show bm12242^8 ≤ scalar12242.lowerTail by norm_num [bm12242, scalar12242])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12242, bm12242, Finset.sum_range_succ, Nat.factorial]

theorem guards12242 :
    agent12242.root+dsL+scalar12242.worldRadius < √(1/100/aL) ∧
    2*(agent12242.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12242, agent12242, scalar12242, tp12242, tm12242, ep12242, em12242, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12242, agent12242, scalar12242, tp12242, tm12242, ep12242, em12242, dsL]

noncomputable def master12242 : MasterCertificate 12242 world12242 agent12242 :=
  master scalar12242 dsL tp12242 tm12242 ep12242 em12242
    (by norm_num [dsL]) (by norm_num [tp12242]) (by norm_num [tm12242])
    (by norm_num [ep12242]) (by norm_num [em12242])
    positive12242 negative12242 tails12242.1 tails12242.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12242.1 guards12242.2

theorem preserves12242 : master12242.toScalarCertificate = scalar12242 := rfl

noncomputable def tp12243 : ℝ := (575771517 / 2500000000)
noncomputable def tm12243 : ℝ := (-((3029924367 / 5000000000)))
noncomputable def ep12243 : ℝ := (50649325427055523 / 100000000000000000000)
noncomputable def em12243 : ℝ := (49570188462864229 / 100000000000000000000)
noncomputable def bp12243 : ℝ := (2879039840205776657 / 6250000000000000000)
noncomputable def bm12243 : ℝ := (5853963028301667187 / 12500000000000000000)

theorem positive12243 :
    Eplus aL (agent12243.root+dsL) scalar12243.worldRadius world12243.frame
      agent12243.frame tp12243 ≤ -ep12243 := by
  apply positive_check (eT := (115673319982219481493 / 100000000000000000000)) (y := (18581875220775661677 / 50000000000000000000)) (u := (14501072285400120551 / 10000000000000000000))
  · norm_num [world12243, agent12243, scalar12243, tp12243, tm12243, ep12243, em12243, dsL]
  · norm_num [world12243, agent12243, scalar12243, tp12243, tm12243, ep12243, em12243, dsL]
  · norm_num [world12243, agent12243, scalar12243, tp12243, tm12243, ep12243, em12243, dsL]
  · norm_num [world12243, agent12243, scalar12243, tp12243, tm12243, ep12243, em12243, dsL]
  · norm_num [world12243, agent12243, scalar12243, tp12243, tm12243, ep12243, em12243, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12243, agent12243, tp12243, tm12243, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12243, agent12243, scalar12243, tp12243, tm12243, ep12243, em12243, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12243, agent12243, tp12243, tm12243, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12243, agent12243, scalar12243, tp12243, tm12243, ep12243, em12243, dsL]

theorem negative12243 :
    Eminus aL (agent12243.root+dsL) scalar12243.worldRadius world12243.frame
      agent12243.frame tm12243 ≤ -em12243 := by
  apply negative_check (lo := (68174453102963165557 / 100000000000000000000)) (hi := (34087226551481582779 / 50000000000000000000))
    (y := (-((70850634878696626203 / 100000000000000000000)))) (u := (3077369319460331019 / 6250000000000000000))
  · norm_num [world12243, agent12243, scalar12243, tp12243, tm12243, ep12243, em12243, dsL]
  · norm_num [world12243, agent12243, scalar12243, tp12243, tm12243, ep12243, em12243, dsL]
  · norm_num [world12243, agent12243, scalar12243, tp12243, tm12243, ep12243, em12243, dsL]
  · norm_num [world12243, agent12243, scalar12243, tp12243, tm12243, ep12243, em12243, dsL]
  · norm_num [world12243, agent12243, scalar12243, tp12243, tm12243, ep12243, em12243, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12243, agent12243, tp12243, tm12243, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12243, agent12243, tp12243, tm12243, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12243, agent12243, scalar12243, tp12243, tm12243, ep12243, em12243, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12243, agent12243, tp12243, tm12243, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12243, agent12243, scalar12243, tp12243, tm12243, ep12243, em12243, dsL]

theorem tails12243 :
    exp (-((12243:ℝ)*ep12243)) ≤ scalar12243.upperTail ∧
    exp (-((12243:ℝ)*em12243)) ≤ scalar12243.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12243:ℝ)) (by norm_num [ep12243]) ?_)
      (show bp12243^8 ≤ scalar12243.upperTail by norm_num [bp12243, scalar12243])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12243, bp12243, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12243:ℝ)) (by norm_num [em12243]) ?_)
      (show bm12243^8 ≤ scalar12243.lowerTail by norm_num [bm12243, scalar12243])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12243, bm12243, Finset.sum_range_succ, Nat.factorial]

theorem guards12243 :
    agent12243.root+dsL+scalar12243.worldRadius < √(1/100/aL) ∧
    2*(agent12243.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12243, agent12243, scalar12243, tp12243, tm12243, ep12243, em12243, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12243, agent12243, scalar12243, tp12243, tm12243, ep12243, em12243, dsL]

noncomputable def master12243 : MasterCertificate 12243 world12243 agent12243 :=
  master scalar12243 dsL tp12243 tm12243 ep12243 em12243
    (by norm_num [dsL]) (by norm_num [tp12243]) (by norm_num [tm12243])
    (by norm_num [ep12243]) (by norm_num [em12243])
    positive12243 negative12243 tails12243.1 tails12243.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12243.1 guards12243.2

theorem preserves12243 : master12243.toScalarCertificate = scalar12243 := rfl

noncomputable def tp12244 : ℝ := (1151594571 / 5000000000)
noncomputable def tm12244 : ℝ := (-((1515019561 / 2500000000)))
noncomputable def ep12244 : ℝ := (50652454029072947 / 100000000000000000000)
noncomputable def em12244 : ℝ := (4957292855744933 / 10000000000000000000)
noncomputable def bp12244 : ℝ := (46059515574815442797 / 100000000000000000000)
noncomputable def bm12244 : ℝ := (23413419335291854079 / 50000000000000000000)

theorem positive12244 :
    Eplus aL (agent12244.root+dsL) scalar12244.worldRadius world12244.frame
      agent12244.frame tp12244 ≤ -ep12244 := by
  apply positive_check (eT := (57836838126066128231 / 50000000000000000000)) (y := (37164601716115490279 / 100000000000000000000)) (u := (18126494662331803179 / 12500000000000000000))
  · norm_num [world12244, agent12244, scalar12244, tp12244, tm12244, ep12244, em12244, dsL]
  · norm_num [world12244, agent12244, scalar12244, tp12244, tm12244, ep12244, em12244, dsL]
  · norm_num [world12244, agent12244, scalar12244, tp12244, tm12244, ep12244, em12244, dsL]
  · norm_num [world12244, agent12244, scalar12244, tp12244, tm12244, ep12244, em12244, dsL]
  · norm_num [world12244, agent12244, scalar12244, tp12244, tm12244, ep12244, em12244, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12244, agent12244, tp12244, tm12244, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12244, agent12244, scalar12244, tp12244, tm12244, ep12244, em12244, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12244, agent12244, tp12244, tm12244, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12244, agent12244, scalar12244, tp12244, tm12244, ep12244, em12244, dsL]

theorem negative12244 :
    Eminus aL (agent12244.root+dsL) scalar12244.worldRadius world12244.frame
      agent12244.frame tm12244 ≤ -em12244 := by
  apply negative_check (lo := (8521760041104283009 / 12500000000000000000)) (hi := (68174080328834264073 / 100000000000000000000))
    (y := (-((1417014351484106543 / 2000000000000000000)))) (u := (24618934196921359367 / 50000000000000000000))
  · norm_num [world12244, agent12244, scalar12244, tp12244, tm12244, ep12244, em12244, dsL]
  · norm_num [world12244, agent12244, scalar12244, tp12244, tm12244, ep12244, em12244, dsL]
  · norm_num [world12244, agent12244, scalar12244, tp12244, tm12244, ep12244, em12244, dsL]
  · norm_num [world12244, agent12244, scalar12244, tp12244, tm12244, ep12244, em12244, dsL]
  · norm_num [world12244, agent12244, scalar12244, tp12244, tm12244, ep12244, em12244, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12244, agent12244, tp12244, tm12244, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12244, agent12244, tp12244, tm12244, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12244, agent12244, scalar12244, tp12244, tm12244, ep12244, em12244, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12244, agent12244, tp12244, tm12244, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12244, agent12244, scalar12244, tp12244, tm12244, ep12244, em12244, dsL]

theorem tails12244 :
    exp (-((12244:ℝ)*ep12244)) ≤ scalar12244.upperTail ∧
    exp (-((12244:ℝ)*em12244)) ≤ scalar12244.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12244:ℝ)) (by norm_num [ep12244]) ?_)
      (show bp12244^8 ≤ scalar12244.upperTail by norm_num [bp12244, scalar12244])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12244, bp12244, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12244:ℝ)) (by norm_num [em12244]) ?_)
      (show bm12244^8 ≤ scalar12244.lowerTail by norm_num [bm12244, scalar12244])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12244, bm12244, Finset.sum_range_succ, Nat.factorial]

theorem guards12244 :
    agent12244.root+dsL+scalar12244.worldRadius < √(1/100/aL) ∧
    2*(agent12244.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12244, agent12244, scalar12244, tp12244, tm12244, ep12244, em12244, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12244, agent12244, scalar12244, tp12244, tm12244, ep12244, em12244, dsL]

noncomputable def master12244 : MasterCertificate 12244 world12244 agent12244 :=
  master scalar12244 dsL tp12244 tm12244 ep12244 em12244
    (by norm_num [dsL]) (by norm_num [tp12244]) (by norm_num [tm12244])
    (by norm_num [ep12244]) (by norm_num [em12244])
    positive12244 negative12244 tails12244.1 tails12244.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12244.1 guards12244.2

theorem preserves12244 : master12244.toScalarCertificate = scalar12244 := rfl

noncomputable def tp12245 : ℝ := (1151646127 / 5000000000)
noncomputable def tm12245 : ℝ := (-((151507693 / 250000000)))
noncomputable def ep12245 : ℝ := (2532779042586853 / 5000000000000000000)
noncomputable def em12245 : ℝ := (24787833506023809 / 50000000000000000000)
noncomputable def bp12245 : ℝ := (46054395169919700147 / 100000000000000000000)
noncomputable def bm12245 : ℝ := (46821974474844353303 / 100000000000000000000)

theorem positive12245 :
    Eplus aL (agent12245.root+dsL) scalar12245.worldRadius world12245.frame
      agent12245.frame tp12245 ≤ -ep12245 := by
  apply positive_check (eT := (11567403283212736337 / 10000000000000000000)) (y := (3716545400063482599 / 10000000000000000000)) (u := (145013193218384436359 / 100000000000000000000))
  · norm_num [world12245, agent12245, scalar12245, tp12245, tm12245, ep12245, em12245, dsL]
  · norm_num [world12245, agent12245, scalar12245, tp12245, tm12245, ep12245, em12245, dsL]
  · norm_num [world12245, agent12245, scalar12245, tp12245, tm12245, ep12245, em12245, dsL]
  · norm_num [world12245, agent12245, scalar12245, tp12245, tm12245, ep12245, em12245, dsL]
  · norm_num [world12245, agent12245, scalar12245, tp12245, tm12245, ep12245, em12245, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12245, agent12245, tp12245, tm12245, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12245, agent12245, scalar12245, tp12245, tm12245, ep12245, em12245, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12245, agent12245, tp12245, tm12245, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12245, agent12245, scalar12245, tp12245, tm12245, ep12245, em12245, dsL]

theorem negative12245 :
    Eminus aL (agent12245.root+dsL) scalar12245.worldRadius world12245.frame
      agent12245.frame tm12245 ≤ -em12245 := by
  apply negative_check (lo := (34086853823274954401 / 50000000000000000000)) (hi := (68173707646549908803 / 100000000000000000000))
    (y := (-((4428175022414112391 / 6250000000000000000)))) (u := (49237827632575588557 / 100000000000000000000))
  · norm_num [world12245, agent12245, scalar12245, tp12245, tm12245, ep12245, em12245, dsL]
  · norm_num [world12245, agent12245, scalar12245, tp12245, tm12245, ep12245, em12245, dsL]
  · norm_num [world12245, agent12245, scalar12245, tp12245, tm12245, ep12245, em12245, dsL]
  · norm_num [world12245, agent12245, scalar12245, tp12245, tm12245, ep12245, em12245, dsL]
  · norm_num [world12245, agent12245, scalar12245, tp12245, tm12245, ep12245, em12245, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12245, agent12245, tp12245, tm12245, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12245, agent12245, tp12245, tm12245, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12245, agent12245, scalar12245, tp12245, tm12245, ep12245, em12245, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12245, agent12245, tp12245, tm12245, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12245, agent12245, scalar12245, tp12245, tm12245, ep12245, em12245, dsL]

theorem tails12245 :
    exp (-((12245:ℝ)*ep12245)) ≤ scalar12245.upperTail ∧
    exp (-((12245:ℝ)*em12245)) ≤ scalar12245.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12245:ℝ)) (by norm_num [ep12245]) ?_)
      (show bp12245^8 ≤ scalar12245.upperTail by norm_num [bp12245, scalar12245])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12245, bp12245, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12245:ℝ)) (by norm_num [em12245]) ?_)
      (show bm12245^8 ≤ scalar12245.lowerTail by norm_num [bm12245, scalar12245])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12245, bm12245, Finset.sum_range_succ, Nat.factorial]

theorem guards12245 :
    agent12245.root+dsL+scalar12245.worldRadius < √(1/100/aL) ∧
    2*(agent12245.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12245, agent12245, scalar12245, tp12245, tm12245, ep12245, em12245, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12245, agent12245, scalar12245, tp12245, tm12245, ep12245, em12245, dsL]

noncomputable def master12245 : MasterCertificate 12245 world12245 agent12245 :=
  master scalar12245 dsL tp12245 tm12245 ep12245 em12245
    (by norm_num [dsL]) (by norm_num [tp12245]) (by norm_num [tm12245])
    (by norm_num [ep12245]) (by norm_num [em12245])
    positive12245 negative12245 tails12245.1 tails12245.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12245.1 guards12245.2

theorem preserves12245 : master12245.toScalarCertificate = scalar12245 := rfl

noncomputable def tp12246 : ℝ := (287924407 / 1250000000)
noncomputable def tm12246 : ℝ := (-((3030268467 / 5000000000)))
noncomputable def ep12246 : ℝ := (50658706697278219 / 100000000000000000000)
noncomputable def em12246 : ℝ := (6197300569063459 / 12500000000000000000)
noncomputable def bp12246 : ℝ := (46049275663059349001 / 100000000000000000000)
noncomputable def bm12246 : ℝ := (23408555559491425301 / 50000000000000000000)

theorem positive12246 :
    Eplus aL (agent12246.root+dsL) scalar12246.worldRadius world12246.frame
      agent12246.frame tp12246 ≤ -ep12246 := by
  apply positive_check (eT := (115674388639942041347 / 100000000000000000000)) (y := (4645788097841155063 / 12500000000000000000)) (u := (145014426969915138211 / 100000000000000000000))
  · norm_num [world12246, agent12246, scalar12246, tp12246, tm12246, ep12246, em12246, dsL]
  · norm_num [world12246, agent12246, scalar12246, tp12246, tm12246, ep12246, em12246, dsL]
  · norm_num [world12246, agent12246, scalar12246, tp12246, tm12246, ep12246, em12246, dsL]
  · norm_num [world12246, agent12246, scalar12246, tp12246, tm12246, ep12246, em12246, dsL]
  · norm_num [world12246, agent12246, scalar12246, tp12246, tm12246, ep12246, em12246, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12246, agent12246, tp12246, tm12246, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12246, agent12246, scalar12246, tp12246, tm12246, ep12246, em12246, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12246, agent12246, tp12246, tm12246, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12246, agent12246, scalar12246, tp12246, tm12246, ep12246, em12246, dsL]

theorem negative12246 :
    Eminus aL (agent12246.root+dsL) scalar12246.worldRadius world12246.frame
      agent12246.frame tm12246 ≤ -em12246 := by
  apply negative_check (lo := (68173336038711005691 / 100000000000000000000)) (hi := (17043334009677751423 / 25000000000000000000))
    (y := (-((70850881584177459617 / 100000000000000000000)))) (u := (24618893819447355237 / 50000000000000000000))
  · norm_num [world12246, agent12246, scalar12246, tp12246, tm12246, ep12246, em12246, dsL]
  · norm_num [world12246, agent12246, scalar12246, tp12246, tm12246, ep12246, em12246, dsL]
  · norm_num [world12246, agent12246, scalar12246, tp12246, tm12246, ep12246, em12246, dsL]
  · norm_num [world12246, agent12246, scalar12246, tp12246, tm12246, ep12246, em12246, dsL]
  · norm_num [world12246, agent12246, scalar12246, tp12246, tm12246, ep12246, em12246, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12246, agent12246, tp12246, tm12246, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12246, agent12246, tp12246, tm12246, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12246, agent12246, scalar12246, tp12246, tm12246, ep12246, em12246, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12246, agent12246, tp12246, tm12246, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12246, agent12246, scalar12246, tp12246, tm12246, ep12246, em12246, dsL]

theorem tails12246 :
    exp (-((12246:ℝ)*ep12246)) ≤ scalar12246.upperTail ∧
    exp (-((12246:ℝ)*em12246)) ≤ scalar12246.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12246:ℝ)) (by norm_num [ep12246]) ?_)
      (show bp12246^8 ≤ scalar12246.upperTail by norm_num [bp12246, scalar12246])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12246, bp12246, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12246:ℝ)) (by norm_num [em12246]) ?_)
      (show bm12246^8 ≤ scalar12246.lowerTail by norm_num [bm12246, scalar12246])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12246, bm12246, Finset.sum_range_succ, Nat.factorial]

theorem guards12246 :
    agent12246.root+dsL+scalar12246.worldRadius < √(1/100/aL) ∧
    2*(agent12246.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12246, agent12246, scalar12246, tp12246, tm12246, ep12246, em12246, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12246, agent12246, scalar12246, tp12246, tm12246, ep12246, em12246, dsL]

noncomputable def master12246 : MasterCertificate 12246 world12246 agent12246 :=
  master scalar12246 dsL tp12246 tm12246 ep12246 em12246
    (by norm_num [dsL]) (by norm_num [tp12246]) (by norm_num [tm12246])
    (by norm_num [ep12246]) (by norm_num [em12246])
    positive12246 negative12246 tails12246.1 tails12246.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12246.1 guards12246.2

theorem preserves12246 : master12246.toScalarCertificate = scalar12246 := rfl

noncomputable def tp12247 : ℝ := (2303498209 / 10000000000)
noncomputable def tm12247 : ℝ := (-((606076609 / 1000000000)))
noncomputable def ep12247 : ℝ := (25330915613748563 / 50000000000000000000)
noncomputable def em12247 : ℝ := (49581140883232437 / 100000000000000000000)
noncomputable def bp12247 : ℝ := (46044157292619583087 / 100000000000000000000)
noncomputable def bm12247 : ℝ := (46812248814838712797 / 100000000000000000000)

theorem positive12247 :
    Eplus aL (agent12247.root+dsL) scalar12247.worldRadius world12247.frame
      agent12247.frame tp12247 ≤ -ep12247 := by
  apply positive_check (eT := (57837372060839710573 / 50000000000000000000)) (y := (7433431003612079207 / 20000000000000000000)) (u := (7250782996952503567 / 5000000000000000000))
  · norm_num [world12247, agent12247, scalar12247, tp12247, tm12247, ep12247, em12247, dsL]
  · norm_num [world12247, agent12247, scalar12247, tp12247, tm12247, ep12247, em12247, dsL]
  · norm_num [world12247, agent12247, scalar12247, tp12247, tm12247, ep12247, em12247, dsL]
  · norm_num [world12247, agent12247, scalar12247, tp12247, tm12247, ep12247, em12247, dsL]
  · norm_num [world12247, agent12247, scalar12247, tp12247, tm12247, ep12247, em12247, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12247, agent12247, tp12247, tm12247, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12247, agent12247, scalar12247, tp12247, tm12247, ep12247, em12247, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12247, agent12247, tp12247, tm12247, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12247, agent12247, scalar12247, tp12247, tm12247, ep12247, em12247, dsL]

theorem negative12247 :
    Eminus aL (agent12247.root+dsL) scalar12247.worldRadius world12247.frame
      agent12247.frame tm12247 ≤ -em12247 := by
  apply negative_check (lo := (68172964626080491369 / 100000000000000000000)) (hi := (6817296462608049137 / 10000000000000000000))
    (y := (-((35425481397483999627 / 50000000000000000000)))) (u := (4923774765251436133 / 10000000000000000000))
  · norm_num [world12247, agent12247, scalar12247, tp12247, tm12247, ep12247, em12247, dsL]
  · norm_num [world12247, agent12247, scalar12247, tp12247, tm12247, ep12247, em12247, dsL]
  · norm_num [world12247, agent12247, scalar12247, tp12247, tm12247, ep12247, em12247, dsL]
  · norm_num [world12247, agent12247, scalar12247, tp12247, tm12247, ep12247, em12247, dsL]
  · norm_num [world12247, agent12247, scalar12247, tp12247, tm12247, ep12247, em12247, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12247, agent12247, tp12247, tm12247, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12247, agent12247, tp12247, tm12247, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12247, agent12247, scalar12247, tp12247, tm12247, ep12247, em12247, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12247, agent12247, tp12247, tm12247, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12247, agent12247, scalar12247, tp12247, tm12247, ep12247, em12247, dsL]

theorem tails12247 :
    exp (-((12247:ℝ)*ep12247)) ≤ scalar12247.upperTail ∧
    exp (-((12247:ℝ)*em12247)) ≤ scalar12247.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12247:ℝ)) (by norm_num [ep12247]) ?_)
      (show bp12247^8 ≤ scalar12247.upperTail by norm_num [bp12247, scalar12247])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12247, bp12247, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12247:ℝ)) (by norm_num [em12247]) ?_)
      (show bm12247^8 ≤ scalar12247.lowerTail by norm_num [bm12247, scalar12247])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12247, bm12247, Finset.sum_range_succ, Nat.factorial]

theorem guards12247 :
    agent12247.root+dsL+scalar12247.worldRadius < √(1/100/aL) ∧
    2*(agent12247.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12247, agent12247, scalar12247, tp12247, tm12247, ep12247, em12247, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12247, agent12247, scalar12247, tp12247, tm12247, ep12247, em12247, dsL]

noncomputable def master12247 : MasterCertificate 12247 world12247 agent12247 :=
  master scalar12247 dsL tp12247 tm12247 ep12247 em12247
    (by norm_num [dsL]) (by norm_num [tp12247]) (by norm_num [tm12247])
    (by norm_num [ep12247]) (by norm_num [em12247])
    positive12247 negative12247 tails12247.1 tails12247.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12247.1 guards12247.2

theorem preserves12247 : master12247.toScalarCertificate = scalar12247 := rfl

noncomputable def tp12248 : ℝ := (57590029 / 250000000)
noncomputable def tm12248 : ℝ := (-((6060995193 / 10000000000)))
noncomputable def ep12248 : ℝ := (25332477088408769 / 50000000000000000000)
noncomputable def em12248 : ℝ := (49583875723319851 / 100000000000000000000)
noncomputable def bp12248 : ℝ := (23019520122884256467 / 50000000000000000000)
noncomputable def bm12248 : ℝ := (23403693881850931921 / 50000000000000000000)

theorem positive12248 :
    Eplus aL (agent12248.root+dsL) scalar12248.worldRadius world12248.frame
      agent12248.frame tp12248 ≤ -ep12248 := by
  apply positive_check (eT := (23135019924196797161 / 20000000000000000000)) (y := (37168005820990098491 / 100000000000000000000)) (u := (72508446870890983791 / 50000000000000000000))
  · norm_num [world12248, agent12248, scalar12248, tp12248, tm12248, ep12248, em12248, dsL]
  · norm_num [world12248, agent12248, scalar12248, tp12248, tm12248, ep12248, em12248, dsL]
  · norm_num [world12248, agent12248, scalar12248, tp12248, tm12248, ep12248, em12248, dsL]
  · norm_num [world12248, agent12248, scalar12248, tp12248, tm12248, ep12248, em12248, dsL]
  · norm_num [world12248, agent12248, scalar12248, tp12248, tm12248, ep12248, em12248, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12248, agent12248, tp12248, tm12248, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12248, agent12248, scalar12248, tp12248, tm12248, ep12248, em12248, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12248, agent12248, tp12248, tm12248, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12248, agent12248, scalar12248, tp12248, tm12248, ep12248, em12248, dsL]

theorem negative12248 :
    Eminus aL (agent12248.root+dsL) scalar12248.worldRadius world12248.frame
      agent12248.frame tm12248 ≤ -em12248 := by
  apply negative_check (lo := (34086296693580897571 / 50000000000000000000)) (hi := (68172593387161795143 / 100000000000000000000))
    (y := (-((17712761152467693151 / 25000000000000000000)))) (u := (9847541473743094143 / 20000000000000000000))
  · norm_num [world12248, agent12248, scalar12248, tp12248, tm12248, ep12248, em12248, dsL]
  · norm_num [world12248, agent12248, scalar12248, tp12248, tm12248, ep12248, em12248, dsL]
  · norm_num [world12248, agent12248, scalar12248, tp12248, tm12248, ep12248, em12248, dsL]
  · norm_num [world12248, agent12248, scalar12248, tp12248, tm12248, ep12248, em12248, dsL]
  · norm_num [world12248, agent12248, scalar12248, tp12248, tm12248, ep12248, em12248, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12248, agent12248, tp12248, tm12248, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12248, agent12248, tp12248, tm12248, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12248, agent12248, scalar12248, tp12248, tm12248, ep12248, em12248, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12248, agent12248, tp12248, tm12248, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12248, agent12248, scalar12248, tp12248, tm12248, ep12248, em12248, dsL]

theorem tails12248 :
    exp (-((12248:ℝ)*ep12248)) ≤ scalar12248.upperTail ∧
    exp (-((12248:ℝ)*em12248)) ≤ scalar12248.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12248:ℝ)) (by norm_num [ep12248]) ?_)
      (show bp12248^8 ≤ scalar12248.upperTail by norm_num [bp12248, scalar12248])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12248, bp12248, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12248:ℝ)) (by norm_num [em12248]) ?_)
      (show bm12248^8 ≤ scalar12248.lowerTail by norm_num [bm12248, scalar12248])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12248, bm12248, Finset.sum_range_succ, Nat.factorial]

theorem guards12248 :
    agent12248.root+dsL+scalar12248.worldRadius < √(1/100/aL) ∧
    2*(agent12248.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12248, agent12248, scalar12248, tp12248, tm12248, ep12248, em12248, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12248, agent12248, scalar12248, tp12248, tm12248, ep12248, em12248, dsL]

noncomputable def master12248 : MasterCertificate 12248 world12248 agent12248 :=
  master scalar12248 dsL tp12248 tm12248 ep12248 em12248
    (by norm_num [dsL]) (by norm_num [tp12248]) (by norm_num [tm12248])
    (by norm_num [ep12248]) (by norm_num [em12248])
    positive12248 negative12248 tails12248.1 tails12248.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12248.1 guards12248.2

theorem preserves12248 : master12248.toScalarCertificate = scalar12248 := rfl

noncomputable def tp12249 : ℝ := (1151852039 / 5000000000)
noncomputable def tm12249 : ℝ := (-((6061224197 / 10000000000)))
noncomputable def ep12249 : ℝ := (50668075810736927 / 100000000000000000000)
noncomputable def em12249 : ℝ := (4958660935367827 / 10000000000000000000)
noncomputable def bp12249 : ℝ := (46033924335331777477 / 100000000000000000000)
noncomputable def bm12249 : ℝ := (23401263882124030733 / 50000000000000000000)

theorem positive12249 :
    Eplus aL (agent12249.root+dsL) scalar12249.worldRadius world12249.frame
      agent12249.frame tp12249 ≤ -ep12249 := by
  apply positive_check (eT := (115675454911196861259 / 100000000000000000000)) (y := (4646107044291472751 / 12500000000000000000)) (u := (145018127164059641617 / 100000000000000000000))
  · norm_num [world12249, agent12249, scalar12249, tp12249, tm12249, ep12249, em12249, dsL]
  · norm_num [world12249, agent12249, scalar12249, tp12249, tm12249, ep12249, em12249, dsL]
  · norm_num [world12249, agent12249, scalar12249, tp12249, tm12249, ep12249, em12249, dsL]
  · norm_num [world12249, agent12249, scalar12249, tp12249, tm12249, ep12249, em12249, dsL]
  · norm_num [world12249, agent12249, scalar12249, tp12249, tm12249, ep12249, em12249, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12249, agent12249, tp12249, tm12249, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12249, agent12249, scalar12249, tp12249, tm12249, ep12249, em12249, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12249, agent12249, tp12249, tm12249, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12249, agent12249, scalar12249, tp12249, tm12249, ep12249, em12249, dsL]

theorem negative12249 :
    Eminus aL (agent12249.root+dsL) scalar12249.worldRadius world12249.frame
      agent12249.frame tm12249 ≤ -em12249 := by
  apply negative_check (lo := (68172222520147431183 / 100000000000000000000)) (hi := (4260763907509214449 / 6250000000000000000))
    (y := (-((2214097688006445217 / 3125000000000000000)))) (u := (24618833643059272577 / 50000000000000000000))
  · norm_num [world12249, agent12249, scalar12249, tp12249, tm12249, ep12249, em12249, dsL]
  · norm_num [world12249, agent12249, scalar12249, tp12249, tm12249, ep12249, em12249, dsL]
  · norm_num [world12249, agent12249, scalar12249, tp12249, tm12249, ep12249, em12249, dsL]
  · norm_num [world12249, agent12249, scalar12249, tp12249, tm12249, ep12249, em12249, dsL]
  · norm_num [world12249, agent12249, scalar12249, tp12249, tm12249, ep12249, em12249, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12249, agent12249, tp12249, tm12249, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12249, agent12249, tp12249, tm12249, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12249, agent12249, scalar12249, tp12249, tm12249, ep12249, em12249, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12249, agent12249, tp12249, tm12249, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12249, agent12249, scalar12249, tp12249, tm12249, ep12249, em12249, dsL]

theorem tails12249 :
    exp (-((12249:ℝ)*ep12249)) ≤ scalar12249.upperTail ∧
    exp (-((12249:ℝ)*em12249)) ≤ scalar12249.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12249:ℝ)) (by norm_num [ep12249]) ?_)
      (show bp12249^8 ≤ scalar12249.upperTail by norm_num [bp12249, scalar12249])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12249, bp12249, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12249:ℝ)) (by norm_num [em12249]) ?_)
      (show bm12249^8 ≤ scalar12249.lowerTail by norm_num [bm12249, scalar12249])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12249, bm12249, Finset.sum_range_succ, Nat.factorial]

theorem guards12249 :
    agent12249.root+dsL+scalar12249.worldRadius < √(1/100/aL) ∧
    2*(agent12249.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12249, agent12249, scalar12249, tp12249, tm12249, ep12249, em12249, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12249, agent12249, scalar12249, tp12249, tm12249, ep12249, em12249, dsL]

noncomputable def master12249 : MasterCertificate 12249 world12249 agent12249 :=
  master scalar12249 dsL tp12249 tm12249 ep12249 em12249
    (by norm_num [dsL]) (by norm_num [tp12249]) (by norm_num [tm12249])
    (by norm_num [ep12249]) (by norm_num [em12249])
    positive12249 negative12249 tails12249.1 tails12249.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    guards12249.1 guards12249.2

theorem preserves12249 : master12249.toScalarCertificate = scalar12249 := rfl

end BstLean.Part261
