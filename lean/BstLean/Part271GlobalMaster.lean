import BstLean.Part261Checker

/-! One endpoint master on the whole requested dimension interval.
The World allowances are outward maxima of the R0 records. This module alone
does not construct the World, frame, or root supply. -/
namespace BstLean.Part271.GlobalMaster
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261

noncomputable def world : WorldParameters where
  hiddenCharge := (575319735108837 / 500000000000000000)
  frame := (309325988428479383 / 500000000000000000)
  moment := (8485534063 / 1000000000000000000)
  productLo := 2
  productHi := 21/10
  noiseLo := 46/100
  noiseHi := 54/100

noncomputable def agent : AgentParameters :=
  { BstLean.Part192.agentLedgerParameters with
    charge := (3 / 2000)
    frame := (728206725421151407 / 500000000000000000)
    root := (3437069076712937 / 500000000000000000) }

noncomputable def scalar (n : ℕ) (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    ScalarCertificate n world agent where
  dimensionLo := 13225
  dimensionHi := 16199
  dimension_mem := ⟨ha,hb⟩
  noiseLo := 46/100
  noiseHi := 54/100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (13865253 / 5000000000)
  frameLo := (309325988428479383 / 500000000000000000)
  frameHi := (728206725421151407 / 500000000000000000)
  noise_order := by norm_num
  overlap_order := by norm_num
  radius_order := by norm_num
  frame_order := by norm_num
  worldFrame_pos := by norm_num [world]
  agentFrame_pos := by norm_num [agent]
  worldRadius := (13865253 / 5000000000)
  worldRadius_pos := by norm_num
  agentRoot_nonneg := by norm_num [agent]
  retainedCharge := (3 / 2000)
  samplingCharge := (1 / 1000000000000)
  upperTail := (53201544691 / 100000000000000)
  lowerTail := (721825860371 / 1000000000000000)
  retainedCharge_nonneg := by norm_num
  samplingCharge_nonneg := by norm_num
  upperTail_nonneg := by norm_num
  lowerTail_nonneg := by norm_num
  totalBudget := (5007958559 / 1000000000000)
  ledger := by norm_num [world]
  budget := by norm_num

noncomputable def tp : ℝ := (2458550891 / 10000000000)
noncomputable def tm : ℝ := (-1265653671 / 2000000000)
noncomputable def ep : ℝ := (57004446378077929 / 100000000000000000000)
noncomputable def em : ℝ := (13674341472183769 / 25000000000000000000)
noncomputable def bp : ℝ := (38970908496761142243 / 100000000000000000000)
noncomputable def bm : ℝ := (8097184783760543661 / 20000000000000000000)

theorem positive :
    Eplus aL (agent.root+dsL) (13865253 / 5000000000) world.frame agent.frame tp ≤ -ep := by
  apply positive_check (eT := (58213759383529331453 / 50000000000000000000)) (y := (501650211754374337 / 1250000000000000000)) (u := (74689772977301861261 / 50000000000000000000))
  · norm_num [agent,dsL]
  · norm_num
  · norm_num [world]
  · norm_num [agent]
  · norm_num [tp]
  · apply exp_le_taylor (b := 1) 24 <;>
      norm_num [world,tp,Finset.sum_range_succ,Nat.factorial]
  · norm_num [world,agent,dsL]
  · apply exp_le_taylor (b := 1) 24 <;>
      norm_num [Finset.sum_range_succ,Nat.factorial]
  · norm_num [world,agent,dsL,tp,ep]

theorem negative :
    Eminus aL (agent.root+dsL) (13865253 / 5000000000) world.frame agent.frame tm ≤ -em := by
  apply negative_check (lo := (8450529241331808829 / 12500000000000000000)) (hi := (67604233930654470633 / 100000000000000000000))
    (y := (-14545087870690262893 / 20000000000000000000)) (u := (24161697029658760801 / 50000000000000000000))
  · norm_num
  · norm_num [world]
  · norm_num [agent]
  · norm_num [tm]
  · norm_num [agent,dsL]
  · apply le_exp_taylor (b := 1) 24 <;>
      norm_num [world,tm,Finset.sum_range_succ,Nat.factorial]
  · apply exp_le_taylor (b := 1) 24 <;>
      norm_num [world,tm,Finset.sum_range_succ,Nat.factorial]
  · norm_num
  · norm_num [world,agent,dsL]
  · apply exp_le_taylor (b := 1) 24 <;>
      norm_num [Finset.sum_range_succ,Nat.factorial]
  · norm_num
  · norm_num [world,agent,dsL,tm,em]

theorem tails {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    exp (-((n:ℝ)*ep)) ≤ (scalar n ha hb).upperTail ∧
    exp (-((n:ℝ)*em)) ≤ (scalar n ha hb).lowerTail := by
  have hn : (13225:ℝ) ≤ n := by exact_mod_cast ha
  constructor
  · apply le_trans (tail8 hn (by norm_num [ep]) ?_)
      (show bp^8 ≤ (scalar n ha hb).upperTail by norm_num [bp,scalar])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep,bp,Finset.sum_range_succ,Nat.factorial]
  · apply le_trans (tail8 hn (by norm_num [em]) ?_)
      (show bm^8 ≤ (scalar n ha hb).lowerTail by norm_num [bm,scalar])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em,bm,Finset.sum_range_succ,Nat.factorial]

theorem guards : agent.root+dsL+(13865253 / 5000000000) < √(1/100/aL) ∧
    2*(agent.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [agent,dsL]
  · apply le_trans _ x0_lo
    norm_num [agent,dsL]

noncomputable def certificate (n : ℕ) (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    MasterCertificate n world agent :=
  BstLean.Part261.master (scalar n ha hb) dsL tp tm ep em
    (by norm_num [dsL]) (by norm_num [tp]) (by norm_num [tm])
    (by norm_num [ep]) (by norm_num [em]) positive negative
    (tails ha hb).1 (tails ha hb).2
    (by
      convert BstLean.Part243.row_sampling using 1 <;>
        norm_num [scalar,BstLean.Part243.rowSamplingAllowance])
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      convert BstLean.Part243.row_sampling using 1 <;>
        norm_num [scalar,BstLean.Part243.rowSamplingAllowance])
    guards.1 guards.2

theorem compatible (n : ℕ) (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    agent.charge ≤ (certificate n ha hb).retainedCharge := le_rfl

end BstLean.Part271.GlobalMaster
