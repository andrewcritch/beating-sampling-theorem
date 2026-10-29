import BstLean.Part254GaussianData
import BstLean.Part291CentreTail0
import BstLean.Part263Events
import BstLean.Part291Windows
namespace BstLean.BlueprintLow
open Real BstLean.Part254 BstLean.Part146

theorem lowExpCoreAxial : exp (-((2592/625) : ℝ)) ≤ (7904309352620941864901022633/500000000000000000000000000000) := by
  apply BstLean.Part269.Tails.exp_negative_sixteen_bound (E := ((1295892957503417481/1000000000000000000) : ℝ))
  all_goals norm_num [Finset.sum_range_succ,Nat.factorial]

theorem lowTailCoreAxial : gaussianTail (72/25) ≤ (3976772356218232048567106307/1000000000000000000000000000000) := by
  have h := gaussianTail_enclosure (t := ((72/25) : ℝ)) (lo := 0) (hi := ((7904309352620941864901022633/500000000000000000000000000000) : ℝ))
    (L := 0) (U := ((3976772356218232048567106307/1000000000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
    (exp_nonneg _) (by convert lowExpCoreAxial using 1 <;> norm_num)
    (by norm_num) (by norm_num [nP,eP])
  exact h.2

theorem lowExpCorePair : exp (-((106929/20000) : ℝ)) ≤ (1191259222545507711075342691/250000000000000000000000000000) := by
  apply BstLean.Part269.Tails.exp_negative_sixteen_bound (E := ((1396757005616755769/1000000000000000000) : ℝ))
  all_goals norm_num [Finset.sum_range_succ,Nat.factorial]

theorem lowTailCorePair : gaussianTail (327/100) ≤ (1075476249840540980986933423/1000000000000000000000000000000) := by
  have h := gaussianTail_enclosure (t := ((327/100) : ℝ)) (lo := 0) (hi := ((1191259222545507711075342691/250000000000000000000000000000) : ℝ))
    (L := 0) (U := ((1075476249840540980986933423/1000000000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
    (exp_nonneg _) (by convert lowExpCorePair using 1 <;> norm_num)
    (by norm_num) (by norm_num [nP,eP])
  exact h.2

theorem lowExpCoreRadius : exp (-((781/100) : ℝ)) ≤ (6338406997214649722139743/15625000000000000000000000000) := by
  apply BstLean.Part269.Tails.exp_negative_sixteen_bound (E := ((407314623638986333/250000000000000000) : ℝ))
  all_goals norm_num [Finset.sum_range_succ,Nat.factorial]

theorem lowExpWideRadius : exp (-((20/1) : ℝ)) ≤ (2061153939767738937057/1000000000000000000000000000000) := by
  apply BstLean.Part269.Tails.exp_negative_sixteen_bound (E := ((872585730969164319/250000000000000000) : ℝ))
  all_goals norm_num [Finset.sum_range_succ,Nat.factorial]

theorem lowExpTI : exp (-((46/1) : ℝ)) ≤ (10531/10^24) := by
  have hE : 0 < (177254/10000 : ℝ) := by norm_num
  have hsum : (177254/10000 : ℝ) ≤
      ∑ i ∈ Finset.range 16, ((46/16 : ℝ) ^ i / i.factorial) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hexp := hsum.trans
    (sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 46/16) 16)
  have he : exp (46 : ℝ) = exp (46/16 : ℝ) ^ 16 := by
    convert exp_nat_mul (46/16 : ℝ) 16 using 1 <;> norm_num
  have hp : (177254/10000 : ℝ) ^ 16 ≤ exp (46 : ℝ) := by
    rw [he]
    exact pow_le_pow_left₀ (by norm_num) hexp 16
  have hinv : exp (-46 : ℝ) ≤ ((177254/10000 : ℝ) ^ 16)⁻¹ := by
    rw [exp_neg]
    exact (inv_le_inv₀ (exp_pos _) (pow_pos hE 16)).mpr hp
  have hB : ((177254/10000 : ℝ) ^ 16)⁻¹ ≤ (10531/10^24 : ℝ) := by
    norm_num
  simpa using hinv.trans hB

theorem lowCorePair_cap : gaussianPair lowCoreWindow ≤ (1075476249840540980986933423/1000000000000000000000000000000) := by
  unfold gaussianPair
  rw [show lowCoreWindow.pair = 327/100 by norm_num [lowCoreWindow]]
  exact lowTailCorePair
theorem lowCoreOutside_cap : gaussianOutside lowCoreWindow ≤ (4788088451861707213000993411/1000000000000000000000000000000) := by
  unfold gaussianOutside
  rw [show lowCoreWindow.t = 72/25 by norm_num [lowCoreWindow],
    show lowCoreWindow.z = 781/100 by norm_num [lowCoreWindow]]
  have hmul : 2 * exp (-((781/100 : ℝ))) ≤
      2 * (6338406997214649722139743/15625000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left lowExpCoreRadius (by norm_num : (0 : ℝ) ≤ 2)
  exact (add_le_add lowTailCoreAxial hmul).trans (by norm_num)
theorem lowWideOutside_cap : gaussianOutside lowWideWindow ≤ (3047741939767738937057/500000000000000000000000000000) := by
  unfold gaussianOutside
  rw [show lowWideWindow.t = 6 by norm_num [lowWideWindow],
    show lowWideWindow.z = 20 by norm_num [lowWideWindow]]
  have hexp : exp (-20 : ℝ) ≤
      (2061153939767738937057/1000000000000000000000000000000 : ℝ) := by
    simpa using lowExpWideRadius
  have hmul : 2 * exp (-20 : ℝ) ≤
      2 * (2061153939767738937057/1000000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ 2)
  exact (add_le_add gaussianTail_6.2 hmul).trans (by norm_num)
theorem lowBadMass_cap : gaussianTail lowWideWindow.pair + 2 * (BstLean.Part255.delta / 0.00025) ≤ (1681082001/250000000000000000000000) := by
  have htail := gaussianTail_8.2
  have hexp : exp (-46 : ℝ) ≤ (10531/10^24 : ℝ) := by
    simpa using lowExpTI
  unfold BstLean.Part255.delta
  change gaussianTail 8 + 2 * (65 * exp (-46) / 0.00025) ≤ _
  rw [show 2 * (65 * exp (-46) / 0.00025) = (2 * 65 / 0.00025) * exp (-46) by ring]
  calc
    _ ≤ (1244193/10^21 : ℝ) + (2 * 65 / 0.00025) * exp (-46) :=
      add_le_add htail le_rfl
    _ ≤ (1244193/10^21 : ℝ) + (2 * 65 / 0.00025) * (10531/10^24) :=
      add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ 2 * 65 / 0.00025))
    _ ≤ _ := by norm_num
end BstLean.BlueprintLow
