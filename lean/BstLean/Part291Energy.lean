import BstLean.Part291Band
import BstLean.Part277Uniform
import BstLean.Part277Instances
import BstLean.Part253EnergyUpper

/-! Endpoint certificates for the full low-band World window. -/
namespace BstLean.BlueprintLow
open Real Set BstLean.Part130 BstLean.Part206 BstLean.Part211

theorem centreEnergyUpperBand {n : ℕ} (hn : 8000 ≤ n) {q : ℝ}
    (hq : 0 ≤ q) (hqu : q ≤ 528 / 1000) :
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11 / 1000)) q ≤ agentEnergyCap := by
  have hk1 : kappa q ≤ 0.627895484988 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528 : ℝ)) (s := (0.849244370014 : ℝ))
    · exact hq
    · convert hqu using 1 <;> norm_num
    all_goals norm_num
  have hk2 : kappa (0.630986840195 : ℝ) ≤ 0.699885919761 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.630986840195 : ℝ)) (s := (0.775793534068 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_upper_from_kappasP (n0 := 8000) (by norm_num) hn
    (q := q) (t := (3.464101615138 : ℝ)) (s0 := (0.999999984374 : ℝ)) (g0 := (0.998268667967 : ℝ))
    (G := (1.001732800808 : ℝ)) (t2 := (3.467101615139 : ℝ)) (r := (89.442719099991 : ℝ)) (F := (0.010727 : ℝ))
    (U := (0.792792838634 : ℝ)) (R := (0.793658864038 : ℝ)) (Q2 := (0.630986840195 : ℝ)) (T := (0.837316357567 : ℝ))
    (B := (707768 / 1000000 : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩)
    (by norm_num) (by norm_num) (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
    hk1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hk2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem centreEnergyLowerBand {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hw : θ ∈ Icc (46 / 100 : ℝ) (528 / 1000)) :
    (0 ≤ meanLowerRoot n θ ∧
      0 ≤ kappa (meanLowerRoot n θ ^ 2 / gPlus n) - 2 / (n : ℝ) ^ 2 ∧
      0 ≤ √(gMinus n * (kappa (meanLowerRoot n θ ^ 2 / gPlus n) - 2 / (n : ℝ) ^ 2)) -
        2 * √(12 * gPlus n) / n - finiteEnergy n n (11 / 1000) / √(n : ℝ)) ∧
    (665 / 1000 : ℝ) ≤ energyLower n (gMinus n) (gPlus n) (finiteEnergy n n (11 / 1000)) θ := by
  have hk0 : (0.590432841418 : ℝ) ≤ kappa (1 - (528 / 1000 : ℝ)) := by
    apply BstLean.Part253.kappa_lower_rational (s := (0.881598548093 : ℝ)) <;> norm_num
  have hk1 : (0.668542176369 : ℝ) ≤ kappa (0.587557134547 : ℝ) := by
    apply BstLean.Part253.kappa_lower_rational (s := (0.809182682490 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_lower_dataP (n0 := 8000) (by norm_num) hn
    (θhi := (528 / 1000 : ℝ)) (by norm_num) hw
    (t := (3.464101615138 : ℝ)) (t2 := (3.467101615139 : ℝ)) (s0 := (0.999999984374 : ℝ))
    (s1 := (0.768052608984 : ℝ)) (s2 := (0.816936152148 : ℝ)) (K0 := (0.590432841418 : ℝ)) (K1 := (0.668542176369 : ℝ))
    (q1 := (0.587557134547 : ℝ)) (G := (1.001732800808 : ℝ)) (g0 := (0.998268667967 : ℝ))
    (F := (0.010727 : ℝ)) (r := (89.442719099991 : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) hk0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk1 (by norm_num)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (by convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num)
  norm_num only [Nat.cast_ofNat] at h
  refine ⟨⟨h.1, h.2.1, le_trans (by norm_num) h.2.2.1⟩,
    le_trans ?_ (h.2.2.2 (by trivial))⟩
  norm_num

end BstLean.BlueprintLow
