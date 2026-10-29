import BstLean.Part277Instances
namespace BstLean.Part281
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem energy_lower_data {n : ℕ} (hn : 11883 ≤ n) {θ : ℝ}
    (hw : θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0 ≤ meanLowerRoot n θ ∧
      0 ≤ kappa (meanLowerRoot n θ ^ 2 / BstLean.Part211.gPlus n) - 2 / (n : ℝ) ^ 2 ∧
      0 ≤ √(gMinus n * (kappa (meanLowerRoot n θ ^ 2 / BstLean.Part211.gPlus n) -
        2 / (n : ℝ) ^ 2)) - 2 * √(12 * BstLean.Part211.gPlus n) / n -
        finiteEnergy n n (11 / 1000) / √(n : ℝ)) ∧
    (0.665 : ℝ) ≤ energyLower n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) θ := by
  have hK0 : (0.592401616394 : ℝ) ≤ kappa (1 - (0.525 : ℝ)) := by
    apply BstLean.Part253.kappa_lower_rational (s := (0.879985795339 : ℝ)) <;> norm_num
  have hK1 : (0.670565768293 : ℝ) ≤ kappa (0.590462546227 : ℝ) := by
    apply BstLean.Part253.kappa_lower_rational (s := (0.807065041680 : ℝ)) <;> norm_num
  have h := BstLean.Part277.energy_lower_dataP (n0 := 11883) (by norm_num) hn
    (θhi := (0.525 : ℝ)) (θ := θ) (by norm_num) (by convert hw using 1 <;> norm_num)
    (t := (3.464102 : ℝ)) (t2 := (3.466121307361 : ℝ)) (s1 := (0.769446655805 : ℝ)) (s2 := (0.818403351700 : ℝ))
    (K0 := (0.592401616394 : ℝ)) (K1 := (0.670565768293 : ℝ)) (q1 := (0.590462546227 : ℝ))
    (G := (1.001166409778 : ℝ)) (g0 := (0.998834255926 : ℝ)) (F := (0.008771 : ℝ)) (r := (109.009173 : ℝ))
    (s0 := (0.999999992918 : ℝ))
    (sqrt_le_iff.mpr (by norm_num)) hK0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hK1 (by norm_num)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (sqrt_le_iff.mpr (by norm_num)) (by norm_num) (by norm_num)
    (by convert BstLean.Part277.finite_centre_11883 hn using 1 <;> norm_num)
  obtain ⟨h1,h2,h3,h4⟩ := h
  have hp : (0 : ℝ) ≤ 0.818403351700 - 2 * 3.466121307361 / 11883 - 0.008771 / 109.009173 := by norm_num
  exact ⟨⟨h1,h2,le_trans hp h3⟩,le_trans (by norm_num) (h4 hp)⟩
end BstLean.Part281
