import BstLean.Part291GBNetwork

/-! Normalize the two Holder steps to the paper's GB coefficient. -/
namespace BstLean.BlueprintLow
open Real MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part188 BstLean.Part229

theorem gb_formula {L K F H B : ℝ} (hK : 0 ≤ K) (hF : 0 ≤ F)
    (hH : 0 ≤ H) (hB : 0 ≤ B) :
    L ^ (41 / 45 : ℝ) * (K * F ^ (45 / 4 : ℝ) *
      (((1 + H) ^ 32) ^ (1 / 16 : ℝ) * (B ^ 12) ^ (15 / 16 : ℝ))) ^ (4 / 45 : ℝ) =
      L ^ (41 / 45 : ℝ) * K ^ (4 / 45 : ℝ) *
        (1 + H) ^ (8 / 45 : ℝ) * F * B := by
  have hh : 0 ≤ 1 + H := by linarith
  have hE : ((1 + H) ^ 32) ^ (1 / 16 : ℝ) = (1 + H) ^ 2 := by
    rw [← rpow_natCast, ← rpow_mul hh]
    norm_num
  have hG : (B ^ 12) ^ (15 / 16 : ℝ) = B ^ (45 / 4 : ℝ) := by
    rw [← rpow_natCast, ← rpow_mul hB]
    norm_num
  rw [hE, hG, mul_rpow (mul_nonneg hK (rpow_nonneg hF _)) (by positivity),
    mul_rpow hK (rpow_nonneg hF _), mul_rpow (sq_nonneg _) (rpow_nonneg hB _),
    ← rpow_mul hF, ← rpow_mul hB, ← rpow_natCast, ← rpow_mul hh]
  norm_num
  ring

theorem gb_network_cap_normalized {n : ℕ} (hn : 1 ≤ n) (D : Design n) (c : Ret n)
    (v : Fin (mA n) → ℝ) (hv : normSq v = 1)
    {a d M H U : ℝ} (hd : 0 < d) (had : d ≤ a) (hU : 0 ≤ U)
    (hM : DirectionMoment D c M) (hH : EnergyMoment D c H)
    (hsecond : (∫ ξ, residualTest D c v ξ ^ 2 ∂stdGauss (Fin n)) ≤ U) :
    (∫ ξ, capEnergy a d (centreCoordinate D c) (residualTest D c v) ξ
      ∂stdGauss (Fin n)) ≤
      (U / d) ^ (41 / 45 : ℝ) * ((n : ℝ) / d) ^ (4 / 45 : ℝ) *
        (1 + H) ^ (8 / 45 : ℝ) * ((a - d) / d ^ 2) * (M / n) := by
  have h := gb_network_cap hn D c v hv hd had hU hM hH hsecond
  rw [gb_formula (by positivity) (by positivity) hH.1 (div_nonneg hM.1 (Nat.cast_nonneg _))] at h
  exact h

end BstLean.BlueprintLow
