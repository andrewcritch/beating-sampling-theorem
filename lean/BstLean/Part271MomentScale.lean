import BstLean.Part271R3Bounds

/-! Preserve the factor `1 / mW n` in the World moment before interval evaluation. -/
namespace BstLean.Part271.R3
open Real BstLean.Part130 BstLean.Part137 BstLean.Part140 BstLean.Part159
open BstLean.Part227

noncomputable def arCore (n : ℕ) : ℝ := √(10 + 25 / (mW n : ℝ))

noncomputable def chCore (n : ℕ) : ℝ :=
  √(6 * (1 + 5 / (mW n : ℝ)) +
    (kappa 0 * (√5 + √(2 / ((2*n : ℕ) : ℝ))) +
      √((1 + 2 / ((2*n : ℕ) : ℝ)) / 2)) ^ 2)

noncomputable def lxCore (n : ℕ) : ℝ :=
  (1001/1000) * (chCore n / kap1 (2*n)) + BstLean.Part210.Rnew n +
    (1001/1000) * (√(645/10000) / kap1 (2*n)) * √(1 + arW n)

noncomputable def momentMain (n : ℕ) : ℝ :=
  ((202831/100000) / (1-1/50)^2 *
    (arCore n + (2+1/50) * lxCore n))^2 /
      (((202225/100000)-1)^2 * cRhoG (202225/100000) (202831/100000) (1/50))

noncomputable def momentResidual (n : ℕ) : ℝ :=
  2 * (arCore n ^ 2 + lxCore n ^ 2) / (1/50)^2

theorem arW_scale {n : ℕ} (hm : 0 < (mW n : ℝ)) :
    arW n = arCore n / √(mW n : ℝ) := by
  unfold arW arCore
  rw [← Real.sqrt_div' _ hm.le]
  congr 1
  field_simp [ne_of_gt hm]
  <;> ring

theorem cHat2_scale {n : ℕ} (hm : 0 < (mW n : ℝ)) :
    cHat2 (2*n) (mW n) = chCore n / √(mW n : ℝ) := by
  unfold cHat2 chCore
  rw [← Real.sqrt_div' _ hm.le]
  congr 1
  ring

theorem perturbation_scale (n : ℕ) :
    √(perturbation n) = √(645/10000) / √(mW n : ℝ) := by
  unfold perturbation
  norm_num only [show (10 : ℝ)^4 = 10000 by norm_num]
  exact Real.sqrt_div (by norm_num) _

theorem lxG_scale {n : ℕ} (hm : 0 < (mW n : ℝ)) :
    lxG n (√(perturbation n)) (BstLean.Part210.Rnew n / √(mW n : ℝ))
      (1001/1000) = lxCore n / √(mW n : ℝ) := by
  unfold lxG lxCore
  rw [cHat2_scale hm, perturbation_scale]
  ring

theorem moment_scale {n : ℕ} (hm : 0 < (mW n : ℝ)) :
    momentValue n (202225/100000) (202831/100000) (1/50) =
      ((n : ℝ) * momentMain n + momentResidual n) / (mW n : ℝ) := by
  unfold momentValue vPert
  rw [lxG_scale hm, arW_scale hm]
  have hs : (√(mW n : ℝ))^2 = (mW n : ℝ) := Real.sq_sqrt hm.le
  calc
    _ = ((n : ℝ) * momentMain n + momentResidual n) / (√(mW n : ℝ))^2 := by
      unfold momentMain momentResidual
      ring
    _ = _ := by rw [hs]

theorem moment_envelope {n : ℕ} {C D : ℝ} (hm : 0 < (mW n : ℝ))
    (hC : momentMain n ≤ C) (hD : momentResidual n ≤ D) :
    momentValue n (202225/100000) (202831/100000) (1/50) ≤
      ((n : ℝ) * C + D) / (mW n : ℝ) := by
  rw [moment_scale hm]
  apply div_le_div_of_nonneg_right _ hm.le
  exact add_le_add (mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg n)) hD

end BstLean.Part271.R3
