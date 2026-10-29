import BstLean.Part56Low_Laplace
import BstLean.Part56PropD_Split

namespace BstLean.Part56.LowAngular

open MeasureTheory ProbabilityTheory BstLean.Part29 BstLean.Part53
open BstLean.Part56

lemma cap_exponent_nonneg (a r L : ℝ) (hL : 0 < L)
    (hcap : 1 - (a / Real.sqrt (a ^ 2 + r ^ 2)) ^ 2 < (4 * L + 1)⁻¹) :
    0 ≤ a ^ 2 / 4 - L * r ^ 2 := by
  have hden : 0 < a ^ 2 + r ^ 2 := by
    by_contra h
    have hz : a ^ 2 + r ^ 2 = 0 := le_antisymm (le_of_not_gt h) (by positivity)
    have ha : a = 0 := by nlinarith [sq_nonneg r]
    have hr : r = 0 := by nlinarith [sq_nonneg a]
    simp only [ha, hr, zero_pow (by decide : 2 ≠ 0), zero_add, Real.sqrt_zero,
      div_zero, sub_zero] at hcap
    have ht : (4 * L + 1)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).2 (by linarith)
    linarith
  have hs : (a / Real.sqrt (a ^ 2 + r ^ 2)) ^ 2 = a ^ 2 / (a ^ 2 + r ^ 2) := by
    rw [div_pow, Real.sq_sqrt hden.le]
  rw [hs] at hcap
  have he : 1 - a ^ 2 / (a ^ 2 + r ^ 2) = r ^ 2 / (a ^ 2 + r ^ 2) := by
    field_simp
    ring
  rw [he] at hcap
  have hb : r ^ 2 * (4 * L + 1) < a ^ 2 + r ^ 2 := by
    have hc : r ^ 2 / (a ^ 2 + r ^ 2) < 1 / (4 * L + 1) := by
      simpa only [one_div] using hcap
    simpa only [one_mul] using (div_lt_div_iff₀ hden (by positivity : 0 < 4 * L + 1)).mp hc
  nlinarith

lemma angular_moment_minorant (a r L : ℝ) (hL : 0 < L) (k : ℕ) :
    ((4 * L + 1)⁻¹) ^ k * (1 - Real.exp (a ^ 2 / 4 - L * r ^ 2)) ≤
      (1 - (a / Real.sqrt (a ^ 2 + r ^ 2)) ^ 2) ^ k := by
  have hy : 0 ≤ 1 - (a / Real.sqrt (a ^ 2 + r ^ 2)) ^ 2 := by
    have ha := axialS_abs_le_one a r
    change |a / Real.sqrt (a ^ 2 + r ^ 2)| ≤ 1 at ha
    have h := (abs_le.mp ha)
    nlinarith
  by_cases hc : 1 - (a / Real.sqrt (a ^ 2 + r ^ 2)) ^ 2 < (4 * L + 1)⁻¹
  · have he : 1 ≤ Real.exp (a ^ 2 / 4 - L * r ^ 2) :=
      Real.one_le_exp_iff.mpr (cap_exponent_nonneg a r L hL hc)
    exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)).trans
      (pow_nonneg hy k)
  · have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (4 * L + 1)⁻¹) (le_of_not_gt hc) k
    have he : 1 - Real.exp (a ^ 2 / 4 - L * r ^ 2) ≤ 1 := by
      linarith [Real.exp_pos (a ^ 2 / 4 - L * r ^ 2)]
    exact (mul_le_of_le_one_right (by positivity) he).trans hp

lemma weighted_angular_lower (m k : ℕ) (L W : ℝ) (hL : 0 < L) (hW : 0 ≤ W)
    (w : ℝ × (Fin m → ℝ) → ℝ) (hw : StronglyMeasurable w)
    (hw0 : ∀ p, 0 ≤ w p) (hwW : ∀ p, w p ≤ W)
    (hwi : Integrable w ((gaussianReal 0 1).prod (stdGauss (Fin m))))
    (hw1 : ∫ p, w p ∂(gaussianReal 0 1).prod (stdGauss (Fin m)) = 1)
    (hyi : Integrable (fun p => w p *
      (1 - (p.1 / Real.sqrt (p.1 ^ 2 + (radF53 p.2) ^ 2)) ^ 2) ^ k)
      ((gaussianReal 0 1).prod (stdGauss (Fin m)))) :
    ((4 * L + 1)⁻¹) ^ k *
        (1 - W * Real.sqrt 2 * ((Real.sqrt (1 + 2 * L))⁻¹) ^ m) ≤
      ∫ p, w p * (1 - (p.1 / Real.sqrt (p.1 ^ 2 + (radF53 p.2) ^ 2)) ^ 2) ^ k
        ∂(gaussianReal 0 1).prod (stdGauss (Fin m)) := by
  let E : ℝ × (Fin m → ℝ) → ℝ := fun p => Real.exp (p.1 ^ 2 / 4 - L * ∑ i, p.2 i ^ 2)
  have hE := LowLaplace.gaussian_cap_majorant_integrable m L hL
  have hEm : StronglyMeasurable E := by
    apply Continuous.stronglyMeasurable
    dsimp only [E]
    fun_prop
  have hwe : Integrable (fun p => w p * E p)
      ((gaussianReal 0 1).prod (stdGauss (Fin m))) := by
    apply (hE.const_mul W).mono' (hw.mul hEm).aestronglyMeasurable
    exact ae_of_all _ fun p => by
      change ‖w p * E p‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 p) (Real.exp_pos _).le)]
      exact mul_le_mul_of_nonneg_right (hwW p) (Real.exp_pos _).le
  have heBound : (∫ p, w p * E p ∂(gaussianReal 0 1).prod (stdGauss (Fin m))) ≤
      W * Real.sqrt 2 * ((Real.sqrt (1 + 2 * L))⁻¹) ^ m := by
    have h := integral_mono_ae hwe (hE.const_mul W)
      (ae_of_all _ fun p => mul_le_mul_of_nonneg_right (hwW p) (Real.exp_pos _).le)
    simpa only [integral_const_mul, LowLaplace.gaussian_cap_majorant_integral m L hL,
      mul_assoc] using h
  have hrad (z : Fin m → ℝ) : (radF53 z) ^ 2 = ∑ i, z i ^ 2 := by
    exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _) 
  have hp := integral_mono_ae
    ((hwi.sub hwe).const_mul (((4 * L + 1)⁻¹) ^ k)) hyi
    (ae_of_all _ fun p => by
      have h := mul_le_mul_of_nonneg_left
        (angular_moment_minorant p.1 (radF53 p.2) L hL k) (hw0 p)
      rw [hrad] at h
      simp only [Pi.sub_apply, E, hrad]
      nlinarith)
  simp only [Pi.sub_apply] at hp
  rw [integral_const_mul, integral_sub hwi hwe, hw1] at hp
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left heBound 1) (by positivity)).trans hp


end BstLean.Part56.LowAngular
