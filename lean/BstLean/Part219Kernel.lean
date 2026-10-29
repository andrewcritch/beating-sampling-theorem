import BstLean.Part219Ideal
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Scalar derivative bounds for the paper's weighted kernel secant. -/
namespace BstLean.Part219
open Real Set
open BstLean.Part130 BstLean.Part145

lemma kappa_chord {v : ℝ} (hv : v ∈ Icc (-1 : ℝ) 1) :
    kappa v ≤ (1 + v) / 2 := by
  have h := kappa_convexOn.2 (show (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)
    (show (1 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)
    (by linarith [hv.2] : 0 ≤ (1 - v) / 2)
    (by linarith [hv.1] : 0 ≤ (1 + v) / 2) (by ring)
  simp only [smul_eq_mul, kappa_neg_one, kappa_one, mul_zero, mul_one, zero_add] at h
  convert h using 1 <;> congr 1 <;> ring

lemma kg_derivative {v : ℝ} (hv : v ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt kg (1 / (π * √(1 - v ^ 2))) v := by
  have h := ((hasDerivAt_arccos (by linarith [hv.1]) (by linarith [hv.2])).const_sub π)
    |>.div_const π
  convert h using 1 <;> first | rfl | ring

noncomputable def kernelSecond (v : ℝ) : ℝ :=
  kg v ^ 2 / (π * √(1 - kappa v ^ 2)) + kg (kappa v) / (π * √(1 - v ^ 2))

lemma kernelSecond_nonneg (v : ℝ) : 0 ≤ kernelSecond v := by
  unfold kernelSecond
  exact add_nonneg (div_nonneg (sq_nonneg _) (mul_nonneg pi_pos.le (sqrt_nonneg _)))
    (div_nonneg (kg_nonneg _) (mul_nonneg pi_pos.le (sqrt_nonneg _)))

lemma kernelSlope_derivative {v : ℝ} (hv : v ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt kernelSlope (kernelSecond v) v := by
  have hk := kappa_mem hv.1.le hv.2.le
  have hkc := kappa_chord ⟨hv.1.le, hv.2.le⟩
  have hkv : kappa v ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hk.1], by linarith [hv.2]⟩
  have hd : HasDerivAt kappa (kg v) v := hasDerivAt_kappa hv.1 hv.2
  have h := ((kg_derivative hkv).comp v hd).mul (kg_derivative hv)
  rw [show kernelSlope = (kg ∘ kappa) * kg from rfl]
  convert h using 1
  unfold kernelSecond
  dsimp only [Function.comp_def]
  ring

lemma sphere_root_pos {v : ℝ} (hv : v ∈ Ioo (-1 : ℝ) 1) :
    0 < √(1 - v ^ 2) := by
  apply sqrt_pos.mpr
  nlinarith [mul_pos (by linarith [hv.1] : 0 < 1 + v) (by linarith [hv.2] : 0 < 1 - v)]

lemma root_ratio_bound {v : ℝ} (hv : v ∈ Icc (-1 : ℝ) 1) :
    √(1 - v ^ 2) ≤ √2 * √(1 - kappa v ^ 2) := by
  have hk := kappa_mem hv.1 hv.2
  have hc := kappa_chord hv
  have hsq := pow_le_pow_left₀ hk.1 hc 2
  have hv2 : 0 ≤ 1 - v ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hv.2) (by linarith [hv.1] : 0 ≤ 1 + v)
    nlinarith
  have hk2 : 0 ≤ 1 - kappa v ^ 2 := by nlinarith [hk.1, hk.2]
  apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
  rw [mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sq_sqrt hk2, sq_sqrt hv2]
  nlinarith [sq_nonneg (v - 1)]

/-- This global weighted derivative bound also covers negative kernel arguments. -/
theorem kernelSecond_weighted {v : ℝ} (hv : v ∈ Ioo (-1 : ℝ) 1) :
    kernelSecond v * √(1 - v ^ 2) ≤ 77 / 100 := by
  have hA := sphere_root_pos hv
  have hk := kappa_mem hv.1.le hv.2.le
  have hc := kappa_chord ⟨hv.1.le, hv.2.le⟩
  have hB := sphere_root_pos (show kappa v ∈ Ioo (-1 : ℝ) 1 from
    ⟨by linarith [hk.1], by linarith [hv.2]⟩)
  have hg2 : kg v ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ (kg_nonneg v) (kg_le_one v) 2
    simpa only [one_pow] using h
  have hnum : kg v ^ 2 * √(1 - v ^ 2) ≤ √2 * √(1 - kappa v ^ 2) :=
    (mul_le_mul_of_nonneg_right hg2 hA.le).trans
      (by simpa only [one_mul] using root_ratio_bound ⟨hv.1.le, hv.2.le⟩)
  have hratio : kg v ^ 2 * √(1 - v ^ 2) / √(1 - kappa v ^ 2) ≤ √2 :=
    (div_le_iff₀ hB).mpr hnum
  have he : kernelSecond v * √(1 - v ^ 2) =
      (kg v ^ 2 * √(1 - v ^ 2) / √(1 - kappa v ^ 2) + kg (kappa v)) / π := by
    unfold kernelSecond
    field_simp
    <;> ring
  rw [he]
  refine (div_le_div_of_nonneg_right (add_le_add hratio (kg_le_one _)) pi_pos.le).trans ?_
  apply (div_le_iff₀ pi_pos).mpr
  have h2 : √(2 : ℝ) ≤ 283 / 200 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  linarith [pi_gt_d2]

lemma kg_le_three_quarters {v : ℝ} (hv : v ≤ 27 / 50) : kg v ≤ 3 / 4 := by
  have hsq : (27 / 25 : ℝ) ≤ √2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hcos : v ≤ cos (π / 4) := by rw [cos_pi_div_four]; linarith
  have har := arccos_le_arccos hcos
  rw [arccos_cos (by positivity) (by linarith [pi_pos])] at har
  unfold kg
  apply (div_le_iff₀ pi_pos).mpr
  linarith

/-- A coarse rational enclosure suffices on the central interval. -/
theorem kernelSecond_central {v : ℝ} (hv : v ∈ Icc (0 : ℝ) (27 / 50)) :
    kernelSecond v ≤ 77 / 100 := by
  have hv' : v ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hk := kappa_mem hv'.1.le hv'.2.le
  have hc := kappa_chord ⟨hv'.1.le, hv'.2.le⟩
  have hA : (4 / 5 : ℝ) ≤ √(1 - v ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    have h := pow_le_pow_left₀ hv.1 hv.2 2
    nlinarith
  have hB : (3 / 5 : ℝ) ≤ √(1 - kappa v ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    have hkc : kappa v ≤ 4 / 5 := by linarith [hv.2]
    have h := pow_le_pow_left₀ hk.1 hkc 2
    nlinarith
  have hA0 : 0 < √(1 - v ^ 2) := lt_of_lt_of_le (by norm_num) hA
  have hB0 : 0 < √(1 - kappa v ^ 2) := lt_of_lt_of_le (by norm_num) hB
  have hg2 : kg v ^ 2 ≤ 9 / 16 := by
    have h := pow_le_pow_left₀ (kg_nonneg v) (kg_le_three_quarters hv.2) 2
    norm_num at h
    exact h
  have h1 : kg v ^ 2 / √(1 - kappa v ^ 2) ≤ 15 / 16 := by
    apply (div_le_iff₀ hB0).mpr
    linarith
  have h2 : kg (kappa v) / √(1 - v ^ 2) ≤ 5 / 4 := by
    apply (div_le_iff₀ hA0).mpr
    linarith [kg_le_one (kappa v)]
  have he : kernelSecond v =
      (kg v ^ 2 / √(1 - kappa v ^ 2) + kg (kappa v) / √(1 - v ^ 2)) / π := by
    unfold kernelSecond
    ring
  rw [he]
  apply (div_le_iff₀ pi_pos).mpr
  linarith [pi_gt_three]

#print axioms kernelSecond_weighted
#print axioms kernelSecond_central
end BstLean.Part219
