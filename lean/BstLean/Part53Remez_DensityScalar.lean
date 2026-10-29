import Mathlib

namespace BstLean.Part53.RemezAux

open MeasureTheory

noncomputable def radialWeight (q t : ℝ) : ℝ :=
  Real.exp ((q - 1) * Real.log t - q / 2 * (t ^ 2 - 1))

theorem radialWeight_pos (q t : ℝ) : 0 < radialWeight q t := Real.exp_pos _

theorem radialWeight_gaussian_upper {q t : ℝ} (hq : 1 ≤ q) (ht : 0 < t) :
    radialWeight q t ≤ Real.exp (1 / (2 * q)) *
      Real.exp (-(q / 2) * (t - (1 - 1 / q)) ^ 2) := by
  rw [radialWeight, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlog := Real.log_le_sub_one_of_pos ht
  have h := mul_le_mul_of_nonneg_left hlog (sub_nonneg.mpr hq)
  have he : (q - 1) * (t - 1) - q / 2 * (t ^ 2 - 1) =
      1 / (2 * q) + -(q / 2) * (t - (1 - 1 / q)) ^ 2 := by
    field_simp
    <;> ring
  linarith

theorem radialWeight_local_lower {q t : ℝ} (hq : 1 ≤ q)
    (ht : 59 / 60 ≤ t) (ht' : t ≤ 61 / 60) (hz : q * (t - 1) ^ 2 ≤ 1 / 4) :
    3 / 5 ≤ radialWeight q t := by
  have ht0 : 0 < t := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos ht0
  have h := mul_le_mul_of_nonneg_left hlog (sub_nonneg.mpr hq)
  have hdiv : (q * (t - 1) ^ 2 + (t - 1)) / t ≤ 1 / 3 := by
    rw [div_le_iff₀ ht0]
    nlinarith
  have he : (q - 1) * (1 - t⁻¹) - q / 2 * (t ^ 2 - 1) =
      -(q * (t - 1) ^ 2) / 2 - (q * (t - 1) ^ 2 + (t - 1)) / t := by
    field_simp
    <;> ring
  have hexp : -(1 / 2 : ℝ) ≤ (q - 1) * Real.log t - q / 2 * (t ^ 2 - 1) := by
    linarith
  have hhalf := Real.exp_le_two_add_div_two_sub (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hhalf' : (3 / 5 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
    rw [Real.exp_neg, ← one_div, le_div_iff₀ (Real.exp_pos _)]
    norm_num at hhalf
    nlinarith
  exact hhalf'.trans (Real.exp_le_exp.mpr hexp)

theorem radialWeight_integrableOn {q : ℝ} (hq : 1 ≤ q) :
    IntegrableOn (radialWeight q) (Set.Ioi 0) volume := by
  let g : ℝ → ℝ := fun t => Real.exp (1 / (2 * q)) *
    Real.exp (-(q / 2) * (t - (1 - 1 / q)) ^ 2)
  have hg : Integrable g volume :=
    ((integrable_exp_neg_mul_sq (show 0 < q / 2 by linarith)).comp_sub_right
      (1 - 1 / q)).const_mul _
  apply hg.integrableOn.mono' (show AEStronglyMeasurable (radialWeight q)
      (volume.restrict (Set.Ioi 0)) from (by unfold radialWeight; fun_prop))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_pos (radialWeight_pos q t)]
  exact radialWeight_gaussian_upper hq ht

theorem radialWeight_integral_upper {q : ℝ} (hq : 1000 ≤ q) :
    ∫ t in Set.Ioi (0 : ℝ), radialWeight q t ≤ 3 / Real.sqrt q := by
  have hq0 : 0 < q := by linarith
  let g : ℝ → ℝ := fun t => Real.exp (1 / (2 * q)) *
    Real.exp (-(q / 2) * (t - (1 - 1 / q)) ^ 2)
  have hg : Integrable g volume :=
    ((integrable_exp_neg_mul_sq (show 0 < q / 2 by linarith)).comp_sub_right
      (1 - 1 / q)).const_mul _
  have hδ : Real.exp (1 / (2 * q)) ≤ 101 / 100 := by
    calc
      _ ≤ Real.exp (1 / 2000) := Real.exp_le_exp.mpr (by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith)
      _ ≤ (2 + (1 / 2000 : ℝ)) / (2 - 1 / 2000) :=
        Real.exp_le_two_add_div_two_sub (by norm_num) (by norm_num)
      _ ≤ _ := by norm_num
  have hs : Real.sqrt (2 * Real.pi) ≤ 29 / 10 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith [Real.pi_lt_four]
  calc
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), g t :=
      setIntegral_mono_on (radialWeight_integrableOn (by linarith)) hg.integrableOn
        measurableSet_Ioi (fun t ht => radialWeight_gaussian_upper (by linarith) ht)
    _ ≤ ∫ t, g t := setIntegral_le_integral hg (.of_forall fun t => by dsimp [g]; positivity)
    _ = Real.exp (1 / (2 * q)) * Real.sqrt (Real.pi / (q / 2)) := by
      dsimp [g]
      rw [integral_const_mul,
        integral_sub_right_eq_self (fun x : ℝ => Real.exp (-(q / 2) * x ^ 2)) (1 - 1 / q),
        integral_gaussian]
    _ = (Real.exp (1 / (2 * q)) * Real.sqrt (2 * Real.pi)) / Real.sqrt q := by
      rw [show Real.pi / (q / 2) = (2 * Real.pi) / q by ring,
        Real.sqrt_div (show 0 ≤ 2 * Real.pi by positivity)]
      ring
    _ ≤ 3 / Real.sqrt q := by
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact (mul_le_mul hδ hs (Real.sqrt_nonneg _)
        (by norm_num : (0 : ℝ) ≤ 101 / 100)).trans (by norm_num)

noncomputable def halfWidth (q : ℝ) : ℝ := 1 / (2 * Real.sqrt q)

theorem radialWeight_interval_lower {q t : ℝ} (hq : 1000 ≤ q)
    (ht : t ∈ Set.Icc (1 - halfWidth q) (1 + halfWidth q)) :
    3 / 5 ≤ radialWeight q t := by
  have hq0 : 0 < q := by linarith
  have hs : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0.le
  have hs30 : 30 ≤ Real.sqrt q := by nlinarith [Real.sqrt_nonneg q]
  have hw0 : 0 ≤ halfWidth q := by unfold halfWidth; positivity
  have hw : halfWidth q ≤ 1 / 60 := by
    unfold halfWidth
    rw [div_le_iff₀ (by positivity)]
    linarith
  have he : q * halfWidth q ^ 2 = 1 / 4 := by
    unfold halfWidth
    rw [div_pow, mul_pow, Real.sq_sqrt hq0.le]
    field_simp
    <;> ring
  have hz : q * (t - 1) ^ 2 ≤ 1 / 4 := by
    have h := mul_nonneg (show 0 ≤ halfWidth q - (t - 1) by linarith [ht.2])
      (show 0 ≤ halfWidth q + (t - 1) by linarith [ht.1])
    have h' := mul_nonneg hq0.le h
    nlinarith
  apply radialWeight_local_lower (by linarith) (by linarith [ht.1]) (by linarith [ht.2]) hz

theorem normalized_radialWeight_lower {q A t : ℝ} (hq : 1000 ≤ q) (hA : 0 ≤ A)
    (hmass : A * (∫ s in Set.Ioi (0 : ℝ), radialWeight q s) = 1)
    (ht : t ∈ Set.Icc (1 - halfWidth q) (1 + halfWidth q)) :
    Real.sqrt q / 5 ≤ A * radialWeight q t := by
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr (by linarith)
  have h := mul_le_mul_of_nonneg_left (radialWeight_integral_upper hq) hA
  rw [hmass, ← mul_div_assoc, le_div_iff₀ hs] at h
  have h' := mul_le_mul_of_nonneg_left (radialWeight_interval_lower hq ht) hA
  nlinarith

end BstLean.Part53.RemezAux
