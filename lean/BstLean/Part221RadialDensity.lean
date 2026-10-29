import BstLean.Part53Remez_Radial
import BstLean.Part217Rate
import BstLean.Part53Polar

/-! The Gaussian radial density supplies its tangent tail bound. -/
namespace BstLean.Part221
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (radF53 measurable_radF)
open BstLean.Part53.RemezAux (gaussianRadialFactor gaussianRadialFactor_nonneg
  gaussian_radius_integral gaussian_radius_integrable)
open BstLean.Part217 (radialRate radialRate_shift)

noncomputable def radialWeight (d : ℕ) (r : ℝ) : ℝ := r ^ (d - 1) * exp (-r ^ 2 / 2)

lemma radialWeight_exp {d : ℕ} {r : ℝ} (hr : 0 < r) :
    radialWeight d r = exp (-radialRate (d - 1 : ℕ) r) := by
  unfold radialWeight radialRate
  rw [show -(r ^ 2 / 2 - ((d - 1 : ℕ) : ℝ) * log r) =
    ((d - 1 : ℕ) : ℝ) * log r + (-r ^ 2 / 2) by ring,
    exp_add, exp_nat_mul, exp_log hr]

theorem radialWeight_tangent {d : ℕ} {a r : ℝ} (ha : 0 < a) (har : a ≤ r) :
    radialWeight d r ≤ radialWeight d a *
      exp (-(a - ((d - 1 : ℕ) : ℝ) / a) * (r - a)) := by
  have hs := radialRate_shift (d := ((d - 1 : ℕ) : ℝ)) (Nat.cast_nonneg _) ha
    (sub_nonneg.mpr har)
  rw [show a + (r - a) = r by ring] at hs
  rw [radialWeight_exp (ha.trans_le har), radialWeight_exp ha, ← exp_add]
  apply exp_le_exp.mpr
  nlinarith [sq_nonneg (r - a)]

lemma radialWeight_integrable (d : ℕ) (hd : 1 ≤ d) :
    IntegrableOn (radialWeight d) (Ioi 0) := by
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have h := gaussian_radius_integrable (Fin d) (fun _ => (1 : ℝ)) (integrable_const 1)
  change IntegrableOn (fun r : ℝ => r ^ (d - 1) * exp (-r ^ 2 / 2)) (Ioi 0)
  simpa using h

theorem gaussian_radius_tail_integral {d : ℕ} (hd : 1 ≤ d) {a : ℝ} (ha : 0 ≤ a) :
    (stdGauss (Fin d)).real {z | a < radF53 z} =
      gaussianRadialFactor (Fin d) * ∫ r in Ioi a, radialWeight d r := by
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have h := gaussian_radius_integral (Fin d) ((Ioi a).indicator (fun _ => (1 : ℝ)))
  have he : (fun z : Fin d → ℝ => (Ioi a).indicator (fun _ => (1 : ℝ))
      (sqrt (∑ i, z i ^ 2))) = {z | a < radF53 z}.indicator (fun _ => (1 : ℝ)) := by
    funext z; rfl
  rw [he, integral_indicator (measurableSet_lt measurable_const measurable_radF),
    integral_const] at h
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_one] at h
  change (stdGauss (Fin d)).real {z | a < radF53 z} = _ at h
  rw [h]
  congr 1
  have he' : (fun r : ℝ => r ^ (Fintype.card (Fin d) - 1) * exp (-r ^ 2 / 2) *
      (Ioi a).indicator (fun _ => (1 : ℝ)) r) = (Ioi a).indicator (radialWeight d) := by
    funext r; by_cases hr : r ∈ Ioi a <;> simp [hr, radialWeight]
  rw [he', integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  have hset : Ioi a ∩ Ioi (0 : ℝ) = Ioi a := inter_eq_left.mpr (Ioi_subset_Ioi ha)
  rw [hset]

theorem gaussian_radius_density_tail {d : ℕ} (hd : 1 ≤ d) {a : ℝ} (ha : 0 < a)
    (hden : 0 < a ^ 2 - ((d - 1 : ℕ) : ℝ)) :
    (stdGauss (Fin d)).real {z | a < radF53 z} ≤
      gaussianRadialFactor (Fin d) *
        (a ^ d * exp (-a ^ 2 / 2) / (a ^ 2 - ((d - 1 : ℕ) : ℝ))) := by
  let s : ℝ := a - ((d - 1 : ℕ) : ℝ) / a
  have hs : 0 < s := by
    dsimp [s]
    rw [sub_pos, div_lt_iff₀ ha]
    nlinarith
  have hi := (radialWeight_integrable d hd).mono_set (Ioi_subset_Ioi ha.le)
  have hexp := integrableOn_exp_mul_Ioi (neg_neg_of_pos hs) a
  have hpt : ∀ r ∈ Ioi a, radialWeight d r ≤
      (radialWeight d a * exp (s * a)) * exp (-s * r) := by
    intro r hr
    refine (radialWeight_tangent ha hr.le).trans_eq ?_
    have he : -s * (r - a) = s * a + -s * r := by ring
    change radialWeight d a * exp (-s * (r - a)) = _
    rw [he, exp_add]; ring
  have hb := integral_mono_ae hi (hexp.const_mul (radialWeight d a * exp (s * a)))
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ hpt))
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hs)] at hb
  have he : radialWeight d a * exp (s * a) * (-exp (-s * a) / -s) =
      a ^ d * exp (-a ^ 2 / 2) / (a ^ 2 - ((d - 1 : ℕ) : ℝ)) := by
    have hee : exp (s * a) * exp (-s * a) = 1 := by
      rw [← exp_add, show s * a + -s * a = 0 by ring, exp_zero]
    have hsa : s * a = a ^ 2 - ((d - 1 : ℕ) : ℝ) := by dsimp [s]; field_simp
    have hp : a ^ d = a ^ (d - 1) * a := by
      rw [← pow_succ, Nat.sub_add_cancel hd]
    calc _ = radialWeight d a * (exp (s * a) * exp (-s * a)) / s := by ring
      _ = radialWeight d a / s := by rw [hee, mul_one]
      _ = _ := by
        rw [← hsa, hp]
        unfold radialWeight
        field_simp
  rw [he] at hb
  rw [gaussian_radius_tail_integral hd ha.le]
  exact mul_le_mul_of_nonneg_left hb (gaussianRadialFactor_nonneg _)

theorem radialWeight_mass {d : ℕ} (hd : 1 ≤ d) :
    (∫ r in Ioi (0 : ℝ), radialWeight d r) =
      (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) * (1 / 2) * Gamma ((d : ℝ) / 2) := by
  have hdR : ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hd
  have he : radialWeight d = fun r : ℝ => r ^ ((d - 1 : ℕ) : ℝ) *
      exp (-(1 / 2) * r ^ (2 : ℝ)) := by
    funext r
    simp only [radialWeight, rpow_natCast, show (2 : ℝ) = ((2 : ℕ) : ℝ) from rfl]
    congr 2; ring
  rw [he, integral_rpow_mul_exp_neg_mul_rpow (by norm_num : (0 : ℝ) < 2)
    (by linarith [Nat.cast_nonneg (α := ℝ) (d - 1)] : -1 < ((d - 1 : ℕ) : ℝ))
    (by norm_num : (0 : ℝ) < 1 / 2), hdR]

/-- Normalization uses the exact Gamma value in every positive integer dimension. -/
theorem gaussianRadialFactor_gamma {d : ℕ} (hd : 1 ≤ d) :
    gaussianRadialFactor (Fin d) =
      ((1 / 2 : ℝ) ^ (-(d : ℝ) / 2) * (1 / 2) * Gamma ((d : ℝ) / 2))⁻¹ := by
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have h := gaussian_radius_integral (Fin d) (fun _ => (1 : ℝ))
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, Fintype.card_fin, mul_one] at h
  change 1 = gaussianRadialFactor (Fin d) * ∫ r in Ioi (0 : ℝ), radialWeight d r at h
  rw [radialWeight_mass hd] at h
  exact eq_inv_of_mul_eq_one_left h.symm

lemma gaussianRadialFactor_pos {d : ℕ} (hd : 1 ≤ d) : 0 < gaussianRadialFactor (Fin d) := by
  rw [gaussianRadialFactor_gamma hd]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

noncomputable def densityRate (d : ℕ) (r : ℝ) : ℝ :=
  BstLean.Part217.correctedRadialRate (d : ℝ) r - log (gaussianRadialFactor (Fin d))

theorem densityRate_exp {d : ℕ} (hd : 1 ≤ d) {a : ℝ} (ha : 0 < a)
    (hden : 0 < a ^ 2 - (d : ℝ) + 1) :
    exp (-densityRate d a) = gaussianRadialFactor (Fin d) *
      (a ^ d * exp (-a ^ 2 / 2) / (a ^ 2 - (d : ℝ) + 1)) := by
  unfold densityRate BstLean.Part217.correctedRadialRate radialRate
  have he : -(a ^ 2 / 2 - (d : ℝ) * log a + log (a ^ 2 - (d : ℝ) + 1) -
      log (gaussianRadialFactor (Fin d))) =
      log (gaussianRadialFactor (Fin d)) + (d : ℝ) * log a + (-a ^ 2 / 2) -
        log (a ^ 2 - (d : ℝ) + 1) := by ring
  rw [he, exp_sub, exp_add, exp_add, exp_log (gaussianRadialFactor_pos hd),
    exp_nat_mul, exp_log ha, exp_log hden]
  ring

theorem gaussian_radius_rate_tail {d : ℕ} (hd : 1 ≤ d) {a : ℝ} (ha : 0 < a)
    (hden : 0 < a ^ 2 - (d : ℝ) + 1) :
    (stdGauss (Fin d)).real {z | a < radF53 z} ≤ exp (-densityRate d a) := by
  have he : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub hd]; norm_num
  rw [densityRate_exp hd ha hden]
  have hden' : 0 < a ^ 2 - ((d - 1 : ℕ) : ℝ) := by rw [he]; linarith
  simpa only [he, sub_sub, sub_add] using gaussian_radius_density_tail hd ha hden'

end BstLean.Part221
