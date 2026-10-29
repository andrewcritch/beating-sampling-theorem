import BstLean.Part221RadialDensity
import BstLean.Part221Curvature
import BstLean.Part221Polar
import BstLean.Part221Factorial
import BstLean.Part153Bin

/-! Calibrated Gaussian active maxima under the retained-data distribution. -/
namespace BstLean.Part221
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (radF53 measurable_radF)
open BstLean.Part217

lemma gaussian_positive_half : (gaussianReal 0 1).real (Ioi (0 : ℝ)) = 1 / 2 := by
  have h := BstLean.Part153.int_mask
  have he : BstLean.Part151.mask = (Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) := by
    funext z; simp [BstLean.Part151.mask, Set.indicator_apply]
  rw [he, integral_indicator measurableSet_Ioi, integral_const] at h
  simpa using h

noncomputable def activeData (m d : ℕ) : Measure ((Fin m → ℝ) × (Fin m → Fin d → ℝ)) :=
  (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod
    (Measure.pi (fun _ : Fin m => stdGauss (Fin d)))

instance activeData_probability (m d : ℕ) : IsProbabilityMeasure (activeData m d) := by
  unfold activeData; infer_instance

lemma measurable_activeRadius {m d : ℕ} (hm : 0 < m) :
    Measurable (fun p : (Fin m → ℝ) × (Fin m → Fin d → ℝ) => activeRadius hm p.1 p.2) := by
  have he : (fun p : (Fin m → ℝ) × (Fin m → Fin d → ℝ) => activeRadius hm p.1 p.2) =
      Finset.univ.sup' (show (Finset.univ : Finset (Fin m)).Nonempty from
        ⟨⟨0, hm⟩, Finset.mem_univ _⟩)
        (fun i p => if 0 < p.1 i then radF53 (p.2 i) else 0) := by
    funext p
    rw [Finset.sup'_apply]
    unfold activeRadius activeMaximum coordinateGate
    congr 1
    funext i
    by_cases hi : 0 < p.1 i <;> simp [hi]
  rw [he]
  apply Finset.measurable_sup'
  intro i hi
  exact Measurable.ite (measurableSet_lt measurable_const
    ((measurable_pi_apply i).comp measurable_fst))
    (measurable_radF.comp ((measurable_pi_apply i).comp measurable_snd)) measurable_const

theorem activeRadius_row_probability {m d : ℕ} (i : Fin m) (r : ℝ) :
    (activeData m d).real {p | coordinateGate (p.1 i) = true ∧ r < radF53 (p.2 i)} =
      (1 / 2) * (stdGauss (Fin d)).real {g | r < radF53 g} := by
  have he : {p : (Fin m → ℝ) × (Fin m → Fin d → ℝ) |
      coordinateGate (p.1 i) = true ∧ r < radF53 (p.2 i)} =
      {Z | 0 < Z i} ×ˢ {G | r < radF53 (G i)} := by
    ext p; simp [coordinateGate]
  rw [he, activeData, measureReal_prod_prod]
  have hz : (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).real {Z | 0 < Z i} = 1 / 2 := by
    have h := (measurePreserving_eval (fun _ : Fin m => gaussianReal 0 1) i).measure_preimage
      (s := Ioi (0 : ℝ)) measurableSet_Ioi.nullMeasurableSet
    have h' := congrArg ENNReal.toReal h
    exact h'.trans gaussian_positive_half
  have hg : (Measure.pi (fun _ : Fin m => stdGauss (Fin d))).real {G | r < radF53 (G i)} =
      (stdGauss (Fin d)).real {g | r < radF53 g} := by
    have h := (measurePreserving_eval (fun _ : Fin m => stdGauss (Fin d)) i).measure_preimage
      (s := {g | r < radF53 g}) (measurableSet_lt measurable_const measurable_radF).nullMeasurableSet
    exact congrArg ENNReal.toReal h
  rw [hz, hg]

theorem activeRadius_shifted_tail {m d : ℕ} (hm : 0 < m) (hd : 1 ≤ d)
    {a t c : ℝ} (ha : 0 < a) (hden : 0 < a ^ 2 - (d : ℝ) + 1)
    (hcal : (m : ℝ) / 2 * exp (-densityRate d a) ≤ 1)
    (hshift : ∀ v : ℝ, 0 < v → t * v + c * v ^ 2 / 2 ≤
      densityRate d (a + v) - densityRate d a) :
    ∀ v : ℝ, 0 < v → (activeData m d).real {p | a + v < activeRadius hm p.1 p.2} ≤
      exp (-t * v - c * v ^ 2 / 2) := by
  apply activeMaximum_shifted_tail (μ := activeData m d) hm
    (fun (p : (Fin m → ℝ) × (Fin m → Fin d → ℝ)) i => coordinateGate (p.1 i))
    (fun p i => radF53 (p.2 i)) ha.le hcal
  intro i v hv
  rw [activeRadius_row_probability]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hden' : 0 < (a + v) ^ 2 - (d : ℝ) + 1 := by nlinarith
  refine (gaussian_radius_rate_tail hd (by linarith : 0 < a + v) hden').trans ?_
  apply exp_le_exp.mpr
  linarith [hshift v hv]

theorem activeRadius_basic_tail {m d : ℕ} (hm : 0 < m) (hd : 1 ≤ d)
    {a : ℝ} (ha : 0 < a) (hden : 0 < a ^ 2 - (d : ℝ) + 1)
    (hcal : (m : ℝ) / 2 * exp (-densityRate d a) ≤ 1) :
    ∀ v : ℝ, 0 < v → (activeData m d).real {p | a + v < activeRadius hm p.1 p.2} ≤
      exp (-(a - (d : ℝ) / a) * v - v ^ 2 / 2) := by
  have hshift : ∀ v : ℝ, 0 < v → (a - (d : ℝ) / a) * v + 1 * v ^ 2 / 2 ≤
      densityRate d (a + v) - densityRate d a := by
    intro v hv
    have h := correctedRadialRate_shift (Nat.cast_nonneg d) ha hden hv.le
    dsimp [densityRate]
    linarith
  simpa only [one_mul] using activeRadius_shifted_tail hm hd ha hden hcal hshift

theorem activeRadius_large_tail {m d : ℕ} (hm : 0 < m) (hd : 3 ≤ d)
    {a : ℝ} (ha : 0 < a) (hden : 0 < a ^ 2 - (d : ℝ) + 1)
    (hy : ((d : ℝ) - 1) * ((d : ℝ) + 1 + sqrt (4 * (d : ℝ) + 1)) / ((d : ℝ) - 2) ≤ a ^ 2)
    (hcal : (m : ℝ) / 2 * exp (-densityRate d a) ≤ 1) :
    ∀ v : ℝ, 0 < v → (activeData m d).real {p | a + v < activeRadius hm p.1 p.2} ≤
      exp (-radialSlope (d : ℝ) a * v - v ^ 2 / 2) := by
  have hshift : ∀ v : ℝ, 0 < v → radialSlope (d : ℝ) a * v + 1 * v ^ 2 / 2 ≤
      densityRate d (a + v) - densityRate d a := by
    intro v hv
    have h := correctedRate_shift_large
      (by exact_mod_cast (show 2 < d by omega) : (2 : ℝ) < d) ha hden hy hv.le
    dsimp [densityRate]
    linarith
  simpa only [one_mul] using activeRadius_shifted_tail hm (by omega) ha hden hcal hshift

/-- The factorial majorant is an actual retained-data moment at any integer order. -/
theorem activeRadius_factorial_moment {m d : ℕ} (hm : 0 < m) (hd : 1 ≤ d)
    {a : ℝ} (ha : 0 < a) (ha2 : (d : ℝ) < a ^ 2)
    (hcal : (m : ℝ) / 2 * exp (-densityRate d a) ≤ 1) (ell : ℕ) :
    (∫⁻ Z, ∫⁻ G, ENNReal.ofReal (activeRadius hm Z G ^ ell)
      ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d))
      ∂Measure.pi (fun _ : Fin m => gaussianReal 0 1)) ≤
      ENNReal.ofReal (factorialMoment ell a (a - (d : ℝ) / a)) := by
  have h := shifted_tail_factorial (measurable_activeRadius hm)
    (fun p => activeMaximum_nonneg hm _ (fun i => sqrt_nonneg _)) ha
    (radial_slope_pos ha ha2) (by norm_num : (0 : ℝ) ≤ 1)
    (by simpa only [one_mul] using activeRadius_basic_tail hm hd ha (by linarith) hcal) ell
  have hmeas : Measurable (fun p : (Fin m → ℝ) × (Fin m → Fin d → ℝ) =>
      ENNReal.ofReal (activeRadius hm p.1 p.2 ^ ell)) :=
    ENNReal.measurable_ofReal.comp ((measurable_activeRadius hm).pow_const ell)
  rw [activeData, lintegral_prod _ hmeas.aemeasurable] at h
  exact h

noncomputable def automaticRadius (m d : ℕ) : ℝ :=
  (sqrt (d : ℝ) + 1) + sqrt (2 * max
    (log ((m : ℝ) / 2) - densityRate d (sqrt (d : ℝ) + 1)) 0)

/-- This formula supplies a calibration without a finite scalar certificate. -/
theorem automaticRadius_guards {m d : ℕ} (hm : 0 < m) (hd : 1 ≤ d) :
    0 < automaticRadius m d ∧ (d : ℝ) < automaticRadius m d ^ 2 ∧
      (m : ℝ) / 2 * exp (-densityRate d (automaticRadius m d)) ≤ 1 := by
  let a0 : ℝ := sqrt (d : ℝ) + 1
  let v : ℝ := sqrt (2 * max (log ((m : ℝ) / 2) - densityRate d a0) 0)
  have ha0 : 0 < a0 := by dsimp [a0]; positivity
  have hs := sq_sqrt (Nat.cast_nonneg (α := ℝ) d)
  have ha02 : (d : ℝ) < a0 ^ 2 := by dsimp [a0]; nlinarith [sqrt_nonneg (d : ℝ)]
  have hv : 0 ≤ v := sqrt_nonneg _
  have hv2 : v ^ 2 = 2 * max (log ((m : ℝ) / 2) - densityRate d a0) 0 :=
    sq_sqrt (by positivity)
  have hA : automaticRadius m d = a0 + v := rfl
  have ha : 0 < automaticRadius m d := by rw [hA]; linarith
  have ha2 : (d : ℝ) < automaticRadius m d ^ 2 := by rw [hA]; nlinarith
  refine ⟨ha, ha2, ?_⟩
  have hshift := correctedRadialRate_shift (Nat.cast_nonneg d) ha0 (by linarith) hv
  have hsl := mul_nonneg (radial_slope_pos ha0 ha02).le hv
  have hmax := le_max_left (log ((m : ℝ) / 2) - densityRate d a0) 0
  have hr : log ((m : ℝ) / 2) ≤ densityRate d (automaticRadius m d) := by
    rw [hA]
    dsimp [densityRate] at hmax hv2 ⊢
    nlinarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have he := exp_le_exp.mpr (neg_le_neg hr)
  have hid : (m : ℝ) / 2 * exp (-log ((m : ℝ) / 2)) = 1 := by
    rw [exp_neg, exp_log (by positivity), mul_inv_cancel₀ (by positivity)]
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq hid

end BstLean.Part221
