import BstLean.Part130Row

/-!
# Part 182 (file `Kap`): the two bivariate Gaussian facts of Lemma TI

No proof is left open; no `native_decide` or `axiom` is used.

Paper source: `proofs/option-n/theorem7-04-frame-numerator.tex`, § "The two-input bounds":
"The two-dimensional Gaussian polar integral gives `E R(Z)R(Z') = κ(c)/2` and
`P(Z > 0, Z' > 0) = κ̇(c)/2` for correlation `c`", with `κ̇(c) = 1 − arccos(c)/π`.

* `kdot q = 1 − arccos q/π` (the paper's `κ̇`).
* `angular_pos`, `radial_one`, `core2D_pos`: the two-dimensional pieces.
* **`orthant_prob`** (Sheppard's formula): for unit `a, b ∈ ℝ^k` and `ξ` standard Gaussian,
  `Pr(a·ξ > 0 ∧ b·ξ > 0) = κ̇(a·b)/2`.
* **`kernel_unit`** (arc-cosine kernel): `E[ReLU(a·ξ)·ReLU(b·ξ)] = κ(a·b)/2` (a corollary of
  Part 130 `row_formula_std`).
* `kdot_monotoneOn`, `half_le_kdot`, `kdot_le_one`, `hasDerivAt_kappa_kdot` (`κ′ = κ̇`),
  `kappa_one` (Part 130).
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130

variable {k : ℕ}

/-- `κ̇(q) = 1 − arccos(q)/π`. -/
noncomputable def kdot (q : ℝ) : ℝ := 1 - Real.arccos q / π

/-- The indicator of `t > 0`. -/
noncomputable def posI (t : ℝ) : ℝ := if 0 < t then 1 else 0

lemma posI_of_pos {t : ℝ} (h : 0 < t) : posI t = 1 := by simp [posI, h]

lemma posI_of_nonpos {t : ℝ} (h : t ≤ 0) : posI t = 0 := by simp [posI, not_lt.mpr h]

lemma posI_mul_of_pos {c : ℝ} (hc : 0 < c) (t : ℝ) : posI (c * t) = posI t := by
  unfold posI
  by_cases ht : 0 < t
  · simp [ht, mul_pos hc ht]
  · have : ¬ 0 < c * t := by
      intro h; exact ht (pos_of_mul_pos_right h hc.le)
    simp [ht, this]

lemma measurable_posI : Measurable posI := by
  unfold posI
  exact Measurable.ite measurableSet_Ioi measurable_const measurable_const

/-! ## The two-dimensional pieces -/

/-- The angular integral: `∫_{−π}^{π} 1[cos θ > 0]·1[cos(θ − ψ) > 0] dθ = π − ψ`. -/
lemma angular_pos {ψ : ℝ} (h0 : 0 ≤ ψ) (h1 : ψ ≤ π) :
    ∫ θ in Ioo (-π) π, posI (cos θ) * posI (cos (θ - ψ)) = π - ψ := by
  have hp := pi_pos
  have hmeas : Measurable (fun θ : ℝ => posI (cos θ) * posI (cos (θ - ψ))) :=
    (measurable_posI.comp continuous_cos.measurable).mul
      (measurable_posI.comp (continuous_cos.comp (continuous_id.sub continuous_const)).measurable)
  have hbdd : ∀ θ : ℝ, ‖posI (cos θ) * posI (cos (θ - ψ))‖ ≤ 1 := by
    intro θ
    unfold posI
    split_ifs <;> simp
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun θ : ℝ => posI (cos θ) * posI (cos (θ - ψ)))
      volume a b := fun a b =>
    (intervalIntegrable_const (c := (1 : ℝ))).mono_fun hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun θ => by simpa using hbdd θ)
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_add_adjacent_intervals (hint (-π) (ψ - π / 2)) (hint (ψ - π / 2) π),
    ← intervalIntegral.integral_add_adjacent_intervals (hint (ψ - π / 2) (π / 2)) (hint (π / 2) π)]
  have z1 : ∫ θ in (-π)..(ψ - π / 2), posI (cos θ) * posI (cos (θ - ψ)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro θ hθ
      rw [uIcc_of_le (by linarith)] at hθ
      obtain ⟨ha, hb⟩ := hθ
      by_cases hc : θ ≤ -(π / 2)
      · have : cos θ ≤ 0 := by
          rw [← cos_neg]
          exact cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
        simp [posI_of_nonpos this]
      · have : cos (θ - ψ) ≤ 0 := by
          rw [← cos_neg]
          exact cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
        simp [posI_of_nonpos this]
  have z3 : ∫ θ in (π / 2)..π, posI (cos θ) * posI (cos (θ - ψ)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro θ hθ
      rw [uIcc_of_le (by linarith)] at hθ
      obtain ⟨ha, hb⟩ := hθ
      have : cos θ ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le ha (by linarith)
      simp [posI_of_nonpos this]
  have z2 : ∫ θ in (ψ - π / 2)..(π / 2), posI (cos θ) * posI (cos (θ - ψ)) = π - ψ := by
    have hne : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ π / 2 := by
      rw [ae_iff]
      have e : {a : ℝ | ¬ a ≠ π / 2} = {π / 2} := by ext a; simp
      rw [e]; exact measure_singleton _
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (1 : ℝ))]
    · simp; ring
    · filter_upwards [hne] with θ hθne hθ
      rw [uIoc_of_le (by linarith)] at hθ
      obtain ⟨ha, hb⟩ := hθ
      have hb' : θ < π / 2 := lt_of_le_of_ne hb hθne
      have c1 : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith, hb'⟩
      have c2 : 0 < cos (θ - ψ) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
      simp [posI_of_pos c1, posI_of_pos c2]
  rw [z1, z2, z3]
  ring

/-- `∫₀^∞ r e^{−r²/2} dr = 1`. -/
lemma radial_one : ∫ r in Ioi (0 : ℝ), r * exp (-r ^ 2 / 2) = 1 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  have e : ∫ r in Ioi (0 : ℝ), r * exp (-r ^ 2 / 2) =
      ∫ r in Ioi (0 : ℝ), r ^ (1 : ℝ) * exp (-(1 / 2) * r ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    rw [rpow_one, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast]
    congr 2
    ring
  rw [e, h]
  rw [show (1 + 1 : ℝ) / 2 = 1 by norm_num, Gamma_one]
  norm_num

/-- **The two-dimensional orthant integral**: for `0 ≤ ψ ≤ π`,
`Pr(ξ₀ > 0, cos ψ·ξ₀ + sin ψ·ξ₁ > 0) = (π − ψ)/(2π)`. -/
theorem core2D_pos {ψ : ℝ} (h0 : 0 ≤ ψ) (h1 : ψ ≤ π) :
    ∫ ξ, posI (ξ 0) * posI (cos ψ * ξ 0 + sin ψ * ξ 1) ∂stdGauss (Fin 2) =
      (π - ψ) / (2 * π) := by
  let G : ℝ × ℝ → ℝ := fun p => posI p.1 * posI (cos ψ * p.1 + sin ψ * p.2)
  have s1 : ∫ ξ, posI (ξ 0) * posI (cos ψ * ξ 0 + sin ψ * ξ 1) ∂stdGauss (Fin 2) =
      ∫ p, G p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    have := (measurePreserving_finTwoArrow (gaussianReal 0 1)).integral_comp' G
    rw [← this]
    rfl
  have hγ : gaussianReal 0 1 = volume.withDensity (gaussianPDF 0 1) :=
    gaussianReal_of_var_ne_zero 0 one_ne_zero
  have s2 : ∫ p, G p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) =
      ∫ p : ℝ × ℝ, (gaussianPDF 0 1 p.1 * gaussianPDF 0 1 p.2).toReal • G p := by
    rw [hγ, prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1)]
    rw [← Measure.volume_eq_prod]
    refine integral_withDensity_eq_integral_toReal_smul ?_ ?_ G
    · exact ((measurable_gaussianPDF 0 1).comp measurable_fst).mul
        ((measurable_gaussianPDF 0 1).comp measurable_snd)
    · refine Filter.Eventually.of_forall fun p => ?_
      exact ENNReal.mul_lt_top (by simp [gaussianPDF]) (by simp [gaussianPDF])
  rw [s1, s2, ← integral_comp_polarCoord_symm]
  have s3 : ∫ p in polarCoord.target, p.1 • ((gaussianPDF 0 1 (polarCoord.symm p).1 *
        gaussianPDF 0 1 (polarCoord.symm p).2).toReal • G (polarCoord.symm p)) =
      ∫ p in polarCoord.target, ((2 * π)⁻¹ * (p.1 * exp (-p.1 ^ 2 / 2))) *
        (posI (cos p.2) * posI (cos (p.2 - ψ))) := by
    refine setIntegral_congr_fun polarCoord.open_target.measurableSet fun p hp => ?_
    rw [polarCoord_target] at hp
    have hr : 0 < p.1 := hp.1
    simp only [polarCoord_symm_apply, G, smul_eq_mul]
    rw [gauss_density_polar, posI_mul_of_pos hr,
      show cos ψ * (p.1 * cos p.2) + sin ψ * (p.1 * sin p.2) = p.1 * cos (p.2 - ψ) by
        rw [cos_sub]; ring,
      posI_mul_of_pos hr]
    ring
  rw [s3, polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [integral_prod_mul (μ := volume.restrict (Ioi (0 : ℝ))) (ν := volume.restrict (Ioo (-π) π))
    (fun r : ℝ => (2 * π)⁻¹ * (r * exp (-r ^ 2 / 2)))
    (fun θ : ℝ => posI (cos θ) * posI (cos (θ - ψ)))]
  rw [integral_const_mul, radial_one, angular_pos h0 h1]
  field_simp

/-! ## Unit vectors in `ℝ^k` -/

/-- **Sheppard's formula, integral form**: for unit `h, h′ ∈ ℝ^k`,
`E[1[w·h > 0]·1[w·h′ > 0]] = (π − arccos(h·h′))/(2π)`. -/
theorem orthant_std {h h' : Fin k → ℝ} (hh : normSq h = 1) (hh' : normSq h' = 1) :
    ∫ w, posI (∑ j, w j * h j) * posI (∑ j, w j * h' j) ∂stdGauss (Fin k) =
      (π - Real.arccos (∑ j, h j * h' j)) / (2 * π) := by
  classical
  set d := ∑ j, h j * h' j with hd
  have habs : |d| ≤ 1 := by
    have := abs_dot_le h h'
    rwa [hh, hh', Real.sqrt_one, mul_one] at this
  have hc1 : -1 ≤ d ∧ d ≤ 1 := abs_le.mp habs
  set ψ := Real.arccos d with hψ
  have hψ0 : 0 ≤ ψ := Real.arccos_nonneg d
  have hψ1 : ψ ≤ π := Real.arccos_le_pi d
  have hcos : cos ψ = d := Real.cos_arccos hc1.1 hc1.2
  let A : Matrix (Fin 2) (Fin k) ℝ := Matrix.of ![h, h']
  let B : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of ![![1, 0], ![cos ψ, sin ψ]]
  have hAB : A * A.transpose = B * B.transpose := by
    have haa : ∑ j, h j * h j = 1 := by
      rw [← hh]; exact Finset.sum_congr rfl fun j _ => (sq _).symm
    have hbb : ∑ j, h' j * h' j = 1 := by
      rw [← hh']; exact Finset.sum_congr rfl fun j _ => (sq _).symm
    have hd' : ∑ j, h' j * h j = d := Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hsc := sin_sq_add_cos_sq ψ
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, B, Matrix.mul_apply, Fin.sum_univ_two, haa, hbb, hd', ← hd]
    · rw [hcos]
    · rw [hcos]
    · nlinarith
  have hmap := BstLean.Part105.gaussLin105 (Fin k) (Fin 2) (Fin 2) A B hAB
  let g : (Fin 2 → ℝ) → ℝ := fun y => posI (y 0) * posI (y 1)
  have hg : Measurable g :=
    (measurable_posI.comp (measurable_pi_apply 0)).mul (measurable_posI.comp (measurable_pi_apply 1))
  have e1 : ∫ w, posI (∑ j, w j * h j) * posI (∑ j, w j * h' j) ∂stdGauss (Fin k) =
      ∫ w, g (A.mulVec w) ∂stdGauss (Fin k) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [g, A, Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    congr 2 <;> exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have e2 : ∫ w, g (A.mulVec w) ∂stdGauss (Fin k) = ∫ ξ, g (B.mulVec ξ) ∂stdGauss (Fin 2) := by
    rw [← integral_map (measurable_mulVec_left A).aemeasurable hg.aestronglyMeasurable, hmap,
      integral_map (measurable_mulVec_left B).aemeasurable hg.aestronglyMeasurable]
  have e3 : ∀ ξ : Fin 2 → ℝ, g (B.mulVec ξ) =
      posI (ξ 0) * posI (cos ψ * ξ 0 + sin ψ * ξ 1) := by
    intro ξ
    simp only [g, B, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, add_zero, one_mul]
  rw [e1, e2]
  simp_rw [e3]
  rw [core2D_pos hψ0 hψ1]

/-- **Sheppard's formula** (the mask overlap of Lemma TI): for unit `a, b ∈ ℝ^k` and a standard
Gaussian `w`, `Pr(w·a > 0 ∧ w·b > 0) = κ̇(a·b)/2`. -/
theorem orthant_prob {a b : Fin k → ℝ} (ha : normSq a = 1) (hb : normSq b = 1) :
    (stdGauss (Fin k)).real {w | 0 < ∑ j, w j * a j ∧ 0 < ∑ j, w j * b j} =
      kdot (∑ j, a j * b j) / 2 := by
  have hP : IsProbabilityMeasure (stdGauss (Fin k)) := by unfold stdGauss; infer_instance
  have hma : Measurable (fun w : Fin k → ℝ => ∑ j, w j * a j) :=
    Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).mul_const _
  have hmb : Measurable (fun w : Fin k → ℝ => ∑ j, w j * b j) :=
    Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).mul_const _
  have hS : MeasurableSet {w : Fin k → ℝ | 0 < ∑ j, w j * a j ∧ 0 < ∑ j, w j * b j} :=
    (measurableSet_lt measurable_const hma).inter (measurableSet_lt measurable_const hmb)
  rw [← integral_indicator_one hS]
  have e : ({w : Fin k → ℝ | 0 < ∑ j, w j * a j ∧ 0 < ∑ j, w j * b j}.indicator 1 :
      (Fin k → ℝ) → ℝ) = fun w => posI (∑ j, w j * a j) * posI (∑ j, w j * b j) := by
    funext w
    by_cases h1 : 0 < ∑ j, w j * a j <;> by_cases h2 : 0 < ∑ j, w j * b j <;>
      simp [Set.indicator, posI, h1, h2]
  rw [e, orthant_std ha hb, kdot]
  have hp := pi_pos
  field_simp

/-- **The arc-cosine kernel** (the first-layer mean of Lemma TI): for unit `a, b ∈ ℝ^k` and a
standard Gaussian `w`, `E[ReLU(w·a)·ReLU(w·b)] = κ(a·b)/2`. -/
theorem kernel_unit {a b : Fin k → ℝ} (ha : normSq a = 1) (hb : normSq b = 1) :
    ∫ w, relu (∑ j, w j * a j) * relu (∑ j, w j * b j) ∂stdGauss (Fin k) =
      kappa (∑ j, a j * b j) / 2 := by
  have h := row_formula_std a b
  rw [ha, hb, Real.sqrt_one, one_mul, one_mul, div_one] at h
  linarith

/-! ## Elementary properties of `κ̇` -/

theorem kdot_monotoneOn : MonotoneOn kdot (Icc (-1) 1) := by
  intro x _ y _ hxy
  unfold kdot
  have := Real.arccos_le_arccos hxy
  have hp := pi_pos
  have : Real.arccos y / π ≤ Real.arccos x / π := div_le_div_of_nonneg_right this hp.le
  linarith

theorem half_le_kdot {q : ℝ} (hq : 0 ≤ q) : 1 / 2 ≤ kdot q := by
  unfold kdot
  have h := Real.arccos_le_pi_div_two.mpr hq
  have hp := pi_pos
  have : Real.arccos q / π ≤ 1 / 2 := by
    rw [div_le_iff₀ hp]; linarith
  linarith

theorem kdot_le_one (q : ℝ) : kdot q ≤ 1 := by
  unfold kdot
  have := Real.arccos_nonneg q
  have hp := pi_pos
  have : 0 ≤ Real.arccos q / π := div_nonneg this hp.le
  linarith

theorem kdot_nonneg (q : ℝ) : 0 ≤ kdot q := by
  unfold kdot
  have := Real.arccos_le_pi q
  have hp := pi_pos
  have : Real.arccos q / π ≤ 1 := by rw [div_le_iff₀ hp]; linarith
  linarith

/-- `κ′ = κ̇` on `(−1, 1)`. -/
theorem hasDerivAt_kappa_kdot {t : ℝ} (h1 : -1 < t) (h2 : t < 1) :
    HasDerivAt kappa (kdot t) t := by
  have h := hasDerivAt_kappa h1 h2
  convert h using 1
  unfold kdot
  have hp := pi_pos
  field_simp

end BstLean.Part182

open BstLean.Part182 in
#print axioms orthant_prob
open BstLean.Part182 in
#print axioms kernel_unit
open BstLean.Part182 in
#print axioms hasDerivAt_kappa_kdot
open BstLean.Part182 in
#print axioms kdot_monotoneOn
open BstLean.Part182 in
#print axioms half_le_kdot
