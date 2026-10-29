import BstLean.Part157All
import BstLean.Part141All

/-!
# Part 159 (file `CN`): the closed form of the constant `c_N` for even `N`

Role: `delegations/statements/p159-spec.md`, item 3 (toward `ConstC`). Do not use `sorry`,
`native_decide` or `axiom`.

`c_N = cN N = E_u ReLU(u₁)`, `u` uniform on the unit sphere of `ℝ^N` (Part 137). The paper's
program uses `c̃_N = π̃⁻¹·∏_{j=1}^{n−1} 2j/(2j+1)` for `N = 2n`.

* `radI p = ∫_0^∞ r^p e^{−r²/2} dr`; `radI_step`: `radI (p+2) = (p+1)·radI p`; `radI_zero`,
  `radI_one`.
* `cN_radial`: `c_{M+1} = radI M/(√(2π)·radI (M+1))` (polar decomposition of the Gaussian weight;
  the proof of the polar formula is that of Part 29).
* **`cN_even`**: `c_{2n} = π⁻¹·∏_{j=1}^{n−1} 2j/(2j+1)` for every `n ≥ 1`.
* `cNt_eq`: `c̃_N = c_N·π/π̃` for `N = 2n`.
-/

namespace BstLean.Part159

open MeasureTheory Real
open BstLean.Part29 (uniformSphere)
open BstLean.Part130
open BstLean.Part137 (cN gfun)
open BstLean.Part157 (cNt piT)

/-- The polar formula for a function that is homogeneous of degree `k` on rays, against the
Gaussian weight (the statement and the proof of `polar_homogeneous` of Part 29). -/
private lemma polar_hom (n k : ℕ) (hn : 1 ≤ n) (P : EuclideanSpace ℝ (Fin n) → ℝ)
    (hP : ∀ (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
      (r : ℝ), 0 < r → P (r • u.1) = r ^ k * P u.1) :
    (∫ x, P x * Real.exp (-‖x‖ ^ 2 / 2)) =
      (∫ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, P u.1
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) *
      ∫ r in Set.Ioi (0 : ℝ), r ^ (n - 1 + k) * Real.exp (-r ^ 2 / 2) := by
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let E := EuclideanSpace ℝ (Fin n)
  let μ : Measure E := volume
  let f := fun z : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) =>
    P z.1.1 * (z.2.1 ^ k * Real.exp (-z.2.1 ^ 2 / 2))
  have hcomp : ∀ x : ({(0 : E)}ᶜ : Set E),
      f (homeomorphUnitSphereProd E x) = P x.1 * Real.exp (-‖x.1‖ ^ 2 / 2) := by
    intro x
    let z := homeomorphUnitSphereProd E x
    have hx : x.1 = z.2.1 • z.1.1 := by
      have h := congrArg Subtype.val ((homeomorphUnitSphereProd E).symm_apply_apply x)
      rw [homeomorphUnitSphereProd_symm_apply_coe] at h
      exact h.symm
    rw [hx]
    have hu : ‖z.1.1‖ = 1 := by simp
    change P z.1.1 * (z.2.1 ^ k * Real.exp (-z.2.1 ^ 2 / 2)) = _
    rw [hP z.1 z.2.1 z.2.2, norm_smul, Real.norm_eq_abs, abs_of_pos z.2.2, hu,
      mul_one]
    ring
  calc
    _ = ∫ x : ({(0 : E)}ᶜ : Set E), P x.1 * Real.exp (-‖x.1‖ ^ 2 / 2)
        ∂(μ.comap (↑)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl
        (fun x => P x * Real.exp (-‖x‖ ^ 2 / 2)),
        restrict_compl_singleton]
    _ = ∫ z, f z ∂μ.toSphere.prod (.volumeIoiPow (Module.finrank ℝ E - 1)) := by
      simpa only [Function.comp_def, hcomp] using
        μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
          (Homeomorph.measurableEmbedding _) f
    _ = (∫ u, P u.1 ∂μ.toSphere) *
        ∫ r : Set.Ioi (0 : ℝ), r.1 ^ k * Real.exp (-r.1 ^ 2 / 2)
          ∂Measure.volumeIoiPow (n - 1) := by
      simpa [f, E] using integral_prod_mul
        (fun u : Metric.sphere (0 : E) 1 => P u.1)
        (fun r : Set.Ioi (0 : ℝ) => r.1 ^ k * Real.exp (-r.1 ^ 2 / 2))
    _ = _ := by
      congr 1
      simp only [Measure.volumeIoiPow, ENNReal.ofReal]
      rw [integral_withDensity_eq_integral_smul
        ((measurable_subtype_coe.pow_const _).real_toNNReal)]
      rw [integral_subtype_comap measurableSet_Ioi
        (fun r : ℝ => Real.toNNReal (r ^ (n - 1)) •
          (r ^ k * Real.exp (-r ^ 2 / 2)))]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hr.le _),
        pow_add]
      ring

/-- `radI p = ∫_0^∞ r^p e^{−r²/2} dr`. -/
noncomputable def radI (p : ℕ) : ℝ := ∫ r in Set.Ioi (0 : ℝ), r ^ p * Real.exp (-r ^ 2 / 2)

lemma radI_value (p : ℕ) :
    radI p = (1 / 2 : ℝ) ^ (-((p + 1 : ℕ) : ℝ) / 2) * (1 / 2) *
      Real.Gamma (((p + 1 : ℕ) : ℝ) / 2) := by
  unfold radI
  convert integral_rpow_mul_exp_neg_mul_rpow
    (p := 2) (q := ((p : ℕ) : ℝ)) (b := 1 / 2)
    (by norm_num) (by exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _))
    (by norm_num) using 1
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp only [Real.rpow_natCast, Real.rpow_two]
    congr 2
    ring
  · push_cast
    rfl

lemma radI_pos (p : ℕ) : 0 < radI p := by
  rw [radI_value]
  have hg : 0 < Real.Gamma (((p + 1 : ℕ) : ℝ) / 2) :=
    Real.Gamma_pos_of_pos (div_pos (by exact_mod_cast (show 0 < p + 1 by omega)) (by norm_num))
  positivity

/-- `radI (p+2) = (p+1)·radI p`. -/
lemma radI_step (p : ℕ) : radI (p + 2) = ((p : ℝ) + 1) * radI p := by
  rw [radI_value (p + 2), radI_value p]
  have ha : (((p + 2 + 1 : ℕ) : ℝ) / 2) = ((p + 1 : ℕ) : ℝ) / 2 + 1 := by
    push_cast
    ring
  rw [ha, Real.Gamma_add_one
    (ne_of_gt (div_pos (by exact_mod_cast (show 0 < p + 1 by omega)) (by norm_num)))]
  have hb : -((p + 2 + 1 : ℕ) : ℝ) / 2 = -((p + 1 : ℕ) : ℝ) / 2 + (-1) := by
    push_cast
    ring
  rw [hb, Real.rpow_add (by norm_num), Real.rpow_neg_one]
  push_cast
  ring

/-- `radI 1 = 1`. -/
lemma radI_one : radI 1 = 1 := by
  rw [radI_value]
  have e : -(((1 + 1 : ℕ) : ℝ)) / 2 = -1 := by norm_num
  have e2 : (((1 + 1 : ℕ) : ℝ)) / 2 = 1 := by norm_num
  rw [e, e2, Real.rpow_neg_one, Real.Gamma_one]
  norm_num

/-- `radI 0 = √(π/2)`. -/
lemma radI_zero : radI 0 = √(π / 2) := by
  unfold radI
  have h := integral_gaussian_Ioi (1 / 2 : ℝ)
  have e : ∀ r : ℝ, r ^ 0 * Real.exp (-r ^ 2 / 2) = Real.exp (-(1 / 2) * r ^ 2) := by
    intro r
    rw [pow_zero, one_mul]
    congr 1
    ring
  simp_rw [e]
  rw [h]
  have h2 : π / (1 / 2) = 4 * (π / 2) := by ring
  rw [h2, Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  ring

/-! ## Gaussian integrals with one distinguished coordinate -/

lemma gauss1 : ∫ t : ℝ, Real.exp (-t ^ 2 / 2) = √(2 * π) := by
  have h := integral_gaussian (1 / 2 : ℝ)
  have e : ∀ t : ℝ, Real.exp (-t ^ 2 / 2) = Real.exp (-(1 / 2) * t ^ 2) := by
    intro t
    congr 1
    ring
  simp_rw [e]
  rw [h]
  congr 1
  ring

/-- `∫ f(x₀) e^{−|x|²/2} dx = (∫ f(t) e^{−t²/2} dt)·(√(2π))^M` on `ℝ^{M+1}`. -/
lemma gaussE (M : ℕ) (f : ℝ → ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin (M + 1)), f (x 0) * Real.exp (-‖x‖ ^ 2 / 2)) =
      (∫ t : ℝ, f t * Real.exp (-t ^ 2 / 2)) * √(2 * π) ^ M := by
  classical
  let F : Fin (M + 1) → ℝ → ℝ :=
    fun i t => (if i = 0 then f t else 1) * Real.exp (-t ^ 2 / 2)
  have hp (x : Fin (M + 1) → ℝ) :
      f (x 0) * Real.exp (-(∑ i, x i ^ 2) / 2) = ∏ i, F i (x i) := by
    simp only [F]
    rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    congr 1
    · rw [Finset.prod_ite_eq' Finset.univ (0 : Fin (M + 1)) (fun i => f (x i))]
      simp
    · congr 1
      simp only [neg_div, Finset.sum_div, Finset.sum_neg_distrib]
  calc
    _ = ∫ x : Fin (M + 1) → ℝ, f (x 0) * Real.exp (-(∑ i, x i ^ 2) / 2) := by
      simpa only [EuclideanSpace.real_norm_sq_eq] using
        (PiLp.volume_preserving_ofLp (Fin (M + 1))).integral_comp
          (MeasurableEquiv.toLp 2 (Fin (M + 1) → ℝ)).symm.measurableEmbedding
          (fun x : Fin (M + 1) → ℝ => f (x 0) * Real.exp (-(∑ i, x i ^ 2) / 2))
    _ = ∏ i : Fin (M + 1), ∫ t : ℝ, F i t := by
      simp_rw [hp]
      exact integral_fintype_prod_volume_eq_prod F
    _ = _ := by
      rw [Fin.prod_univ_succ]
      simp only [F, ite_true, Fin.succ_ne_zero, ite_false, one_mul, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
      rw [gauss1]

lemma relu_mul_pos {r : ℝ} (hr : 0 < r) (a : ℝ) : relu (r * a) = r * relu a := by
  unfold relu
  rcases le_total 0 a with h | h
  · rw [max_eq_right h, max_eq_right (mul_nonneg hr.le h)]
  · rw [max_eq_left h, max_eq_left (mul_nonpos_of_nonneg_of_nonpos hr.le h), mul_zero]

lemma relu_gauss : ∫ t : ℝ, relu t * Real.exp (-t ^ 2 / 2) = 1 := by
  have e : (fun t : ℝ => relu t * Real.exp (-t ^ 2 / 2)) =
      (Set.Ioi (0 : ℝ)).indicator (fun t => t ^ 1 * Real.exp (-t ^ 2 / 2)) := by
    funext t
    unfold relu
    by_cases ht : t ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem ht, max_eq_right (le_of_lt ht), pow_one]
    · rw [Set.indicator_of_notMem ht, max_eq_left (not_lt.mp ht), zero_mul]
  rw [e, integral_indicator measurableSet_Ioi]
  exact radI_one

/-- **`c_{M+1} = radI M/(√(2π)·radI (M+1))`.** -/
theorem cN_radial (M : ℕ) : cN (M + 1) = radI M / (√(2 * π) * radI (M + 1)) := by
  let σ := (volume : Measure (EuclideanSpace ℝ (Fin (M + 1)))).toSphere
  have hA : (0 : ℝ) < √(2 * π) := Real.sqrt_pos.2 (by positivity)
  have h1 := polar_hom (M + 1) 1 (by omega) (fun x => relu (x 0))
    (by
      intro u r hr
      simp only [PiLp.smul_apply, smul_eq_mul, pow_one]
      exact relu_mul_pos hr _)
  have h0 := polar_hom (M + 1) 0 (by omega) (fun _ => (1 : ℝ)) (by simp)
  rw [gaussE M relu, relu_gauss, one_mul] at h1
  have hg0 := gaussE M (fun _ => (1 : ℝ))
  simp only [one_mul] at hg0 h0
  rw [gauss1] at hg0
  rw [hg0] at h0
  have ee1 : M + 1 - 1 + 1 = M + 1 := by omega
  have ee0 : M + 1 - 1 + 0 = M := by omega
  rw [ee1] at h1
  rw [ee0] at h0
  change √(2 * π) ^ M = (∫ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin (M + 1))) 1,
    relu (u.1 0) ∂σ) * radI (M + 1) at h1
  have hone : (∫ _u : Metric.sphere (0 : EuclideanSpace ℝ (Fin (M + 1))) 1, (1 : ℝ) ∂σ) =
      σ.real Set.univ := by
    simp [Measure.real]
  change √(2 * π) * √(2 * π) ^ M =
    (∫ _u : Metric.sphere (0 : EuclideanSpace ℝ (Fin (M + 1))) 1, (1 : ℝ) ∂σ) * radI M at h0
  rw [hone] at h0
  have hR1 := radI_pos (M + 1)
  have hR0 := radI_pos M
  have hS : σ.real Set.univ ≠ 0 := by
    intro hs
    rw [hs, zero_mul] at h0
    have : 0 < √(2 * π) * √(2 * π) ^ M := by positivity
    linarith
  have hm : Measurable (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (M + 1))) 1 =>
      WithLp.ofLp x.1) := by fun_prop
  have hc : Continuous (fun u : Fin (M + 1) → ℝ => relu (∑ i, e0 (M + 1) i * u i)) :=
    continuous_relu.comp (continuous_finsetSum _ fun i _ => continuous_const.mul
      (continuous_apply i))
  have hsum : ∀ x : Fin (M + 1) → ℝ, ∑ i, e0 (M + 1) i * x i = x 0 := by
    intro x
    rw [Finset.sum_eq_single (0 : Fin (M + 1))]
    · simp [e0]
    · intro i _ hi
      have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      simp [e0, this]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hcN : cN (M + 1) = (σ.real Set.univ)⁻¹ *
      ∫ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin (M + 1))) 1, relu (u.1 0) ∂σ := by
    unfold cN gfun
    rw [uniformSphere, integral_smul_measure, integral_map hm.aemeasurable
      hc.aestronglyMeasurable]
    simp_rw [hsum]
    change (σ Set.univ)⁻¹.toReal * _ = _
    rw [ENNReal.toReal_inv]
    rfl
  rw [hcN]
  set S1 := ∫ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin (M + 1))) 1, relu (u.1 0) ∂σ
    with hS1
  have hS1v : S1 = √(2 * π) ^ M / radI (M + 1) := by
    rw [eq_div_iff hR1.ne']
    exact h1.symm
  have hσv : σ.real Set.univ = √(2 * π) * √(2 * π) ^ M / radI M := by
    rw [eq_div_iff hR0.ne']
    exact h0.symm
  rw [hS1v, hσv]
  have hAM : (0 : ℝ) < √(2 * π) ^ M := by positivity
  field_simp

/-- **The closed form of `c_N` for even `N`**: `c_{2(k+1)} = π⁻¹·∏_{j=1}^{k} 2j/(2j+1)`. -/
theorem cN_even_succ (k : ℕ) :
    cN (2 * (k + 1)) = π⁻¹ * ∏ j ∈ Finset.Icc 1 k, (2 * (j : ℝ)) / (2 * (j : ℝ) + 1) := by
  have hA : (0 : ℝ) < √(2 * π) := Real.sqrt_pos.2 (by positivity)
  induction k with
  | zero =>
    have e : 2 * (0 + 1) = 1 + 1 := by norm_num
    rw [e, cN_radial 1, radI_one]
    have h2 : radI (1 + 1) = radI 0 := by
      have := radI_step 0
      simpa using this
    rw [h2, radI_zero]
    simp only [Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1), Finset.prod_empty, mul_one]
    rw [← Real.sqrt_mul (by positivity)]
    have h3 : 2 * π * (π / 2) = π ^ 2 := by ring
    rw [h3, Real.sqrt_sq pi_pos.le, one_div]
  | succ k ih =>
    have e : 2 * (k + 1 + 1) = (2 * k + 3) + 1 := by ring
    have e' : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
    rw [e, cN_radial (2 * k + 3)]
    rw [e', cN_radial (2 * k + 1)] at ih
    have s1 : radI (2 * k + 3) = ((2 * k + 1 : ℕ) + 1 : ℝ) * radI (2 * k + 1) := by
      have := radI_step (2 * k + 1)
      simpa using this
    have s2 : radI (2 * k + 3 + 1) = ((2 * k + 2 : ℕ) + 1 : ℝ) * radI (2 * k + 2) := by
      have := radI_step (2 * k + 2)
      simpa using this
    have e2 : 2 * k + 1 + 1 = 2 * k + 2 := by ring
    rw [e2] at ih
    have hprod : π⁻¹ * ∏ j ∈ Finset.Icc 1 (k + 1), (2 * (j : ℝ)) / (2 * (j : ℝ) + 1) =
        radI (2 * k + 1) / (√(2 * π) * radI (2 * k + 2)) *
          (2 * ((k + 1 : ℕ) : ℝ) / (2 * ((k + 1 : ℕ) : ℝ) + 1)) := by
      rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1), ← mul_assoc, ← ih]
    rw [s1, s2, hprod]
    have hR1 := radI_pos (2 * k + 1)
    have hR2 := radI_pos (2 * k + 2)
    push_cast
    field_simp
    ring

/-- **`c_{2n} = π⁻¹·∏_{j=1}^{n−1} 2j/(2j+1)`** for every `n ≥ 1`. -/
theorem cN_even {n : ℕ} (hn : 1 ≤ n) :
    cN (2 * n) = π⁻¹ * ∏ j ∈ Finset.Icc 1 (n - 1), (2 * (j : ℝ)) / (2 * (j : ℝ) + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simpa using cN_even_succ k

/-- The constant of the paper's program against the exact constant: `c̃_N·π̃ = c_N·π`. -/
theorem cNt_eq {n : ℕ} (hn : 1 ≤ n) : cNt n = (piT n)⁻¹ * (π * cN (2 * n)) := by
  rw [cN_even hn]
  unfold cNt
  rw [← mul_assoc π, mul_inv_cancel₀ pi_ne_zero, one_mul]

end BstLean.Part159

open BstLean.Part159 in
#print axioms radI_step
open BstLean.Part159 in
#print axioms radI_one
open BstLean.Part159 in
#print axioms radI_zero
open BstLean.Part159 in
#print axioms cN_radial
open BstLean.Part159 in
#print axioms cN_even
open BstLean.Part159 in
#print axioms cNt_eq
