import BstLean.Part29ExactFormula
import BstLean.Part29Parity
import BstLean.Part29GaussProd
import BstLean.Part29Gauss

/-!
# Part 29: the uniform law on the sphere has the moments the proof assumes

`uniformSphere n` is the uniform probability measure on the Euclidean unit sphere of `ℝⁿ`: the normalized
`toSphere` of Lebesgue measure on `EuclideanSpace ℝ (Fin n)`, moved to `Fin n → ℝ`. (It is built on the
Euclidean space because the norm on `Fin n → ℝ` is the sup norm, whose unit sphere is a cube.) This file
proves `SphereMoments` and `SphereParity` for it, which discharges the last hypotheses of part 29.

Plan (`delegations/answers/sphere-moments-scout-opus.md`): one formula
`∫ ∏ x (τ s) = (∏ᵢ gaussMom cᵢ) · R₀ / R_r`, `R_k = ∫_{Ioi 0} ρ^{n−1+k} e^{−ρ²/2}`, `R_{k+2} = (n+k) R_k`, from the
polar decomposition `measurePreserving_homeomorphUnitSphereProd` against the Gaussian weight.
-/

namespace BstLean.Part29

open MeasureTheory

/-- The uniform probability measure on the Euclidean unit sphere, on `Fin n → ℝ`. -/
noncomputable def uniformSphere (n : ℕ) : Measure (Fin n → ℝ) :=
  let σ := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
  (σ Set.univ)⁻¹ • σ.map (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => WithLp.ofLp x.1)

private lemma polar_homogeneous (n k : ℕ) (hn : 1 ≤ n) (P : EuclideanSpace ℝ (Fin n) → ℝ)
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

private lemma weighted_gauss_moment (k : ℕ) :
    (∫ x : ℝ, x ^ k * Real.exp (-x ^ 2 / 2)) =
      Real.sqrt (2 * Real.pi) * gaussMom k := by
  have h := gaussMom_eq k
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul (by norm_num),
    ProbabilityTheory.gaussianPDFReal_def] at h
  simp only [NNReal.coe_one, mul_one, sub_zero, smul_eq_mul] at h
  simp_rw [show ∀ x : ℝ, (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) * x ^ k =
    (Real.sqrt (2 * Real.pi))⁻¹ * (x ^ k * Real.exp (-x ^ 2 / 2)) by intro x; ring] at h
  rw [integral_const_mul] at h
  have hs : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  calc
    _ = Real.sqrt (2 * Real.pi) *
        ((Real.sqrt (2 * Real.pi))⁻¹ * ∫ x : ℝ, x ^ k * Real.exp (-x ^ 2 / 2)) := by
      rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
    _ = _ := by rw [h]

private lemma weighted_prod_moment (n r : ℕ) (τ : Fin r → Fin n) :
    (∫ x : EuclideanSpace ℝ (Fin n), (∏ s, x (τ s)) * Real.exp (-‖x‖ ^ 2 / 2)) =
      Real.sqrt (2 * Real.pi) ^ n *
        ∏ i, gaussMom (Finset.univ.filter (fun s => τ s = i)).card := by
  classical
  have hp (x : Fin n → ℝ) : (∏ s, x (τ s)) * Real.exp (-(∑ i, x i ^ 2) / 2) =
      ∏ i, x i ^ (Finset.univ.filter (fun s => τ s = i)).card *
        Real.exp (-x i ^ 2 / 2) := by
    rw [show (∏ s, x (τ s)) = ∏ i, x i ^ (Finset.univ.filter (fun s => τ s = i)).card
      by simpa using (Finset.prod_fiberwise' Finset.univ τ x).symm]
    rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    congr 2
    simp only [neg_div, Finset.sum_div, Finset.sum_neg_distrib]
  calc
    _ = ∫ x : Fin n → ℝ, (∏ s, x (τ s)) * Real.exp (-(∑ i, x i ^ 2) / 2) := by
      simpa only [EuclideanSpace.real_norm_sq_eq] using
        (PiLp.volume_preserving_ofLp (Fin n)).integral_comp
          (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding
          (fun x : Fin n → ℝ => (∏ s, x (τ s)) * Real.exp (-(∑ i, x i ^ 2) / 2))
    _ = ∏ i : Fin n, ∫ x : ℝ,
        x ^ (Finset.univ.filter (fun s => τ s = i)).card * Real.exp (-x ^ 2 / 2) := by
      simp_rw [hp]
      exact integral_fintype_prod_volume_eq_prod (fun (i : Fin n) (x : ℝ) =>
        x ^ (Finset.univ.filter (fun s => τ s = i)).card * Real.exp (-x ^ 2 / 2))
    _ = _ := by
      simp_rw [weighted_gauss_moment]
      rw [Finset.prod_mul_distrib]
      simp

private lemma radial_value (n k : ℕ) (hn : 1 ≤ n) :
    (∫ r in Set.Ioi (0 : ℝ), r ^ (n - 1 + k) * Real.exp (-r ^ 2 / 2)) =
      (1 / 2 : ℝ) ^ (-((n + k : ℕ) : ℝ) / 2) * (1 / 2) *
        Real.Gamma (((n + k : ℕ) : ℝ) / 2) := by
  have hc : ((n - 1 + k : ℕ) : ℝ) + 1 = ((n + k : ℕ) : ℝ) := by
    exact_mod_cast (show n - 1 + k + 1 = n + k by omega)
  convert integral_rpow_mul_exp_neg_mul_rpow
    (p := 2) (q := ((n - 1 + k : ℕ) : ℝ)) (b := 1 / 2)
    (by norm_num) (by exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _))
    (by norm_num) using 1
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp only [Real.rpow_natCast, Real.rpow_two]
    congr 2
    ring
  · rw [hc]

private lemma radial_pos (n k : ℕ) (hn : 1 ≤ n) :
    0 < ∫ r in Set.Ioi (0 : ℝ), r ^ (n - 1 + k) * Real.exp (-r ^ 2 / 2) := by
  rw [radial_value n k hn]
  have hg : 0 < Real.Gamma (((n + k : ℕ) : ℝ) / 2) :=
    Real.Gamma_pos_of_pos (div_pos (by exact_mod_cast (show 0 < n + k by omega))
      (by norm_num))
  positivity

private lemma radial_step (n k : ℕ) (hn : 1 ≤ n) :
    (∫ r in Set.Ioi (0 : ℝ), r ^ (n - 1 + (k + 2)) * Real.exp (-r ^ 2 / 2)) =
      (n + k : ℝ) * ∫ r in Set.Ioi (0 : ℝ),
        r ^ (n - 1 + k) * Real.exp (-r ^ 2 / 2) := by
  rw [radial_value n (k + 2) hn, radial_value n k hn]
  have ha : (((n + (k + 2) : ℕ) : ℝ) / 2) = ((n + k : ℕ) : ℝ) / 2 + 1 := by
    push_cast
    ring
  rw [ha, Real.Gamma_add_one
    (ne_of_gt (div_pos (by exact_mod_cast (show 0 < n + k by omega)) (by norm_num)))]
  have hb : -((n + (k + 2) : ℕ) : ℝ) / 2 = -((n + k : ℕ) : ℝ) / 2 + (-1) := by
    push_cast
    ring
  rw [hb, Real.rpow_add (by norm_num), Real.rpow_neg_one]
  norm_num
  ring

theorem uniformSphere_isProbability (n : ℕ) (hn : 1 ≤ n) : IsProbabilityMeasure (uniformSphere n) := by
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let σ := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
  have hm : Measurable (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      WithLp.ofLp x.1) := by fun_prop
  have hzero : σ Set.univ ≠ 0 := by
    exact (Measure.measure_univ_ne_zero).2 (Measure.toSphere_ne_zero volume)
  refine ⟨?_⟩
  simp only [uniformSphere, Measure.smul_apply, Measure.map_apply hm MeasurableSet.univ,
    Set.preimage_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hzero (measure_ne_top σ Set.univ)

/-- It is supported on the Euclidean unit sphere. -/
theorem uniformSphere_ae_sphere (n : ℕ) :
    ∀ᵐ x ∂(uniformSphere n), ∑ i, x i ^ 2 = 1 := by
  let σ := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
  have hm : Measurable (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      WithLp.ofLp x.1) := by fun_prop
  apply Measure.ae_smul_measure
  apply (ae_map_iff hm.aemeasurable
    (measurableSet_eq_fun
      (by fun_prop : Measurable (fun x : Fin n → ℝ => ∑ i, x i ^ 2))
      measurable_const)).2
  apply ae_of_all
  intro x
  have hx : ‖x.1‖ = 1 := by simp
  simpa [hx] using (EuclideanSpace.real_norm_sq_eq x.1).symm

private lemma sphere_prod_integrable (n r : ℕ) (hn : 1 ≤ n) (τ : Fin r → Fin n) :
    Integrable (fun x : Fin n → ℝ => ∏ s, x (τ s)) (uniformSphere n) := by
  let σ := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
  have hm : Measurable (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      WithLp.ofLp x.1) := by fun_prop
  have hz : σ Set.univ ≠ 0 := by
    let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    exact (Measure.measure_univ_ne_zero).2 (Measure.toSphere_ne_zero volume)
  apply Integrable.smul_measure _ (ENNReal.inv_ne_top.mpr hz)
  apply (integrable_map_measure
    ((by fun_prop : Continuous (fun x : Fin n → ℝ => ∏ s, x (τ s))).aestronglyMeasurable)
    hm.aemeasurable).2
  apply Integrable.of_bound
    ((by fun_prop : Continuous (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      ∏ s, x.1 (τ s))).aestronglyMeasurable) 1
  apply ae_of_all
  intro x
  change ‖∏ s, x.1 (τ s)‖ ≤ 1
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro s hs
    positivity
  · intro s hs
    have hx : ‖x.1‖ = 1 := by simp
    exact (PiLp.norm_apply_le x.1 (τ s)).trans_eq hx

private lemma sphere_prod_moment (n r : ℕ) (hn : 1 ≤ n) (τ : Fin r → Fin n) :
    (∫ x, ∏ s, x (τ s) ∂uniformSphere n) =
      (∏ i, gaussMom (Finset.univ.filter (fun s => τ s = i)).card) *
      (∫ ρ in Set.Ioi (0 : ℝ), ρ ^ (n - 1) * Real.exp (-ρ ^ 2 / 2)) /
      (∫ ρ in Set.Ioi (0 : ℝ), ρ ^ (n - 1 + r) * Real.exp (-ρ ^ 2 / 2)) := by
  classical
  let σ := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
  let R := fun k : ℕ => ∫ ρ in Set.Ioi (0 : ℝ),
    ρ ^ (n - 1 + k) * Real.exp (-ρ ^ 2 / 2)
  let A := Real.sqrt (2 * Real.pi) ^ n
  have hpol := polar_homogeneous n r hn (fun x => ∏ s, x (τ s))
    (by
      intro u ρ hρ
      simp only [PiLp.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin])
  have hprod : A * (∏ i, gaussMom (Finset.univ.filter (fun s => τ s = i)).card) =
      (∫ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, ∏ s, u.1 (τ s) ∂σ) *
        R r := by
    rw [← weighted_prod_moment n r τ]
    exact hpol
  have hzero := polar_homogeneous n 0 hn (fun _ => (1 : ℝ)) (by simp)
  have hnorm : A = σ.real Set.univ * R 0 := by
    have hg := weighted_prod_moment n 0 (fun s => Fin.elim0 s)
    simpa [A, R, σ, gaussMom] using hg.symm.trans hzero
  have hA : A ≠ 0 := by dsimp [A]; positivity
  have hS : σ.real Set.univ ≠ 0 := by
    intro hs
    rw [hs, zero_mul] at hnorm
    exact hA hnorm
  have hR : R r ≠ 0 := ne_of_gt (radial_pos n r hn)
  have hm : Measurable (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      WithLp.ofLp x.1) := by fun_prop
  rw [uniformSphere, integral_smul_measure, integral_map hm.aemeasurable
    ((by fun_prop : Continuous (fun x : Fin n → ℝ => ∏ s, x (τ s))).aestronglyMeasurable)]
  change (σ Set.univ)⁻¹.toReal *
    (∫ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, ∏ s, u.1 (τ s) ∂σ) = _
  rw [ENNReal.toReal_inv]
  change (σ.real Set.univ)⁻¹ * _ = _
  change _ = (∏ i, gaussMom (Finset.univ.filter (fun s => τ s = i)).card) * R 0 / R r
  apply (eq_div_iff hR).2
  rw [mul_assoc, ← hprod, hnorm]
  field_simp

private lemma radial_even (n j : ℕ) (hn : 1 ≤ n) :
    (∫ ρ in Set.Ioi (0 : ℝ), ρ ^ (n - 1 + 2 * j) * Real.exp (-ρ ^ 2 / 2)) =
      (∏ a ∈ Finset.range j, (n + 2 * a : ℝ)) *
        ∫ ρ in Set.Ioi (0 : ℝ), ρ ^ (n - 1) * Real.exp (-ρ ^ 2 / 2) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, radial_step n (2 * j) hn, ih,
      Finset.prod_range_succ]
    push_cast
    ring

private lemma sphere_prod_odd (n r : ℕ) (hn : 1 ≤ n) (τ : Fin r → Fin n)
    (ho : ∃ i, Odd (Finset.univ.filter (fun s => τ s = i)).card) :
    (∫ x, ∏ s, x (τ s) ∂uniformSphere n) = 0 := by
  classical
  rw [sphere_prod_moment n r hn τ]
  obtain ⟨i, hi⟩ := ho
  have he : ¬Even (Finset.univ.filter (fun s => τ s = i)).card := Nat.not_even_iff_odd.mpr hi
  have hz : (∏ i, gaussMom (Finset.univ.filter (fun s => τ s = i)).card) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp [gaussMom, he])
  rw [hz, zero_mul, zero_div]

private lemma sphere_prod_even (n j : ℕ) (hn : 1 ≤ n) (τ : Fin (2 * j) → Fin n) :
    (∫ x, ∏ s, x (τ s) ∂uniformSphere n) =
      (∏ i, gaussMom (Finset.univ.filter (fun s => τ s = i)).card) /
        ∏ a ∈ Finset.range j, (n + 2 * a : ℝ) := by
  rw [sphere_prod_moment n (2 * j) hn τ, radial_even n j hn]
  exact mul_div_mul_right _ _ (ne_of_gt (by simpa using radial_pos n 0 hn))

private lemma count_three {n : ℕ} (a b c i : Fin n) :
    (Finset.univ.filter (fun s : Fin 3 => (![a, b, c] : Fin 3 → Fin n) s = i)).card =
      (if a = i then 1 else 0) + (if b = i then 1 else 0) + (if c = i then 1 else 0) := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero, add_assoc]
  rfl

theorem uniformSphere_moments (n : ℕ) (hn : 1 ≤ n) : SphereMoments n (uniformSphere n) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa using sphere_prod_integrable n 1 hn ![i]
  · intro i j
    simpa [Fin.prod_univ_two] using sphere_prod_integrable n 2 hn ![i, j]
  · intro i j k
    simpa [Fin.prod_univ_succ, mul_assoc] using sphere_prod_integrable n 3 hn ![i, j, k]
  · intro i j k l
    simpa [Fin.prod_univ_succ, mul_assoc] using sphere_prod_integrable n 4 hn ![i, j, k, l]
  · intro i
    have ho : ∃ a, Odd (Finset.univ.filter (fun s : Fin 1 => (![i] : Fin 1 → Fin n) s = a)).card :=
      ⟨i, by simp⟩
    simpa using sphere_prod_odd n 1 hn ![i] ho
  · intro i j
    have hg := (gaussMoments_std (D := n)).m2 i j
    have hp := gaussProd_moment n 2 ![i, j]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hp
    rw [hg] at hp
    have hs := sphere_prod_even n 1 hn ![i, j]
    simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.prod_univ_zero, mul_one] at hs
    rw [← hp] at hs
    by_cases hij : i = j <;>
      simpa [hij, Finset.prod_range_succ, Finset.prod_range_zero] using hs
  · intro i j k
    have ho : ∃ a, Odd (Finset.univ.filter
        (fun s : Fin 3 => (![i, j, k] : Fin 3 → Fin n) s = a)).card := by
      by_cases hij : i = j
      · subst j
        by_cases hik : i = k
        · subst k
          refine ⟨i, ?_⟩
          rw [count_three]
          norm_num
        · refine ⟨k, ?_⟩
          simp [count_three, hik]
      · by_cases hik : i = k
        · subst k
          refine ⟨j, ?_⟩
          simp [count_three, hij]
        · refine ⟨i, ?_⟩
          simp [count_three, Ne.symm hij, Ne.symm hik]
    simpa [Fin.prod_univ_succ, mul_assoc] using sphere_prod_odd n 3 hn ![i, j, k] ho
  · intro i j k l
    have hg := (gaussMoments_std (D := n)).m4 i j k l
    have hp := gaussProd_moment n 4 ![i, j, k, l]
    simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.prod_univ_zero, mul_one, ← mul_assoc] at hp
    rw [hg] at hp
    have hs := sphere_prod_even n 2 hn ![i, j, k, l]
    simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.prod_univ_zero, mul_one, ← mul_assoc] at hs
    rw [← hp] at hs
    simpa [Finset.prod_range_succ, Finset.prod_range_zero] using hs

theorem uniformSphere_parity (n : ℕ) (hn : 1 ≤ n) :
    SphereParity n (uniformSphere n) (1 / ((n : ℝ) * (n + 2) * (n + 4) * (n + 6))) := by
  classical
  refine ⟨fun r _ τ => sphere_prod_integrable n r hn τ,
    fun r _ τ ho => sphere_prod_odd n r hn τ ho, ?_⟩
  intro σ hσ
  let τ : Fin 8 → Fin n := Fin.append σ σ
  have hp (x : Fin n → ℝ) : (∏ s, x (τ s)) = ∏ s, x (σ s) ^ 2 := by
    change (∏ s : Fin (4 + 4), x (Fin.append σ σ s)) = _
    rw [Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [← Finset.prod_mul_distrib]
    simp [pow_two]
  have hc (i : Fin n) : (Finset.univ.filter (fun s => τ s = i)).card =
      2 * (Finset.univ.filter (fun s => σ s = i)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    change (∑ s : Fin (4 + 4), if Fin.append σ σ s = i then 1 else 0) = _
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    omega
  have hg : (∏ i, gaussMom (Finset.univ.filter (fun s => τ s = i)).card) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    rw [hc]
    by_cases he : ∃ s, σ s = i
    · obtain ⟨s, hs⟩ := he
      have hf : (Finset.univ.filter (fun t => σ t = i)) = {s} := by
        ext t
        simp [← hs, hσ.eq_iff]
      simp [hf, gaussMom, Nat.doubleFactorial]
    · have hf : (Finset.univ.filter (fun t => σ t = i)) = ∅ := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]
        exact fun ht => he ⟨t, ht⟩
      simp [hf, gaussMom]
  have hs := sphere_prod_even n 4 hn τ
  rw [hg] at hs
  simp_rw [hp] at hs
  norm_num [Finset.prod_range_succ, Finset.prod_range_zero, mul_assoc] at hs ⊢
  exact hs

end BstLean.Part29
