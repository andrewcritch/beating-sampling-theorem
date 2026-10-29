import BstLean.Part158Basic

/-!
# Part 158 (file `Theta`): the derivative in `θ` of the interpolation

Do not use `sorry`, `native_decide` or `axiom`.

`dthU dF c s x ξ = E_{ξ'} Σ_k (dF x (c ξ + s ξ'))_k (−s ξ_k + c ξ'_k)` is the derivative of
`θ ↦ U F (cos θ) (sin θ) x ξ`. Three differentiations under an integral give the derivative of
`θ ↦ Psi μ L F (cos θ) (sin θ)` (`Fam.Psi_theta`).
-/

namespace BstLean.Part158

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)

variable {X : Type*} [MeasurableSpace X] {ι : Type} [Fintype ι]
  {F : X → (ι → ℝ) → ℝ} {dF : X → (ι → ℝ) → ι → ℝ} {a b C : ℝ}

/-- The sum of the absolute values of the coordinates. -/
noncomputable def N1 (ξ : ι → ℝ) : ℝ := ∑ k, |ξ k|

lemma N1_nonneg (ξ : ι → ℝ) : 0 ≤ N1 ξ := Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma measurable_N1 : Measurable (N1 : (ι → ℝ) → ℝ) :=
  Finset.measurable_sum _ fun k _ => (measurable_pi_apply k).abs

lemma integrable_N1 : Integrable (N1 : (ι → ℝ) → ℝ) (stdGauss ι) :=
  integrable_finsetSum _ fun k _ => (BstLean.Part152.integrable_coord k).abs

/-- The integrand of `dthU`. -/
noncomputable def dthI (dF : X → (ι → ℝ) → ι → ℝ) (c s : ℝ) (x : X) (ξ ξ' : ι → ℝ) : ℝ :=
  ∑ k, dF x (c • ξ + s • ξ') k * (-s * ξ k + c * ξ' k)

/-- The derivative of `θ ↦ U F (cos θ) (sin θ) x ξ`. -/
noncomputable def dthU (dF : X → (ι → ℝ) → ι → ℝ) (c s : ℝ) (x : X) (ξ : ι → ℝ) : ℝ :=
  ∫ ξ', dthI dF c s x ξ ξ' ∂stdGauss ι

lemma Fam.dthI_le (h : Fam F dF a b C) {c s : ℝ} (hc : |c| ≤ 1) (hs : |s| ≤ 1) (x : X)
    (ξ ξ' : ι → ℝ) : |dthI dF c s x ξ ξ'| ≤ C * (N1 ξ + N1 ξ') := by
  unfold dthI N1
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  have h1 := h.hC x (c • ξ + s • ξ') k
  have hC : 0 ≤ C := (abs_nonneg _).trans h1
  have h2 : |-s * ξ k + c * ξ' k| ≤ |ξ k| + |ξ' k| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_neg]
    have := mul_le_mul_of_nonneg_right hs (abs_nonneg (ξ k))
    have := mul_le_mul_of_nonneg_right hc (abs_nonneg (ξ' k))
    linarith
  exact mul_le_mul h1 h2 (abs_nonneg _) hC

lemma Fam.measurable_dthI3 (h : Fam F dF a b C) (c s : ℝ) :
    Measurable (fun p : (X × (ι → ℝ)) × (ι → ℝ) => dthI dF c s p.1.1 p.1.2 p.2) := by
  unfold dthI
  refine Finset.measurable_sum _ fun k _ => (h.mdF3 c s k).mul ?_
  exact (((measurable_pi_apply k).comp (measurable_snd.comp measurable_fst)).const_mul _).add
    (((measurable_pi_apply k).comp measurable_snd).const_mul _)

lemma Fam.measurable_dthI (h : Fam F dF a b C) (c s : ℝ) (x : X) (ξ : ι → ℝ) :
    Measurable (fun ξ' => dthI dF c s x ξ ξ') :=
  (h.measurable_dthI3 c s).comp
    (measurable_const.prodMk measurable_id : Measurable fun ξ' : ι → ℝ => ((x, ξ), ξ'))

lemma Fam.measurable_dthU (h : Fam F dF a b C) (c s : ℝ) :
    Measurable (fun p : X × (ι → ℝ) => dthU dF c s p.1 p.2) :=
  ((h.measurable_dthI3 c s).stronglyMeasurable.integral_prod_right' (ν := stdGauss ι)).measurable

/-- `E N1`. -/
noncomputable def EN1 (ι : Type) [Fintype ι] : ℝ := ∫ ξ : ι → ℝ, N1 ξ ∂stdGauss ι

lemma EN1_nonneg : 0 ≤ EN1 ι := integral_nonneg fun ξ => N1_nonneg ξ

lemma Fam.integrable_dthI (h : Fam F dF a b C) {c s : ℝ} (hc : |c| ≤ 1) (hs : |s| ≤ 1) (x : X)
    (ξ : ι → ℝ) : Integrable (fun ξ' => dthI dF c s x ξ ξ') (stdGauss ι) :=
  Integrable.mono' (((integrable_const (N1 ξ)).add integrable_N1).const_mul C)
    (h.measurable_dthI c s x ξ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ' => by
      rw [Real.norm_eq_abs]; exact h.dthI_le hc hs x ξ ξ')

lemma Fam.dthU_le (h : Fam F dF a b C) {c s : ℝ} (hc : |c| ≤ 1) (hs : |s| ≤ 1) (x : X)
    (ξ : ι → ℝ) : |dthU dF c s x ξ| ≤ C * (N1 ξ + EN1 ι) := by
  unfold dthU
  refine (abs_integral_le_integral_abs).trans ?_
  have := integral_mono (h.integrable_dthI hc hs x ξ).abs
    (((integrable_const (N1 ξ)).add integrable_N1).const_mul C)
    (fun ξ' => h.dthI_le hc hs x ξ ξ')
  refine this.trans (le_of_eq ?_)
  rw [integral_const_mul]
  simp only [Pi.add_apply]
  rw [integral_add (integrable_const _) integrable_N1]
  simp [EN1]

/-- The derivative of `F x` along the path `cos θ · ξ + sin θ · ξ'`. -/
lemma Fam.path_deriv (h : Fam F dF a b C) (x : X) (ξ ξ' : ι → ℝ) (θ : ℝ) :
    HasDerivAt (fun θ => F x (cos θ • ξ + sin θ • ξ')) (dthI dF (cos θ) (sin θ) x ξ ξ') θ := by
  have hγ : HasDerivAt (fun θ : ℝ => cos θ • ξ + sin θ • ξ') (-sin θ • ξ + cos θ • ξ') θ :=
    ((hasDerivAt_cos θ).smul_const ξ).add ((hasDerivAt_sin θ).smul_const ξ')
  have key : HasDerivAt (fun θ => F x (cos θ • ξ + sin θ • ξ'))
      (dotL (dF x (cos θ • ξ + sin θ • ξ')) (-sin θ • ξ + cos θ • ξ')) θ :=
    (h.hd x (cos θ • ξ + sin θ • ξ')).comp_hasDerivAt θ hγ
  rw [dotL_apply] at key
  convert key using 1
  simp [dthI]

/-- **The derivative of `U` in `θ`.** -/
theorem Fam.U_theta (h : Fam F dF a b C) (x : X) (ξ : ι → ℝ) (θ : ℝ) :
    HasDerivAt (fun θ => U F (cos θ) (sin θ) x ξ) (dthU dF (cos θ) (sin θ) x ξ) θ := by
  unfold U dthU
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := stdGauss ι)
    (F := fun θ ξ' => F x (cos θ • ξ + sin θ • ξ'))
    (F' := fun θ ξ' => dthI dF (cos θ) (sin θ) x ξ ξ')
    (bound := fun ξ' => C * (N1 ξ + N1 ξ')) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun θ => (h.integrable_F _ _ x ξ).aestronglyMeasurable)
    (h.integrable_F _ _ x ξ) (h.measurable_dthI _ _ x ξ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ' θ _ => ?_)
    (((integrable_const (N1 ξ)).add integrable_N1).const_mul C)
    (Filter.Eventually.of_forall fun ξ' θ _ => h.path_deriv x ξ ξ' θ)).2
  rw [Real.norm_eq_abs]
  exact h.dthI_le (abs_cos_le_one θ) (abs_sin_le_one θ) x ξ ξ'

/-- The derivative of `T` in `θ`. -/
noncomputable def dthT (μ : Measure X) (L : ℝ) (F : X → (ι → ℝ) → ℝ) (dF : X → (ι → ℝ) → ι → ℝ)
    (c s : ℝ) (ξ : ι → ℝ) : ℝ :=
  L⁻¹ * ∫ x, dthU dF c s x ξ / U F c s x ξ ∂μ

lemma Fam.ratio_le (h : Fam F dF a b C) {c s : ℝ} (hc : |c| ≤ 1) (hs : |s| ≤ 1) (x : X)
    (ξ : ι → ℝ) : |dthU dF c s x ξ / U F c s x ξ| ≤ C * (N1 ξ + EN1 ι) / a := by
  rw [abs_div, abs_of_pos (h.U_pos c s x ξ)]
  have h1 := h.dthU_le hc hs x ξ
  exact div_le_div₀ ((abs_nonneg _).trans h1) h1 h.ha (h.U_lo c s x ξ)

lemma Fam.measurable_ratio (h : Fam F dF a b C) (c s : ℝ) :
    Measurable (fun p : X × (ι → ℝ) => dthU dF c s p.1 p.2 / U F c s p.1 p.2) :=
  (h.measurable_dthU c s).div (h.measurable_U c s)

lemma Fam.measurable_dthT (h : Fam F dF a b C) (μ : Measure X) [SFinite μ] (L c s : ℝ) :
    Measurable (dthT μ L F dF c s) := by
  have h1 : Measurable (fun p : (ι → ℝ) × X => dthU dF c s p.2 p.1 / U F c s p.2 p.1) :=
    (h.measurable_ratio c s).comp measurable_swap
  exact (h1.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable.const_mul _

lemma Fam.integrable_ratio (h : Fam F dF a b C) (μ : Measure X) [IsFiniteMeasure μ] {c s : ℝ}
    (hc : |c| ≤ 1) (hs : |s| ≤ 1) (ξ : ι → ℝ) :
    Integrable (fun x => dthU dF c s x ξ / U F c s x ξ) μ :=
  Integrable.of_bound ((h.measurable_ratio c s).comp measurable_prodMk_right).aestronglyMeasurable
    (C * (N1 ξ + EN1 ι) / a) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact h.ratio_le hc hs x ξ)

lemma Fam.dthT_le (h : Fam F dF a b C) (μ : Measure X) [IsFiniteMeasure μ] (L : ℝ) {c s : ℝ}
    (hc : |c| ≤ 1) (hs : |s| ≤ 1) (ξ : ι → ℝ) :
    |dthT μ L F dF c s ξ| ≤ |L⁻¹| * (C * (N1 ξ + EN1 ι) / a * μ.real Set.univ) := by
  unfold dthT
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (abs_integral_le_integral_abs).trans ?_
  have := integral_mono (h.integrable_ratio μ hc hs ξ).abs
    (integrable_const (C * (N1 ξ + EN1 ι) / a)) (fun x => h.ratio_le hc hs x ξ)
  simpa [mul_comm] using this

/-- **The derivative of `T` in `θ`.** -/
theorem Fam.T_theta (h : Fam F dF a b C) (μ : Measure X) [IsFiniteMeasure μ] (L : ℝ)
    (ξ : ι → ℝ) (θ : ℝ) :
    HasDerivAt (fun θ => T μ L F (cos θ) (sin θ) ξ) (dthT μ L F dF (cos θ) (sin θ) ξ) θ := by
  unfold T dthT
  refine HasDerivAt.const_mul _ ?_
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun θ x => log (U F (cos θ) (sin θ) x ξ))
    (F' := fun θ x => dthU dF (cos θ) (sin θ) x ξ / U F (cos θ) (sin θ) x ξ)
    (bound := fun _ => C * (N1 ξ + EN1 ι) / a) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun θ => (h.integrable_logU μ _ _ ξ).aestronglyMeasurable)
    (h.integrable_logU μ _ _ ξ)
    ((h.measurable_ratio _ _).comp measurable_prodMk_right).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x θ _ => ?_) (integrable_const _)
    (Filter.Eventually.of_forall fun x θ _ => ?_)).2
  · rw [Real.norm_eq_abs]
    exact h.ratio_le (abs_cos_le_one θ) (abs_sin_le_one θ) x ξ
  · exact (h.U_theta x ξ θ).log (h.U_pos _ _ x ξ).ne'

/-- **The derivative of `Psi` in `θ`, first form.** -/
theorem Fam.Psi_theta (h : Fam F dF a b C) (μ : Measure X) [IsFiniteMeasure μ] (L θ : ℝ) :
    HasDerivAt (fun θ => Psi μ L F (cos θ) (sin θ))
      (∫ ξ, exp (T μ L F (cos θ) (sin θ) ξ) * dthT μ L F dF (cos θ) (sin θ) ξ ∂stdGauss ι) θ := by
  unfold Psi
  set M := |L⁻¹| * ((|log a| + |log b|) * μ.real Set.univ) with hM
  have iE : ∀ θ : ℝ, Integrable (fun ξ => exp (T μ L F (cos θ) (sin θ) ξ)) (stdGauss ι) :=
    fun θ => Integrable.of_bound (h.measurable_T μ L _ _).exp.aestronglyMeasurable (exp M)
      (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact exp_le_exp.mpr ((le_abs_self _).trans (h.T_le μ L _ _ ξ)))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := stdGauss ι)
    (F := fun θ ξ => exp (T μ L F (cos θ) (sin θ) ξ))
    (F' := fun θ ξ => exp (T μ L F (cos θ) (sin θ) ξ) * dthT μ L F dF (cos θ) (sin θ) ξ)
    (bound := fun ξ => exp M * (|L⁻¹| * (C * (N1 ξ + EN1 ι) / a * μ.real Set.univ)))
    (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun θ => (iE θ).aestronglyMeasurable) (iE θ)
    ((h.measurable_T μ L _ _).exp.mul (h.measurable_dthT μ L _ _)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ θ _ => ?_) ?_
    (Filter.Eventually.of_forall fun ξ θ _ => (h.T_theta μ L ξ θ).exp)).2
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact mul_le_mul (exp_le_exp.mpr ((le_abs_self _).trans (h.T_le μ L _ _ ξ)))
      (h.dthT_le μ L (abs_cos_le_one θ) (abs_sin_le_one θ) ξ) (abs_nonneg _) (exp_pos _).le
  · refine Integrable.const_mul (Integrable.const_mul ?_ _) _
    refine Integrable.mul_const (Integrable.div_const (Integrable.const_mul ?_ _) _) _
    exact integrable_N1.add (integrable_const _)

end BstLean.Part158

open BstLean.Part158 in
#print axioms Fam.Psi_theta
