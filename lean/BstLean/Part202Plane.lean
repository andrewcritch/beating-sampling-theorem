import BstLean.Part202Moment

/-! The actual two-direction Gaussian plane split used by the conditional passes. -/
namespace BstLean.Part202
open MeasureTheory ProbabilityTheory Real Filter Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part170
open BstLean.Part134 (res)
open BstLean.Part157 (cOf)
open BstLean.Part167 (perp)

/-- The coefficient is totalized at a zero direction. -/
noncomputable def planeCoefficient {d : ℕ} (h : Fin d → ℝ) (ξ : Fin 1 → ℝ) : ℝ :=
  (normSq h)⁻¹ * cOf 1 h ξ 0

/-- Reassemble the retained plane and the fresh transverse row. -/
noncomputable def planeAssemble {d : ℕ} (h g : Fin d → ℝ)
    (p : ((Fin 1 → ℝ) × (Fin 1 → ℝ)) × (Fin d → ℝ)) : Fin d → ℝ :=
  planeCoefficient h p.1.1 • h +
    perp h (planeCoefficient (res h g) p.1.2 • res h g + perp (res h g) p.2)

lemma continuous_planeCoefficient {d : ℕ} (h : Fin d → ℝ) :
    Continuous (planeCoefficient h) := by unfold planeCoefficient cOf; fun_prop

lemma continuous_planeAssemble {d : ℕ} (h g : Fin d → ℝ) :
    Continuous (planeAssemble h g) := by
  unfold planeAssemble
  exact ((continuous_planeCoefficient h).comp (continuous_fst.comp continuous_fst)).smul
    continuous_const |>.add ((continuous_perp h).comp
      ((((continuous_planeCoefficient (res h g)).comp (continuous_snd.comp continuous_fst)).smul
        continuous_const).add ((continuous_perp (res h g)).comp continuous_snd)))

/-- The two-direction split restores the whole Gaussian distribution, including zero directions. -/
theorem planeAssemble_gaussian {d : ℕ} (h g : Fin d → ℝ) :
    Measure.map (planeAssemble h g)
      (((stdGauss (Fin 1)).prod (stdGauss (Fin 1))).prod (stdGauss (Fin d))) =
    stdGauss (Fin d) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hm := (continuous_planeAssemble h g).measurable
  rw [lintegral_map hf hm]
  rw [lintegral_prod (fun q => f (planeAssemble h g q)) (hf.comp hm).aemeasurable]
  rw [lintegral_prod (fun ξ => ∫⁻ η, f (planeAssemble h g (ξ, η)) ∂stdGauss (Fin d))
    (hf.comp hm).lintegral_prod_right'.aemeasurable]
  have hp := BstLean.Part167.plane_split_vecMul (q := 1) 1 h g
    (W := fun _ => fun _ => (1 : ℝ)) measurable_const
    (F := fun q => f q.2.2) (hf.comp (measurable_snd.comp measurable_snd))
  have hn : normSq (fun _ : Fin 1 => (1 : ℝ)) = 1 := by simp [normSq]
  simp only [Fin.sum_univ_one, one_mul, hn, Real.sqrt_one, one_smul] at hp
  change (∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ η, f (planeAssemble h g ((ξ₁, ξ₂), η))
    ∂stdGauss (Fin d) ∂stdGauss (Fin 1) ∂stdGauss (Fin 1)) = _
  dsimp only [planeAssemble, planeCoefficient]
  rw [← hp]
  have hvm : Measurable (fun M : Matrix (Fin 1) (Fin d) ℝ =>
      vecMul (fun _ : Fin 1 => (1 : ℝ)) M) :=
    BstLean.Part167.measurable_vecMul_joint.comp (measurable_const.prodMk measurable_id)
  calc _ = ∫⁻ z, f z ∂Measure.map (fun M : Matrix (Fin 1) (Fin d) ℝ =>
        vecMul (fun _ : Fin 1 => (1 : ℝ)) M) (gaussMat 1 d 1) :=
          (lintegral_map hf hvm).symm
    _ = _ := by
      rw [BstLean.Part153.gaussMat_vecMul]
      simp only [hn, Real.sqrt_one, one_mul, one_smul, Measure.map_id']

section
variable {V : Type*} [MeasurableSpace V] {μ : Measure V} [IsProbabilityMeasure μ]
variable {d : ℕ} {a : V → Fin d → ℝ}

/-- The trace agrees with the difference of the two first-layer energy tables. -/
theorem covarianceTrace_eq_energy (ha : Measurable a) {K : ℝ}
    (hK : ∀ v, ‖a v‖ ≤ K) :
    covarianceTrace μ a = (∫ v, normSq (a v) ∂μ) - normSq (vmean μ a) := by
  have i1 : ∀ i : Fin d, Integrable (fun v => a v i) μ :=
    fun i => int_comp_bdd ha hK (continuous_apply i)
  have i2 : ∀ i : Fin d, Integrable (fun v => a v i ^ 2) μ :=
    fun i => int_comp_bdd ha hK ((continuous_apply i).pow 2)
  have ic : ∀ i : Fin d, Integrable (fun v => (a v i - vmean μ a i) ^ 2) μ :=
    fun i => int_comp_bdd ha hK (((continuous_apply i).sub continuous_const).pow 2)
  unfold covarianceTrace BstLean.Part151.TR normSq
  simp only [Pi.sub_apply]
  rw [integral_finsetSum _ fun i _ => ic i]
  have he : ∀ i : Fin d, (∫ v, (a v i - vmean μ a i) ^ 2 ∂μ) =
      (∫ v, a v i ^ 2 ∂μ) - vmean μ a i ^ 2 :=
    fun i => BstLean.Part183.int_sq_sub_mean (i1 i) (i2 i)
  simp_rw [he]
  rw [Finset.sum_sub_distrib, integral_finsetSum _ fun i _ => i2 i]

/-- The retained part of a row at a fixed input. -/
noncomputable def planeRow (μ : Measure V) (a : V → Fin d → ℝ) (h : Fin d → ℝ)
    (ξ : (Fin 1 → ℝ) × (Fin 1 → ℝ)) (v : V) : ℝ :=
  planeCoefficient h ξ.1 * (h ⬝ᵥ a v) +
    planeCoefficient (res h (vmean μ a)) ξ.2 * (res h (vmean μ a) ⬝ᵥ a v)

/-- Supply every field of the conditional-row interface from the established plane split. -/
noncomputable def planeSplit (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    (h : Fin d → ℝ) (ell : ℝ)
    (hCov : ∀ e, ∫ v, (e ⬝ᵥ (a v - vmean μ a)) ^ 2 ∂μ ≤ ell ^ 2 * normSq e) :
    RowSplit μ ((stdGauss (Fin 1)).prod (stdGauss (Fin 1))) a d ell where
  c := planeRow μ a h
  w := fun v => BstLean.Part183.wT μ a h (a v)
  assemble := planeAssemble h (vmean μ a)
  measurable_c := by
    unfold planeRow
    exact (((continuous_planeCoefficient h).measurable.comp
      (measurable_fst.comp measurable_fst)).mul
        (measurable_dot measurable_const (ha.comp measurable_snd))).add
      (((continuous_planeCoefficient (res h (vmean μ a))).measurable.comp
        (measurable_snd.comp measurable_fst)).mul
          (measurable_dot measurable_const (ha.comp measurable_snd)))
  measurable_w := (BstLean.Part183.continuous_wT (μ := μ) a h).measurable.comp ha
  bounded_c := by
    intro ξ
    have hc : Continuous (fun y : Fin d → ℝ =>
        planeCoefficient h ξ.1 * (h ⬝ᵥ y) +
          planeCoefficient (res h (vmean μ a)) ξ.2 * (res h (vmean μ a) ⬝ᵥ y)) := by
      fun_prop
    obtain ⟨C, hC⟩ := BstLean.Part184.bdd_comp hK hc
    exact ⟨C, fun v => by simpa only [planeRow, Real.norm_eq_abs] using hC v⟩
  bounded_w := BstLean.Part184.bdd_comp hK (BstLean.Part183.continuous_wT (μ := μ) a h)
  mean_w := BstLean.Part184.wT_mean ha hK h
  covariance_w := BstLean.Part184.wT_cov (sq_nonneg ell) hCov h
  measurable_assemble := (continuous_planeAssemble h (vmean μ a)).measurable
  gaussian_assemble := planeAssemble_gaussian h (vmean μ a)
  row_identity := by
    intro ξ η v
    unfold planeRow planeAssemble BstLean.Part183.wT
    rw [BstLean.Part167.perp_plane, add_dotProduct, smul_dotProduct,
      add_dotProduct, smul_dotProduct, perp_dot, perp_dot]
    ring

/-- The paper conditional plane row satisfies the sharp variance bound. -/
theorem plane_row_variance (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    (h : Fin d → ℝ) (ell : ℝ)
    (hCov : ∀ e, ∫ v, (e ⬝ᵥ (a v - vmean μ a)) ^ 2 ∂μ ≤ ell ^ 2 * normSq e) :
    ∫⁻ q, ENNReal.ofReal (|rowFluct (planeSplit ha hK h ell hCov) q| ^ 2)
      ∂(((stdGauss (Fin 1)).prod (stdGauss (Fin 1))).prod (stdGauss (Fin d))) ≤
      ENNReal.ofReal (2 * ell ^ 2 * covarianceTrace μ a) :=
  row_variance (planeSplit ha hK h ell hCov) ha hK

/-- The paper conditional plane row satisfies every factorial moment bound. -/
theorem plane_row_factorial (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    (h : Fin d → ℝ) (ell : ℝ)
    (hCov : ∀ e, ∫ v, (e ⬝ᵥ (a v - vmean μ a)) ^ 2 ∂μ ≤ ell ^ 2 * normSq e)
    (k : ℕ) (hk : 3 ≤ k) :
    ∫⁻ q, ENNReal.ofReal (|rowFluct (planeSplit ha hK h ell hCov) q| ^ k)
      ∂(((stdGauss (Fin 1)).prod (stdGauss (Fin 1))).prod (stdGauss (Fin d))) ≤
      ENNReal.ofReal ((k.factorial : ℝ) * beta ^ (k - 2) * rowScale μ a ell ^ k) :=
  row_factorial_moment (planeSplit ha hK h ell hCov) ha hK k hk

end
end BstLean.Part202
