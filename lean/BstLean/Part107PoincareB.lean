import BstLean.Part107PoincareA

/-!
# Part 107, Gaussian Poincaré inequality, file B: the energy bound along the rotation path
`E (f(X_a) − f(X))² ≤ a² ∫ Γ dγ`.
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part48 (rotX rotY rot_preserving)
open BstLean.Part105

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `Φ(x, z) = (Σ_i z_i ∂_i f(x))²` as an extended nonnegative real. -/
noncomputable def gradPhi107 (f : (ι → ℝ) → ℝ) (q : (ι → ℝ) × (ι → ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal ((∑ i, q.2 i * fderiv ℝ f q.1 (Pi.single i 1)) ^ 2)

lemma measurable_gradPhi107 (f : (ι → ℝ) → ℝ) : Measurable (gradPhi107 f) := by
  unfold gradPhi107
  refine ENNReal.measurable_ofReal.comp (Measurable.pow_const ?_ 2)
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((measurable_pi_apply i).comp measurable_snd).mul
    ((measurable_fderiv_apply_const ℝ f (Pi.single i 1)).comp measurable_fst)

omit [Fintype ι] [DecidableEq ι] in
lemma measurable_rot107 :
    Measurable (fun w : ((ι → ℝ) × (ι → ℝ)) × ℝ => (rotX w.2 w.1.1 w.1.2, rotY w.2 w.1.1 w.1.2)) := by
  refine Measurable.prodMk ?_ ?_
  · refine measurable_pi_iff.mpr fun i => ?_
    simp only [rotX]
    fun_prop
  · refine measurable_pi_iff.mpr fun i => ?_
    simp only [rotY]
    fun_prop

omit [DecidableEq ι] in
lemma ae_fst_mem107 (U : Set (ι → ℝ))
    (hpath : ∀ᵐ p ∂(stdGauss ι).prod (stdGauss ι), ∀ θ : ℝ, rotX θ p.1 p.2 ∈ U) :
    ∀ᵐ x ∂stdGauss ι, x ∈ U := by
  have h := Measure.ae_ae_of_ae_prod hpath
  filter_upwards [h] with x hx
  obtain ⟨z, hz⟩ := hx.exists
  have := hz 0
  simpa [rotX_eq107] using this

lemma gradPhi_lintegral_le107 (f : (ι → ℝ) → ℝ) (U : Set (ι → ℝ)) (Γ : (ι → ℝ) → ℝ)
    (hΓ : Integrable Γ (stdGauss ι))
    (hb : ∀ x ∈ U, ∑ i, (fderiv ℝ f x (Pi.single i 1)) ^ 2 ≤ Γ x)
    (hU : ∀ᵐ x ∂stdGauss ι, x ∈ U) :
    0 ≤ ∫ x, Γ x ∂stdGauss ι ∧
    ∫⁻ q, gradPhi107 f q ∂(stdGauss ι).prod (stdGauss ι) ≤
      ENNReal.ofReal (∫ x, Γ x ∂stdGauss ι) := by
  have hnn : 0 ≤ᵐ[stdGauss ι] Γ := by
    filter_upwards [hU] with x hx
    exact (Finset.sum_nonneg fun i _ => sq_nonneg _).trans (hb x hx)
  refine ⟨integral_nonneg_of_ae hnn, ?_⟩
  rw [lintegral_prod _ (measurable_gradPhi107 f).aemeasurable,
    ofReal_integral_eq_lintegral_ofReal hΓ hnn]
  refine lintegral_mono_ae ?_
  filter_upwards [hU] with x hx
  simp only [gradPhi107]
  rw [← ofReal_integral_eq_lintegral_ofReal (lin_sq_integrable107 _)
    (Filter.Eventually.of_forall fun z => sq_nonneg _), lin_sq_integral107]
  exact ENNReal.ofReal_le_ofReal (hb x hx)

/-- **The energy bound**: `E (f(X_a) − f(X))² ≤ a² ∫ Γ`. -/
theorem energy107 (f : (ι → ℝ) → ℝ) (U : Set (ι → ℝ)) (Γ : (ι → ℝ) → ℝ) (hUo : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hΓ : Integrable Γ (stdGauss ι))
    (hb : ∀ x ∈ U, ∑ i, (fderiv ℝ f x (Pi.single i 1)) ^ 2 ≤ Γ x)
    (hpath : ∀ᵐ p ∂(stdGauss ι).prod (stdGauss ι), ∀ θ : ℝ, rotX θ p.1 p.2 ∈ U)
    {a : ℝ} (ha : 0 ≤ a) :
    ∫⁻ p, ENNReal.ofReal ((f (rotX a p.1 p.2) - f p.1) ^ 2) ∂(stdGauss ι).prod (stdGauss ι) ≤
      ENNReal.ofReal (a ^ 2 * ∫ x, Γ x ∂stdGauss ι) := by
  obtain ⟨hI, hK⟩ := gradPhi_lintegral_le107 f U Γ hΓ hb (ae_fst_mem107 U hpath)
  have hΦ := measurable_gradPhi107 f
  calc ∫⁻ p, ENNReal.ofReal ((f (rotX a p.1 p.2) - f p.1) ^ 2) ∂(stdGauss ι).prod (stdGauss ι)
      ≤ ∫⁻ p, ENNReal.ofReal a * (∫⁻ θ in Set.Ioc 0 a,
          gradPhi107 f (rotX θ p.1 p.2, rotY θ p.1 p.2)) ∂(stdGauss ι).prod (stdGauss ι) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hpath] with p hp
        obtain ⟨hc, hbd⟩ := path_bound107 f U hUo hf p.1 p.2 hp ha
        refine (ENNReal.ofReal_le_ofReal hbd).trans (le_of_eq ?_)
        have hint : IntegrableOn (fun θ => (fderiv ℝ f (rotX θ p.1 p.2) (rotY θ p.1 p.2)) ^ 2)
            (Set.Ioc 0 a) := ((hc.pow 2).intervalIntegrable 0 a).1
        rw [ENNReal.ofReal_mul ha, intervalIntegral.integral_of_le ha,
          ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall fun θ => sq_nonneg _)]
        congr 2
        funext θ
        simp only [gradPhi107]
        rw [fderiv_apply_sum107]
    _ = ENNReal.ofReal a * ∫⁻ p, (∫⁻ θ in Set.Ioc 0 a,
          gradPhi107 f (rotX θ p.1 p.2, rotY θ p.1 p.2)) ∂(stdGauss ι).prod (stdGauss ι) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal a * ∫⁻ θ in Set.Ioc 0 a, ∫⁻ p,
          gradPhi107 f (rotX θ p.1 p.2, rotY θ p.1 p.2) ∂(stdGauss ι).prod (stdGauss ι) := by
        rw [lintegral_lintegral_swap]
        exact (hΦ.comp measurable_rot107).aemeasurable
    _ = ENNReal.ofReal a * ∫⁻ _θ in Set.Ioc 0 a,
          ∫⁻ q, gradPhi107 f q ∂(stdGauss ι).prod (stdGauss ι) := by
        congr 2
        funext θ
        exact (rot_preserving θ).lintegral_comp hΦ
    _ = ENNReal.ofReal a * ((∫⁻ q, gradPhi107 f q ∂(stdGauss ι).prod (stdGauss ι)) *
          ENNReal.ofReal a) := by
        simp
    _ ≤ ENNReal.ofReal a * (ENNReal.ofReal (∫ x, Γ x ∂stdGauss ι) * ENNReal.ofReal a) := by
        gcongr
    _ = ENNReal.ofReal (a ^ 2 * ∫ x, Γ x ∂stdGauss ι) := by
        rw [← ENNReal.ofReal_mul hI, ← ENNReal.ofReal_mul ha]
        congr 1
        ring

end BstLean.Part107
