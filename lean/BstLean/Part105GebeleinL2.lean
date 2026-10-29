import BstLean.Part105Gebelein
import BstLean.Part105Law

/-!
# Part 105: the Gebelein inequality for square-integrable functions

* `ou_map_snd`: the second marginal of `(X, ρ X + √(1−ρ²) Z)` is standard Gaussian.
* `gebelein_L2`: the Gebelein inequality for `f, g ∈ L²(γ)`, from the bounded case
  (`gebelein`) by density of the simple functions in `L²`.
* `gebelein_cov`: the covariance form on a general probability space.
* `ouPair_of_cov`: every linear image of a standard Gaussian with covariance
  `[[I, ρI], [ρI, I]]` has the distribution of the pair `(X, ρ X + √(1−ρ²) Z)`.
-/

namespace BstLean.Part105

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)

/-! ## An abstract density argument -/

section Density

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {γ : Measure α} {P : Measure β}
  {φ₁ φ₂ : β → α}

lemma cross_congr (h₁ : MeasurePreserving φ₁ P γ) (h₂ : MeasurePreserving φ₂ P γ)
    {f f' g g' : α → ℝ} (hf : f =ᵐ[γ] f') (hg : g =ᵐ[γ] g') :
    ∫ w, f (φ₁ w) * g (φ₂ w) ∂P = ∫ w, f' (φ₁ w) * g' (φ₂ w) ∂P := by
  refine integral_congr_ae ?_
  filter_upwards [h₁.quasiMeasurePreserving.ae_eq_comp hf,
    h₂.quasiMeasurePreserving.ae_eq_comp hg] with w h1 h2
  simp only [Function.comp_apply] at h1 h2
  rw [h1, h2]

lemma var_congr {f f' : α → ℝ} (hf : f =ᵐ[γ] f') :
    ∫ x, (f x - ∫ y, f y ∂γ) ^ 2 ∂γ = ∫ x, (f' x - ∫ y, f' y ∂γ) ^ 2 ∂γ := by
  rw [integral_congr_ae hf]
  refine integral_congr_ae ?_
  filter_upwards [hf] with x hx
  rw [hx]

variable [IsProbabilityMeasure γ]

/-- The constant function `1` in `L²`. -/
noncomputable def oneL2 (γ : Measure α) [IsProbabilityMeasure γ] : Lp ℝ 2 γ :=
  (memLp_const (1 : ℝ)).toLp _

lemma inner_oneL2 (F : Lp ℝ 2 γ) : inner ℝ (oneL2 γ) F = ∫ x, F x ∂γ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_const (1 : ℝ) (μ := γ) (p := 2))] with x hx
  simp only [oneL2, hx]
  simp

omit [IsProbabilityMeasure γ] in
lemma norm_sq_L2 (F : Lp ℝ 2 γ) : ‖F‖ ^ 2 = ∫ x, F x ^ 2 ∂γ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [pow_two]

lemma norm_sq_centre (F : Lp ℝ 2 γ) :
    ‖F - (∫ y, F y ∂γ) • oneL2 γ‖ ^ 2 = ∫ x, (F x - ∫ y, F y ∂γ) ^ 2 ∂γ := by
  rw [norm_sq_L2]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub F ((∫ y, F y ∂γ) • oneL2 γ),
    Lp.coeFn_smul (∫ y, F y ∂γ) (oneL2 γ),
    MemLp.coeFn_toLp (memLp_const (1 : ℝ) (μ := γ) (p := 2))] with x h1 h2 h3
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply]
  unfold oneL2
  rw [h3, smul_eq_mul, mul_one]

omit [IsProbabilityMeasure γ] in
lemma inner_comp (h₁ : MeasurePreserving φ₁ P γ) (h₂ : MeasurePreserving φ₂ P γ)
    (F G : Lp ℝ 2 γ) :
    inner ℝ (Lp.compMeasurePreserving φ₁ h₁ F) (Lp.compMeasurePreserving φ₂ h₂ G) =
      ∫ w, F (φ₁ w) * G (φ₂ w) ∂P := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_compMeasurePreserving F h₁,
    Lp.coeFn_compMeasurePreserving G h₂] with w h1 h2
  rw [h1, h2]
  simp [mul_comm]

lemma bm_simpleFunc (s : SimpleFunc α ℝ) : BM (s : α → ℝ) := by
  refine ⟨s.measurable, ?_⟩
  obtain ⟨C, hC⟩ := s.exists_forall_norm_le
  exact ⟨C, fun x => by simpa using hC x⟩

/-- Density: an inequality of Gebelein type that holds for bounded measurable functions holds for
square-integrable functions. -/
theorem density_L2 (h₁ : MeasurePreserving φ₁ P γ) (h₂ : MeasurePreserving φ₂ P γ) (c : ℝ)
    (hBM : ∀ f g : α → ℝ, BM f → BM g →
      |∫ w, f (φ₁ w) * g (φ₂ w) ∂P - (∫ x, f x ∂γ) * ∫ x, g x ∂γ| ≤
        c * Real.sqrt (∫ x, (f x - ∫ y, f y ∂γ) ^ 2 ∂γ) *
          Real.sqrt (∫ x, (g x - ∫ y, g y ∂γ) ^ 2 ∂γ))
    {f g : α → ℝ} (hf : MemLp f 2 γ) (hg : MemLp g 2 γ) :
    |∫ w, f (φ₁ w) * g (φ₂ w) ∂P - (∫ x, f x ∂γ) * ∫ x, g x ∂γ| ≤
      c * Real.sqrt (∫ x, (f x - ∫ y, f y ∂γ) ^ 2 ∂γ) *
        Real.sqrt (∫ x, (g x - ∫ y, g y ∂γ) ^ 2 ∂γ) := by
  have key : ∀ F G : Lp ℝ 2 γ,
      |inner ℝ (Lp.compMeasurePreserving φ₁ h₁ F) (Lp.compMeasurePreserving φ₂ h₂ G) -
          inner ℝ (oneL2 γ) F * inner ℝ (oneL2 γ) G| ≤
        c * Real.sqrt (‖F - (inner ℝ (oneL2 γ) F) • oneL2 γ‖ ^ 2) *
          Real.sqrt (‖G - (inner ℝ (oneL2 γ) G) • oneL2 γ‖ ^ 2) := by
    have hc1 : Continuous (Lp.compMeasurePreserving (E := ℝ) (p := 2) φ₁ h₁) :=
      (Lp.isometry_compMeasurePreserving h₁).continuous
    have hc2 : Continuous (Lp.compMeasurePreserving (E := ℝ) (p := 2) φ₂ h₂) :=
      (Lp.isometry_compMeasurePreserving h₂).continuous
    refine (Lp.simpleFunc.denseRange (E := ℝ) (μ := γ) (p := 2)
      ENNReal.ofNat_ne_top).induction_on₂ ?_ ?_
    · apply isClosed_le
      · exact ((((hc1.comp continuous_fst).inner (hc2.comp continuous_snd))).sub
          ((continuous_const.inner continuous_fst).mul
            (continuous_const.inner continuous_snd))).abs
      · refine (continuous_const.mul (Real.continuous_sqrt.comp ?_)).mul
          (Real.continuous_sqrt.comp ?_)
        · fun_prop
        · fun_prop
    · intro s t
      have hs := Lp.simpleFunc.toSimpleFunc_eq_toFun s
      have ht := Lp.simpleFunc.toSimpleFunc_eq_toFun t
      have := hBM _ _ (bm_simpleFunc (Lp.simpleFunc.toSimpleFunc s))
        (bm_simpleFunc (Lp.simpleFunc.toSimpleFunc t))
      rw [cross_congr h₁ h₂ hs ht, var_congr hs, var_congr ht, integral_congr_ae hs,
        integral_congr_ae ht] at this
      rw [inner_comp, inner_oneL2, inner_oneL2, norm_sq_centre, norm_sq_centre]
      exact this
  have hF := hf.coeFn_toLp
  have hG := hg.coeFn_toLp
  have := key (hf.toLp f) (hg.toLp g)
  rw [inner_comp, inner_oneL2, inner_oneL2, norm_sq_centre, norm_sq_centre,
    cross_congr h₁ h₂ hF hG, var_congr hF, var_congr hG, integral_congr_ae hF,
    integral_congr_ae hG] at this
  exact this

omit [IsProbabilityMeasure γ] in
lemma cross_integrable (h₁ : MeasurePreserving φ₁ P γ)
    (h₂ : MeasurePreserving φ₂ P γ) {f g : α → ℝ} (hf : MemLp f 2 γ) (hg : MemLp g 2 γ) :
    Integrable (fun w => f (φ₁ w) * g (φ₂ w)) P :=
  (hf.comp_measurePreserving h₁).integrable_mul (hg.comp_measurePreserving h₂)

end Density

variable {ι : Type*} [Fintype ι]

/-! ## Item 1: the second marginal -/

theorem ou_map_snd {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    ((stdGauss ι).prod (stdGauss ι)).map (fun w => ρ • w.1 + sC ρ • w.2) = stdGauss ι := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (meas_comb ρ (sC ρ)) hs]
  have h := gauss_comb (ι := ι) ρ (sC ρ) (sC_nonneg ρ) (s.indicator fun _ => (1 : ℝ))
    (measurable_const.indicator hs)
  rw [sC_sq hρ, show ρ ^ 2 + (1 - ρ ^ 2) = 1 by ring, Real.sqrt_one] at h
  simp only [one_smul] at h
  have h' : ∫ w, ((fun w : (ι → ℝ) × (ι → ℝ) => ρ • w.1 + sC ρ • w.2) ⁻¹' s).indicator
      (fun _ => (1 : ℝ)) w ∂((stdGauss ι).prod (stdGauss ι)) =
      ∫ z, s.indicator (fun _ => (1 : ℝ)) z ∂stdGauss ι := by
    rw [← h]
    rfl
  rw [integral_indicator_const _ ((meas_comb ρ (sC ρ)) hs), integral_indicator_const _ hs] at h'
  simp only [smul_eq_mul, mul_one] at h'
  exact (measureReal_eq_measureReal_iff).1 h'

lemma ou_mp_snd {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    MeasurePreserving (fun w : (ι → ℝ) × (ι → ℝ) => ρ • w.1 + sC ρ • w.2)
      ((stdGauss ι).prod (stdGauss ι)) (stdGauss ι) :=
  ⟨meas_comb ρ (sC ρ), ou_map_snd hρ⟩

lemma ou_mp_fst :
    MeasurePreserving (fun w : (ι → ℝ) × (ι → ℝ) => w.1)
      ((stdGauss ι).prod (stdGauss ι)) (stdGauss ι) :=
  measurePreserving_fst

/-! ## Item 2: the Gebelein inequality in `L²` -/

theorem gebelein_L2 {ρ : ℝ} (hρ : |ρ| ≤ 1) {f g : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (stdGauss ι)) (hg : MemLp g 2 (stdGauss ι)) :
    |∫ w, f w.1 * g (ρ • w.1 + sC ρ • w.2) ∂((stdGauss ι).prod (stdGauss ι)) -
        (∫ x, f x ∂stdGauss ι) * ∫ x, g x ∂stdGauss ι| ≤
      |ρ| * Real.sqrt (∫ x, (f x - ∫ y, f y ∂stdGauss ι) ^ 2 ∂stdGauss ι) *
        Real.sqrt (∫ x, (g x - ∫ y, g y ∂stdGauss ι) ^ 2 ∂stdGauss ι) :=
  density_L2 ou_mp_fst (ou_mp_snd hρ) |ρ| (fun _ _ hf' hg' => gebelein hρ hf' hg') hf hg

theorem gebelein_L2_integrable {ρ : ℝ} (hρ : |ρ| ≤ 1) {f g : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (stdGauss ι)) (hg : MemLp g 2 (stdGauss ι)) :
    Integrable (fun w => f w.1 * g (ρ • w.1 + sC ρ • w.2))
      ((stdGauss ι).prod (stdGauss ι)) :=
  cross_integrable ou_mp_fst (ou_mp_snd hρ) hf hg

/-! ## Item 3: the covariance form on a general probability space -/

lemma mp_integral_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} {φ : α → β} (hmp : MeasurePreserving φ μ ν) {H : β → ℝ}
    (hH : AEStronglyMeasurable H ν) : ∫ x, H (φ x) ∂μ = ∫ y, H y ∂ν := by
  rw [← hmp.map_eq] at hH ⊢
  exact (integral_map hmp.measurable.aemeasurable hH).symm

theorem gebelein_cov {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ρ : ℝ} (hρ : |ρ| ≤ 1) (X Y : Ω → ι → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hlaw : P.map (fun ω => (X ω, Y ω)) =
      ((stdGauss ι).prod (stdGauss ι)).map (fun p => (p.1, ρ • p.1 + sC ρ • p.2)))
    {f g : (ι → ℝ) → ℝ} (hf : MemLp f 2 (stdGauss ι)) (hg : MemLp g 2 (stdGauss ι)) :
    |cov[fun ω => f (X ω), fun ω => g (Y ω); P]| ≤
      |ρ| * Real.sqrt (Var[fun ω => f (X ω); P]) * Real.sqrt (Var[fun ω => g (Y ω); P]) := by
  have hψ : Measurable (fun p : (ι → ℝ) × (ι → ℝ) => (p.1, ρ • p.1 + sC ρ • p.2)) :=
    measurable_fst.prodMk (meas_comb ρ (sC ρ))
  have hXY : Measurable (fun ω => (X ω, Y ω)) := hX.prodMk hY
  have mpX : MeasurePreserving X P (stdGauss ι) := by
    refine ⟨hX, ?_⟩
    have : P.map X = (P.map (fun ω => (X ω, Y ω))).map Prod.fst := by
      rw [Measure.map_map measurable_fst hXY]; rfl
    rw [this, hlaw, Measure.map_map measurable_fst hψ]
    exact ou_mp_fst.map_eq
  have mpY : MeasurePreserving Y P (stdGauss ι) := by
    refine ⟨hY, ?_⟩
    have : P.map Y = (P.map (fun ω => (X ω, Y ω))).map Prod.snd := by
      rw [Measure.map_map measurable_snd hXY]; rfl
    rw [this, hlaw, Measure.map_map measurable_snd hψ]
    exact ou_map_snd hρ
  have mpXY : MeasurePreserving (fun ω => (X ω, Y ω)) P
      (((stdGauss ι).prod (stdGauss ι)).map (fun p => (p.1, ρ • p.1 + sC ρ • p.2))) :=
    ⟨hXY, hlaw⟩
  have mpψ : MeasurePreserving (fun p : (ι → ℝ) × (ι → ℝ) => (p.1, ρ • p.1 + sC ρ • p.2))
      ((stdGauss ι).prod (stdGauss ι))
      (((stdGauss ι).prod (stdGauss ι)).map (fun p => (p.1, ρ • p.1 + sC ρ • p.2))) :=
    ⟨hψ, rfl⟩
  have mp1 : MeasurePreserving (Prod.fst : (ι → ℝ) × (ι → ℝ) → ι → ℝ)
      (((stdGauss ι).prod (stdGauss ι)).map (fun p => (p.1, ρ • p.1 + sC ρ • p.2)))
      (stdGauss ι) := by
    refine ⟨measurable_fst, ?_⟩
    rw [Measure.map_map measurable_fst hψ]
    exact ou_mp_fst.map_eq
  have mp2 : MeasurePreserving (Prod.snd : (ι → ℝ) × (ι → ℝ) → ι → ℝ)
      (((stdGauss ι).prod (stdGauss ι)).map (fun p => (p.1, ρ • p.1 + sC ρ • p.2)))
      (stdGauss ι) := by
    refine ⟨measurable_snd, ?_⟩
    rw [Measure.map_map measurable_snd hψ]
    exact ou_map_snd hρ
  have hfX : MemLp (fun ω => f (X ω)) 2 P := hf.comp_measurePreserving mpX
  have hgY : MemLp (fun ω => g (Y ω)) 2 P := hg.comp_measurePreserving mpY
  have hEf : ∫ ω, f (X ω) ∂P = ∫ x, f x ∂stdGauss ι :=
    mp_integral_ae mpX hf.aestronglyMeasurable
  have hEg : ∫ ω, g (Y ω) ∂P = ∫ x, g x ∂stdGauss ι :=
    mp_integral_ae mpY hg.aestronglyMeasurable
  have hVf : Var[fun ω => f (X ω); P] = ∫ x, (f x - ∫ y, f y ∂stdGauss ι) ^ 2 ∂stdGauss ι := by
    rw [variance_eq_integral hfX.aemeasurable, hEf]
    exact mp_integral_ae mpX (H := fun x => (f x - ∫ y, f y ∂stdGauss ι) ^ 2)
      ((hf.aestronglyMeasurable.sub aestronglyMeasurable_const).pow 2)
  have hVg : Var[fun ω => g (Y ω); P] = ∫ x, (g x - ∫ y, g y ∂stdGauss ι) ^ 2 ∂stdGauss ι := by
    rw [variance_eq_integral hgY.aemeasurable, hEg]
    exact mp_integral_ae mpY (H := fun x => (g x - ∫ y, g y ∂stdGauss ι) ^ 2)
      ((hg.aestronglyMeasurable.sub aestronglyMeasurable_const).pow 2)
  have hH : AEStronglyMeasurable (fun p : (ι → ℝ) × (ι → ℝ) => f p.1 * g p.2)
      (((stdGauss ι).prod (stdGauss ι)).map (fun p => (p.1, ρ • p.1 + sC ρ • p.2))) :=
    (hf.aestronglyMeasurable.comp_measurePreserving mp1).mul
      (hg.aestronglyMeasurable.comp_measurePreserving mp2)
  have hE : ∫ ω, f (X ω) * g (Y ω) ∂P =
      ∫ w, f w.1 * g (ρ • w.1 + sC ρ • w.2) ∂((stdGauss ι).prod (stdGauss ι)) := by
    rw [mp_integral_ae mpXY (H := fun p : (ι → ℝ) × (ι → ℝ) => f p.1 * g p.2) hH,
      ← mp_integral_ae mpψ (H := fun p : (ι → ℝ) × (ι → ℝ) => f p.1 * g p.2) hH]
  rw [covariance_eq_sub hfX hgY, hVf, hVg]
  simp only [Pi.mul_apply]
  rw [hE, hEf, hEg]
  exact gebelein_L2 hρ hf hg

/-! ## Item 4: linear images with covariance `[[I, ρI], [ρI, I]]` -/

theorem ouPair_of_cov {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] {ρ : ℝ} (hρ : |ρ| ≤ 1)
    (A : Matrix (ι ⊕ ι) κ ℝ)
    (hA : A * A.transpose = Matrix.fromBlocks 1 (ρ • 1) (ρ • 1) 1) :
    (stdGauss κ).map (fun ξ => (fun i => A.mulVec ξ (Sum.inl i), fun i => A.mulVec ξ (Sum.inr i))) =
      ((stdGauss ι).prod (stdGauss ι)).map (fun p => (p.1, ρ • p.1 + sC ρ • p.2)) := by
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ ι => ℝ)
  let B : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ := Matrix.fromBlocks 1 0 (ρ • 1) (sC ρ • 1)
  have hs : ρ * ρ + sC ρ * sC ρ = 1 := by
    have := sC_sq hρ
    nlinarith
  have hAB : A * A.transpose = B * B.transpose := by
    rw [hA]
    simp only [B, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_zero,
      Matrix.mul_smul, Matrix.mul_one, Matrix.mul_zero,
      smul_zero, add_zero, smul_smul, ← add_smul, hs, one_smul]
  have hL : (fun ξ : κ → ℝ => ((fun i => A.mulVec ξ (Sum.inl i), fun i => A.mulVec ξ (Sum.inr i)) :
      (ι → ℝ) × (ι → ℝ))) = e ∘ (fun ξ => A.mulVec ξ) := rfl
  have hR : (fun p : (ι → ℝ) × (ι → ℝ) => (p.1, ρ • p.1 + sC ρ • p.2)) ∘ e =
      e ∘ (fun ξ => B.mulVec ξ) := by
    funext ξ
    simp only [Function.comp_apply, B, Matrix.fromBlocks_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]
    refine Prod.ext ?_ ?_
    · rfl
    · funext a
      simp [e, MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi]
  have hprod : (stdGauss ι).prod (stdGauss ι) = (stdGauss (ι ⊕ ι)).map e :=
    ((measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ ι => gaussianReal 0 1)).map_eq).symm
  have hψ : Measurable (fun p : (ι → ℝ) × (ι → ℝ) => (p.1, ρ • p.1 + sC ρ • p.2)) :=
    measurable_fst.prodMk (meas_comb ρ (sC ρ))
  rw [hL, hprod, Measure.map_map hψ e.measurable, hR,
    ← Measure.map_map e.measurable (by fun_prop), ← Measure.map_map e.measurable (by fun_prop),
    gaussLin105 _ _ _ A B hAB]

#print axioms ou_map_snd
#print axioms gebelein_L2
#print axioms gebelein_L2_integrable
#print axioms gebelein_cov
#print axioms ouPair_of_cov

end BstLean.Part105
