import BstLean.Part53Defs

/-!
# Part 53, wave 1: the direction and the radius of a standard Gaussian are independent

Specification: `delegations/answers/p53-spec-opus.md` §3.8.
Replace each `sorry` by a proof. Do not edit the statements. Do not use `native_decide` or `axiom`
anywhere. This file imports `Part53Defs` only (a prover may also import finished Part 29–52 files,
but no other Part 53 wave-1 file).

Proved here: the product density `stdGauss_density`, polar coordinates `polar_lintegral`
(`measurePreserving_homeomorphUnitSphereProd`), the radial weight `Wrad53`, then Tonelli
(`gauss_polar_gen`). The original suggested route was: rotation invariance of `stdGauss` (orthogonal maps preserve it; Part 46's
`gaussian_basis_preserving`), so the conditional law of `Z/‖Z‖` given `‖Z‖` is the rotation-invariant
law on the sphere, which is unique. Alternatively: Mathlib's polar coordinates on
`EuclideanSpace` (`MeasureTheory.Measure.toSphere`, `homeomorphUnitSphereProd`,
`Measure.measurePreserving_homeomorphUnitSphereProd`) and the radial density of `stdGauss`. At
`|ι| = 0` both sides are `F 0 0`.
-/

namespace BstLean.Part53

open MeasureTheory BstLean.Cost ProbabilityTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM phiSq colM contr trL frob IsSymmT Tens TSymm fval In41 Pn heavyCount)
open BstLean.Part43 (BofQ varFQ)

variable {n d : ℕ}

/-- The product Gaussian density. -/
noncomputable def gdens53 {ι : Type*} [Fintype ι] (z : ι → ℝ) : ℝ := ∏ i, gaussianPDFReal 0 1 (z i)

lemma stdGauss_density {ι : Type*} [Fintype ι] :
    stdGauss ι = (volume : Measure (ι → ℝ)).withDensity (fun z => ENNReal.ofReal (gdens53 z)) := by
  classical
  unfold stdGauss
  apply Measure.pi_eq
  intro s hs
  have hmeas : ∀ i, Measurable ((s i).indicator (gaussianPDFReal 0 1)) :=
    fun i => (measurable_gaussianPDFReal 0 1).indicator (hs i)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have he : ∀ z : ι → ℝ, (Set.univ.pi s).indicator (fun z => ENNReal.ofReal (gdens53 z)) z =
      ENNReal.ofReal (∏ i, (s i).indicator (gaussianPDFReal 0 1) (z i)) := by
    intro z
    by_cases hz : z ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hz]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      rw [Set.indicator_of_mem (hz i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hz]
      have hz' : ∃ i, z i ∉ s i := by
        simpa only [Set.mem_pi, Set.mem_univ, forall_true_left, not_forall] using hz
      obtain ⟨i, hi⟩ := hz'
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _), ENNReal.ofReal_zero]
  simp_rw [he]
  have hint : ∀ i, Integrable ((s i).indicator (gaussianPDFReal 0 1)) (volume : Measure ℝ) :=
    fun i => (integrable_gaussianPDFReal 0 1).indicator (hs i)
  have hnn : ∀ i x, 0 ≤ (s i).indicator (gaussianPDFReal 0 1) x :=
    fun i x => Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) x
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [show (volume : Measure (ι → ℝ)) = Measure.pi (fun _ => volume) from rfl,
      integral_fintype_prod_eq_prod (𝕜 := ℝ) (fun i => (s i).indicator (gaussianPDFReal 0 1)),
      ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hnn i))]
    apply Finset.prod_congr rfl
    intro i _
    rw [ofReal_integral_eq_lintegral_ofReal (hint i) (Filter.Eventually.of_forall (hnn i)),
      gaussianReal_of_var_ne_zero 0 one_ne_zero, withDensity_apply _ (hs i),
      ← lintegral_indicator (hs i)]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ s i
    · simp [Set.indicator_of_mem hx, gaussianPDF]
    · simp [Set.indicator_of_notMem hx]
  · exact Integrable.fintype_prod (f := fun i => (s i).indicator (gaussianPDFReal 0 1)) hint
  · exact Filter.Eventually.of_forall fun z => Finset.prod_nonneg fun i _ => hnn i _


/-- Polar coordinates for a lower integral on `EuclideanSpace ℝ ι`. -/
lemma polar_lintegral {ι : Type} [Fintype ι] [Nonempty ι] (K : EuclideanSpace ℝ ι → ℝ≥0∞) :
    ∫⁻ x, K x = ∫⁻ p, K (p.2.1 • p.1.1) ∂((volume : Measure (EuclideanSpace ℝ ι)).toSphere.prod
      (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ ι) - 1))) := by
  have hcomp : ∀ x : ({(0 : EuclideanSpace ℝ ι)}ᶜ : Set (EuclideanSpace ℝ ι)),
      K x.1 = (fun p : Metric.sphere (0 : EuclideanSpace ℝ ι) 1 × Set.Ioi (0 : ℝ) => K (p.2.1 • p.1.1))
        (homeomorphUnitSphereProd (EuclideanSpace ℝ ι) x) := by
    intro x
    have h := congrArg Subtype.val ((homeomorphUnitSphereProd (EuclideanSpace ℝ ι)).symm_apply_apply x)
    rw [homeomorphUnitSphereProd_symm_apply_coe] at h
    simp only
    rw [h]
  calc ∫⁻ x, K x = ∫⁻ x in {(0 : EuclideanSpace ℝ ι)}ᶜ, K x := by rw [restrict_compl_singleton]
    _ = ∫⁻ x : ({(0 : EuclideanSpace ℝ ι)}ᶜ : Set (EuclideanSpace ℝ ι)), K x.1 ∂((volume : Measure (EuclideanSpace ℝ ι)).comap (↑)) :=
        (lintegral_subtype_comap (measurableSet_singleton _).compl K).symm
    _ = _ := by
        simp_rw [hcomp]
        exact ((volume : Measure (EuclideanSpace ℝ ι)).measurePreserving_homeomorphUnitSphereProd.lintegral_comp_emb
          (Homeomorph.measurableEmbedding _)
          (fun p : Metric.sphere (0 : EuclideanSpace ℝ ι) 1 × Set.Ioi (0 : ℝ) => K (p.2.1 • p.1.1)))


/-- The radial Gaussian weight. -/
noncomputable def Wrad53 (ι : Type) [Fintype ι] (ρ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι * Real.exp (-ρ ^ 2 / 2))

lemma gdens_sphere {ι : Type} [Fintype ι] (s : Metric.sphere (0 : EuclideanSpace ℝ ι) 1) (ρ : ℝ) :
    gdens53 (ρ • WithLp.ofLp s.1) = (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι * Real.exp (-ρ ^ 2 / 2) := by
  unfold gdens53
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero, Pi.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
  congr 2
  have hs : ∑ i, (s.1 i) ^ 2 = 1 := by
    have h1 : ‖s.1‖ = 1 := by simp
    have := EuclideanSpace.real_norm_sq_eq s.1
    rw [h1] at this
    simpa using this.symm
  calc ∑ i, -(ρ * WithLp.ofLp s.1 i) ^ 2 / 2 = -(ρ ^ 2 * ∑ i, (s.1 i) ^ 2) / 2 := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_div]
        apply Finset.sum_congr rfl; intro i _; simp; ring
    _ = -ρ ^ 2 / 2 := by rw [hs, mul_one]

lemma gauss_polar_formula {ι : Type} [Fintype ι] [Nonempty ι] (H : (ι → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ Z, H Z ∂stdGauss ι = ∫⁻ p, H (p.2.1 • WithLp.ofLp p.1.1) * Wrad53 ι p.2.1
      ∂((volume : Measure (EuclideanSpace ℝ ι)).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ ι) - 1))) := by
  have hg : Measurable (fun z : ι → ℝ => ENNReal.ofReal (gdens53 z)) := by
    unfold gdens53
    exact ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ =>
      (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i))
  rw [stdGauss_density, lintegral_withDensity_eq_lintegral_mul _ hg hH]
  rw [← (PiLp.volume_preserving_ofLp ι).lintegral_comp_emb
    (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurableEmbedding]
  rw [polar_lintegral]
  apply lintegral_congr
  intro p
  simp only [Pi.mul_apply, WithLp.ofLp_smul]
  rw [gdens_sphere, mul_comm]
  rfl


/-- `Z/‖Z‖` and `‖Z‖`. -/
noncomputable def unitF53 {ι : Type} [Fintype ι] (Z : ι → ℝ) : ι → ℝ := (1 / Real.sqrt (∑ i, Z i ^ 2)) • Z
noncomputable def radF53 {ι : Type} [Fintype ι] (Z : ι → ℝ) : ℝ := Real.sqrt (∑ i, Z i ^ 2)

lemma measurable_radF {ι : Type} [Fintype ι] : Measurable (radF53 (ι := ι)) := by
  unfold radF53; fun_prop

lemma measurable_unitF {ι : Type} [Fintype ι] : Measurable (unitF53 (ι := ι)) := by
  unfold unitF53
  exact (measurable_const.div (Real.continuous_sqrt.measurable.comp (by fun_prop))).smul measurable_id

lemma sphere_sumsq {ι : Type} [Fintype ι] (s : Metric.sphere (0 : EuclideanSpace ℝ ι) 1) :
    ∑ i, (WithLp.ofLp s.1 i) ^ 2 = 1 := by
  have h1 : ‖s.1‖ = 1 := by simp
  have := EuclideanSpace.real_norm_sq_eq s.1
  rw [h1] at this
  simpa using this.symm

lemma radF_polar {ι : Type} [Fintype ι] (s : Metric.sphere (0 : EuclideanSpace ℝ ι) 1) (ρ : Set.Ioi (0 : ℝ)) :
    radF53 (ρ.1 • WithLp.ofLp s.1) = ρ.1 := by
  unfold radF53
  have : ∑ i, ((ρ.1 • WithLp.ofLp s.1) i) ^ 2 = ρ.1 ^ 2 := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [← Finset.mul_sum, sphere_sumsq, mul_one]
  rw [this, Real.sqrt_sq ρ.2.le]

lemma unitF_polar {ι : Type} [Fintype ι] (s : Metric.sphere (0 : EuclideanSpace ℝ ι) 1) (ρ : Set.Ioi (0 : ℝ)) :
    unitF53 (ρ.1 • WithLp.ofLp s.1) = WithLp.ofLp s.1 := by
  have h := radF_polar s ρ
  unfold radF53 at h
  unfold unitF53
  rw [h, smul_smul, one_div, inv_mul_cancel₀ (ne_of_gt ρ.2), one_smul]

theorem gauss_polar_gen {ι : Type} [Fintype ι] (F : (ι → ℝ) → ℝ → ℝ≥0∞)
    (hF : Measurable (Function.uncurry F)) :
    ∫⁻ Z, F (unitF53 Z) (radF53 Z) ∂stdGauss ι =
      ∫⁻ Z, ∫⁻ Z', F (unitF53 Z) (radF53 Z') ∂stdGauss ι ∂stdGauss ι := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [lintegral_unique, measure_univ, mul_one]
  · set σ := (volume : Measure (EuclideanSpace ℝ ι)).toSphere with hσ
    set ν := Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ ι) - 1) with hν
    have hW : Measurable (Wrad53 ι) := by unfold Wrad53; fun_prop
    have hFm : ∀ {α : Type} [MeasurableSpace α] {a : α → ι → ℝ} {b : α → ℝ}, Measurable a → Measurable b →
        Measurable (fun x => F (a x) (b x)) := fun ha hb => hF.comp (ha.prodMk hb)
    set Φ : (ι → ℝ) → ℝ≥0∞ := fun v => ∫⁻ ρ, F v ρ.1 * Wrad53 ι ρ.1 ∂ν with hΦ
    have hΦm : Measurable Φ := by
      have : Measurable (Function.uncurry fun (v : ι → ℝ) (ρ : Set.Ioi (0 : ℝ)) => F v ρ.1 * Wrad53 ι ρ.1) :=
        (hFm measurable_fst (measurable_subtype_coe.comp measurable_snd)).mul
          (hW.comp (measurable_subtype_coe.comp measurable_snd))
      exact this.lintegral_prod_right'
    have hofLp : Measurable (fun s : Metric.sphere (0 : EuclideanSpace ℝ ι) 1 => WithLp.ofLp s.1) := by
      fun_prop
    have prodI : ∀ G : Metric.sphere (0 : EuclideanSpace ℝ ι) 1 × Set.Ioi (0 : ℝ) → ℝ≥0∞, Measurable G →
        ∫⁻ p, G p ∂(σ.prod ν) = ∫⁻ s, ∫⁻ ρ, G (s, ρ) ∂ν ∂σ := fun G hG => lintegral_prod G hG.aemeasurable
    have hsnd : Measurable (fun p : Metric.sphere (0 : EuclideanSpace ℝ ι) 1 × Set.Ioi (0 : ℝ) => p.2.1) :=
      measurable_subtype_coe.comp measurable_snd
    have hfst : Measurable (fun p : Metric.sphere (0 : EuclideanSpace ℝ ι) 1 × Set.Ioi (0 : ℝ) =>
        WithLp.ofLp p.1.1) := hofLp.comp measurable_fst
    -- inner integral
    have hA : ∀ v, ∫⁻ Z', F v (radF53 Z') ∂stdGauss ι = σ Set.univ * Φ v := by
      intro v
      rw [gauss_polar_formula _ (hFm measurable_const measurable_radF)]
      simp_rw [radF_polar]
      rw [← hσ, ← hν, prodI (fun p => F v p.2.1 * Wrad53 ι p.2.1)
        ((hFm measurable_const hsnd).mul (hW.comp hsnd))]
      show ∫⁻ _s, Φ v ∂σ = _
      rw [lintegral_const, mul_comm]
    have hB : ∫⁻ Z, F (unitF53 Z) (radF53 Z) ∂stdGauss ι = ∫⁻ s, Φ (WithLp.ofLp s.1) ∂σ := by
      rw [gauss_polar_formula _ (hFm measurable_unitF measurable_radF)]
      simp_rw [radF_polar, unitF_polar]
      rw [← hσ, ← hν, prodI (fun p => F (WithLp.ofLp p.1.1) p.2.1 * Wrad53 ι p.2.1)
        ((hFm hfst hsnd).mul (hW.comp hsnd))]
    have hC : ∫⁻ Z, Φ (unitF53 Z) ∂stdGauss ι = (∫⁻ ρ, Wrad53 ι ρ.1 ∂ν) * ∫⁻ s, Φ (WithLp.ofLp s.1) ∂σ := by
      rw [gauss_polar_formula (fun Z => Φ (unitF53 Z)) (hΦm.comp measurable_unitF)]
      simp_rw [unitF_polar]
      rw [← hσ, ← hν, prodI (fun p => Φ (WithLp.ofLp p.1.1) * Wrad53 ι p.2.1)
        ((hΦm.comp hfst).mul (hW.comp hsnd))]
      show ∫⁻ s, ∫⁻ ρ, Φ (WithLp.ofLp s.1) * Wrad53 ι ρ.1 ∂ν ∂σ = _
      simp_rw [lintegral_const_mul _ (show Measurable (fun ρ : Set.Ioi (0 : ℝ) => Wrad53 ι ρ.1) from
        hW.comp measurable_subtype_coe)]
      rw [lintegral_mul_const _ (show Measurable (fun s : Metric.sphere (0 : EuclideanSpace ℝ ι) 1 =>
        Φ (WithLp.ofLp s.1)) from hΦm.comp hofLp), mul_comm]
    have hD : σ Set.univ * ∫⁻ ρ, Wrad53 ι ρ.1 ∂ν = 1 := by
      have h := gauss_polar_formula (ι := ι) (fun _ => 1) measurable_const
      rw [lintegral_const, measure_univ, one_mul] at h
      simp only [one_mul] at h
      rw [← hσ, ← hν, prodI (fun p => Wrad53 ι p.2.1) (hW.comp hsnd)] at h
      change 1 = ∫⁻ _s, ∫⁻ ρ, Wrad53 ι ρ.1 ∂ν ∂σ at h
      rw [lintegral_const] at h
      rw [h, mul_comm]
    calc ∫⁻ Z, F (unitF53 Z) (radF53 Z) ∂stdGauss ι = ∫⁻ s, Φ (WithLp.ofLp s.1) ∂σ := hB
      _ = σ Set.univ * ((∫⁻ ρ, Wrad53 ι ρ.1 ∂ν) * ∫⁻ s, Φ (WithLp.ofLp s.1) ∂σ) := by
          rw [← mul_assoc, hD, one_mul]
      _ = σ Set.univ * ∫⁻ Z, Φ (unitF53 Z) ∂stdGauss ι := by rw [hC]
      _ = ∫⁻ Z, σ Set.univ * Φ (unitF53 Z) ∂stdGauss ι := (lintegral_const_mul _ (hΦm.comp measurable_unitF)).symm
      _ = _ := by
          apply lintegral_congr; intro Z; rw [hA]

/-- **Polar independence** (proved). -/
theorem gaussPolar53 : GaussPolar53 := fun _ _ F hF => gauss_polar_gen F hF

end BstLean.Part53
