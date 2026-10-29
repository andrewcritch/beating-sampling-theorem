import BstLean.Part56PropD_Split

/-! Bingham disintegration with an independent perpendicular Gaussian direction. -/
namespace BstLean.Part56

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (unitF53 radF53)

variable {k : ℕ}

noncomputable def axialWeight (t : ℝ) (v : Fin (k + 1) → ℝ) (a r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (t * axialS a r ^ 2) / BstLean.Part50.ZA (k + 1) (rk1 t v))

/-- The axial state is retained and the perpendicular direction is sampled independently. -/
theorem lawRK_lintegral_polar
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ (Fin (k + 1))))
    (v : Fin (k + 1) → ℝ) (hb : b 0 = WithLp.toLp 2 v)
    (t : ℝ) (F : (Fin (k + 1) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x ∂lawRK (k + 1) t v) =
      ∫⁻ a, ∫⁻ z, ∫⁻ g,
        F (polarPoint v (perpDir v g) a (radF53 z)) * axialWeight t v a (radF53 z)
        ∂stdGauss (Fin (k + 1)) ∂stdGauss (Fin k)
        ∂ProbabilityTheory.gaussianReal 0 1 := by
  rw [lawRK_lintegral_gauss (k + 1) (by omega) t v F hF]
  let G : (Fin (k + 1) → ℝ) → ℝ≥0∞ := fun g =>
    F (unitF53 g) * ENNReal.ofReal (Real.exp (t * (∑ i, v i * unitF53 g i) ^ 2) /
      BstLean.Part50.ZA (k + 1) (rk1 t v))
  have hG : Measurable G := by
    apply (hF.comp BstLean.Part53.measurable_unitF).mul
    unfold unitF53
    fun_prop
  change (∫⁻ g, G g ∂stdGauss (Fin (k + 1))) = _
  rw [basis_cons_lintegral b G hG]
  dsimp only [G]
  simp_rw [← basisReconstruct_eq_symm, normalized_basis_axial b v hb,
    normalized_basis_cons b v hb]
  change (∫⁻ a, ∫⁻ z,
    F (polarPoint v (tailReconstruct b (unitF53 z)) a (radF53 z)) *
      axialWeight t v a (radF53 z)
    ∂stdGauss (Fin k) ∂ProbabilityTheory.gaussianReal 0 1) = _
  apply lintegral_congr
  intro a
  let H : ℝ → (Fin k → ℝ) → ℝ≥0∞ := fun r w =>
    F (polarPoint v (tailReconstruct b w) a r) * axialWeight t v a r
  have hH : Measurable (Function.uncurry H) := by
    apply (hF.comp ?_).mul
    · try dsimp only [H, Function.uncurry, axialWeight, polarPoint, axialS, axialR,
        tailReconstruct, basisReconstruct]
      fun_prop
    · try dsimp only [H, Function.uncurry, axialWeight, polarPoint, axialS, axialR,
        tailReconstruct, basisReconstruct]
      fun_prop
  change (∫⁻ z, H (radF53 z) (unitF53 z) ∂stdGauss (Fin k)) = _
  rw [rad_direction_resample H hH]
  apply lintegral_congr
  intro z
  have hpoint : Measurable (fun w : Fin (k + 1) → ℝ =>
      F (polarPoint v w a (radF53 z)) * axialWeight t v a (radF53 z)) := by
    apply (hF.comp ?_).mul measurable_const
    unfold polarPoint
    fun_prop
  exact (perpDir_lintegral_tail b v hb _ hpoint).symm

noncomputable def axialMeasure (t : ℝ) (v : Fin (k + 1) → ℝ) :
    Measure (ℝ × (Fin k → ℝ)) :=
  ((ProbabilityTheory.gaussianReal 0 1).prod (stdGauss (Fin k))).withDensity
    (fun p => axialWeight t v p.1 (radF53 p.2))

noncomputable def polarState (v : Fin (k + 1) → ℝ)
    (p : (ℝ × (Fin k → ℝ)) × (Fin (k + 1) → ℝ)) : Fin (k + 1) → ℝ :=
  polarPoint v (perpDir v p.2) p.1.1 (radF53 p.1.2)

theorem measurable_polarState (v : Fin (k + 1) → ℝ) : Measurable (polarState v) := by
  unfold polarState polarPoint axialS axialR perpDir radF53
  fun_prop

theorem axialMeasure_lintegral (t : ℝ) (v : Fin (k + 1) → ℝ)
    (F : (ℝ × (Fin k → ℝ)) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p ∂axialMeasure t v) =
      ∫⁻ a, ∫⁻ z, F (a, z) * axialWeight t v a (radF53 z)
        ∂stdGauss (Fin k) ∂ProbabilityTheory.gaussianReal 0 1 := by
  have hw : Measurable (fun p : ℝ × (Fin k → ℝ) => axialWeight t v p.1 (radF53 p.2)) := by
    unfold axialWeight axialS radF53
    fun_prop
  unfold axialMeasure
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hF]
  simp only [Pi.mul_apply]
  rw [lintegral_prod (fun p : ℝ × (Fin k → ℝ) =>
    axialWeight t v p.1 (radF53 p.2) * F p) (hw.mul hF).aemeasurable]
  simp only [mul_comm]

/-- The Bingham law is the image of an axial probability law times an independent direction. -/
theorem lawRK_eq_polar_map
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ (Fin (k + 1))))
    (v : Fin (k + 1) → ℝ) (hb : b 0 = WithLp.toLp 2 v) (t : ℝ) :
    lawRK (k + 1) t v =
      ((axialMeasure t v).prod (stdGauss (Fin (k + 1)))).map (polarState v) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lawRK_lintegral_polar b v hb t F hF,
    lintegral_map hF (measurable_polarState v)]
  rw [lintegral_prod (fun p => F (polarState v p))
    (hF.comp (measurable_polarState v)).aemeasurable]
  rw [axialMeasure_lintegral t v (fun p =>
    ∫⁻ g, F (polarState v (p, g)) ∂stdGauss (Fin (k + 1)))
    (hF.comp (measurable_polarState v)).lintegral_prod_right']
  apply lintegral_congr
  intro a
  apply lintegral_congr
  intro z
  rw [lintegral_mul_const (f := fun g => F (polarPoint v (perpDir v g) a (radF53 z)))
    (axialWeight t v a (radF53 z))]
  · rfl
  · apply hF.comp
    unfold polarPoint perpDir
    fun_prop

theorem axialMeasure_probability
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ (Fin (k + 1))))
    (v : Fin (k + 1) → ℝ) (hb : b 0 = WithLp.toLp 2 v) (t : ℝ) :
    IsProbabilityMeasure (axialMeasure t v) := by
  letI : IsProbabilityMeasure (lawRK (k + 1) t v) :=
    (BstLean.Part50.binghamA_antipodal (by omega) (rk1 t v)).sph.prob
  have h := congrArg (fun μ : Measure (Fin (k + 1) → ℝ) => μ Set.univ)
    (lawRK_eq_polar_map b v hb t)
  simp only [measure_univ, Measure.map_apply (measurable_polarState v) MeasurableSet.univ,
    Set.preimage_univ, Measure.prod_apply, MeasurableSet.univ, lintegral_one] at h
  exact ⟨h.symm⟩

end BstLean.Part56
