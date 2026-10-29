import BstLean.Part57PropD_Polar

/-! Rank-r Bingham disintegration with an independent perpendicular Gaussian direction. -/
namespace BstLean.Part57.PropD57
open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (unitF53 radF53)
open BstLean.Part56 (rad_direction_resample basisReconstruct_eq_symm)

variable {r k : ℕ}

noncomputable def axialWeightR (t : Fin r → ℝ) (v : Fin r → Fin (r + k) → ℝ) (a : Fin r → ℝ) (R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (∑ i, t i * axialY a R i ^ 2) / BstLean.Part50.ZA (r + k) (rkR t v))

/-- The axial state is retained and the perpendicular direction is sampled independently. -/
theorem lawRR_lintegral_polar
    (b : OrthonormalBasis (Fin (r + k)) ℝ (EuclideanSpace ℝ (Fin (r + k))))
    (v : Fin r → Fin (r + k) → ℝ) (hb : ∀ a : Fin r, b (Fin.castAdd k a) = WithLp.toLp 2 (v a))
    (hn : 1 ≤ r+k) (t : Fin r → ℝ) (F : (Fin (r + k) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x ∂lawRR (r + k) t v) =
      ∫⁻ a, ∫⁻ z, ∫⁻ g,
        F (polarPointR v (perpDirR v g) a (radF53 z)) * axialWeightR t v a (radF53 z)
        ∂stdGauss (Fin (r + k)) ∂stdGauss (Fin k)
        ∂stdGauss (Fin r) := by
  rw [lawRR_lintegral_gauss (r + k) hn t v F hF]
  let G : (Fin (r + k) → ℝ) → ℝ≥0∞ := fun g =>
    F (unitF53 g) * ENNReal.ofReal (Real.exp (∑ i, t i * coordY v (unitF53 g) i ^ 2) /
      BstLean.Part50.ZA (r + k) (rkR t v))
  have hG : Measurable G := by
    apply (hF.comp BstLean.Part53.measurable_unitF).mul
    unfold unitF53 coordY
    fun_prop
  change (∫⁻ g, G g ∂stdGauss (Fin (r + k))) = _
  rw [basis_join_lintegral b G hG]
  dsimp only [G]
  simp_rw [normalized_coord_join b v hb,
    normalized_reconstruct_join b v hb]
  change (∫⁻ a, ∫⁻ z,
    F (polarPointR v (tailR b (unitF53 z)) a (radF53 z)) *
      axialWeightR t v a (radF53 z)
    ∂stdGauss (Fin k) ∂stdGauss (Fin r)) = _
  apply lintegral_congr
  intro a
  let H : ℝ → (Fin k → ℝ) → ℝ≥0∞ := fun r w =>
    F (polarPointR v (tailR b w) a r) * axialWeightR t v a r
  have hH : Measurable (Function.uncurry H) := by
    have hP : Measurable (fun p : ℝ × (Fin k → ℝ) =>
        polarPointR v (tailR b p.2) a p.1) := by
      unfold polarPointR
      fun_prop
    have hW : Measurable (fun p : ℝ × (Fin k → ℝ) => axialWeightR t v a p.1) := by
      unfold axialWeightR
      fun_prop
    exact (hF.comp hP).mul hW
  change (∫⁻ z, H (radF53 z) (unitF53 z) ∂stdGauss (Fin k)) = _
  rw [rad_direction_resample H hH]
  apply lintegral_congr
  intro z
  have hpoint : Measurable (fun w : Fin (r + k) → ℝ =>
      F (polarPointR v w a (radF53 z)) * axialWeightR t v a (radF53 z)) := by
    apply (hF.comp ?_).mul measurable_const
    unfold polarPointR spanV
    fun_prop
  exact (perpDirR_lintegral_tail b v hb _ hpoint).symm

noncomputable def axialMeasureR (t : Fin r → ℝ) (v : Fin r → Fin (r + k) → ℝ) :
    Measure ((Fin r → ℝ) × (Fin k → ℝ)) :=
  ((stdGauss (Fin r)).prod (stdGauss (Fin k))).withDensity
    (fun p => axialWeightR t v p.1 (radF53 p.2))

noncomputable def polarStateR (v : Fin r → Fin (r + k) → ℝ)
    (p : ((Fin r → ℝ) × (Fin k → ℝ)) × (Fin (r + k) → ℝ)) : Fin (r + k) → ℝ :=
  polarPointR v (perpDirR v p.2) p.1.1 (radF53 p.1.2)

theorem measurable_polarStateR (v : Fin r → Fin (r + k) → ℝ) : Measurable (polarStateR v) := by
  unfold polarStateR polarPointR axialY axialRad perpDirR spanV coordY radF53
  fun_prop

theorem axialMeasureR_lintegral (t : Fin r → ℝ) (v : Fin r → Fin (r + k) → ℝ)
    (F : ((Fin r → ℝ) × (Fin k → ℝ)) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p ∂axialMeasureR t v) =
      ∫⁻ a, ∫⁻ z, F (a, z) * axialWeightR t v a (radF53 z)
        ∂stdGauss (Fin k) ∂stdGauss (Fin r) := by
  have hw : Measurable (fun p : (Fin r → ℝ) × (Fin k → ℝ) => axialWeightR t v p.1 (radF53 p.2)) := by
    unfold axialWeightR axialY radF53
    fun_prop
  unfold axialMeasureR
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hF]
  simp only [Pi.mul_apply]
  rw [lintegral_prod (fun p : (Fin r → ℝ) × (Fin k → ℝ) =>
    axialWeightR t v p.1 (radF53 p.2) * F p) (hw.mul hF).aemeasurable]
  simp only [mul_comm]

/-- The Bingham law is the image of an axial probability law times an independent direction. -/
theorem lawRR_eq_polar_map
    (b : OrthonormalBasis (Fin (r + k)) ℝ (EuclideanSpace ℝ (Fin (r + k))))
    (v : Fin r → Fin (r + k) → ℝ) (hb : ∀ a : Fin r, b (Fin.castAdd k a) = WithLp.toLp 2 (v a)) (hn : 1 ≤ r+k) (t : Fin r → ℝ) :
    lawRR (r + k) t v =
      ((axialMeasureR t v).prod (stdGauss (Fin (r + k)))).map (polarStateR v) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lawRR_lintegral_polar b v hb hn t F hF,
    lintegral_map hF (measurable_polarStateR v)]
  rw [lintegral_prod (fun p => F (polarStateR v p))
    (hF.comp (measurable_polarStateR v)).aemeasurable]
  rw [axialMeasureR_lintegral t v (fun p =>
    ∫⁻ g, F (polarStateR v (p, g)) ∂stdGauss (Fin (r + k)))
    (hF.comp (measurable_polarStateR v)).lintegral_prod_right']
  apply lintegral_congr
  intro a
  apply lintegral_congr
  intro z
  rw [lintegral_mul_const (f := fun g => F (polarPointR v (perpDirR v g) a (radF53 z)))
    (axialWeightR t v a (radF53 z))]
  · rfl
  · apply hF.comp
    unfold polarPointR
    exact (measurable_const : Measurable (fun _ : Fin (r+k) → ℝ => spanV v (axialY a (radF53 z)))).add
      ((measurable_const : Measurable (fun _ : Fin (r+k) → ℝ => axialRad a (radF53 z))).smul
        (KeyProof.measurable_dir v))

theorem axialMeasureR_probability
    (b : OrthonormalBasis (Fin (r + k)) ℝ (EuclideanSpace ℝ (Fin (r + k))))
    (v : Fin r → Fin (r + k) → ℝ) (hb : ∀ a : Fin r, b (Fin.castAdd k a) = WithLp.toLp 2 (v a)) (hn : 1 ≤ r+k) (t : Fin r → ℝ) :
    IsProbabilityMeasure (axialMeasureR t v) := by
  letI : IsProbabilityMeasure (lawRR (r + k) t v) :=
    (BstLean.Part50.binghamA_antipodal hn (rkR t v)).sph.prob
  have h := congrArg (fun μ : Measure (Fin (r + k) → ℝ) => μ Set.univ)
    (lawRR_eq_polar_map b v hb hn t)
  simp only [measure_univ, Measure.map_apply (measurable_polarStateR v) MeasurableSet.univ,
    Set.preimage_univ, Measure.prod_apply, MeasurableSet.univ, lintegral_one] at h
  exact ⟨h.symm⟩


end BstLean.Part57.PropD57
