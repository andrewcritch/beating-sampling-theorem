import BstLean.Part53Defs
import BstLean.Part53Remez_DensityScalar

namespace BstLean.Part53.RemezAux

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)

/-- The product Gaussian density. -/
noncomputable def gaussianDensity {ι : Type*} [Fintype ι] (z : ι → ℝ) : ℝ := ∏ i, gaussianPDFReal 0 1 (z i)

lemma stdGauss_as_density {ι : Type*} [Fintype ι] :
    stdGauss ι = (volume : Measure (ι → ℝ)).withDensity (fun z => ENNReal.ofReal (gaussianDensity z)) := by
  classical
  unfold stdGauss
  apply Measure.pi_eq
  intro s hs
  have hmeas : ∀ i, Measurable ((s i).indicator (gaussianPDFReal 0 1)) :=
    fun i => (measurable_gaussianPDFReal 0 1).indicator (hs i)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have he : ∀ z : ι → ℝ, (Set.univ.pi s).indicator (fun z => ENNReal.ofReal (gaussianDensity z)) z =
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


lemma gaussianDensity_nonneg {ι : Type} [Fintype ι] (Z : ι → ℝ) :
    0 ≤ gaussianDensity Z := by
  classical
  exact Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg 0 1 (Z i))

lemma gaussianDensity_measurable {ι : Type} [Fintype ι] :
    Measurable (gaussianDensity : (ι → ℝ) → ℝ) := by
  classical
  unfold gaussianDensity
  exact Finset.measurable_prod _ (fun i _ =>
    (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i))

lemma gaussianDensity_eq_exp {ι : Type} [Fintype ι] (Z : ι → ℝ) :
    gaussianDensity Z = (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι *
      Real.exp (-(∑ i, Z i ^ 2) / 2) := by
  classical
  unfold gaussianDensity
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
  rw [← Finset.sum_div, ← Finset.sum_neg_distrib]

lemma sqrt_sumsq_ofLp {ι : Type} [Fintype ι] (Z : EuclideanSpace ℝ ι) :
    Real.sqrt (∑ i, (WithLp.ofLp Z i) ^ 2) = ‖Z‖ := by
  rw [← EuclideanSpace.real_norm_sq_eq Z, Real.sqrt_sq (norm_nonneg Z)]

noncomputable def gaussianRadialFactor (ι : Type) [Fintype ι] : ℝ :=
  (Fintype.card ι : ℝ) * (volume : Measure (EuclideanSpace ℝ ι)).real (Metric.ball 0 1) *
    (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι

lemma gaussianRadialFactor_nonneg (ι : Type) [Fintype ι] :
    0 ≤ gaussianRadialFactor ι := by unfold gaussianRadialFactor; positivity

theorem gaussian_radius_integral (ι : Type) [Fintype ι] [Nonempty ι] (F : ℝ → ℝ) :
    ∫ Z, F (Real.sqrt (∑ i, Z i ^ 2)) ∂stdGauss ι =
      gaussianRadialFactor ι * ∫ r in Set.Ioi (0 : ℝ),
        r ^ (Fintype.card ι - 1) * Real.exp (-r ^ 2 / 2) * F r := by
  classical
  have hd : Measurable (fun Z : ι → ℝ => ENNReal.ofReal (gaussianDensity Z)) :=
    ENNReal.measurable_ofReal.comp gaussianDensity_measurable
  rw [stdGauss_as_density, integral_withDensity_eq_integral_toReal_smul hd
    (.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (gaussianDensity_nonneg _), smul_eq_mul]
  rw [← (PiLp.volume_preserving_ofLp ι).integral_comp
    (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurableEmbedding]
  have he (Z : EuclideanSpace ℝ ι) :
      gaussianDensity (WithLp.ofLp Z) * F (Real.sqrt (∑ i, (WithLp.ofLp Z i) ^ 2)) =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι *
        (Real.exp (-‖Z‖ ^ 2 / 2) * F ‖Z‖) := by
    rw [gaussianDensity_eq_exp, sqrt_sumsq_ofLp, ← EuclideanSpace.real_norm_sq_eq Z]
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_fun_norm_addHaar
    (volume : Measure (EuclideanSpace ℝ ι)) (fun r : ℝ => Real.exp (-r ^ 2 / 2) * F r)]
  simp only [finrank_euclideanSpace, nsmul_eq_mul, smul_eq_mul]
  unfold gaussianRadialFactor
  simp only [← mul_assoc]
  ring

theorem gaussian_radius_integrable (ι : Type) [Fintype ι] [Nonempty ι] (F : ℝ → ℝ)
    (hF : Integrable (fun Z => F (Real.sqrt (∑ i, Z i ^ 2))) (stdGauss ι)) :
    IntegrableOn (fun r => r ^ (Fintype.card ι - 1) * Real.exp (-r ^ 2 / 2) * F r)
      (Set.Ioi 0) volume := by
  have hd : Measurable (fun Z : ι → ℝ => ENNReal.ofReal (gaussianDensity Z)) :=
    ENNReal.measurable_ofReal.comp gaussianDensity_measurable
  rw [stdGauss_as_density] at hF
  have hi := (integrable_withDensity_iff_integrable_smul' hd
    (.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hF
  simp only [ENNReal.toReal_ofReal (gaussianDensity_nonneg _), smul_eq_mul] at hi
  have hL := (PiLp.volume_preserving_ofLp ι).integrable_comp_of_integrable hi
  simp only [Function.comp_def] at hL
  have he (Z : EuclideanSpace ℝ ι) :
      gaussianDensity (WithLp.ofLp Z) * F (Real.sqrt (∑ i, (WithLp.ofLp Z i) ^ 2)) =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι *
        (Real.exp (-‖Z‖ ^ 2 / 2) * F ‖Z‖) := by
    rw [gaussianDensity_eq_exp, sqrt_sumsq_ofLp, ← EuclideanSpace.real_norm_sq_eq Z]
    ring
  simp_rw [he] at hL
  have hc : ((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι) ≠ 0 := by positivity
  have hb : Integrable (fun Z : EuclideanSpace ℝ ι => Real.exp (-‖Z‖ ^ 2 / 2) * F ‖Z‖)
      volume := by
    apply (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc) _).mp
    convert hL using 1
  have hr := (integrable_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ ι))
    (f := fun r : ℝ => Real.exp (-r ^ 2 / 2) * F r)).mp hb
  simpa only [finrank_euclideanSpace, smul_eq_mul, mul_assoc] using hr

lemma radialWeight_eq_pow (Q : ℕ) (hQ : 1 ≤ Q) {t : ℝ} (ht : 0 < t) :
    radialWeight Q t = t ^ (Q - 1) * Real.exp (-(Q : ℝ) / 2 * (t ^ 2 - 1)) := by
  unfold radialWeight
  rw [show ((Q : ℝ) - 1) * Real.log t - (Q : ℝ) / 2 * (t ^ 2 - 1) =
      ((Q - 1 : ℕ) : ℝ) * Real.log t + (-(Q : ℝ) / 2 * (t ^ 2 - 1)) by
        rw [Nat.cast_sub hQ]; push_cast; ring,
    Real.exp_add, Real.exp_nat_mul, Real.exp_log ht]

lemma scaled_raw_weight (Q : ℕ) (hQ : 1 ≤ Q) {t : ℝ} (ht : 0 < t) :
    (Real.sqrt Q * t) ^ (Q - 1) * Real.exp (-(Real.sqrt Q * t) ^ 2 / 2) =
      (Real.sqrt Q) ^ (Q - 1) * Real.exp (-(Q : ℝ) / 2) * radialWeight Q t := by
  rw [radialWeight_eq_pow Q hQ ht, mul_pow, mul_pow,
    Real.sq_sqrt (show (0 : ℝ) ≤ Q by positivity)]
  rw [show -((Q : ℝ) * t ^ 2) / 2 =
      -(Q : ℝ) / 2 + (-(Q : ℝ) / 2 * (t ^ 2 - 1)) by ring, Real.exp_add]
  ring

noncomputable def normalizedRadialFactor (ι : Type) [Fintype ι] : ℝ :=
  gaussianRadialFactor ι * (Real.sqrt (Fintype.card ι)) ^ Fintype.card ι *
    Real.exp (-(Fintype.card ι : ℝ) / 2)

lemma normalizedRadialFactor_nonneg (ι : Type) [Fintype ι] :
    0 ≤ normalizedRadialFactor ι := by
  unfold normalizedRadialFactor
  exact mul_nonneg (mul_nonneg (gaussianRadialFactor_nonneg ι) (by positivity)) (by positivity)

theorem normalized_radius_integral (ι : Type) [Fintype ι] [Nonempty ι] (F : ℝ → ℝ) :
    ∫ Z, F (Real.sqrt (∑ i, Z i ^ 2) / Real.sqrt (Fintype.card ι)) ∂stdGauss ι =
      normalizedRadialFactor ι * ∫ t in Set.Ioi (0 : ℝ), radialWeight (Fintype.card ι) t * F t := by
  let Q := Fintype.card ι
  have hQ : 1 ≤ Q := Fintype.card_pos
  have hs : 0 < Real.sqrt Q := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < Q from hQ))
  rw [gaussian_radius_integral ι (fun r => F (r / Real.sqrt Q))]
  let g : ℝ → ℝ := fun r => r ^ (Q - 1) * Real.exp (-r ^ 2 / 2) * F (r / Real.sqrt Q)
  have hscale := integral_comp_mul_left_Ioi' g 0 hs
  simp only [mul_zero, smul_eq_mul] at hscale
  change gaussianRadialFactor ι * (∫ r in Set.Ioi (0 : ℝ), g r) = _
  rw [← hscale]
  have hi : (∫ t in Set.Ioi (0 : ℝ), g (Real.sqrt Q * t)) =
      (Real.sqrt Q) ^ (Q - 1) * Real.exp (-(Q : ℝ) / 2) *
        ∫ t in Set.Ioi (0 : ℝ), radialWeight Q t * F t := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp [g]
    rw [mul_div_cancel_left₀ t hs.ne', scaled_raw_weight Q hQ ht]
    ring
  rw [hi]
  have hp : Real.sqrt Q * (Real.sqrt Q) ^ (Q - 1) = (Real.sqrt Q) ^ Q := by
    rw [← pow_succ']
    congr 1
    omega
  unfold normalizedRadialFactor
  change _ = gaussianRadialFactor ι * (Real.sqrt Q) ^ Q * Real.exp (-(Q : ℝ) / 2) * _
  rw [show gaussianRadialFactor ι * (Real.sqrt Q *
      ((Real.sqrt Q) ^ (Q - 1) * Real.exp (-(Q : ℝ) / 2) *
        ∫ t in Set.Ioi (0 : ℝ), radialWeight Q t * F t)) =
      gaussianRadialFactor ι * (Real.sqrt Q * (Real.sqrt Q) ^ (Q - 1)) *
        Real.exp (-(Q : ℝ) / 2) * (∫ t in Set.Ioi (0 : ℝ), radialWeight Q t * F t) by ring]
  rw [hp]

lemma normalized_radius_mass (ι : Type) [Fintype ι] [Nonempty ι] :
    normalizedRadialFactor ι * ∫ t in Set.Ioi (0 : ℝ), radialWeight (Fintype.card ι) t = 1 := by
  have h := normalized_radius_integral ι (fun _ => 1)
  simpa only [integral_const, probReal_univ, one_smul, mul_one] using h.symm

theorem normalized_radius_integrable (ι : Type) [Fintype ι] [Nonempty ι] (F : ℝ → ℝ)
    (hF : Integrable (fun Z => F (Real.sqrt (∑ i, Z i ^ 2) /
      Real.sqrt (Fintype.card ι))) (stdGauss ι)) :
    IntegrableOn (fun t => radialWeight (Fintype.card ι) t * F t) (Set.Ioi 0) volume := by
  let Q := Fintype.card ι
  have hQ : 1 ≤ Q := Fintype.card_pos
  have hs : 0 < Real.sqrt Q := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < Q from hQ))
  let g : ℝ → ℝ := fun r => r ^ (Q - 1) * Real.exp (-r ^ 2 / 2) * F (r / Real.sqrt Q)
  have hg : IntegrableOn g (Set.Ioi 0) volume :=
    gaussian_radius_integrable ι (fun r => F (r / Real.sqrt Q)) hF
  have hsc : IntegrableOn (fun t => g (Real.sqrt Q * t)) (Set.Ioi 0) volume :=
    (integrableOn_Ioi_comp_mul_left_iff g 0 hs).mpr (by simpa only [mul_zero] using hg)
  have he : Set.EqOn (fun t => g (Real.sqrt Q * t))
      (fun t => ((Real.sqrt Q) ^ (Q - 1) * Real.exp (-(Q : ℝ) / 2)) *
        (radialWeight Q t * F t)) (Set.Ioi 0) := by
    intro t ht
    dsimp [g]
    rw [mul_div_cancel_left₀ t hs.ne', scaled_raw_weight Q hQ ht]
    ring
  have hi := hsc.congr_fun he measurableSet_Ioi
  have hc : ((Real.sqrt Q) ^ (Q - 1) * Real.exp (-(Q : ℝ) / 2)) ≠ 0 := by positivity
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc) _).mp hi

theorem radial_interval_comparison (ι : Type) [Fintype ι] (hQ : 1000 ≤ Fintype.card ι)
    (p : Polynomial ℝ)
    (hp : Integrable (fun Z => (p.eval (Real.sqrt (∑ i, Z i ^ 2) /
      Real.sqrt (Fintype.card ι))) ^ 2) (stdGauss ι)) :
    (Real.sqrt (Fintype.card ι) / 5) *
      (∫ t in (1 - halfWidth (Fintype.card ι))..(1 + halfWidth (Fintype.card ι)), p.eval t ^ 2) ≤
      ∫ Z, (p.eval (Real.sqrt (∑ i, Z i ^ 2) / Real.sqrt (Fintype.card ι))) ^ 2 ∂stdGauss ι := by
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let Q := Fintype.card ι
  let w := halfWidth Q
  let A := normalizedRadialFactor ι
  have hQr : (1000 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hs : 30 ≤ Real.sqrt Q := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_num; linarith)
  have hw : 0 < w := by dsimp [w, halfWidth]; positivity
  have hw1 : w ≤ 1 / 60 := by
    dsimp [w, halfWidth]
    exact (div_le_div_iff₀ (by positivity) (by norm_num)).mpr (by linarith)
  have hsub : Set.Ioc (1 - w) (1 + w) ⊆ Set.Ioi (0 : ℝ) := by
    intro t ht
    simp only [Set.mem_Ioc, Set.mem_Ioi] at ht ⊢
    linarith
  let f : ℝ → ℝ := fun t => A * radialWeight Q t * p.eval t ^ 2
  have hi : IntegrableOn f (Set.Ioi 0) volume := by
    dsimp only [IntegrableOn, f]
    simp_rw [mul_assoc]
    exact (normalized_radius_integrable ι (fun t => p.eval t ^ 2) hp).const_mul A
  have hmono : (Real.sqrt Q / 5) * (∫ t in Set.Ioc (1-w) (1+w), p.eval t ^ 2) ≤
      ∫ t in Set.Ioc (1-w) (1+w), f t := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on
      ((p.continuous.pow 2).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self |>.const_mul _)
      (hi.mono_set hsub) measurableSet_Ioc
    intro t ht
    have hlow := normalized_radialWeight_lower (q := (Q : ℝ)) hQr
      (normalizedRadialFactor_nonneg ι) (normalized_radius_mass ι)
      (show t ∈ Set.Icc (1 - halfWidth Q) (1 + halfWidth Q) from ⟨ht.1.le, ht.2⟩)
    exact mul_le_mul_of_nonneg_right hlow (sq_nonneg _)
  have hbig : (∫ t in Set.Ioc (1-w) (1+w), f t) ≤ ∫ t in Set.Ioi (0 : ℝ), f t := by
    apply setIntegral_mono_set hi
      (Filter.Eventually.of_forall fun t => ?_) (Filter.Eventually.of_forall hsub)
    dsimp [f, A]
    exact mul_nonneg (mul_nonneg (normalizedRadialFactor_nonneg ι)
      (radialWeight_pos _ _).le) (sq_nonneg _)
  rw [normalized_radius_integral ι (fun t => p.eval t ^ 2)]
  rw [intervalIntegral.integral_of_le (by linarith : 1-w ≤ 1+w)]
  change (Real.sqrt Q / 5) * (∫ t in Set.Ioc (1-w) (1+w), p.eval t ^ 2) ≤ _
  have he : (∫ t in Set.Ioi (0 : ℝ), f t) =
      A * ∫ t in Set.Ioi (0 : ℝ), radialWeight Q t * p.eval t ^ 2 := by
    simp only [f, mul_assoc, integral_const_mul]
  exact hmono.trans (hbig.trans_eq he)

end BstLean.Part53.RemezAux
