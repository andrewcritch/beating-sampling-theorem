import BstLean.Part57PropD_Bingham
import BstLean.Part57PropD_Bounds

/-! The axial law gives positive perpendicular radius almost everywhere. -/
namespace BstLean.Part57.PropD57
open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (radF53 unitF53)
variable {r k : ℕ}

theorem gauss_ne_zero_ae (k : ℕ) (hk : 1 ≤ k) : ∀ᵐ z ∂stdGauss (Fin k), z ≠ 0 := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hz : stdGauss (Fin k) {(0 : Fin k → ℝ)} = 0 := by
    change (Measure.pi (fun _ : Fin k => gaussianReal 0 1)) {0} = 0
    exact measure_singleton _
  rw [ae_iff]
  simpa only [not_not, Set.setOf_eq_eq_singleton] using hz

theorem sumsq_pos_of_ne_zero {ι : Type*} [Fintype ι] (z : ι → ℝ) (hz : z ≠ 0) :
    0 < ∑ i, z i ^ 2 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hz (funext h)
  exact lt_of_lt_of_le (sq_pos_of_ne_zero hi)
    (Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i))

theorem gauss_rad_pos_ae (k : ℕ) (hk : 1 ≤ k) :
    ∀ᵐ z ∂stdGauss (Fin k), 0 < radF53 z := by
  filter_upwards [gauss_ne_zero_ae k hk] with z hz
  exact Real.sqrt_pos_of_pos (sumsq_pos_of_ne_zero z hz)

theorem axialMeasureR_rad_pos_ae (t : Fin r → ℝ) (V : Fin r → Fin (r+k) → ℝ)
    (hk : 1 ≤ k) : ∀ᵐ p ∂axialMeasureR t V, 0 < radF53 p.2 := by
  have h : ∀ᵐ p ∂(stdGauss (Fin r)).prod (stdGauss (Fin k)), 0 < radF53 p.2 :=
    (MeasureTheory.Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const
      (BstLean.Part53.measurable_radF.comp measurable_snd))).mpr
        (Filter.Eventually.of_forall fun _ => gauss_rad_pos_ae k hk)
  have hac : axialMeasureR t V ≪ (stdGauss (Fin r)).prod (stdGauss (Fin k)) :=
    withDensity_absolutelyContinuous _ _
  exact h.filter_mono hac.ae_le

theorem axialMeasureR_axialRad_pos_ae (t : Fin r → ℝ) (V : Fin r → Fin (r+k) → ℝ)
    (hk : 1 ≤ k) : ∀ᵐ p ∂axialMeasureR t V, 0 < axialRad p.1 (radF53 p.2) := by
  filter_upwards [axialMeasureR_rad_pos_ae t V hk] with p hp
  unfold axialRad
  apply div_pos hp
  apply Real.sqrt_pos_of_pos
  exact add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (sq_pos_of_pos hp)

theorem unitF53_sumsq_of_ne_zero (z : Fin k → ℝ) (hz : z ≠ 0) :
    ∑ i, unitF53 z i ^ 2 = 1 := by
  have hs := sumsq_pos_of_ne_zero z hz
  unfold unitF53
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [div_pow, one_pow, Real.sq_sqrt hs.le]
  simpa only [one_div] using inv_mul_cancel₀ hs.ne'

theorem perpDirR_unit_ae
    (b : OrthonormalBasis (Fin (r+k)) ℝ (EuclideanSpace ℝ (Fin (r+k))))
    (V : Fin r → Fin (r+k) → ℝ)
    (hb : ∀ a : Fin r, b (Fin.castAdd k a) = WithLp.toLp 2 (V a)) (hk : 1 ≤ k) :
    ∀ᵐ g ∂stdGauss (Fin (r+k)), ∑ i, perpDirR V g i ^ 2 = 1 := by
  have hm : (stdGauss (Fin (r+k))).map (perpDirR V) =
      (stdGauss (Fin k)).map (fun z => tailR b (unitF53 z)) := by
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_map hF (KeyProof.measurable_dir V),
      lintegral_map hF]
    · exact perpDirR_lintegral_tail b V hb F hF
    · exact (measurable_tailR b |>.comp BstLean.Part53.measurable_unitF)
  have hs : MeasurableSet {w : Fin (r+k) → ℝ | ∑ i, w i ^ 2 = 1} := by
    exact measurableSet_eq_fun (by fun_prop) measurable_const
  have ht : ∀ᵐ z ∂stdGauss (Fin k), ∑ i, tailR b (unitF53 z) i ^ 2 = 1 := by
    filter_upwards [gauss_ne_zero_ae k hk] with z hz
    rw [tailR_sumsq, unitF53_sumsq_of_ne_zero z hz]
  have ht' := (MeasureTheory.ae_map_iff
    (measurable_tailR b |>.comp BstLean.Part53.measurable_unitF).aemeasurable hs).mpr ht
  change ∀ᵐ w ∂(stdGauss (Fin k)).map (fun z => tailR b (unitF53 z)),
    ∑ i, w i ^ 2 = 1 at ht'
  rw [← hm] at ht'
  exact (MeasureTheory.ae_map_iff (KeyProof.measurable_dir V).aemeasurable hs).mp ht'

theorem coordY_span_perp (V : Fin r → Fin n → ℝ) (hV : OrthoF V)
    (y : Fin r → ℝ) (u : ℝ) (g : Fin n → ℝ) :
    coordY V (spanV V y + u • perpDirR V g) = y := by
  classical
  ext a
  simp only [coordY, Pi.add_apply, Pi.smul_apply, smul_eq_mul, spanV, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  have ht : (∑ i, V a i * (u * perpDirR V g i)) = 0 := by
    rw [show (∑ i, V a i * (u * perpDirR V g i)) = u * ∑ i, V a i * perpDirR V g i by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
      perpDirR_orthogonal V hV g a, mul_zero]
  rw [ht, add_zero, Finset.sum_comm]
  have he b : (∑ i, V a i * (y b * V b i)) = y b * (if a=b then 1 else 0) := by
    rw [← hV a b, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [he]
  simp

theorem rhoSq_span_perp (V : Fin r → Fin n → ℝ) (hV : OrthoF V)
    (y : Fin r → ℝ) (u : ℝ) (g : Fin n → ℝ)
    (hg : ∑ i, perpDirR V g i ^ 2 = 1) :
    rhoSq V (spanV V y + u • perpDirR V g) = u ^ 2 := by
  unfold rhoSq
  rw [coordY_span_perp V hV y u g]
  simp only [Pi.add_apply, spanV, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left,
    mul_pow, ← Finset.mul_sum, hg, mul_one]

end BstLean.Part57.PropD57
