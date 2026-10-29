import BstLean.Part272Kernel
import BstLean.Part272Tilt

/-!
# Part 272 (V3a): the law of one coordinate of a uniform direction

`coord_law`: for `N ≥ 3`, `T = (G/|G|)₀` with `G` standard Gaussian in `ℝ^N` has density
proportional to `(1 − z²)^{(N−3)/2}` on `[−1, 1]`.

Proof: split `G = (x, w)`; for `w ≠ 0` substitute `x = |w| z/√(1 − z²)` (`coordSub_gaussian`);
exchange the integrals (`integrable_coordKer`); the inner Gaussian integral is a radial tilt
(`radial_tilt`). The constant drops out after normalization with `g = 1`.
-/

namespace BstLean.Part272

open Real MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (unitF53 radF53 measurable_radF measurable_unitF)
open BstLean.Part162 (radF_nonneg)

/-- The Gaussian density at the substituted point. -/
theorem pdf_coordSub {r z : ℝ} (hz : z ∈ Ioo (-1 : ℝ) 1) :
    gaussianPDFReal 0 1 (coordSub r z) =
      (√(2*π))⁻¹ * exp (-(1/(1-z^2)-1)*r^2/2) := by
  have hb := coordSub_base_pos hz
  have hs : √(1-z^2) ≠ 0 := (sqrt_pos.mpr hb).ne'
  rw [gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  congr 2
  unfold coordSub
  rw [div_pow, mul_pow, sq_sqrt hb.le]
  field_simp
  ring

/-- The transformed kernel on `ℝ^k × (−1, 1)`. -/
noncomputable def coordKer (g : ℝ → ℝ) {k : ℕ} (p : (Fin k → ℝ) × ℝ) : ℝ :=
  (g p.2 * ((√(2*π))⁻¹ / ((1-p.2^2)*√(1-p.2^2)))) *
    (radF53 p.1 * exp (-(1/(1-p.2^2)-1)*(radF53 p.1)^2/2))

theorem measurable_coordKer {k : ℕ} {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable (coordKer g (k := k)) := by
  have hz : Measurable (fun p : (Fin k → ℝ) × ℝ => p.2) := measurable_snd
  have hv : Measurable (fun p : (Fin k → ℝ) × ℝ => 1 - p.2^2) :=
    measurable_const.sub (hz.pow_const 2)
  have hR : Measurable (fun p : (Fin k → ℝ) × ℝ => radF53 p.1) :=
    measurable_radF.comp measurable_fst
  unfold coordKer
  exact ((hg.comp hz).mul (measurable_const.div (hv.mul hv.sqrt))).mul
    (hR.mul (Real.measurable_exp.comp
      ((((measurable_const.div hv).sub measurable_const).neg.mul (hR.pow_const 2)).div_const 2)))

/-- For a positive tail radius the scalar Gaussian integral is the kernel integral. -/
theorem coordSub_ker {k : ℕ} (g : ℝ → ℝ) {w : Fin k → ℝ} (hr : 0 < radF53 w) :
    ∫ x, g (x/√(x^2+(radF53 w)^2)) ∂gaussianReal 0 1 =
      ∫ z in Ioo (-1 : ℝ) 1, coordKer g (w, z) := by
  rw [coordSub_gaussian hr]
  refine setIntegral_congr_fun measurableSet_Ioo fun z hz => ?_
  dsimp only [coordKer]
  rw [pdf_coordSub hz]
  ring

/-- The inner Gaussian integral of the kernel (radial tilt). -/
theorem coordKer_tilt {k : ℕ} (hk : 2 ≤ k) (g : ℝ → ℝ) {z : ℝ} (hz : z ∈ Ioo (-1 : ℝ) 1) :
    ∫ w, coordKer g (w, z) ∂stdGauss (Fin k) =
      (∫ w, radF53 w ∂stdGauss (Fin k)) * (√(2*π))⁻¹ * (g z * (√(1-z^2))^(k-2)) := by
  have hb := coordSub_base_pos hz
  have hs : 0 < √(1-z^2) := sqrt_pos.mpr hb
  have h3 : (√(1-z^2))^(k+1) = (√(1-z^2))^(k-2) * ((1-z^2)*√(1-z^2)) := by
    rw [show k+1 = (k-2)+3 by omega, pow_add,
      show (√(1-z^2))^3 = (1-z^2)*√(1-z^2) by rw [pow_succ, sq_sqrt hb.le]]
  have hd : (1-z^2)*√(1-z^2) ≠ 0 := (mul_pos hb hs).ne'
  dsimp only [coordKer]
  rw [integral_const_mul, radial_tilt hb, h3, div_eq_mul_inv]
  calc _ = (∫ w, radF53 w ∂stdGauss (Fin k)) * (√(2*π))⁻¹ * (g z * (√(1-z^2))^(k-2)) *
        (((1-z^2)*√(1-z^2)) * ((1-z^2)*√(1-z^2))⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hd, mul_one]

theorem norm_coordKer {k : ℕ} (g : ℝ → ℝ) {z : ℝ} (hz : z ∈ Ioo (-1 : ℝ) 1)
    (w : Fin k → ℝ) :
    ‖coordKer g (w, z)‖ = coordKer (fun z => |g z|) (w, z) := by
  have hb := coordSub_base_pos hz
  have hs : 0 < √(1-z^2) := sqrt_pos.mpr hb
  dsimp only [coordKer]
  rw [Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (div_nonneg (inv_nonneg.mpr (sqrt_nonneg _)) (mul_pos hb hs).le),
    abs_of_nonneg (mul_nonneg (radF_nonneg w) (exp_pos _).le)]

theorem integrable_coordKer_slice {k : ℕ} [Nonempty (Fin k)] (g : ℝ → ℝ) {z : ℝ}
    (hz : z ∈ Ioo (-1 : ℝ) 1) :
    Integrable (fun w => coordKer g (w, z)) (stdGauss (Fin k)) := by
  have hb := coordSub_base_pos hz
  have hc : 0 ≤ 1/(1-z^2)-1 := by
    rw [sub_nonneg, le_div_iff₀ hb]
    nlinarith [sq_nonneg z]
  dsimp only [coordKer]
  refine Integrable.const_mul ?_ _
  refine (BstLean.Part162.integrable_radF_pow (d := k) 1).mono' ?_ ?_
  · exact (measurable_radF.mul (Real.measurable_exp.comp
      ((measurable_const.mul (measurable_radF.pow_const 2)).div_const 2))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun w => ?_
    have hr := radF_nonneg w
    have he : exp (-(1/(1-z^2)-1)*(radF53 w)^2/2) ≤ 1 :=
      exp_le_one_iff.mpr (by nlinarith [mul_nonneg hc (sq_nonneg (radF53 w))])
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr (exp_pos _).le), pow_one]
    calc radF53 w * exp (-(1/(1-z^2)-1)*(radF53 w)^2/2) ≤ radF53 w * 1 :=
          mul_le_mul_of_nonneg_left he hr
      _ = radF53 w := mul_one _

/-- The kernel is integrable on the product, which justifies the exchange of integrals. -/
theorem integrable_coordKer {k : ℕ} (hk : 2 ≤ k) {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ}
    (hM : ∀ z ∈ Icc (-1 : ℝ) 1, |g z| ≤ M) :
    Integrable (coordKer g) ((stdGauss (Fin k)).prod (volume.restrict (Ioo (-1 : ℝ) 1))) := by
  haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  rw [integrable_prod_iff' (measurable_coordKer hg).aestronglyMeasurable]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact integrable_coordKer_slice g hz
  · set C := ∫ w, radF53 w ∂stdGauss (Fin k) with hCdef
    have hC : 0 ≤ C := integral_nonneg fun w => radF_nonneg w
    have hcongr : (fun z => ∫ w, ‖coordKer g (w, z)‖ ∂stdGauss (Fin k))
        =ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)]
        fun z => C * (√(2*π))⁻¹ * (|g z| * (√(1-z^2))^(k-2)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
      rw [integral_congr_ae (Filter.Eventually.of_forall fun w => norm_coordKer g hz w)]
      exact coordKer_tilt hk _ hz
    refine Integrable.congr ?_ hcongr.symm
    haveI : IsFiniteMeasure (volume.restrict (Ioo (-1 : ℝ) 1)) :=
      isFiniteMeasure_restrict.mpr (by simp)
    have hK : 0 ≤ C * (√(2*π))⁻¹ := mul_nonneg hC (inv_nonneg.mpr (sqrt_nonneg _))
    refine (integrable_const (C * (√(2*π))⁻¹ * M)).mono' ?_ ?_
    · exact (measurable_const.mul ((continuous_abs.measurable.comp hg).mul
        (((measurable_const.sub (measurable_id.pow_const 2)).sqrt).pow_const _))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
      have hp : (√(1-z^2))^(k-2) ≤ 1 :=
        pow_le_one₀ (sqrt_nonneg _) ((sqrt_le_sqrt (by nlinarith : 1-z^2 ≤ 1)).trans_eq sqrt_one)
      have hg' := hM z (Ioo_subset_Icc_self hz)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK
        (mul_nonneg (abs_nonneg _) (pow_nonneg (sqrt_nonneg _) _)))]
      calc C * (√(2*π))⁻¹ * (|g z| * (√(1-z^2))^(k-2)) ≤ C * (√(2*π))⁻¹ * (M * 1) := by
            apply mul_le_mul_of_nonneg_left _ hK
            exact mul_le_mul hg' hp (pow_nonneg (sqrt_nonneg _) _) ((abs_nonneg _).trans hg')
        _ = C * (√(2*π))⁻¹ * M := by ring

/-- The coordinate law before normalization. -/
theorem coord_unnorm {N : ℕ} (hN : 3 ≤ N) {g : ℝ → ℝ} (hg : Measurable g)
    (hb : ∃ M, ∀ z ∈ Icc (-1 : ℝ) 1, |g z| ≤ M) :
    ∫ v, g (unitF53 v ⟨0, by omega⟩) ∂stdGauss (Fin N) =
      (∫ w, radF53 w ∂stdGauss (Fin (N-1))) * (√(2*π))⁻¹ *
        ∫ z in Ioo (-1 : ℝ) 1, g z * (√(1-z^2))^(N-3) := by
  obtain ⟨M, hM⟩ := hb
  have hk : 2 ≤ N - 1 := by omega
  have hmeasP : Measurable (fun p : ℝ × (Fin (N-1) → ℝ) =>
      g (p.1/√(p.1^2+(radF53 p.2)^2))) :=
    hg.comp (measurable_fst.div ((measurable_fst.pow_const 2).add
      ((measurable_radF.comp measurable_snd).pow_const 2)).sqrt)
  have hintP : Integrable (fun p : ℝ × (Fin (N-1) → ℝ) =>
      g (p.1/√(p.1^2+(radF53 p.2)^2))) ((gaussianReal 0 1).prod (stdGauss (Fin (N-1)))) := by
    refine (integrable_const M).mono' hmeasP.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    exact hM _ (scalar_coord_mem _ _)
  rw [coord_split (by omega) hg, integral_prod_symm _ hintP]
  have hnz : ∀ᵐ w ∂stdGauss (Fin (N-1)), BstLean.Part130.normSq w ≠ 0 :=
    ae_iff.mpr (by simpa using BstLean.Part161.stdGauss_normSq_zero (k := N-1) (by omega))
  have hae : ∀ᵐ w ∂stdGauss (Fin (N-1)),
      ∫ x, g (x/√(x^2+(radF53 w)^2)) ∂gaussianReal 0 1 =
        ∫ z in Ioo (-1 : ℝ) 1, coordKer g (w, z) := by
    filter_upwards [hnz] with w hw
    have hr : 0 < radF53 w :=
      sqrt_pos.mpr (lt_of_le_of_ne (BstLean.Part130.normSq_nonneg w) (Ne.symm hw))
    exact coordSub_ker g hr
  rw [integral_congr_ae hae,
    integral_integral_swap (f := fun w z => coordKer g (w, z)) (integrable_coordKer hk hg hM),
    setIntegral_congr_fun measurableSet_Ioo (fun z hz => coordKer_tilt hk g hz),
    integral_const_mul, show N - 1 - 2 = N - 3 by omega]

/-- **V3a.** The first coordinate of a uniform direction in `ℝ^N` (`N ≥ 3`) has density
proportional to `(1 − z²)^{(N−3)/2}` on `[−1, 1]`. -/
theorem coord_law {N : ℕ} (hN : 3 ≤ N) {g : ℝ → ℝ} (hg : Measurable g)
    (hb : ∃ M, ∀ z ∈ Set.Icc (-1:ℝ) 1, |g z| ≤ M) :
    ∫ v, g (unitF53 v ⟨0, by omega⟩) ∂stdGauss (Fin N) =
      (∫ z in (-1:ℝ)..1, g z * (1 - z ^ 2) ^ (((N:ℝ) - 3) / 2)) /
      (∫ z in (-1:ℝ)..1, (1 - z ^ 2) ^ (((N:ℝ) - 3) / 2)) := by
  have hpow : ∀ z ∈ Ioo (-1:ℝ) 1, (1 - z^2) ^ (((N:ℝ) - 3) / 2) = (√(1-z^2))^(N-3) := by
    intro z hz
    have hb := coordSub_base_pos hz
    rw [show (√(1-z^2))^(N-3) = (√(1-z^2))^((N-3 : ℕ) : ℝ) from (rpow_natCast _ _).symm,
      sqrt_eq_rpow, ← rpow_mul hb.le]
    congr 1
    rw [Nat.cast_sub (by omega : 3 ≤ N)]
    push_cast
    ring
  have hI : ∀ f : ℝ → ℝ, ∫ z in (-1:ℝ)..1, f z = ∫ z in Ioo (-1:ℝ) 1, f z := fun f => by
    rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
  have hg' : ∫ z in Ioo (-1:ℝ) 1, g z * (1 - z^2) ^ (((N:ℝ) - 3) / 2) =
      ∫ z in Ioo (-1:ℝ) 1, g z * (√(1-z^2))^(N-3) :=
    setIntegral_congr_fun measurableSet_Ioo fun z hz => by simp only [hpow z hz]
  have h1' : ∫ z in Ioo (-1:ℝ) 1, (1 - z^2) ^ (((N:ℝ) - 3) / 2) =
      ∫ z in Ioo (-1:ℝ) 1, (√(1-z^2))^(N-3) :=
    setIntegral_congr_fun measurableSet_Ioo fun z hz => by simp only [hpow z hz]
  rw [hI, hI, hg', h1', coord_unnorm hN hg hb]
  have h1 := coord_unnorm hN (g := fun _ => (1:ℝ)) measurable_const ⟨1, fun z _ => by simp⟩
  have hone : ∫ v : Fin N → ℝ, (1:ℝ) ∂stdGauss (Fin N) = 1 := by simp
  simp only [one_mul] at h1
  rw [hone] at h1
  have hW : (∫ z in Ioo (-1:ℝ) 1, (√(1-z^2))^(N-3)) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    exact one_ne_zero h1
  rw [eq_div_iff hW]
  calc _ = (∫ w, radF53 w ∂stdGauss (Fin (N-1))) * (√(2*π))⁻¹ *
        (∫ z in Ioo (-1:ℝ) 1, (√(1-z^2))^(N-3)) *
        ∫ z in Ioo (-1:ℝ) 1, g z * (√(1-z^2))^(N-3) := by ring
    _ = _ := by rw [← h1, one_mul]

end BstLean.Part272

#print axioms BstLean.Part272.coord_law
