import BstLean.Part211Smooth
import BstLean.Part211Radial

/-! The sharp first-layer scalar moment under the actual Gaussian row distribution. -/
namespace BstLean.Part211
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part137 (psiS measurable_psiS)

theorem gaussian_smoothing_integrable {n : ℕ} (u : Fin n → ℝ) (a s : ℝ) :
    Integrable (fun g : Fin n → ℝ => psiS (s * radialRoot g) (a * (g ⬝ᵥ u)) ^ 2)
      (stdGauss (Fin n)) := by
  have hi := ((BstLean.Part160.MFB.lin_moments u).2.2.1.const_mul (a ^ 2)).add
    (((BstLean.Part149.stdGauss_normSq n).1.div_const n).const_mul (s ^ 2))
  apply hi.mono'
  · exact ((measurable_psiS.comp ((measurable_const.mul
        (continuous_normSq.measurable.div_const n).sqrt).prodMk
        (measurable_const.mul (by unfold dotProduct; fun_prop)))).pow_const 2).aestronglyMeasurable
  · exact ae_of_all _ fun g => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have h := psiS_square_bound (s * radialRoot g) (a * (g ⬝ᵥ u))
      change _ ≤ a ^ 2 * (g ⬝ᵥ u) ^ 2 + s ^ 2 * (normSq g / n)
      simpa only [mul_pow, radialRoot_sq] using h

/-- The radial dependence costs at most `5 s²/n` above and `7 s²/n` below. -/
theorem gaussian_smoothing_moment {n : ℕ} (hn : 1 ≤ n) {u : Fin n → ℝ}
    (hu : normSq u = 1) (a : ℝ) {s : ℝ} (hs : 0 < s) :
    let I := 2 * ∫ g : Fin n → ℝ, psiS (s * radialRoot g) (a * (g ⬝ᵥ u)) ^ 2
      ∂stdGauss (Fin n)
    let K := (a ^ 2 + s ^ 2) * kappa (a ^ 2 / (a ^ 2 + s ^ 2))
    K - 7 * s ^ 2 / n ≤ I ∧ I ≤ K + 5 * s ^ 2 / n := by
  let μ := stdGauss (Fin n)
  let f := fun g : Fin n → ℝ => psiS (s * radialRoot g) (a * (g ⬝ᵥ u)) ^ 2
  let f0 := fun g : Fin n → ℝ => psiS s (a * (g ⬝ᵥ u)) ^ 2
  let w := fun z : ℝ => s * smoothSlope (a * z) s
  let d := fun g : Fin n → ℝ => w (g ⬝ᵥ u) * (radialRoot g - 1)
  let r := fun g : Fin n → ℝ => s ^ 2 * (radialRoot g - 1) ^ 2
  have hwm : Measurable w := by
    unfold w smoothSlope
    apply Measurable.mul measurable_const
    exact ((measurable_const.mul (measurable_psiS.comp
      (measurable_const.prodMk (measurable_const.mul measurable_id)))).mul
      (BstLean.Part153.continuous_phiG.measurable.comp
        ((measurable_const.mul measurable_id).div_const _)))
  have hwb : ∀ z, 0 ≤ w z ∧ w z ≤ s ^ 2 := by
    intro z
    obtain ⟨h0, h1⟩ := smoothSlope_bounds (a * z) hs
    exact ⟨mul_nonneg hs.le h0, by dsimp [w]; nlinarith [mul_le_mul_of_nonneg_left h1 hs.le]⟩
  have hid : Integrable d μ := bounded_mul_integrable (radialRoot_sub_integrable n)
    (hwm.comp (by unfold dotProduct; fun_prop))
    (fun g => by rw [abs_of_nonneg (hwb _).1]; exact (hwb _).2)
  have hir : Integrable r μ := (radialRoot_error hn).1.const_mul _
  have hif : Integrable f μ := gaussian_smoothing_integrable u a s
  have hm0 : Measurable (fun z : ℝ => psiS s (a * z) ^ 2) := by
    exact (measurable_psiS.comp (measurable_const.prodMk
      (measurable_const.mul measurable_id))).pow_const 2
  have hif0 : Integrable f0 μ := by
    apply BstLean.Part150.gauss_lin_integrable u hm0
    simpa only [show (∑ j, u j ^ 2) = 1 from hu, sqrt_one, one_mul] using
      BstLean.Part153.integrable_psi_sq a s
  have hK : 2 * (∫ g, f0 g ∂μ) = (a ^ 2 + s ^ 2) * kappa (a ^ 2 / (a ^ 2 + s ^ 2)) := by
    dsimp [f0, μ]
    rw [BstLean.Part150.gauss_lin_integral u hm0]
    simp only [show (∑ j, u j ^ 2) = 1 from hu, sqrt_one, one_mul]
    exact BstLean.Part153.psi_sq_row a s
  have hpt : ∀ g, |f g - f0 g - d g| ≤ r g := by
    intro g
    have h := smooth_square_taylor (a * (g ⬝ᵥ u)) hs
      (mul_nonneg hs.le (sqrt_nonneg (normSq g / n)))
    convert h using 1
    · congr 1
      dsimp [f, f0, d, w, radialRoot]
      ring
    · dsimp [r, radialRoot]
      ring
  have hl : (∫ g, f0 g ∂μ) + (∫ g, d g ∂μ) - (∫ g, r g ∂μ) ≤ ∫ g, f g ∂μ := by
    rw [← integral_add hif0 hid, ← integral_sub (f := fun g => f0 g + d g) (g := r) (hif0.add hid) hir]
    exact integral_mono ((hif0.add hid).sub hir) hif fun g => by
      have := (abs_le.mp (hpt g)).1
      linarith
  have hh : (∫ g, f g ∂μ) ≤ (∫ g, f0 g ∂μ) + (∫ g, d g ∂μ) + (∫ g, r g ∂μ) := by
    rw [← integral_add hif0 hid, ← integral_add (f := fun g => f0 g + d g) (g := r) (hif0.add hid) hir]
    exact integral_mono hif ((hif0.add hid).add hir) fun g => by
      have := (abs_le.mp (hpt g)).2
      linarith
  have hr : (∫ g, r g ∂μ) ≤ s ^ 2 * (2 / n) := by
    dsimp [r]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (radialRoot_error hn).2 (sq_nonneg _)
  obtain ⟨hdl, hdu⟩ := weighted_root_bounds hn hu (sq_nonneg s) hwm hwb
  change -(3 * s ^ 2 / (2 * n)) ≤ ∫ g, d g ∂μ at hdl
  change (∫ g, d g ∂μ) ≤ s ^ 2 / (2 * n) at hdu
  change _ ≤ 2 * (∫ g, f g ∂μ) ∧ 2 * (∫ g, f g ∂μ) ≤ _
  have he1 : 3 * s ^ 2 / (2 * (n : ℝ)) = 3 / 2 * (s ^ 2 / n) := by ring
  have he2 : s ^ 2 / (2 * (n : ℝ)) = 1 / 2 * (s ^ 2 / n) := by ring
  have he3 : s ^ 2 * (2 / (n : ℝ)) = 2 * (s ^ 2 / n) := by ring
  rw [he1] at hdl
  rw [he2] at hdu
  rw [he3] at hr
  simp only [mul_div_assoc] at *
  constructor <;> linarith

end BstLean.Part211
