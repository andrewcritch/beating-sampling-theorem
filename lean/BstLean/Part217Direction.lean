import BstLean.Part217Active
import BstLean.Part212Radius

/-! The exact radial coefficient applies after conditioning on gates and lengths. -/
namespace BstLean.Part217
open MeasureTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (radF53 unitF53)

theorem active_direction_moment {m d j : ℕ} (hm : 0 < m) (hd : 2 ≤ d) (hj : 1 ≤ j)
    (D : Fin m → Bool) {R c : Fin m → ℝ} (hR : ∀ i, 0 ≤ R i)
    (hoff : ∀ i, D i = false → c i = 0) {B : ℝ} (hB : squaredNorm c ≤ B) :
    ∫ G, radF53 (∑ i, (c i * R i) • unitF53 (G i)) ^ (2 * j)
      ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d)) ≤
        BstLean.Part212.exactRadius d j ^ (2 * j) *
          (activeMaximum hm D R ^ 2 * B) ^ j := by
  have h := BstLean.Part212.direction_sum_exact hd hm hj (fun i => c i * R i)
  have hr : radF53 (fun i => c i * R i) ^ (2 * j) ≤
      (activeMaximum hm D R ^ 2 * B) ^ j := by
    rw [pow_mul, BstLean.Part162.radF_sq]
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => sq_nonneg _)
      (active_coefficient_energy hm D hR hoff hB) j
  exact h.trans (mul_le_mul_of_nonneg_left hr
    (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _))

theorem active_direction_lintegral {m d j : ℕ} (hm : 0 < m) (hd : 2 ≤ d) (hj : 1 ≤ j)
    (D : Fin m → Bool) {R c : Fin m → ℝ} (hR : ∀ i, 0 ≤ R i)
    (hoff : ∀ i, D i = false → c i = 0) {B : ℝ} (hB : squaredNorm c ≤ B) :
    ∫⁻ G, ENNReal.ofReal (radF53 (∑ i, (c i * R i) • unitF53 (G i)) ^ (2 * j))
      ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d)) ≤
        ENNReal.ofReal (BstLean.Part212.exactRadius d j ^ (2 * j) *
          (activeMaximum hm D R ^ 2 * B) ^ j) := by
  have hmeas : Measurable (fun G : Fin m → Fin d → ℝ =>
      radF53 (∑ i, (c i * R i) • unitF53 (G i)) ^ (2 * j)) := by
    apply Measurable.pow_const
    apply BstLean.Part53.measurable_radF.comp
    apply Finset.measurable_sum
    intro i _
    exact (BstLean.Part53.measurable_unitF.comp
      (measurable_pi_apply (a := i))).const_smul (c i * R i)
  have hbound : ∀ G : Fin m → Fin d → ℝ,
      radF53 (∑ i, (c i * R i) • unitF53 (G i)) ^ (2 * j) ≤
        (∑ i, |c i * R i|) ^ (2 * j) := by
    intro G
    refine pow_le_pow_left₀ (sqrt_nonneg _)
      ((BstLean.Part162.radF_sum_le _ _).trans ?_) _
    exact Finset.sum_le_sum fun i _ => by
      have := BstLean.Part162.radF_unitF_le (G i)
      nlinarith [abs_nonneg (c i * R i)]
  have hi : Integrable (fun G : Fin m → Fin d → ℝ =>
      radF53 (∑ i, (c i * R i) • unitF53 (G i)) ^ (2 * j))
        (Measure.pi (fun _ : Fin m => stdGauss (Fin d))) := by
    refine (integrable_const ((∑ i, |c i * R i|) ^ (2 * j))).mono'
      hmeas.aestronglyMeasurable (ae_of_all _ fun G => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (pow_nonneg (BstLean.Part162.radF_nonneg _) _)]
    exact hbound G
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ fun G => pow_nonneg (sqrt_nonneg _) _)]
  exact ENNReal.ofReal_le_ofReal (active_direction_moment hm hd hj D hR hoff hB)

theorem active_mixed_direction_moment {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    {m d j : ℕ} (hm : 0 < m) (hd : 2 ≤ d) (hj : 1 ≤ j)
    (D : Ω → Fin m → Bool) (R c : Ω → Fin m → ℝ)
    (hR : ∀ ω i, 0 ≤ R ω i) (hoff : ∀ ω i, D ω i = false → c ω i = 0)
    {B M : ℝ} (hB0 : 0 ≤ B) (hB : ∀ ω, squaredNorm (c ω) ≤ B)
    (hM : (∫⁻ ω, ENNReal.ofReal (activeMaximum hm (D ω) (R ω) ^ (2 * j)) ∂mu) ≤
      ENNReal.ofReal M) :
    (∫⁻ ω, ∫⁻ G, ENNReal.ofReal
      (radF53 (∑ i, (c ω i * R ω i) • unitF53 (G i)) ^ (2 * j))
      ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d)) ∂mu) ≤
        ENNReal.ofReal (BstLean.Part212.exactRadius d j ^ (2 * j) * B ^ j * M) := by
  have hK0 : 0 ≤ BstLean.Part212.exactRadius d j ^ (2 * j) * B ^ j := by
    apply mul_nonneg
    · rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _
    · exact pow_nonneg hB0 _
  have hi : ∀ ω, (∫⁻ G, ENNReal.ofReal
      (radF53 (∑ i, (c ω i * R ω i) • unitF53 (G i)) ^ (2 * j))
      ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d))) ≤
        ENNReal.ofReal (BstLean.Part212.exactRadius d j ^ (2 * j) * B ^ j) *
          ENNReal.ofReal (activeMaximum hm (D ω) (R ω) ^ (2 * j)) := by
    intro ω
    have h := active_direction_lintegral hm hd hj (D ω) (hR ω) (hoff ω) (hB ω)
    refine h.trans_eq ?_
    rw [← ENNReal.ofReal_mul hK0]
    congr 1
    rw [mul_pow, ← pow_mul]
    ring
  refine (lintegral_mono hi).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul hK0]
  exact mul_le_mul' le_rfl hM

end BstLean.Part217
