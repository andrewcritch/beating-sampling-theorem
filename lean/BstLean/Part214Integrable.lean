import BstLean.Part214Diagonal

/-! All actual row-discrepancy sixth moments are integrable. -/
namespace BstLean.Part214
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part137 BstLean.Part205
open BstLean.Part105

lemma smoothing_square_bound (x s : ℝ) : psiS s x ^ 2 ≤ x ^ 2 + s ^ 2 := by
  have i1 : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := by
    simpa only [pow_one] using integrable_pow_gauss 1
  have i2 := integrable_pow_gauss 2
  have ie : Integrable (fun z : ℝ => (x + s * z) ^ 2) (gaussianReal 0 1) := by
    have he : (fun z : ℝ => (x + s * z) ^ 2) = fun z => x ^ 2 + (2 * x * s) * z + s ^ 2 * z ^ 2 := by
      funext z; ring
    rw [he]
    exact ((integrable_const _).add (i1.const_mul _)).add (i2.const_mul _)
  calc
    _ ≤ ∫ z, relu (x + s * z) ^ 2 ∂gaussianReal 0 1 := psiS_sq_le _ _
    _ ≤ ∫ z, (x + s * z) ^ 2 ∂gaussianReal 0 1 :=
      integral_mono (integrable_relu_shift_sq _ _) ie (fun z => relu_sq_le _)
    _ = _ := by
      have he : (fun z : ℝ => (x + s * z) ^ 2) = fun z => x ^ 2 + (2 * x * s) * z + s ^ 2 * z ^ 2 := by
        funext z; ring
      have ia : Integrable (fun z : ℝ => x ^ 2 + (2 * x * s) * z) (gaussianReal 0 1) :=
        (integrable_const (x ^ 2)).add (i1.const_mul (2 * x * s))
      rw [he, integral_add ia (i2.const_mul (s ^ 2)),
        integral_add (integrable_const (x ^ 2)) (i1.const_mul (2 * x * s)),
        integral_const_mul, integral_const_mul,
        integral_id_gaussianReal, gaussMom_eq]
      norm_num [gaussMom, Nat.doubleFactorial]

theorem rowDiscrepancy_six_integrable {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m)
    (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    Integrable (fun ξ => rowDiscrepancy M₁ ξ ^ 6) (stdGauss (Fin m)) := by
  have := uniformSphere_isProbability N hN
  let g : (Fin N → ℝ) → Fin m → ℝ := fun u => reluV (M₁.mulVec u)
  let Q := firstQ M₁
  let h := h1bar M₁
  let s := worldSigma M₁
  let A := 2 * (Q + normSq h)
  let B := 2 * s ^ 2
  have hQ : 0 ≤ Q := integral_nonneg fun _ => normSq_nonneg _
  have hA : 0 ≤ A := mul_nonneg (by norm_num) (add_nonneg hQ (normSq_nonneg h))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have iQ := sphere_cont_integrable hN (continuous_normSq.comp (continuous_h1_u M₁))
  have hm2 : ∀ ξ, rowMean g ξ ^ 2 ≤ normSq ξ * Q := by
    intro ξ
    have ir : Integrable (fun u => rowInput g ξ u ^ 2) (uniformSphere N) := sphere_cont_integrable hN
      (((rowInput_continuous g (continuous_h1_u M₁)).comp
        (continuous_const.prodMk continuous_id)).pow 2)
    refine (sq_integral_le ir).trans ?_
    change (∫ u, rowInput g ξ u ^ 2 ∂uniformSphere N) ≤
      normSq ξ * ∫ u, normSq (g u) ∂uniformSphere N
    rw [← integral_const_mul]
    exact integral_mono ir (iQ.const_mul _) fun u =>
      (relu_sq_le _).trans (by simpa [dotp] using dotL_sq_le ξ (g u))
  have hs2 : ∀ ξ, rowSmooth h s ξ ^ 2 ≤ normSq ξ * normSq h + s ^ 2 := by
    intro ξ
    exact (smoothing_square_bound (dotp ξ h) s).trans
      (add_le_add (by simpa [dotp] using dotL_sq_le ξ h) (le_refl (s ^ 2)))
  have hb : ∀ ξ, rowDiscrepancy M₁ ξ ^ 2 ≤ A * normSq ξ + B := by
    intro ξ
    change (rowMean g ξ - rowSmooth h s ξ) ^ 2 ≤ _
    dsimp [A, B]
    nlinarith [hm2 ξ, hs2 ξ, sq_nonneg (rowMean g ξ + rowSmooth h s ξ)]
  have ip : Integrable (fun ξ : Fin m → ℝ => (A * normSq ξ + B) ^ 3) (stdGauss (Fin m)) := by
    have he : (fun ξ : Fin m → ℝ => (A * normSq ξ + B) ^ 3) = fun ξ =>
        A ^ 3 * normSq ξ ^ 3 + (3 * A ^ 2 * B) * normSq ξ ^ 2 +
          (3 * A * B ^ 2) * normSq ξ + B ^ 3 := by funext ξ; ring
    rw [he]
    exact (((gaussian_normSq_pow_integrable hm 3).const_mul _).add
      ((gaussian_normSq_pow_integrable hm 2).const_mul _)).add
      ((BstLean.Part137.gauss_normSq m).1.const_mul _) |>.add (integrable_const _)
  refine Integrable.mono' ip
    ((measurable_rowDiscrepancy M₁).pow_const 6).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg (rowDiscrepancy M₁ ξ)) (hb ξ) 3

end BstLean.Part214
#print axioms BstLean.Part214.rowDiscrepancy_six_integrable
