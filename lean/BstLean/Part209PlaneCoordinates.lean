import BstLean.Part209Bernstein
import BstLean.Part209PlaneConstants
import BstLean.Part209MomentTools

/-! Two scalar coordinates give the fixed-pair plane moment. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part130 BstLean.Part152 BstLean.Part153
open BstLean.Part151 (mask mask_nonneg)

variable {n d P : ℕ}

noncomputable def coordinateError (n : ℕ) (a b u : Fin d → ℝ)
    (M : Matrix (Fin (n ^ 2)) (Fin d) ℝ) : ℝ :=
  (∑ j, gatedRow a b u (rowOf j M)) - ((n ^ 2 : ℕ) : ℝ) / 2 * dotp (kernelVector a b) u

lemma measurable_coordinateError (a b u : Fin d → ℝ) : Measurable (coordinateError n a b u) := by
  apply Measurable.sub_const
  exact Finset.measurable_sum _ fun j _ => (measurable_gatedRow a b u).comp (measurable_rowOf j)

lemma gatedRow_quadratic_le (a b u w : Fin d → ℝ) :
    |gatedRow a b u w| ≤ (dotp w u ^ 2 + dotp w b ^ 2) / 2 := by
  unfold gatedRow
  rw [abs_mul, abs_mul, abs_of_nonneg (mask_nonneg _)]
  have h := mul_le_mul
    (mul_le_mul_of_nonneg_right (BstLean.Part153.mask_le_one (dotp w a)) (abs_nonneg (dotp w u)))
    (abs_relu_le (dotp w b)) (abs_nonneg (relu (dotp w b)))
    (by positivity : 0 ≤ 1 * |dotp w u|)
  simp only [one_mul] at h
  nlinarith [sq_nonneg (|dotp w u| - |dotp w b|), sq_abs (dotp w u), sq_abs (dotp w b)]

theorem coordinateError_tail (hn : 1 ≤ n) (a : Fin d → ℝ) {b u : Fin d → ℝ}
    (hb : normSq b = 1) (hu : normSq u = 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    (gaussMat (n ^ 2) d 1).real {M | (2 * sqrt 2 * (n : ℝ)) * sqrt τ + 2 * τ <
      |coordinateError n a b u M|} ≤ 2 * exp (-τ) := by
  have hdom : ∀ w : Fin d → ℝ, |gatedRow a b u w| ≤
      1 * (((w ⬝ᵥ u) / sqrt 1) ^ 2 + ((w ⬝ᵥ b) / sqrt 1) ^ 2) / 2 := by
    intro w
    simpa only [sqrt_one, div_one, one_mul, dotp, dotProduct] using gatedRow_quadratic_le a b u w
  have h := BstLean.Part182.s2_dev (by norm_num : (0 : ℝ) < 1) (measurable_gatedRow a b u)
    hu hb (by norm_num : (0 : ℝ) < 1) hdom (by positivity : 0 < n ^ 2) hτ
  simp only [sqrt_one, one_smul, mul_one] at h
  rw [gatedRow_mean] at h
  have hs : sqrt (2 * ((n ^ 2 : ℕ) : ℝ) * τ) = sqrt 2 * (n : ℝ) * sqrt τ := by
    push_cast
    rw [sqrt_mul (by positivity), sqrt_mul (by norm_num), sqrt_sq (by positivity)]
  rw [hs] at h
  convert h using 2
  ext M
  simp only [Set.mem_setOf_eq]
  unfold coordinateError
  congr 2 <;> ring

lemma coordinateError_zero (a b : Fin d → ℝ) (M : Matrix (Fin (n ^ 2)) (Fin d) ℝ) :
    coordinateError n a b 0 M = 0 := by simp [coordinateError, gatedRow, dotp]

theorem coordinateError_moment (hn : 1 ≤ n) (hP : 1 ≤ P) (a : Fin d → ℝ)
    {b u : Fin d → ℝ} (hb : normSq b = 1) (hu : u = 0 ∨ normSq u = 1) :
    Integrable (fun M => |coordinateError n a b u M| ^ (2 * P)) (gaussMat (n ^ 2) d 1) ∧
    (∫ M, |coordinateError n a b u M| ^ (2 * P) ∂gaussMat (n ^ 2) d 1) ≤
      bernMoment (2 * sqrt 2 * (n : ℝ)) 2 2 P ^ (2 * P) := by
  rcases hu with rfl | hu
  · simp only [coordinateError_zero, abs_zero, zero_pow (by omega : 2 * P ≠ 0), integral_zero]
    exact ⟨integrable_const _, by unfold bernMoment; positivity⟩
  · exact bernstein_even_moment (measurable_coordinateError a b u).abs (fun _ => abs_nonneg _)
      (by positivity) (by norm_num) (by norm_num) (fun τ hτ => coordinateError_tail hn a hb hu hτ) hP

/-- The coordinate vectors need not be independent of one another. -/
theorem coordinatePlane_moment (hn : 1 ≤ n) (hP : 1 ≤ P) (a : Fin d → ℝ)
    {b u w : Fin d → ℝ} (hb : normSq b = 1)
    (hu : u = 0 ∨ normSq u = 1) (hw : w = 0 ∨ normSq w = 1) :
    Integrable (fun M => nrm (coordinateError n a b u M • u + coordinateError n a b w M • w) ^ (2 * P))
      (gaussMat (n ^ 2) d 1) ∧
    (∫ M, nrm (coordinateError n a b u M • u + coordinateError n a b w M • w) ^ (2 * P)
      ∂gaussMat (n ^ 2) d 1) ≤ pairPlane n P ^ (2 * P) := by
  obtain ⟨hiu, hbu⟩ := coordinateError_moment hn hP a hb hu
  obtain ⟨hiw, hbw⟩ := coordinateError_moment hn hP a hb hw
  have hC : 0 ≤ bernMoment (2 * sqrt 2 * (n : ℝ)) 2 2 P := by unfold bernMoment; positivity
  obtain ⟨hi, hm⟩ := moment_add (measurable_coordinateError a b u).abs
    (measurable_coordinateError a b w).abs (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)
    (by omega : 1 ≤ 2 * P) hC hC hiu hiw hbu hbw
  have huN : nrm u ≤ 1 := by
    rcases hu with rfl | hu
    · simp [nrm, normSq]
    · simp only [nrm, hu, sqrt_one, le_refl]
  have hwN : nrm w ≤ 1 := by
    rcases hw with rfl | hw
    · simp [nrm, normSq]
    · simp only [nrm, hw, sqrt_one, le_refl]
  have hdom : ∀ M : Matrix (Fin (n ^ 2)) (Fin d) ℝ,
      nrm (coordinateError n a b u M • u + coordinateError n a b w M • w) ^ (2 * P) ≤
        (|coordinateError n a b u M| + |coordinateError n a b w M|) ^ (2 * P) := by
    intro M
    apply pow_le_pow_left₀ (nrm_nonneg _)
    have h := nrm_add_le (coordinateError n a b u M • u) (coordinateError n a b w M • w)
    rw [nrm_smul, nrm_smul] at h
    have h₁ := mul_le_mul_of_nonneg_left huN (abs_nonneg (coordinateError n a b u M))
    have h₂ := mul_le_mul_of_nonneg_left hwN (abs_nonneg (coordinateError n a b w M))
    nlinarith
  have hmeas : Measurable (fun M : Matrix (Fin (n ^ 2)) (Fin d) ℝ =>
      nrm (coordinateError n a b u M • u + coordinateError n a b w M • w) ^ (2 * P)) :=
    (BstLean.Part130.measurable_normSq.comp (((measurable_coordinateError a b u).smul_const u).add
      ((measurable_coordinateError a b w).smul_const w))).sqrt.pow_const _
  have hI := hi.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun M => by
    rw [Real.norm_of_nonneg (pow_nonneg (nrm_nonneg _) _)]; exact hdom M)
  refine ⟨hI, ((integral_mono hI hi hdom).trans hm).trans ?_⟩
  apply pow_le_pow_left₀ (add_nonneg hC hC)
  simpa only [two_mul] using two_bernMoment_le_pairPlane hP n

end BstLean.Part209
