import BstLean.Part209Matrix
import BstLean.Part182SBlk2

/-! A centered gated quadratic row sum under the actual Gaussian matrix distribution. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part130 BstLean.Part152 BstLean.Part153
open BstLean.Part29 (stdGauss)
open BstLean.Part151 (mask measurable_mask mask_nonneg)

variable {d N : ℕ}

noncomputable def quadraticGate (a b u w : Fin d → ℝ) : ℝ :=
  mask (dotp w a) * mask (dotp w b) * dotp w u ^ 2

lemma measurable_quadraticGate (a b u : Fin d → ℝ) : Measurable (quadraticGate a b u) :=
  ((measurable_mask.comp (measurable_dot_left a)).mul
    (measurable_mask.comp (measurable_dot_left b))).mul ((measurable_dot_left u).pow_const 2)

lemma quadraticGate_nonneg (a b u w : Fin d → ℝ) : 0 ≤ quadraticGate a b u w :=
  mul_nonneg (mul_nonneg (mask_nonneg _) (mask_nonneg _)) (sq_nonneg _)

lemma quadraticGate_le (a b u w : Fin d → ℝ) : |quadraticGate a b u w| ≤ dotp w u ^ 2 := by
  rw [abs_of_nonneg (quadraticGate_nonneg a b u w)]
  have h := mul_le_mul (mask_le_one (dotp w a)) (mask_le_one (dotp w b))
    (mask_nonneg _) zero_le_one
  simpa [quadraticGate] using mul_le_mul_of_nonneg_right h (sq_nonneg (dotp w u))

/-- The two-sided Bernstein threshold is stronger than the paper threshold.
The two gates and the quadratic form use the same row. -/
theorem quadraticGate_tail (a b : Fin d → ℝ) {u : Fin d → ℝ} (hu : normSq u = 1)
    (hN : 0 < N) {τ : ℝ} (hτ : 0 ≤ τ) :
    (gaussMat N d 1).real {M | 2 * (sqrt (2 * (N : ℝ) * τ) + τ) <
      |(∑ j, quadraticGate a b u (rowOf j M)) -
        (N : ℝ) * ∫ w, quadraticGate a b u w ∂stdGauss (Fin d)|} ≤ 2 * exp (-τ) := by
  have hdom : ∀ w : Fin d → ℝ, |quadraticGate a b u w| ≤
      1 * (((w ⬝ᵥ u) / sqrt 1) ^ 2 + ((w ⬝ᵥ u) / sqrt 1) ^ 2) / 2 := by
    intro w
    have h := quadraticGate_le a b u w
    change |quadraticGate a b u w| ≤
      1 * ((dotp w u / sqrt 1) ^ 2 + (dotp w u / sqrt 1) ^ 2) / 2
    simpa only [sqrt_one, div_one, one_mul, add_self_div_two] using h
  have h := BstLean.Part182.s2_dev (by norm_num : (0 : ℝ) < 1)
    (measurable_quadraticGate a b u) hu hu (by norm_num : (0 : ℝ) < 1) hdom hN hτ
  simpa only [sqrt_one, one_smul, mul_one] using h

/-- In particular, the scalar quadratic row sum has the displayed paper threshold. -/
theorem quadraticGate_paper_tail (a b : Fin d → ℝ) {u : Fin d → ℝ} (hu : normSq u = 1)
    (hN : 0 < N) {τ : ℝ} (hτ : 0 ≤ τ) :
    (gaussMat N d 1).real {M | sqrt (32 * (N : ℝ) * τ) + 4 * τ <
      |(∑ j, quadraticGate a b u (rowOf j M)) -
        (N : ℝ) * ∫ w, quadraticGate a b u w ∂stdGauss (Fin d)|} ≤ 2 * exp (-τ) := by
  apply le_trans (measureReal_mono (fun M hM => ?_)) (quadraticGate_tail a b hu hN hτ)
  change sqrt (32 * (N : ℝ) * τ) + 4 * τ < _ at hM
  change 2 * (sqrt (2 * (N : ℝ) * τ) + τ) < _
  have he : sqrt (32 * (N : ℝ) * τ) = 4 * sqrt (2 * (N : ℝ) * τ) := by
    rw [show 32 * (N : ℝ) * τ = 16 * (2 * (N : ℝ) * τ) by ring,
      sqrt_mul (by norm_num)]
    norm_num
  rw [he] at hM
  linarith [sqrt_nonneg (2 * (N : ℝ) * τ)]

end BstLean.Part209
