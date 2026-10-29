import BstLean.Part209Overlap
import BstLean.Part209Tail

/-! The paper overlap allowance at every positive even order. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part130 BstLean.Part152 BstLean.Part153

variable {n P : ℕ}

lemma measurable_firstOverlap (x x' : Fin n → ℝ) : Measurable (firstOverlap x x') := by
  unfold firstOverlap dotp reluV relu
  fun_prop

theorem firstOverlap_tail (hn : 1 ≤ n) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    (gaussMat (n ^ 2) n (2 / n)).real {A |
      (4 * sqrt 2 / (n : ℝ)) * sqrt τ + (4 / (n : ℝ) ^ 2) * τ <
        |firstOverlap x x' A - kappa (dotp x x')|} ≤ 2 * exp (-τ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := relu_overlap_tail (m := n ^ 2) (by positivity : 0 < 2 / (n : ℝ))
    hx hx' (by positivity) hτ
  apply le_trans (measureReal_mono (fun A hA => ?_)) h
  change (4 * sqrt 2 / (n : ℝ)) * sqrt τ + (4 / (n : ℝ) ^ 2) * τ <
    |firstOverlap x x' A - kappa (dotp x x')| at hA
  have he : dotp (reluV (A *ᵥ x)) (reluV (A *ᵥ x')) -
      ((n ^ 2 : ℕ) : ℝ) * (2 / (n : ℝ)) / 2 * kappa (dotp x x') =
        (n : ℝ) * (firstOverlap x x' A - kappa (dotp x x')) := by
    unfold firstOverlap
    push_cast
    field_simp
    <;> ring
  change 2 * (2 / (n : ℝ)) * (sqrt (2 * ((n ^ 2 : ℕ) : ℝ) * τ) + τ) < _
  rw [he, abs_mul, abs_of_pos hn0]
  have hs : sqrt (2 * ((n ^ 2 : ℕ) : ℝ) * τ) = sqrt 2 * (n : ℝ) * sqrt τ := by
    push_cast
    rw [sqrt_mul (by positivity), sqrt_mul (by norm_num), sqrt_sq hn0.le]
  rw [hs]
  have hh := mul_lt_mul_of_pos_left hA hn0
  convert hh using 1 <;> field_simp <;> ring

noncomputable def overlapC (n P : ℕ) : ℝ :=
  2 / (n : ℝ) ^ 2 *
    (sqrt 32 * (n : ℝ) * (2 * (P.factorial : ℝ)) ^ (1 / (2 * (P : ℝ))) +
      4 * (2 * ((2 * P).factorial : ℝ)) ^ (1 / (2 * (P : ℝ))))

lemma overlapC_eq (n P : ℕ) :
    overlapC n P = bernMoment (4 * sqrt 2 / (n : ℝ)) (4 / (n : ℝ) ^ 2) 2 P := by
  have hs : sqrt (32 : ℝ) = 4 * sqrt 2 := by
    rw [show (32 : ℝ) = 16 * 2 by norm_num, sqrt_mul (by norm_num)]
    norm_num
  unfold overlapC bernMoment
  rw [hs]
  by_cases hn : (n : ℝ) = 0
  · simp [hn]
  · field_simp
    <;> ring

/-- The overlap bound has exactly the paper constant `C_(2P)`, with shared first-layer weights. -/
theorem firstOverlap_deviation_moment (hn : 1 ≤ n) (hP : 1 ≤ P)
    {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1) :
    Integrable (fun A => |firstOverlap x x' A - kappa (dotp x x')| ^ (2 * P))
      (gaussMat (n ^ 2) n (2 / n)) ∧
    (∫ A, |firstOverlap x x' A - kappa (dotp x x')| ^ (2 * P)
      ∂gaussMat (n ^ 2) n (2 / n)) ≤ overlapC n P ^ (2 * P) := by
  rw [overlapC_eq]
  exact bernstein_even_moment ((measurable_firstOverlap x x').sub measurable_const).abs
    (fun _ => abs_nonneg _) (by positivity) (by positivity) (by norm_num)
    (fun τ hτ => firstOverlap_tail hn hx hx' hτ) hP

end BstLean.Part209
