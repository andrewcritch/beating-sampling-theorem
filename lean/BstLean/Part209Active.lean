import BstLean.Part209GaussianTail
import BstLean.Part209Lengths
import BstLean.Part153Bin
import BstLean.Part153PPs

/-! The positive active-count deviation and its square-root moment. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part152 BstLean.Part153
open BstLean.Part29 (stdGauss)
open BstLean.Part151 (mask mask_nonneg)

noncomputable def activeB (n P : ℕ) : ℝ := (n : ℝ) / 2 * twoGaussConst P

lemma activeB_nonneg (n P : ℕ) : 0 ≤ activeB n P :=
  mul_nonneg (by positivity) (twoGaussConst_nonneg P)

lemma twoGaussConst_sqrt_formula {P : ℕ} (hP : 1 ≤ P) :
    twoGaussConst P = sqrt 2 * (2 * (P.factorial : ℝ)) ^ (1 / (2 * (P : ℝ))) := by
  apply (pow_left_inj₀ (twoGaussConst_nonneg P) (by positivity) (show 2 * P ≠ 0 by omega)).mp
  rw [twoGaussConst_pow hP, mul_pow, pow_mul (sqrt 2) 2 P,
    sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), even_root_pow hP (by positivity)]
  ring

lemma activeB_paper {P : ℕ} (hP : 1 ≤ P) (n : ℕ) :
    activeB n P = (n : ℝ) / sqrt 2 * (2 * (P.factorial : ℝ)) ^ (1 / (2 * (P : ℝ))) := by
  unfold activeB
  rw [twoGaussConst_sqrt_formula hP, ← mul_assoc]
  congr 1
  have hs := sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsp : sqrt (2 : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith

theorem active_count_deviation_moment {n P : ℕ} (hn : 1 ≤ n) (hP : 1 ≤ P) :
    Integrable (fun g : Fin (n ^ 2) → ℝ => max ((∑ i, mask (g i)) - (n : ℝ) ^ 2 / 2) 0 ^ (2 * P))
      (stdGauss (Fin (n ^ 2))) ∧
    (∫ g : Fin (n ^ 2) → ℝ, max ((∑ i, mask (g i)) - (n : ℝ) ^ 2 / 2) 0 ^ (2 * P)
      ∂stdGauss (Fin (n ^ 2))) ≤ activeB n P ^ (2 * P) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : Measurable (fun g : Fin (n ^ 2) → ℝ => ∑ i, mask (g i)) := measurable_cnt _
  have ht : ∀ t : ℝ, 0 < t → (stdGauss (Fin (n ^ 2))).real
      {g | t < max ((∑ i, mask (g i)) - (n : ℝ) ^ 2 / 2) 0} ≤
        2 * exp (-t ^ 2 / (2 * ((n : ℝ) / 2) ^ 2)) := by
    intro t ht
    have h := cnt_tail (m := n ^ 2) (show 0 ≤ t / (n : ℝ) ^ 2 by positivity)
    have he : (1 / 2 + t / (n : ℝ) ^ 2) * ((n ^ 2 : ℕ) : ℝ) = (n : ℝ) ^ 2 / 2 + t := by
      push_cast
      field_simp
      <;> ring
    have hex : -2 * (t / (n : ℝ) ^ 2) ^ 2 * ((n ^ 2 : ℕ) : ℝ) =
        -t ^ 2 / (2 * ((n : ℝ) / 2) ^ 2) := by
      push_cast
      field_simp
      <;> ring
    rw [he, hex] at h
    have hsub := measureReal_mono (μ := stdGauss (Fin (n ^ 2))) (fun g hg => by
      change t < max ((∑ i, mask (g i)) - (n : ℝ) ^ 2 / 2) 0 at hg
      change (n : ℝ) ^ 2 / 2 + t < ∑ i, mask (g i)
      rcases lt_max_iff.mp hg with hg | hg <;> linarith)
    exact (hsub.trans h).trans (by linarith [exp_pos (-t ^ 2 / (2 * ((n : ℝ) / 2) ^ 2))])
  obtain ⟨hi, hb⟩ := gaussian_tail_even_moment
    ((hm.sub_const _).max measurable_const) (fun _ => le_max_right _ _)
    (show 0 < (n : ℝ) / 2 by positivity) (by norm_num : (0 : ℝ) ≤ 2) ht hP
  refine ⟨hi, hb.trans_eq ?_⟩
  rw [activeB, mul_pow, twoGaussConst_pow hP]
  ring

theorem active_count_moment {n P : ℕ} (hn : 1 ≤ n) (hP : 1 ≤ P) :
    Integrable (fun g : Fin (n ^ 2) → ℝ => (∑ i, mask (g i)) ^ (2 * P)) (stdGauss (Fin (n ^ 2))) ∧
    (∫ g : Fin (n ^ 2) → ℝ, (∑ i, mask (g i)) ^ (2 * P) ∂stdGauss (Fin (n ^ 2))) ≤
      ((n : ℝ) ^ 2 / 2 + activeB n P) ^ (2 * P) := by
  obtain ⟨hi, hb⟩ := active_count_deviation_moment hn hP
  exact moment_shift (measurable_cnt _) (((measurable_cnt _).sub_const _).max measurable_const)
    (fun g => Finset.sum_nonneg fun i _ => mask_nonneg _) (fun _ => le_max_right _ _)
    (by positivity) (fun g => by have := le_max_left ((∑ i, mask (g i)) - (n : ℝ) ^ 2 / 2) 0; linarith)
    hP (activeB_nonneg n P) hi hb

/-- The square-root count plus a constant has the allowance used by the tangent operator. -/
theorem active_sqrt_shift_moment {n P : ℕ} (hn : 1 ≤ n) (hP : 1 ≤ P) {c : ℝ} (hc : 0 ≤ c) :
    Integrable (fun g : Fin (n ^ 2) → ℝ => (sqrt (∑ i, mask (g i)) + c) ^ (4 * P))
      (stdGauss (Fin (n ^ 2))) ∧
    (∫ g : Fin (n ^ 2) → ℝ, (sqrt (∑ i, mask (g i)) + c) ^ (4 * P) ∂stdGauss (Fin (n ^ 2))) ≤
      (sqrt ((n : ℝ) ^ 2 / 2 + activeB n P) + c) ^ (4 * P) := by
  obtain ⟨hi, hb⟩ := active_count_moment hn hP
  have he : ∀ z : ℝ, 0 ≤ z → sqrt z ^ (4 * P) = z ^ (2 * P) := by
    intro z hz
    rw [show 4 * P = 2 * (2 * P) by omega, pow_mul, sq_sqrt hz]
  have hiY : Integrable (fun g : Fin (n ^ 2) → ℝ => sqrt (∑ i, mask (g i)) ^ (2 * (2 * P)))
      (stdGauss (Fin (n ^ 2))) := by
    simpa only [show 2 * (2 * P) = 4 * P by omega,
      he _ (Finset.sum_nonneg fun i _ => mask_nonneg _)] using hi
  have hbY : (∫ g : Fin (n ^ 2) → ℝ, sqrt (∑ i, mask (g i)) ^ (2 * (2 * P))
      ∂stdGauss (Fin (n ^ 2))) ≤ sqrt ((n : ℝ) ^ 2 / 2 + activeB n P) ^ (2 * (2 * P)) := by
    rw [show 2 * (2 * P) = 4 * P by omega,
      he ((n : ℝ) ^ 2 / 2 + activeB n P) (add_nonneg (by positivity) (activeB_nonneg n P))]
    simpa only [he _ (Finset.sum_nonneg fun i _ => mask_nonneg _)] using hb
  have h := moment_shift ((measurable_cnt _).sqrt.add_const c) (measurable_cnt _).sqrt
    (fun _ => add_nonneg (sqrt_nonneg _) hc) (fun _ => sqrt_nonneg _) hc
    (fun _ => le_of_eq (add_comm _ _)) (by omega : 1 ≤ 2 * P) (sqrt_nonneg _) hiY hbY
  simpa only [show 2 * (2 * P) = 4 * P by omega, add_comm c] using h

end BstLean.Part209
