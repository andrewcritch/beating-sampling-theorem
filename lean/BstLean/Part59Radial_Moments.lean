import BstLean.Part59Defs
import BstLean.Part53T2_Radial
import BstLean.Part48Hyper

/-! # Part 59: dimension-free bounds for radial displacement moments -/

namespace BstLean.Part59

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD DD)
open BstLean.Part53 (sg)
open BstLean.Part53.T2Aux

private lemma doubling_moment59x (h j : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ι : Type) [Fintype ι] (P : MvPolynomial ι ℝ),
      P.totalDegree ≤ h → (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι) ≤ B →
      (∫ z, (MvPolynomial.eval z P) ^ (2 ^ (j + 1)) ∂stdGauss ι) ≤ C := by
  induction j with
  | zero => exact ⟨B, hB, fun _ _ _ _ hb => by simpa using hb⟩
  | succ j ih =>
    obtain ⟨C, hC, hb⟩ := ih
    obtain ⟨K, hK, hfour⟩ := BstLean.Part48.fourth_moment (2 ^ j * h)
    refine ⟨K * C ^ 2, by positivity, fun ι _ P hP hPb => ?_⟩
    have hd : (P ^ (2 ^ j)).totalDegree ≤ 2 ^ j * h :=
      (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hP)
    have hf := hfour ι (P ^ (2 ^ j)) hd
    have hi := hb ι P hP hPb
    have hnn : 0 ≤ ∫ z, (MvPolynomial.eval z P) ^ (2 ^ (j + 1)) ∂stdGauss ι := by
      apply integral_nonneg
      intro z
      change 0 ≤ (MvPolynomial.eval z P) ^ (2 ^ (j + 1))
      rw [pow_succ, pow_mul]
      exact sq_nonneg _
    have he2 : 2 ^ j * 2 = 2 ^ (j + 1) := by simp [pow_succ]
    have he4 : 2 ^ j * 4 = 2 ^ (j + 1 + 1) := by simp [pow_succ]; omega
    simp only [map_pow, ← pow_mul, he2, he4] at hf
    exact hf.trans (mul_le_mul_of_nonneg_left (by nlinarith :
      (∫ z, (MvPolynomial.eval z P) ^ (2 ^ (j + 1)) ∂stdGauss ι) ^ 2 ≤ C ^ 2) hK.le)

private lemma even_power_le59x (x : ℝ) (r j : ℕ) (hr : 2 * r ≤ 2 ^ (j + 1)) :
    x ^ (2 * r) ≤ 1 + x ^ (2 ^ (j + 1)) := by
  have he : x ^ (2 ^ (j + 1)) = |x| ^ (2 ^ (j + 1)) := by
    rw [pow_succ, mul_comm, pow_mul, pow_mul, sq_abs]
  have her : x ^ (2 * r) = |x| ^ (2 * r) := by
    rw [pow_mul, pow_mul, sq_abs]
  rw [her, he]
  by_cases hx : |x| ≤ 1
  · have hl : |x| ^ (2 * r) ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
    exact hl.trans (le_add_of_nonneg_right (pow_nonneg (abs_nonneg _) _))
  · exact (pow_le_pow_right₀ (le_of_not_ge hx) hr).trans
      (le_add_of_nonneg_left (by norm_num))

/-- Every fixed even moment of a bounded-degree Gaussian polynomial with bounded second moment
has a bound independent of the number of variables. -/
lemma polynomial_even_moment_bound59x (h r : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ι : Type) [Fintype ι] (P : MvPolynomial ι ℝ),
      P.totalDegree ≤ h → (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι) ≤ B →
      (∫ z, (MvPolynomial.eval z P) ^ (2 * r) ∂stdGauss ι) ≤ C := by
  obtain ⟨C, hC, hb⟩ := doubling_moment59x h (2 * r) B hB
  refine ⟨1 + C, by positivity, fun ι _ P hP hPb => ?_⟩
  have hi (a : ℕ) : Integrable (fun z => (MvPolynomial.eval z P) ^ a) (stdGauss ι) := by
    simpa only [map_pow] using BstLean.Part48.gauss_poly_integrable (P ^ a)
  have he : 2 * r ≤ 2 ^ (2 * r + 1) := by
    exact (Nat.le_succ _).trans (Nat.lt_two_pow_self).le
  calc
    _ ≤ ∫ z, (1 : ℝ) + (MvPolynomial.eval z P) ^ (2 ^ (2 * r + 1)) ∂stdGauss ι :=
      integral_mono (hi _) ((integrable_const 1).add (hi _))
        (fun z => even_power_le59x _ _ _ he)
    _ = 1 + ∫ z, (MvPolynomial.eval z P) ^ (2 ^ (2 * r + 1)) ∂stdGauss ι := by
      rw [integral_add (integrable_const 1) (hi _)]; simp
    _ ≤ 1 + C := add_le_add_right (hb ι P hP hPb) _

private lemma radial_degree59x (n d : ℕ) :
    (radialPoly n d (sg n d)).totalDegree ≤ 2 := by
  classical
  unfold radialPoly
  apply MvPolynomial.totalDegree_finsetSum_le
  intro a _
  apply (MvPolynomial.totalDegree_pow _ _).trans
  have hm := MvPolynomial.totalDegree_mul (MvPolynomial.C (sg n d)) (MvPolynomial.X a)
  simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add] at hm
  omega

/-- The centered squared radius has the high-moment decay needed by the binomial expansion. -/
lemma radial_centered_even_moment59x (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n d : ℕ, 1 ≤ n →
      Integrable (fun Z => (radialScale n d Z ^ 2 - 1) ^ (2 * r))
        (stdGauss (CoefIdxD n d)) ∧
      (∫ Z, (radialScale n d Z ^ 2 - 1) ^ (2 * r) ∂stdGauss (CoefIdxD n d)) ≤
        C / DD n d ^ r := by
  obtain ⟨B, hB, hb⟩ := radial_power_variance_bound 1
  obtain ⟨C, hC, hc⟩ := polynomial_even_moment_bound59x 2 r B hB
  refine ⟨C, hC, fun n d hn => ?_⟩
  let Q := radialPoly n d (sg n d) - 1
  let P := MvPolynomial.C (Real.sqrt (DD n d)) * Q
  have hD := BstLean.Part36.DD_pos (d := d) hn
  have hQ : Q.totalDegree ≤ 2 :=
    (MvPolynomial.totalDegree_sub_C_le _ 1).trans (radial_degree59x n d)
  have hP : P.totalDegree ≤ 2 := by
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa [P] using hQ)
  have hi (a : ℕ) : Integrable (fun Z => (MvPolynomial.eval Z Q) ^ a)
      (stdGauss (CoefIdxD n d)) := by
    simpa only [map_pow] using BstLean.Part48.gauss_poly_integrable (Q ^ a)
  have hnorm : (∫ Z, (MvPolynomial.eval Z P) ^ 2 ∂stdGauss (CoefIdxD n d)) ≤ B := by
    simp only [P, map_mul, MvPolynomial.eval_C, mul_pow]
    rw [integral_const_mul, Real.sq_sqrt hD.le]
    have ht := hb n d hn
    have ht' := (le_div_iff₀ hD).mp ht
    simpa [Q, mul_comm] using ht'
  have hbound := hc (CoefIdxD n d) P hP hnorm
  simp only [P, map_mul, MvPolynomial.eval_C, mul_pow] at hbound
  rw [integral_const_mul, pow_mul, Real.sq_sqrt hD.le] at hbound
  have he (Z : CoefIdxD n d → ℝ) :
      radialScale n d Z ^ 2 - 1 = MvPolynomial.eval Z Q := by
    simp [Q, radialScale_sq n d hn]
  simp_rw [he]
  exact ⟨hi _, (le_div_iff₀ (pow_pos hD r)).mpr (by simpa [mul_comm] using hbound)⟩

/-- The normalized radius has even moments of its displacement of order `DD⁻ʳ`. -/
lemma radial_displacement_even_moment59x (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n d : ℕ, 1 ≤ n →
      Integrable (fun Z => (lam59 n d Z - 1) ^ (2 * r))
        (stdGauss (CoefIdxD n d)) ∧
      (∫ Z, (lam59 n d Z - 1) ^ (2 * r) ∂stdGauss (CoefIdxD n d)) ≤
        C / DD n d ^ r := by
  obtain ⟨C, hC, hb⟩ := radial_centered_even_moment59x r
  refine ⟨C, hC, fun n d hn => ?_⟩
  obtain ⟨hi, hbound⟩ := hb n d hn
  have hdom (Z : CoefIdxD n d → ℝ) :
      (lam59 n d Z - 1) ^ (2 * r) ≤ (radialScale n d Z ^ 2 - 1) ^ (2 * r) := by
    have hl : 0 ≤ lam59 n d Z := radialScale_nonneg n d Z
    have hs : (lam59 n d Z - 1) ^ 2 ≤ (lam59 n d Z ^ 2 - 1) ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg (lam59 n d Z - 1))
        (add_nonneg (sq_nonneg (lam59 n d Z)) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hl))]
    change (lam59 n d Z - 1) ^ (2 * r) ≤ (lam59 n d Z ^ 2 - 1) ^ (2 * r)
    simpa only [pow_mul] using pow_le_pow_left₀ (sq_nonneg _) hs r
  have hc : Continuous (fun Z : CoefIdxD n d → ℝ => (lam59 n d Z - 1) ^ (2 * r)) :=
    ((radialScale_continuous n d).sub continuous_const).pow _
  have hir : Integrable (fun Z => (lam59 n d Z - 1) ^ (2 * r))
      (stdGauss (CoefIdxD n d)) := by
    apply hi.mono' hc.aestronglyMeasurable
    filter_upwards [] with Z
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hdom Z
    · rw [pow_mul]; positivity
  exact ⟨hir, (integral_mono hir hi hdom).trans hbound⟩

end BstLean.Part59
