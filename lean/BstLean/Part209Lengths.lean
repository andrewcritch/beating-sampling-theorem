import BstLean.Part200Lengths

/-! Sharp even moments of the first-layer length deviation. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part130 BstLean.Part152 BstLean.Part153 BstLean.Part200

/-- The two-sided Gaussian moment constant at order `2P`. -/
noncomputable def twoGaussConst (P : ℕ) : ℝ :=
  (2 * ((2 : ℝ) ^ P * (P.factorial : ℝ))) ^ (1 / (2 * (P : ℝ)))

lemma twoGaussConst_nonneg (P : ℕ) : 0 ≤ twoGaussConst P := by
  unfold twoGaussConst
  positivity

lemma twoGaussConst_eq (P : ℕ) :
    twoGaussConst P = (2 : ℝ) ^ (1 / (2 * (P : ℝ))) * gaussMomConst P := by
  unfold twoGaussConst gaussMomConst
  rw [Real.mul_rpow (by norm_num) (by positivity)]
  norm_cast

lemma twoGaussConst_pow {P : ℕ} (hP : 1 ≤ P) :
    twoGaussConst P ^ (2 * P) = 2 * ((2 : ℝ) ^ P * (P.factorial : ℝ)) := by
  unfold twoGaussConst
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  have he : 1 / (2 * (P : ℝ)) * ((2 * P : ℕ) : ℝ) = 1 := by
    have hp0 : (P : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [he, Real.rpow_one]

lemma abs_pow_split (z : ℝ) {k : ℕ} (hk : 0 < k) :
    |z| ^ k = max z 0 ^ k + max (-z) 0 ^ k := by
  rcases le_total 0 z with hz | hz
  · simp [abs_of_nonneg hz, max_eq_left hz, max_eq_right (neg_nonpos.mpr hz), hk.ne']
  · simp [abs_of_nonpos hz, max_eq_right hz, max_eq_left (neg_nonneg.mpr hz), hk.ne']

/-- Both one-sided concentration moments combine without a triangle-inequality factor. -/
theorem gaussMat_centered_abs_moment {m k P : ℕ} {g : Matrix (Fin m) (Fin k) ℝ → ℝ}
    {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ M M', |g M - g M'| ≤ L * sqrt (∑ i, ∑ j, (M i j - M' i j) ^ 2))
    {v : ℝ} (hv : 0 ≤ v) (hP : 1 ≤ P) :
    Integrable (fun M => |g M - ∫ M, g M ∂gaussMat m k v| ^ (2 * P)) (gaussMat m k v) ∧
    (∫ M, |g M - ∫ M, g M ∂gaussMat m k v| ^ (2 * P) ∂gaussMat m k v) ≤
      (sqrt v * L * twoGaussConst P) ^ (2 * P) := by
  obtain ⟨hip, hbp⟩ := gaussConc_mat_moment hL0 hL hv P
  have hLn : ∀ M M', |(-g M) - (-g M')| ≤
      L * sqrt (∑ i, ∑ j, (M i j - M' i j) ^ 2) := by
    intro M M'
    simpa only [neg_sub_neg, abs_sub_comm] using hL M M'
  obtain ⟨hin, hbn⟩ := gaussConc_mat_moment hL0 hLn hv P
  simp only [integral_neg, sub_neg_eq_add, neg_add_eq_sub] at hin hbn
  have he : ∀ M, |g M - ∫ M, g M ∂gaussMat m k v| ^ (2 * P) =
      max (g M - ∫ M, g M ∂gaussMat m k v) 0 ^ (2 * P) +
      max ((∫ M, g M ∂gaussMat m k v) - g M) 0 ^ (2 * P) := by
    intro M
    simpa only [neg_sub] using abs_pow_split (g M - ∫ M, g M ∂gaussMat m k v)
      (show 0 < 2 * P by omega)
  simp_rw [he]
  refine ⟨hip.add hin, ?_⟩
  rw [integral_add hip hin, mul_pow, twoGaussConst_pow hP]
  linarith

/-- The paper length allowance at even order `2P`. -/
noncomputable def lengthAlpha (n P : ℕ) : ℝ :=
  2 / (n : ℝ) ^ 2 + sqrt 2 / (n : ℝ) * twoGaussConst P

theorem layerLength_deviation_moment {n P : ℕ} (hn : 2 ≤ n) (hP : 1 ≤ P)
    {x : Fin n → ℝ} (hx : normSq x = 1) :
    Integrable (fun A => |layerLength A x - 1| ^ (2 * P)) (gaussMat (n ^ 2) n (2 / n)) ∧
    (∫ A, |layerLength A x - 1| ^ (2 * P) ∂gaussMat (n ^ 2) n (2 / n)) ≤
      lengthAlpha n P ^ (2 * P) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨_, hlo, hhi⟩ := layerLength_mean hn hx
  obtain ⟨hi, hb⟩ := gaussMat_centered_abs_moment
    (inv_nonneg.mpr (sqrt_nonneg (n : ℝ))) (layerLength_lip (by omega) hx)
    (by positivity : 0 ≤ 2 / (n : ℝ)) hP
  have he : sqrt (2 / (n : ℝ)) * (sqrt (n : ℝ))⁻¹ = sqrt 2 / (n : ℝ) := by
    rw [sqrt_div (by norm_num), div_eq_mul_inv, mul_assoc, ← _root_.mul_inv_rev,
      Real.mul_self_sqrt hn0.le]
    rfl
  rw [he] at hb
  apply moment_shift ((measurable_layerLength x).sub measurable_const).abs
    ((measurable_layerLength x).sub measurable_const).abs
    (fun _ => abs_nonneg _) (fun _ => abs_nonneg _) (by positivity) _ hP
    (mul_nonneg (by positivity) (twoGaussConst_nonneg P)) hi hb
  intro A
  change |layerLength A x - 1| ≤ 2 / (n : ℝ) ^ 2 +
    |layerLength A x - ∫ B, layerLength B x ∂gaussMat (n ^ 2) n (2 / n)|
  have h := abs_add_le
    (layerLength A x - ∫ B, layerLength B x ∂gaussMat (n ^ 2) n (2 / n))
    ((∫ B, layerLength B x ∂gaussMat (n ^ 2) n (2 / n)) - 1)
  rw [sub_add_sub_cancel, abs_of_nonpos (sub_nonpos.mpr hhi)] at h
  linarith

end BstLean.Part209
