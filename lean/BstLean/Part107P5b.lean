import BstLean.Part107P5a

/-!
# Part 107 (P5), tools: facts about `rW`, `rPlus`, the constants, and the variance decomposition
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere)
open BstLean.Part105

lemma measurable_rW (d : ℕ) : Measurable (rW d) := by
  unfold rW
  exact (Finset.measurable_sum _ fun j _ => measurable_id.pow_const j).div_const _

lemma abs_rW_le (d : ℕ) {t : ℝ} (ht : |t| ≤ 1) : |rW d t| ≤ 1 := by
  unfold rW
  have hd : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  rw [abs_div, abs_of_pos hd, div_le_one hd]
  calc |∑ j ∈ Finset.range (d + 1), t ^ j| ≤ ∑ j ∈ Finset.range (d + 1), |t ^ j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (d + 1), (1 : ℝ) := Finset.sum_le_sum fun j _ => by
        rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) ht
    _ = (d : ℝ) + 1 := by simp

lemma rW_le_rPlus (dA : ℕ) {t : ℝ} (ht : |t| ≤ 1 / 10) : rW (2 * dA) t ≤ rPlus dA := by
  unfold rPlus rW
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun j _ => ?_) (by positivity)
  refine (le_abs_self _).trans ?_
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) ht j

lemma sum7_nonneg {t : ℝ} (ht : -1 ≤ t) : 0 ≤ ∑ j ∈ Finset.range 7, t ^ j := by
  have h : 0 ≤ (1 + t) * (1 + t ^ 2 + t ^ 4) + t ^ 6 :=
    add_nonneg (mul_nonneg (by linarith) (by positivity)) (by positivity)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  nlinarith [h]

lemma sum9_nonneg {t : ℝ} (ht : -1 ≤ t) : 0 ≤ ∑ j ∈ Finset.range 9, t ^ j := by
  have h : 0 ≤ (1 + t) * (1 + t ^ 2 + t ^ 4 + t ^ 6) + t ^ 8 :=
    add_nonneg (mul_nonneg (by linarith) (by positivity)) (by positivity)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  nlinarith [h]

lemma rW_nonneg {dA : ℕ} (hd : dA = 3 ∨ dA = 4) {t : ℝ} (ht : -1 ≤ t) : 0 ≤ rW (2 * dA) t := by
  unfold rW
  refine div_nonneg ?_ (by positivity)
  rcases hd with rfl | rfl
  · exact sum7_nonneg ht
  · exact sum9_nonneg ht

lemma rPlus3 : rPlus 3 = 1111111 / 7000000 := by
  norm_num [rPlus, rW, Finset.sum_range_succ]

lemma rPlus4 : rPlus 4 = 111111111 / 900000000 := by
  norm_num [rPlus, rW, Finset.sum_range_succ]

lemma rPlus_facts {dA : ℕ} (hd : dA = 3 ∨ dA = 4) :
    1 / (2 * (dA : ℝ) + 1) ≤ rPlus dA ∧ rPlus dA < 1 ∧ 0 ≤ rPlus dA := by
  rcases hd with rfl | rfl
  · rw [rPlus3]; norm_num
  · rw [rPlus4]; norm_num

lemma cKap_pos {dA : ℕ} (hd : dA = 3 ∨ dA = 4) : 0 < cKap dA := by
  rcases hd with rfl | rfl <;> norm_num [cKap]

lemma delN_nonneg (dA N : ℕ) : 0 ≤ delN dA N := by
  unfold delN Sof
  split_ifs <;> positivity

lemma Lsq_nonneg {dA : ℕ} (hd : dA = 3 ∨ dA = 4) {n : ℕ} (hn : 3 ≤ n) : 0 ≤ Lsq dA n := by
  obtain ⟨-, h1, h0⟩ := rPlus_facts hd
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  unfold Lsq
  refine div_nonneg (mul_nonneg (by positivity) (div_nonneg (by linarith) (by linarith))) ?_
  nlinarith

lemma continuous_kap' (dA : ℕ) : Continuous (kap' dA) := by
  unfold kap'
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_pow j)

lemma integral_affine {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : Integrable f μ) (a b : ℝ) :
    ∫ x, (a + b * f x) ∂μ = a + b * ∫ x, f x ∂μ := by
  rw [integral_add (integrable_const _) (hf.const_mul _), integral_const, integral_const_mul]
  simp

lemma var_decomp {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {X : α → ℝ} (hX : BM X) (c : ℝ) :
    ∫ x, (X x - c) ^ 2 ∂μ = ∫ x, (X x - ∫ y, X y ∂μ) ^ 2 ∂μ + (∫ y, X y ∂μ - c) ^ 2 := by
  obtain ⟨m, hm⟩ : ∃ m, m = ∫ y, X y ∂μ := ⟨_, rfl⟩
  rw [← hm]
  have hd : BM (fun x => X x - m) := hX.sub (BM.const m)
  have e : ∀ x, (X x - c) ^ 2 = (X x - m) ^ 2 + ((2 * (m - c)) * (X x - m) + (m - c) ^ 2) :=
    fun x => by ring
  simp_rw [e]
  have i2 : Integrable (fun x => (2 * (m - c)) * (X x - m) + (m - c) ^ 2) μ :=
    ((hd.integrable μ).const_mul _).add (integrable_const _)
  have h1 : ∫ x, ((X x - m) ^ 2 + ((2 * (m - c)) * (X x - m) + (m - c) ^ 2)) ∂μ =
      ∫ x, (X x - m) ^ 2 ∂μ + ∫ x, ((2 * (m - c)) * (X x - m) + (m - c) ^ 2) ∂μ :=
    integral_add (hd.sq.integrable μ) i2
  have h2 : ∫ x, ((2 * (m - c)) * (X x - m) + (m - c) ^ 2) ∂μ =
      (m - c) ^ 2 + (2 * (m - c)) * ∫ x, (X x - m) ∂μ := by
    rw [← integral_affine μ (hd.integrable μ)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have h3 : ∫ x, (X x - m) ∂μ = 0 := by
    rw [integral_sub (hX.integrable μ) (integrable_const _), integral_const, ← hm]
    simp
  rw [h1, h2, h3]
  ring

end BstLean.Part107
