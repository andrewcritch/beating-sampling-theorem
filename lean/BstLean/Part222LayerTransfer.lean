import BstLean.Part222LayerNorm

/-! The normalized layer radius transfers to each actual Gaussian matrix. -/
namespace BstLean.Part222
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153

noncomputable def layerScale {k : ℕ} (m : ℕ) (v : ℝ) (y : Fin k → ℝ) : ℝ :=
  √((m : ℝ)/2) * √v * nrm y

lemma layerScale_nonneg {k : ℕ} (m : ℕ) (v : ℝ) (y : Fin k → ℝ) :
    0 ≤ layerScale m v y := by
  unfold layerScale
  exact mul_nonneg (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) (nrm_nonneg _)

lemma layerScale_root {m k : ℕ} (hm : 1 ≤ m) (v : ℝ) (y : Fin k → ℝ)
    (x : Fin m → ℝ) :
    nrm (reluV ((√v * √(normSq y)) • x)) = layerScale m v y * layerRoot m x := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have he : √((m : ℝ)/2) * √(2/(m : ℝ)) = 1 := by
    rw [← sqrt_mul (by positivity : 0 ≤ (m : ℝ)/2)]
    have h : (m : ℝ)/2 * (2/(m : ℝ)) = 1 := by field_simp
    rw [h, sqrt_one]
  rw [reluV_smul_of_nonneg (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)),
    nrm_smul, abs_of_nonneg (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))]
  unfold layerScale layerRoot nrm
  have h := congrArg (fun r => r * √v * √(normSq y) * √(normSq (reluV x))) he
  nlinarith only [h]

theorem layer_deviation_moment {m k : ℕ} (hm : 1 ≤ m) (v : ℝ) (y : Fin k → ℝ) :
    Integrable (fun A : Matrix (Fin m) (Fin k) ℝ =>
      |nrm (reluV (A *ᵥ y))-layerScale m v y|^32) (gaussMat m k v) ∧
    (∫ A, |nrm (reluV (A *ᵥ y))-layerScale m v y|^32 ∂gaussMat m k v) ≤
      (layerScale m v y * layerAllowance m)^32 := by
  let s := layerScale m v y
  have hs := layerScale_nonneg m v y
  have he : ∀ x : Fin m → ℝ,
      |nrm (reluV ((√v*√(normSq y)) • x))-s|^32 =
      s^32 * |layerRoot m x-1|^32 := by
    intro x
    rw [layerScale_root hm]
    change |s*layerRoot m x-s|^32 = _
    rw [← mul_sub_one, abs_mul, abs_of_nonneg hs, mul_pow]
  have hg : Measurable (fun z : Fin m → ℝ => |nrm (reluV z)-s|^32) := by
    exact (((continuous_nrm.comp continuous_reluV).measurable.sub_const s).abs).pow_const _
  have hi : Integrable (fun x : Fin m → ℝ =>
      |nrm (reluV ((√v*√(normSq y)) • x))-s|^32) (stdGauss (Fin m)) := by
    simp_rw [he]
    exact (layerRoot_deviation_moment hm).1.const_mul _
  refine ⟨layer_transfer_integrable v y hg hi, ?_⟩
  rw [layer_transfer v y hg]
  simp_rw [he]
  rw [integral_const_mul, mul_pow]
  exact mul_le_mul_of_nonneg_left (layerRoot_deviation_moment hm).2 (pow_nonneg hs _)

/-- The same transfer bounds the uncentred radius moment. -/
theorem layer_radius_moment {m k : ℕ} (hm : 1 ≤ m) (v : ℝ) (y : Fin k → ℝ) :
    Integrable (fun A : Matrix (Fin m) (Fin k) ℝ =>
      nrm (reluV (A *ᵥ y))^32) (gaussMat m k v) ∧
    (∫ A, nrm (reluV (A *ᵥ y))^32 ∂gaussMat m k v) ≤
      (layerScale m v y * (1+layerAllowance m))^32 := by
  let s := layerScale m v y
  have hs := layerScale_nonneg m v y
  have he : ∀ x : Fin m → ℝ,
      nrm (reluV ((√v*√(normSq y)) • x))^32 = s^32 * layerRoot m x^32 := by
    intro x
    rw [layerScale_root hm, mul_pow]
  have hf : MemLp (layerRoot m) 32 (stdGauss (Fin m)) :=
    layerRoot_memLp m (q := 16) (by norm_num)
  have hi0 : Integrable (fun x => layerRoot m x^32) (stdGauss (Fin m)) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (layerRoot_nonneg _ _)] using
      hf.integrable_norm_pow (by norm_num)
  have h0 : (∫ x, layerRoot m x^32 ∂stdGauss (Fin m)) ≤ (1+layerAllowance m)^32 := by
    have h := pow_le_pow_left₀ lpNorm_nonneg (layerRoot_norm hm) 32
    rw [lpNorm_pow32 hf.aestronglyMeasurable] at h
    simpa only [abs_of_nonneg (layerRoot_nonneg _ _)] using h
  have hg : Measurable (fun z : Fin m → ℝ => nrm (reluV z)^32) := by
    exact (continuous_nrm.comp continuous_reluV).measurable.pow_const _
  have hi : Integrable (fun x : Fin m → ℝ =>
      nrm (reluV ((√v*√(normSq y)) • x))^32) (stdGauss (Fin m)) := by
    simp_rw [he]
    exact hi0.const_mul _
  refine ⟨layer_transfer_integrable v y hg hi, ?_⟩
  rw [layer_transfer v y hg]
  simp_rw [he]
  rw [integral_const_mul, mul_pow]
  exact mul_le_mul_of_nonneg_left h0 (pow_nonneg hs _)

#print axioms layer_deviation_moment
#print axioms layer_radius_moment
end BstLean.Part222
