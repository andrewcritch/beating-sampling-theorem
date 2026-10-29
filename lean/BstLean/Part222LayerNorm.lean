import BstLean.Part222Layer

/-! The single-layer allowance controls the actual order-32 norm. -/
namespace BstLean.Part222
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part153 (lpNorm_nat_pow)

lemma lpNorm_pow32 {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    lpNorm f 32 μ^32 = ∫ x, |f x|^32 ∂μ := by
  simpa only [Nat.cast_ofNat] using lpNorm_nat_pow (k := 32) (by norm_num) hf

lemma layerAllowance_nonneg (m : ℕ) : 0 ≤ layerAllowance m := by
  unfold layerAllowance
  exact add_nonneg (mul_nonneg (BstLean.Part195.rotationConstant_nonneg 16)
    (sqrt_nonneg _)) (by positivity)

/-- Rotation acts on the weight coordinates of one layer. -/
theorem layerRoot_centered_moment (m : ℕ) :
    ∫ x, |layerRoot m x - ∫ y, layerRoot m y ∂stdGauss (Fin m)|^32
      ∂stdGauss (Fin m) ≤
    (BstLean.Part195.rotationConstant 16 * √(2 / (m : ℝ)))^32 := by
  have hl := layerRoot_lip m
  have hL := sqrt_nonneg (2 / (m : ℝ))
  have hgrad : Integrable (fun x => BstLean.Part151.gradSq (layerRoot m) x ^ 16)
      (stdGauss (Fin m)) := by
    apply Integrable.of_bound
      ((BstLean.Part151.measurable_gradSq _).pow_const _).aestronglyMeasurable
      (((√(2 / (m : ℝ)))^2)^16)
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (BstLean.Part151.gradSq_nonneg _ _)
        (BstLean.Part151.gradSq_le hL hl x) 16
  have hb : (∫ x, BstLean.Part151.gradSq (layerRoot m) x ^ 16
      ∂stdGauss (Fin m)) ≤ ((√(2 / (m : ℝ)))^2)^16 := by
    have hprob : IsProbabilityMeasure (stdGauss (Fin m)) := by unfold stdGauss; infer_instance
    exact (integral_mono hgrad (integrable_const _) fun x =>
      pow_le_pow_left₀ (BstLean.Part151.gradSq_nonneg _ _)
        (BstLean.Part151.gradSq_le hL hl x) 16).trans_eq (by simp)
  have hr := BstLean.Part195.rotation_even hL hl (q := 16) (by norm_num)
  have hm := hr.trans (mul_le_mul_of_nonneg_left hb
    (pow_nonneg (BstLean.Part195.rotationConstant_nonneg 16) _))
  simpa only [mul_pow, ← pow_mul] using hm

/-- The norm includes the exact mean deficit. -/
theorem layerRoot_deviation_norm {m : ℕ} (hm : 1 ≤ m) :
    lpNorm (fun x => layerRoot m x-1) 32 (stdGauss (Fin m)) ≤ layerAllowance m := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin m)) := by unfold stdGauss; infer_instance
  have hf : MemLp (layerRoot m) 32 (stdGauss (Fin m)) :=
    layerRoot_memLp m (q := 16) (by norm_num)
  let a := ∫ x, layerRoot m x ∂stdGauss (Fin m)
  have hc : MemLp (fun x => layerRoot m x-a) 32 (stdGauss (Fin m)) :=
    hf.sub (memLp_const a)
  have hcn : lpNorm (fun x => layerRoot m x-a) 32 (stdGauss (Fin m)) ≤
      BstLean.Part195.rotationConstant 16 * √(2 / (m : ℝ)) := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0)
      (mul_nonneg (BstLean.Part195.rotationConstant_nonneg 16) (sqrt_nonneg _))
    rw [lpNorm_pow32 hc.aestronglyMeasurable]
    exact layerRoot_centered_moment m
  have hdef := layerRoot_mean_deficit hm
  have he : (fun x => layerRoot m x-1) =
      (fun x => layerRoot m x-a) + (fun _ => a-1) := by funext x; dsimp; ring
  rw [he]
  have ht := lpNorm_add_le hc (g := fun _ => a-1) (by norm_num : (1 : ℝ≥0∞) ≤ 32)
  have ha : lpNorm (fun _ : Fin m → ℝ => a-1) 32 (stdGauss (Fin m)) ≤ 5/(2*m) := by
    rw [lpNorm_const (by norm_num) (MeasureTheory.IsProbabilityMeasure.ne_zero _), probReal_univ]
    simp only [Real.norm_eq_abs, Real.one_rpow, mul_one]
    rw [abs_of_nonpos (by dsimp [a]; linarith [hdef.1])]
    dsimp [a]
    linarith [hdef.2]
  exact ht.trans (add_le_add hcn ha)

theorem layerRoot_deviation_moment {m : ℕ} (hm : 1 ≤ m) :
    Integrable (fun x => |layerRoot m x-1|^32) (stdGauss (Fin m)) ∧
    (∫ x, |layerRoot m x-1|^32 ∂stdGauss (Fin m)) ≤ layerAllowance m^32 := by
  have hf : MemLp (fun x => layerRoot m x-1) 32 (stdGauss (Fin m)) :=
    (layerRoot_memLp m (q := 16) (by norm_num)).sub (memLp_const 1)
  refine ⟨by simpa only [Real.norm_eq_abs] using hf.integrable_norm_pow (by norm_num), ?_⟩
  have h := pow_le_pow_left₀ lpNorm_nonneg (layerRoot_deviation_norm hm) 32
  rwa [lpNorm_pow32 hf.aestronglyMeasurable] at h

theorem layerRoot_norm {m : ℕ} (hm : 1 ≤ m) :
    lpNorm (layerRoot m) 32 (stdGauss (Fin m)) ≤ 1+layerAllowance m := by
  have hf : MemLp (fun x => layerRoot m x-1) 32 (stdGauss (Fin m)) :=
    (layerRoot_memLp m (q := 16) (by norm_num)).sub (memLp_const 1)
  have he : layerRoot m = (fun x => layerRoot m x-1) + (fun _ => 1) := by
    funext x; dsimp; ring
  have ht := lpNorm_add_le hf (g := fun _ => 1) (by norm_num : (1 : ℝ≥0∞) ≤ 32)
  rw [← he] at ht
  have hprob : IsProbabilityMeasure (stdGauss (Fin m)) := by unfold stdGauss; infer_instance
  have hconst : lpNorm (fun _ : Fin m → ℝ => (1 : ℝ)) 32 (stdGauss (Fin m)) = 1 := by
    rw [lpNorm_const (by norm_num) (MeasureTheory.IsProbabilityMeasure.ne_zero _), probReal_univ]
    simp
  rw [hconst] at ht
  exact (ht.trans (add_le_add (layerRoot_deviation_norm hm) (le_refl 1))).trans_eq (add_comm _ _)

#print axioms layerRoot_centered_moment
#print axioms layerRoot_deviation_norm
#print axioms layerRoot_deviation_moment
#print axioms layerRoot_norm
end BstLean.Part222
