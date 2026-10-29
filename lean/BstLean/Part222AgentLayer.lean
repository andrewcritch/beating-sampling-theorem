import BstLean.Part222LayerTransfer
import BstLean.Part177En

/-! Both Agent layers have the same normalized radius allowance at width n squared. -/
namespace BstLean.Part222
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153
open BstLean.Part177 (TH)

noncomputable def agentLayerAllowance (n : ℕ) : ℝ := layerAllowance (mA n)

lemma layerScale_second {n : ℕ} (hn : 1 ≤ n) (y : Fin (mA n) → ℝ) :
    layerScale (mA n) (2/(mA n : ℝ)) y = nrm y := by
  have hm : (0 : ℝ) < mA n := by
    exact_mod_cast (Nat.one_le_pow 2 n hn)
  unfold layerScale
  rw [← sqrt_mul (by positivity : 0 ≤ (mA n : ℝ)/2)]
  have he : (mA n : ℝ)/2 * (2/(mA n : ℝ)) = 1 := by field_simp
  rw [he, sqrt_one, one_mul]

lemma layerScale_first {n : ℕ} (hn : 1 ≤ n) (x : Fin n → ℝ) :
    layerScale (mA n) (2/(n : ℝ)) x = √(n : ℝ)*nrm x := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : (mA n : ℝ) = (n : ℝ)^2 := by unfold mA; push_cast; rfl
  unfold layerScale
  rw [hm, ← sqrt_mul (by positivity : 0 ≤ (n : ℝ)^2/2)]
  have he : (n : ℝ)^2/2 * (2/(n : ℝ)) = n := by field_simp
  rw [he]

/-- Scaling a nonnegative even moment preserves integrability and its allowance. -/
lemma divided_moment {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) {s B : ℝ} (hs : 0 < s)
    (hi : Integrable (fun x => |f x|^32) μ)
    (hb : (∫ x, |f x|^32 ∂μ) ≤ B^32) :
    Integrable (fun x => |f x/s|^32) μ ∧
    (∫ x, |f x/s|^32 ∂μ) ≤ (B/s)^32 := by
  have he : (fun x => |f x/s|^32) = (fun x => |f x|^32/s^32) := by
    funext x
    rw [abs_div, abs_of_pos hs, div_pow]
  rw [he]
  refine ⟨hi.div_const _, ?_⟩
  rw [integral_div, div_pow]
  exact div_le_div_of_nonneg_right hb (pow_nonneg hs.le _)

noncomputable def firstRadius {n : ℕ} (x : Fin n → ℝ)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) : ℝ := nrm (reluV (A *ᵥ x))/√(n : ℝ)

lemma firstRadius_nonneg {n : ℕ} (x : Fin n → ℝ)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) : 0 ≤ firstRadius x A :=
  div_nonneg (nrm_nonneg _) (sqrt_nonneg _)

lemma firstRadius_continuous {n : ℕ} (x : Fin n → ℝ) : Continuous (firstRadius x) := by
  unfold firstRadius
  exact ((continuous_nrm.comp continuous_reluV).comp
    (Continuous.matrix_mulVec continuous_id continuous_const)).div_const _

theorem firstRadius_deviation {n : ℕ} (hn : 1 ≤ n) (x : Fin n → ℝ)
    (hx : normSq x = 1) :
    Integrable (fun A => |firstRadius x A-1|^32) (gaussMat (mA n) n (2/(n : ℝ))) ∧
    (∫ A, |firstRadius x A-1|^32 ∂gaussMat (mA n) n (2/(n : ℝ))) ≤
      agentLayerAllowance n^32 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnS : 0 < √(n : ℝ) := sqrt_pos.mpr hnR
  have hm : 1 ≤ mA n := Nat.one_le_pow _ _ hn
  have he : layerScale (mA n) (2/(n : ℝ)) x = √(n : ℝ) := by
    rw [layerScale_first hn, nrm, hx, sqrt_one, mul_one]
  obtain ⟨hi, hb⟩ := layer_deviation_moment hm (2/(n : ℝ)) x
  rw [he] at hi hb
  have hd := divided_moment (gaussMat (mA n) n (2/(n : ℝ)))
    (fun A => nrm (reluV (A *ᵥ x))-√(n : ℝ)) hnS hi hb
  have hfun : (fun A : Matrix (Fin (mA n)) (Fin n) ℝ =>
      |(nrm (reluV (A *ᵥ x))-√(n : ℝ))/√(n : ℝ)|^32) =
      (fun A => |firstRadius x A-1|^32) := by
    funext A
    congr 2
    unfold firstRadius
    field_simp
  rw [hfun] at hd
  simpa only [mul_div_cancel_left₀ _ hnS.ne', agentLayerAllowance] using hd

theorem firstRadius_moment {n : ℕ} (hn : 1 ≤ n) (x : Fin n → ℝ)
    (hx : normSq x = 1) :
    Integrable (fun A => firstRadius x A^32) (gaussMat (mA n) n (2/(n : ℝ))) ∧
    (∫ A, firstRadius x A^32 ∂gaussMat (mA n) n (2/(n : ℝ))) ≤
      (1+agentLayerAllowance n)^32 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnS : 0 < √(n : ℝ) := sqrt_pos.mpr hnR
  have hm : 1 ≤ mA n := Nat.one_le_pow _ _ hn
  have he : layerScale (mA n) (2/(n : ℝ)) x = √(n : ℝ) := by
    rw [layerScale_first hn, nrm, hx, sqrt_one, mul_one]
  obtain ⟨hi, hb⟩ := layer_radius_moment hm (2/(n : ℝ)) x
  rw [he] at hb
  have hi' : Integrable (fun A : Matrix (Fin (mA n)) (Fin n) ℝ =>
      |nrm (reluV (A *ᵥ x))|^32) (gaussMat (mA n) n (2/(n : ℝ))) := by
    simpa only [abs_of_nonneg (nrm_nonneg _)] using hi
  have hb' : (∫ A : Matrix (Fin (mA n)) (Fin n) ℝ,
      |nrm (reluV (A *ᵥ x))|^32 ∂gaussMat (mA n) n (2/(n : ℝ))) ≤
      (√(n : ℝ)*(1+layerAllowance (mA n)))^32 := by
    simpa only [abs_of_nonneg (nrm_nonneg _)] using hb
  have hd := divided_moment (gaussMat (mA n) n (2/(n : ℝ)))
    (fun A => nrm (reluV (A *ᵥ x))) hnS hi' hb'
  simpa only [firstRadius, abs_div, abs_of_nonneg (nrm_nonneg _), abs_of_nonneg (sqrt_nonneg _),
    mul_div_cancel_left₀ _ hnS.ne', agentLayerAllowance] using hd

noncomputable def secondDeviation {n : ℕ} (x : Fin n → ℝ) (a : TH n) : ℝ :=
  |nrm (hid2 a.1 a.2 x)/√(n : ℝ)-firstRadius x a.1|

theorem secondDeviation_moment {n : ℕ} (hn : 1 ≤ n) (x : Fin n → ℝ)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) :
    Integrable (fun B => secondDeviation x (A,B)^32)
      (gaussMat (mA n) (mA n) (2/(mA n : ℝ))) ∧
    (∫ B, secondDeviation x (A,B)^32 ∂gaussMat (mA n) (mA n) (2/(mA n : ℝ))) ≤
      (firstRadius x A * agentLayerAllowance n)^32 := by
  have hnS : 0 < √(n : ℝ) := sqrt_pos.mpr (by exact_mod_cast hn)
  obtain ⟨hi,hb⟩ := layer_deviation_moment
    (show 1 ≤ mA n from Nat.one_le_pow _ _ hn) (2/(mA n : ℝ)) (reluV (A *ᵥ x))
  rw [layerScale_second hn] at hi hb
  have hd := divided_moment (gaussMat (mA n) (mA n) (2/(mA n : ℝ)))
    (fun B => nrm (reluV (B *ᵥ reluV (A *ᵥ x)))-nrm (reluV (A *ᵥ x))) hnS hi hb
  have he : (fun B : Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
      |(nrm (reluV (B *ᵥ reluV (A *ᵥ x)))-nrm (reluV (A *ᵥ x)))/√(n : ℝ)|^32) =
      (fun B => secondDeviation x (A,B)^32) := by
    funext B
    simp only [secondDeviation, firstRadius, hid2]
    rw [sub_div]
  rw [he] at hd
  have eh : nrm (reluV (A *ᵥ x))*layerAllowance (mA n)/√(n : ℝ) =
      firstRadius x A*agentLayerAllowance n := by
    unfold firstRadius agentLayerAllowance
    ring
  rw [eh] at hd
  exact hd

#print axioms firstRadius_deviation
#print axioms firstRadius_moment
#print axioms secondDeviation_moment
end BstLean.Part222
