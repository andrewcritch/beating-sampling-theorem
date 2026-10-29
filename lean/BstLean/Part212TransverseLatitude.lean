import BstLean.Part167Gam
import BstLean.Part212Transverse

/-! Integrate the actual transverse projection at order 160. -/
namespace BstLean.Part212
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part152 (opN)
open BstLean.Part153 (nrm nrm_nonneg nrm_mulVec_le)
open BstLean.Part167
variable {n m : ℕ}

theorem transverse_latitude160 {u w : Fin n → ℝ} (hu : normSq u = 1) (hw : normSq w = 1)
    (huw : ∑ i, u i * w i = 0) (D : Matrix (Fin m) (Fin n) ℝ) (h r p : Fin m → ℝ) {s : ℝ}
    (hs : 0 ≤ s) :
    ∫⁻ γ, ENNReal.ofReal (latSq (vecMul (p + perp h (perp r (s • γ))) D) u w ^ 80)
        ∂stdGauss (Fin m) ≤
      ENNReal.ofReal ((√(latSq (vecMul p D) u w + s ^ 2 * frobSq (Pmat u w * Dᵀ)) +
        BstLean.Part152.gaussMomConst 80 * (s * opN D)) ^ 160) := by
  set a := Pmat u w *ᵥ vecMul p D
  set B : Matrix (Fin n) (Fin m) ℝ := s • (Pmat u w * Dᵀ * projPerp h * projPerp r) with hB
  have hBv : ∀ γ, B *ᵥ γ = Pmat u w *ᵥ vecMul (perp h (perp r (s • γ))) D := by
    intro γ
    rw [hB, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, BstLean.Part167.projPerp_mulVec, BstLean.Part167.projPerp_mulVec, Matrix.mulVec_transpose,
      perp_smul, perp_smul, Matrix.smul_vecMul, Matrix.mulVec_smul]
  have hpt : ∀ γ, ENNReal.ofReal (latSq (vecMul (p + perp h (perp r (s • γ))) D) u w ^ 80) =
      ENNReal.ofReal (nrm (a + B *ᵥ γ) ^ 160) := by
    intro γ
    rw [Matrix.add_vecMul, latSq_eq hu hw huw, Matrix.mulVec_add, ← hBv]
    unfold nrm
    rw [show (160 : ℕ) = 2 * 80 from rfl, pow_mul, Real.sq_sqrt (normSq_nonneg _)]
  rw [lintegral_congr hpt]
  have hD0 := BstLean.Part152.opN_nonneg D
  have hL : ∀ z, nrm (B *ᵥ z) ≤ (s * opN D) * nrm z := by
    intro z
    rw [hBv]
    refine (nrm_Pmat_le hu hw huw _).trans ?_
    rw [← Matrix.mulVec_transpose]
    refine (nrm_mulVec_le _ _).trans ?_
    rw [BstLean.Part153.opN_transpose]
    have h1 : nrm (perp h (perp r (s • z))) ≤ s * nrm z := by
      refine (nrm_perp_le _ _).trans ((nrm_perp_le _ _).trans (le_of_eq ?_))
      rw [BstLean.Part153.nrm_smul, abs_of_nonneg hs]
    calc opN D * nrm (perp h (perp r (s • z))) ≤ opN D * (s * nrm z) :=
          mul_le_mul_of_nonneg_left h1 hD0
      _ = s * opN D * nrm z := by ring
  refine (transverse_moment160 a B (mul_nonneg hs hD0) hL).trans (ENNReal.ofReal_le_ofReal ?_)
  have hV : normSq a + ∑ i, ∑ j, B i j ^ 2 ≤
      latSq (vecMul p D) u w + s ^ 2 * frobSq (Pmat u w * Dᵀ) := by
    rw [latSq_eq hu hw huw]
    have e : ∑ i, ∑ j, B i j ^ 2 = s ^ 2 * frobSq (Pmat u w * Dᵀ * projPerp h * projPerp r) := by
      unfold frobSq
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hB, Matrix.smul_apply, smul_eq_mul, mul_pow]
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left (frobSq_mul_proj_le (Pmat u w * Dᵀ) h r) (sq_nonneg s)
    linarith
  have hC0 : 0 ≤ BstLean.Part152.gaussMomConst 80 * (s * opN D) :=
    mul_nonneg (BstLean.Part152.gaussMomConst_nonneg 80) (mul_nonneg hs hD0)
  exact pow_le_pow_left₀ (add_nonneg (Real.sqrt_nonneg _) hC0)
    (by linarith [Real.sqrt_le_sqrt hV]) 160

end BstLean.Part212
