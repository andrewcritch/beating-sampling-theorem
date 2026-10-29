import BstLean.Part209Transverse
import BstLean.Part167Gam

/-! Orthogonal plane coordinates, including zero and parallel inputs. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part152 BstLean.Part153 BstLean.Part134 BstLean.Part167

variable {n d : ℕ}

lemma dot_hat_projection (a z : Fin d → ℝ) :
    dotp z (hatV a) • hatV a = ((normSq a)⁻¹ * dotp z a) • a := by
  have hd : dotp z (hatV a) = (nrm a)⁻¹ * dotp z a := by
    unfold dotp hatV
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hd, hatV, smul_smul]
  congr 1
  have he : (nrm a)⁻¹ * (nrm a)⁻¹ = (normSq a)⁻¹ := by
    rw [← _root_.mul_inv_rev, ← sq, nrm, sq_sqrt (normSq_nonneg a)]
  calc (nrm a)⁻¹ * dotp z a * (nrm a)⁻¹ =
      ((nrm a)⁻¹ * (nrm a)⁻¹) * dotp z a := by ring
    _ = _ := by rw [he]

noncomputable def planePart (a b z : Fin d → ℝ) : Fin d → ℝ :=
  dotp z (hatV a) • hatV a + dotp z (hatV (res a b)) • hatV (res a b)

noncomputable def offPlane (a b : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  projPerp a * projPerp (res a b)

lemma offPlane_mulVec (a b z : Fin d → ℝ) :
    offPlane a b *ᵥ z = perp a (perp (res a b) z) := by
  rw [offPlane, ← Matrix.mulVec_mulVec, BstLean.Part167.projPerp_mulVec,
    BstLean.Part167.projPerp_mulVec]

lemma plane_decomposition (a b z : Fin d → ℝ) :
    planePart a b z + offPlane a b *ᵥ z = z := by
  rw [offPlane_mulVec, planePart, dot_hat_projection, dot_hat_projection]
  have h := perp_plane a b z (-((normSq (res a b))⁻¹ * dotp z (res a b)))
  have he : perp (res a b) z =
      -((normSq (res a b))⁻¹ * dotp z (res a b)) • res a b + z := by
    unfold perp dotp
    module
  rw [he, h]
  unfold perp dotp
  module

lemma perp_self (a : Fin d → ℝ) : perp a a = 0 := by
  by_cases ha : a = 0
  · subst ha; simp [perp]
  · have h0 : normSq a ≠ 0 := fun h => ha (normSq_eq_zero h)
    have he : ∑ j, a j * a j = normSq a := by simp [normSq, sq]
    rw [perp, he, inv_mul_cancel₀ h0, one_smul, sub_self]

lemma offPlane_kills (a b : Fin d → ℝ) :
    offPlane a b *ᵥ a = 0 ∧ offPlane a b *ᵥ b = 0 := by
  have horth : ∑ j, a j * res a b j = 0 := by
    by_cases ha : a = 0
    · subst ha; simp
    · have h := res_orth ha b
      simpa only [mul_comm] using h
  have hea : perp (res a b) a = a := by simp only [perp, horth, mul_zero, zero_smul, sub_zero]
  have her : offPlane a b *ᵥ res a b = 0 := by
    rw [offPlane_mulVec, perp_self]
    simp [perp]
  have hA : offPlane a b *ᵥ a = 0 := by rw [offPlane_mulVec, hea, perp_self]
  refine ⟨hA, ?_⟩
  have he : b = lam a b • a + res a b := by unfold res; module
  calc offPlane a b *ᵥ b = offPlane a b *ᵥ (lam a b • a + res a b) := congrArg _ he
    _ = 0 := by rw [Matrix.mulVec_add, Matrix.mulVec_smul, hA, her, smul_zero, zero_add]

lemma offPlane_contract (a b : Fin d → ℝ) (T : Matrix (Fin n) (Fin d) ℝ) :
    opN (T * offPlane a b) ≤ opN T := by
  apply opN_le_of_forall _ (opN_nonneg T)
  intro z
  rw [← Matrix.mulVec_mulVec]
  apply (nrm_mulVec_le T _).trans
  apply mul_le_mul_of_nonneg_left _ (opN_nonneg T)
  rw [offPlane_mulVec]
  exact (nrm_perp_le _ _).trans (nrm_perp_le _ _)

lemma offPlane_kernel (a b : Fin d → ℝ) : offPlane a b *ᵥ kernelVector a b = 0 := by
  obtain ⟨ha, hb⟩ := offPlane_kills a b
  unfold kernelVector
  split_ifs
  · simp
  · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, ha, hb]
    simp

lemma hatV_zero_or_unit (a : Fin d → ℝ) : hatV a = 0 ∨ normSq (hatV a) = 1 := by
  by_cases ha : a = 0
  · left; subst ha; simp [hatV]
  · exact Or.inr (normSq_hatV ha)

end BstLean.Part209
