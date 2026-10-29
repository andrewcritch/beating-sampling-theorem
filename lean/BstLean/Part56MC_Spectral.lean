import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.LinearAlgebra.DFinsupp

namespace BstLean.Part56

theorem mc56_diagonal_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (V : ℕ → Submodule ℝ E) (eig : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hV : OrthogonalFamily ℝ (fun k => V k) (fun k => (V k).subtypeₗᵢ))
    (hdense : (⨆ k, V k).topologicalClosure = ⊤)
    (heigen : ∀ k (x : V k), T (x : E) = eig k • (x : E))
    (heig : ∀ k, |eig k| ≤ C) : ∀ x, ‖T x‖ ≤ C * ‖x‖ := by
  classical
  have hfinite (x : E) (hx : x ∈ ⨆ k, V k) : ‖T x‖ ≤ C * ‖x‖ := by
    obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hx
    obtain ⟨v, rfl⟩ := (Submodule.mem_iSup_finset_iff_exists_sum V x).mp hs
    have hsum : T (∑ k ∈ s, (v k : E)) = ∑ k ∈ s, ((eig k • v k : V k) : E) := by
      simp only [map_sum, heigen, Submodule.coe_smul]
    have hsq : ‖T (∑ k ∈ s, (v k : E))‖ ^ 2 ≤ C ^ 2 * ‖∑ k ∈ s, (v k : E)‖ ^ 2 := by
      rw [hsum]
      change ‖∑ k ∈ s, (V k).subtypeₗᵢ (eig k • v k)‖ ^ 2 ≤
        C ^ 2 * ‖∑ k ∈ s, (V k).subtypeₗᵢ (v k)‖ ^ 2
      rw [hV.norm_sum, hV.norm_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_smul, Real.norm_eq_abs, mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (heig k) 2)
        (sq_nonneg _)
    rw [← mul_pow] at hsq
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp hsq
  have hd : DenseRange (⨆ k, V k).subtype := by
    rw [denseRange_iff_closure_range]
    rw [show Set.range (⨆ k, V k).subtype = (↑(⨆ k, V k) : Set E) by
      ext x; simp]
    change (↑(⨆ k, V k).topologicalClosure : Set E) = Set.univ
    rw [hdense]
    rfl
  exact isClosed_property hd (isClosed_le (by fun_prop) (by fun_prop))
    (fun x => hfinite x x.property)

end BstLean.Part56
