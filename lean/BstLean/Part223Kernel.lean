import BstLean.Part223PlaneTransfer
import BstLean.Part223Canonical

/-! The two-image conditional mean agrees with transverse replacement. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part170
open BstLean.Part134 (lam res projPerp glue)
open BstLean.Part167 (perp perp_smul vecMul_projPerp)

variable {m q : ℕ}

lemma reb_retained (h : Fin m → ℝ) (M N : Matrix (Fin q) (Fin m) ℝ) :
    reb h (M *ᵥ h) N = M - M * projPerp h + N * projPerp h := by
  have he : (normSq h)⁻¹ • Matrix.vecMulVec (M *ᵥ h) h = M - M * projPerp h := by
    rw [projPerp, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
    have hv : M * Matrix.vecMulVec h h = Matrix.vecMulVec (M *ᵥ h) h := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hv]
    abel
  exact congrArg (fun P => P + N * projPerp h) he

lemma row_mul_projPerp (M : Matrix (Fin q) (Fin m) ℝ) (h : Fin m → ℝ) (j : Fin q) :
    (M * projPerp h) j = perp h (M j) :=
  vecMul_projPerp h (M j)

theorem plane_rebuild_eq_replace (h g : Fin m → ℝ)
    (M N : Matrix (Fin q) (Fin m) ℝ) :
    reb h (M *ᵥ h) (reb (res h g) (M *ᵥ g - lam h g • (M *ᵥ h)) N) =
      replaceMatrix h g M N := by
  have he : M *ᵥ g - lam h g • (M *ᵥ h) = M *ᵥ res h g := by
    rw [res, Matrix.mulVec_sub, Matrix.mulVec_smul]
  rw [he, reb_retained, reb_retained]
  have halg : M - M * projPerp h +
      (M - M * projPerp (res h g) + N * projPerp (res h g)) * projPerp h =
      M - (M * projPerp (res h g)) * projPerp h +
        (N * projPerp (res h g)) * projPerp h := by
    rw [Matrix.add_mul, Matrix.sub_mul]
    abel
  rw [halg]
  funext j
  change M j - ((M * projPerp (res h g)) * projPerp h) j +
    ((N * projPerp (res h g)) * projPerp h) j =
      M j - perp h (perp (res h g) (M j)) + perp h (perp (res h g) (N j))
  simp only [row_mul_projPerp]

lemma perp_direction_smul (b z : Fin m → ℝ) {s : ℝ} (hs : s ≠ 0) :
    perp (s • b) z = perp b z := by
  by_cases hb : normSq b = 0
  · have hb0 : b = 0 := by
      by_contra h
      exact BstLean.Part134.normSq_ne_zero h hb
    simp [hb0]
  · unfold perp
    rw [normSq_smul]
    have he : (∑ j, z j * (s • b) j) = s * ∑ j, z j * b j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [he, smul_smul]
    congr 2
    field_simp

lemma transverseProjection_direction_smul (h g z : Fin m → ℝ) {s : ℝ}
    (hs : s ≠ 0) : transverseProjection h (s • g) z = transverseProjection h g z := by
  have he : res h (s • g) = s • res h g := by
    rw [← perp_eq_res, ← perp_eq_res, perp_smul]
  rw [transverseProjection, he, perp_direction_smul _ _ hs]
  rfl

lemma replaceMatrix_direction_smul (h g : Fin m → ℝ) {s : ℝ} (hs : s ≠ 0)
    (M N : Matrix (Fin q) (Fin m) ℝ) :
    replaceMatrix h (s • g) M N = replaceMatrix h g M N := by
  funext j
  simp only [replaceMatrix, replaceTransverse, transverseProjection_direction_smul _ _ _ hs]

lemma replaceMatrix_smul (h g : Fin m → ℝ) (s : ℝ)
    (M N : Matrix (Fin q) (Fin m) ℝ) :
    replaceMatrix h g (s • M) (s • N) = s • replaceMatrix h g M N := by
  funext j
  change s • M j - transverseProjection h g (s • M j) +
    transverseProjection h g (s • N j) = s • (replaceTransverse h g (M j) (N j))
  rw [transverseProjection_smul, transverseProjection_smul]
  simp only [replaceTransverse, smul_add, smul_sub]

#print axioms plane_rebuild_eq_replace
#print axioms replaceMatrix_direction_smul
#print axioms replaceMatrix_smul
end BstLean.Part223
