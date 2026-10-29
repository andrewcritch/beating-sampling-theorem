import BstLean.Part46Defs
import BstLean.Part45NegMom

/-! Gaussian rotation invariance and coefficient energy identities.
The first three lemmas reuse the proofs from `Part45NegMom`. -/

namespace BstLean.Part46.CharFn
open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss qformι)

lemma gaussian_basis_preserving {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (b : OrthonormalBasis κ ℝ (EuclideanSpace ℝ ι)) :
    MeasurePreserving (fun z : ι → ℝ => WithLp.ofLp (b.repr (WithLp.toLp 2 z)))
      (stdGauss ι) (stdGauss κ) := by
  have hι : MeasurePreserving (MeasurableEquiv.toLp 2 (ι → ℝ))
      (stdGauss ι) (stdGaussian (EuclideanSpace ℝ ι)) :=
    ⟨(MeasurableEquiv.toLp 2 (ι → ℝ)).measurable, map_pi_eq_stdGaussian⟩
  have hb : MeasurePreserving b.repr (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ κ)) :=
    ⟨b.repr.continuous.measurable, stdGaussian_map b.repr⟩
  have hκ : MeasurePreserving (MeasurableEquiv.toLp 2 (κ → ℝ))
      (stdGauss κ) (stdGaussian (EuclideanSpace ℝ κ)) :=
    ⟨(MeasurableEquiv.toLp 2 (κ → ℝ)).measurable, map_pi_eq_stdGaussian⟩
  exact hκ.symm.comp (hb.comp hι)

lemma qform_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (z : ι → ℝ) :
    qformι A z = inner ℝ (WithLp.toLp 2 z) (A.toEuclideanLin (WithLp.toLp 2 z)) := by
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct, Matrix.mulVec,
    qformι, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma qform_eigenbasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (z : ι → ℝ) :
    qformι A z = ∑ i, hA.eigenvalues i *
      (hA.eigenvectorBasis.repr (WithLp.toLp 2 z) i) ^ 2 := by
  let b := hA.eigenvectorBasis
  have heig (i : ι) : A.toEuclideanLin (b i) = hA.eigenvalues i • b i := by
    apply WithLp.ofLp_injective
    exact hA.mulVec_eigenvectorBasis i
  have haction (v : EuclideanSpace ℝ ι) :
      A.toEuclideanLin v = ∑ i, (b.repr v i * hA.eigenvalues i) • b i := by
    nth_rw 1 [← b.sum_repr v]
    simp only [map_sum, map_smul, heig, smul_smul]
  rw [qform_inner, haction, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_right, real_inner_comm, ← b.repr_apply_apply]
  dsimp [b]
  ring


lemma frob_eigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) :
    (∑ i, ∑ j, A i j ^ 2) = ∑ i, hA.eigenvalues i ^ 2 := by
  have hs : ∀ i j, A j i = A i j := by
    intro i j
    have h := congrArg (fun M : Matrix ι ι ℝ => M i j) hA.eq
    simpa using h
  have ht : (A * A).trace = ∑ i, ∑ j, A i j ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    simp_rw [hs, ← pow_two]
  rw [← ht]
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_mul, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]
  simp [pow_two]

lemma linear_eigenbasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) (b z : ι → ℝ) :
    (∑ i, b i * z i) = ∑ i, (B.repr (WithLp.toLp 2 b) i) *
      (B.repr (WithLp.toLp 2 z) i) := by
  have h := B.repr.inner_map_map (WithLp.toLp 2 b) (WithLp.toLp 2 z)
  simpa only [EuclideanSpace.inner_toLp_toLp, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, dotProduct, mul_comm] using h.symm

lemma linear_norm_eigenbasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) (b : ι → ℝ) :
    (∑ i, (B.repr (WithLp.toLp 2 b) i) ^ 2) = ∑ i, b i ^ 2 := by
  rw [← EuclideanSpace.real_norm_sq_eq, B.repr.norm_map]
  exact EuclideanSpace.real_norm_sq_eq _

lemma symmetrize {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) :
    (∑ i, ∑ j, A i j * z i * z j) =
      qformι (fun i j => (A i j + A j i) / 2) z := by
  classical
  unfold qformι
  have hswap : (∑ i, ∑ j, A j i * z i * z j) = ∑ i, ∑ j, A i j * z i * z j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hp (i j : Fin n) : (A i j + A j i) / 2 * z i * z j =
      (A i j * z i * z j + A j i * z i * z j) / 2 := by ring
  simp_rw [hp, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [hswap]
  ring

end BstLean.Part46.CharFn
