import BstLean.Part109Defs

/-!
# Part 109: tails of a positive semidefinite Gaussian form given as a Gram form

`gramLower109 : LMLower109 → GramLower109`, `gramUpper109 : DiagCheb109 → GramUpper109`.
Route: the Gram matrix, the spectral theorem, the rotation invariance of the standard Gaussian
(`gaussLin105`).

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part109

open MeasureTheory ProbabilityTheory Matrix
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105

section spectral

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Diagonalization of a real symmetric matrix, in the form used here. -/
lemma diag_form (M : Matrix ι ι ℝ) (hM : M.IsHermitian) :
    ∃ (V : Matrix ι ι ℝ) (lam : ι → ℝ), V * Vᵀ = 1 ∧
      (∀ ξ : ι → ℝ, ∑ c, ∑ c', ξ c * ξ c' * M c c' = ∑ i, lam i * (V.mulVec ξ i) ^ 2) ∧
      (∑ i, lam i = ∑ c, M c c) ∧ (∑ i, lam i ^ 2 = ∑ c, ∑ c', M c c' ^ 2) ∧
      ((∀ ξ : ι → ℝ, 0 ≤ ∑ c, ∑ c', ξ c * ξ c' * M c c') → ∀ i, 0 ≤ lam i) := by
  classical
  set U : Matrix ι ι ℝ := (hM.eigenvectorUnitary : Matrix ι ι ℝ) with hU
  set lam : ι → ℝ := hM.eigenvalues with hlam
  have hstar : star U = Uᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have h1 : Uᵀ * U = 1 := by
    rw [← hstar]
    exact Unitary.coe_star_mul_self hM.eigenvectorUnitary
  have h2 : U * Uᵀ = 1 := by
    rw [← hstar]
    exact Unitary.coe_mul_star_self hM.eigenvectorUnitary
  have hspec : M = U * diagonal lam * Uᵀ := by
    have h := hM.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [← hstar]
    have e : (RCLike.ofReal ∘ hM.eigenvalues : ι → ℝ) = lam := by
      funext i; simp [hlam]
    rw [e] at h
    exact h
  have hsym : Mᵀ = M := by
    have := hM.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hform : ∀ ξ : ι → ℝ,
      ∑ c, ∑ c', ξ c * ξ c' * M c c' = ∑ i, lam i * ((Uᵀ).mulVec ξ i) ^ 2 := by
    intro ξ
    have e1 : ∑ c, ∑ c', ξ c * ξ c' * M c c' = ξ ⬝ᵥ M *ᵥ ξ := by
      simp only [dotProduct, mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
      ring
    rw [e1, hspec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
    simp only [dotProduct, mulVec_diagonal]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have htr : ∑ i, lam i = ∑ c, M c c := by
    have : M.trace = (diagonal lam).trace := by
      rw [hspec, Matrix.trace_mul_cycle, h1, Matrix.one_mul]
    simpa [Matrix.trace] using this.symm
  have htr2 : ∑ i, lam i ^ 2 = ∑ c, ∑ c', M c c' ^ 2 := by
    have e1 : (M * Mᵀ).trace = ∑ c, ∑ c', M c c' ^ 2 := by
      simp [Matrix.trace, Matrix.mul_apply, sq]
    have e2 : M * M = U * (diagonal lam * diagonal lam) * Uᵀ := by
      conv_lhs => rw [hspec]
      calc U * diagonal lam * Uᵀ * (U * diagonal lam * Uᵀ)
          = U * diagonal lam * (Uᵀ * U) * diagonal lam * Uᵀ := by
            simp only [Matrix.mul_assoc]
        _ = U * (diagonal lam * diagonal lam) * Uᵀ := by
            rw [h1]; simp only [Matrix.mul_assoc, Matrix.mul_one]
    have e3 : (M * Mᵀ).trace = (diagonal lam * diagonal lam).trace := by
      rw [hsym, e2, Matrix.trace_mul_cycle, h1, Matrix.one_mul]
    rw [← e1, e3]
    simp [Matrix.trace, sq]
  refine ⟨Uᵀ, lam, ?_, hform, htr, htr2, ?_⟩
  · rw [Matrix.transpose_transpose]; exact h1
  · intro hpos i
    have h := hpos (U.mulVec (Pi.single i 1))
    rw [hform, mulVec_mulVec, h1, one_mulVec] at h
    have e : ∑ j, lam j * (Pi.single i (1 : ℝ) : ι → ℝ) j ^ 2 = lam i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [hj]
      · simp
    rw [e] at h
    exact h

/-- Rotation invariance of the standard Gaussian. -/
lemma stdGauss_map_orth (V : Matrix ι ι ℝ) (hV : V * Vᵀ = 1) :
    (stdGauss ι).map (fun ξ => V.mulVec ξ) = stdGauss ι := by
  classical
  have h := gaussLin105 ι ι ι V (1 : Matrix ι ι ℝ) (by rw [hV]; simp)
  rw [h]
  have : (fun ξ : ι → ℝ => (1 : Matrix ι ι ℝ).mulVec ξ) = id := by
    funext ξ; simp
  rw [this, Measure.map_id]

lemma stdGauss_real_orth (V : Matrix ι ι ℝ) (hV : V * Vᵀ = 1) {S : Set (ι → ℝ)}
    (hS : MeasurableSet S) :
    (stdGauss ι).real {ξ | V.mulVec ξ ∈ S} = (stdGauss ι).real S := by
  have hm : Measurable (fun ξ : ι → ℝ => V.mulVec ξ) := by fun_prop
  have := map_measureReal_apply (μ := stdGauss ι) hm hS
  rw [stdGauss_map_orth V hV] at this
  exact this.symm

end spectral

section gram

variable {ι X : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace X] (μ : Measure X)

omit [DecidableEq ι] in
lemma gram_expand (f : ι → X → ℝ) (hf : ∀ c, MemLp (f c) 2 μ) (ξ : ι → ℝ) :
    ∫ y, (∑ c, ξ c * f c y) ^ 2 ∂μ = ∑ c, ∑ c', ξ c * ξ c' * ∫ y, f c y * f c' y ∂μ := by
  have hint : ∀ c c', Integrable (fun y => f c y * f c' y) μ := fun c c' =>
    (hf c).integrable_mul (hf c')
  have e : ∀ y, (∑ c, ξ c * f c y) ^ 2 = ∑ c, ∑ c', ξ c * ξ c' * (f c y * f c' y) := by
    intro y
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
    ring
  simp_rw [e]
  rw [integral_finsetSum _ fun c _ =>
    integrable_finsetSum _ fun c' _ => (hint c c').const_mul _]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_finsetSum _ fun c' _ => (hint c c').const_mul _]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [integral_const_mul]

/-- The diagonal data of a Gram form. -/
lemma gram_diag (f : ι → X → ℝ) (hf : ∀ c, MemLp (f c) 2 μ) :
    ∃ (V : Matrix ι ι ℝ) (lam : ι → ℝ), V * Vᵀ = 1 ∧ (∀ i, 0 ≤ lam i) ∧
      (∀ ξ : ι → ℝ, ∫ y, (∑ c, ξ c * f c y) ^ 2 ∂μ = ∑ i, lam i * (V.mulVec ξ i) ^ 2) ∧
      (∑ i, lam i = ∑ c, ∫ y, f c y ^ 2 ∂μ) ∧
      (∑ i, lam i ^ 2 = ∑ c, ∑ c', (∫ y, f c y * f c' y ∂μ) ^ 2) := by
  set M : Matrix ι ι ℝ := Matrix.of fun c c' => ∫ y, f c y * f c' y ∂μ with hMdef
  have hM : M.IsHermitian := by
    refine Matrix.IsHermitian.ext fun c c' => ?_
    simp only [star_trivial, hMdef, Matrix.of_apply]
    simp_rw [mul_comm]
  obtain ⟨V, lam, hV, hform, htr, htr2, hpos⟩ := diag_form M hM
  have hexp : ∀ ξ : ι → ℝ,
      ∫ y, (∑ c, ξ c * f c y) ^ 2 ∂μ = ∑ c, ∑ c', ξ c * ξ c' * M c c' := fun ξ =>
    gram_expand μ f hf ξ
  refine ⟨V, lam, hV, ?_, ?_, ?_, ?_⟩
  · refine hpos fun ξ => ?_
    rw [← hexp ξ]
    exact integral_nonneg fun y => sq_nonneg _
  · intro ξ
    rw [hexp ξ]
    exact hform ξ
  · rw [htr]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [hMdef, sq, Matrix.of_apply]
  · rw [htr2]
    rfl

end gram

theorem gramLower109 (h : LMLower109) : GramLower109 := by
  intro ι X _ _ μ _ f hf x hx
  classical
  obtain ⟨V, lam, hV, hlam, hform, htr, htr2⟩ := gram_diag μ f hf
  set S : Set (ι → ℝ) :=
    {η | ∑ i, lam i * (η i ^ 2 - 1) < -(2 * Real.sqrt (x * ∑ i, lam i ^ 2))} with hS
  have hSm : MeasurableSet S := by
    refine measurableSet_lt ?_ measurable_const
    fun_prop
  have hset : {ξ : ι → ℝ | ∫ y, (∑ c, ξ c * f c y) ^ 2 ∂μ <
        ∑ c, ∫ y, f c y ^ 2 ∂μ -
          2 * Real.sqrt (x * ∑ c, ∑ c', (∫ y, f c y * f c' y ∂μ) ^ 2)} =
      {ξ | V.mulVec ξ ∈ S} := by
    ext ξ
    simp only [Set.mem_ofPred_eq, hS]
    rw [hform ξ, ← htr, ← htr2]
    have e : ∑ i, lam i * (V.mulVec ξ i ^ 2 - 1) =
        ∑ i, lam i * V.mulVec ξ i ^ 2 - ∑ i, lam i := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    constructor <;> intro hh <;> linarith
  rw [hset, stdGauss_real_orth V hV hSm]
  exact h ι lam hlam x hx

theorem gramUpper109 (h : DiagCheb109) : GramUpper109 := by
  intro ι X _ _ μ _ f hf t ht
  classical
  obtain ⟨V, lam, hV, hlam, hform, htr, htr2⟩ := gram_diag μ f hf
  set S : Set (ι → ℝ) := {η | t ≤ ∑ i, lam i * (η i ^ 2 - 1)} with hS
  have hSm : MeasurableSet S := by
    refine measurableSet_le measurable_const ?_
    fun_prop
  have hset : {ξ : ι → ℝ | ∑ c, ∫ y, f c y ^ 2 ∂μ + t ≤ ∫ y, (∑ c, ξ c * f c y) ^ 2 ∂μ} =
      {ξ | V.mulVec ξ ∈ S} := by
    ext ξ
    simp only [Set.mem_ofPred_eq, hS]
    rw [hform ξ, ← htr]
    have e : ∑ i, lam i * (V.mulVec ξ i ^ 2 - 1) =
        ∑ i, lam i * V.mulVec ξ i ^ 2 - ∑ i, lam i := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    constructor <;> intro hh <;> linarith
  rw [hset, stdGauss_real_orth V hV hSm, ← htr2]
  exact h ι lam t ht

end BstLean.Part109

#print axioms BstLean.Part109.gramLower109
#print axioms BstLean.Part109.gramUpper109
