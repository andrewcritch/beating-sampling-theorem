import BstLean.Part134Mean
import BstLean.Part134Mehler

/-!
# Part 134, tools for item 3: the operator bound and the pair distribution

* `frame_bound`: if `E_u ⟨ξ_u, w⟩² ≤ L|w|²` for every `w`, then `|E_u α_u ξ_u|² ≤ L·E_u α_u²`.
* `kernel_sum`: `E_{u,u'} ⟨ξ_u, ξ_{u'}⟩ α_u β_{u'} = ⟨E α ξ, E β ξ⟩`.
* `frame_tensor`: the tensor comparison: the family `e_u ⊗ e_u` has the bound `L` of the family
  `e_u`, if `|e_u| ≤ 1`.
* `pair_law`: for unit vectors `e`, `e'` of `ℝ^m` and a standard Gaussian `n × m` matrix `G`,
  the pair `(G e, G e')` is a Gaussian pair with correlation `ρ = ⟨e, e'⟩` in every coordinate.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part134

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105 (BM sC gaussLin105 ouPair_of_cov bm_cauchy_schwarz)
open BstLean.Part130

variable {n m : ℕ} {U : Type*} [MeasurableSpace U]

lemma bm_sum {α : Type*} [MeasurableSpace α] {κ : Type*} (s : Finset κ) {F : κ → α → ℝ}
    (hF : ∀ k ∈ s, BM (F k)) : BM (fun x => ∑ k ∈ s, F k x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using BM.const (α := α) 0
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun k hk => hF k (Finset.mem_insert_of_mem hk))

section frame

variable (μ : Measure U) [IsProbabilityMeasure μ]

/-- `E_{u,u'} ⟨ξ_u, ξ_{u'}⟩ α_u β_{u'} = Σ_k (E α ξ_k)(E β ξ_k)`. -/
lemma kernel_sum {κ : Type} [Fintype κ] {ξ : U → κ → ℝ} (hξ : ∀ k, BM (fun u => ξ u k))
    {α β : U → ℝ} (hα : BM α) (hβ : BM β) :
    ∫ u, (∫ u', (∑ k, ξ u k * ξ u' k) * (α u * β u') ∂μ) ∂μ =
      ∑ k, (∫ u, α u * ξ u k ∂μ) * (∫ u, β u * ξ u k ∂μ) := by
  have e : ∀ u u', (∑ k, ξ u k * ξ u' k) * (α u * β u') =
      ∑ k, (α u * ξ u k) * (β u' * ξ u' k) := by
    intro u u'
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [e]
  have i1 : ∀ u, ∀ k ∈ Finset.univ,
      Integrable (fun u' => (α u * ξ u k) * (β u' * ξ u' k)) μ := fun u k _ =>
    ((hβ.mul (hξ k)).integrable μ).const_mul _
  simp_rw [fun u => integral_finsetSum Finset.univ (i1 u), integral_const_mul]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun k _ => by rw [integral_mul_const]
  · exact fun k _ => ((hα.mul (hξ k)).integrable μ).mul_const _

/-- **The operator bound** (the largest eigenvalue of `Σ = E ξ ξᵀ` is at most `L`): if
`E_u ⟨ξ_u, w⟩² ≤ L|w|²` for every `w`, then `|E_u α_u ξ_u|² ≤ L·E_u α_u²`. -/
lemma frame_bound {κ : Type} [Fintype κ] {ξ : U → κ → ℝ} (hξ : ∀ k, BM (fun u => ξ u k))
    {α : U → ℝ} (hα : BM α) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ w : κ → ℝ, ∫ u, (∑ k, ξ u k * w k) ^ 2 ∂μ ≤ L * ∑ k, w k ^ 2) :
    ∑ k, (∫ u, α u * ξ u k ∂μ) ^ 2 ≤ L * ∫ u, α u ^ 2 ∂μ := by
  set w : κ → ℝ := fun k => ∫ u, α u * ξ u k ∂μ with hw
  set S := ∑ k, w k ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hI0 : 0 ≤ ∫ u, α u ^ 2 ∂μ := integral_nonneg fun u => sq_nonneg _
  have bl : BM (fun u => ∑ k, ξ u k * w k) :=
    bm_sum Finset.univ fun k _ => (hξ k).mul (BM.const (w k))
  have e1 : S = ∫ u, α u * ∑ k, ξ u k * w k ∂μ := by
    have : ∀ u, α u * ∑ k, ξ u k * w k = ∑ k, w k * (α u * ξ u k) := by
      intro u; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    simp_rw [this]
    rw [integral_finsetSum _ fun k _ => ((hα.mul (hξ k)).integrable μ).const_mul _]
    simp_rw [integral_const_mul]
    exact Finset.sum_congr rfl fun k _ => by rw [sq]
  have cs := bm_cauchy_schwarz μ hα bl
  rw [← e1] at cs
  have h2 : S ^ 2 ≤ (∫ u, α u ^ 2 ∂μ) * (L * S) :=
    cs.trans (mul_le_mul_of_nonneg_left (hL w) hI0)
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [← h0]; exact mul_nonneg hL0 hI0
  · have : S * S ≤ (L * ∫ u, α u ^ 2 ∂μ) * S := by nlinarith
    exact le_of_mul_le_mul_right this hpos

/-- **The tensor comparison**: if `|e_u| ≤ 1` and the family `e_u` has the bound `L`, the family
`e_u ⊗ e_u` has the bound `L`. -/
lemma frame_tensor {e : U → Fin m → ℝ} (he : ∀ j, BM (fun u => e u j))
    (hn : ∀ u, normSq (e u) ≤ 1) {L : ℝ}
    (hL : ∀ w : Fin m → ℝ, ∫ u, (∑ j, e u j * w j) ^ 2 ∂μ ≤ L * ∑ j, w j ^ 2)
    (Q : Fin m × Fin m → ℝ) :
    ∫ u, (∑ p : Fin m × Fin m, (e u p.1 * e u p.2) * Q p) ^ 2 ∂μ ≤ L * ∑ p, Q p ^ 2 := by
  have pt : ∀ u, (∑ p : Fin m × Fin m, (e u p.1 * e u p.2) * Q p) ^ 2 ≤
      ∑ j, (∑ k, e u k * Q (j, k)) ^ 2 := by
    intro u
    have e1 : ∑ p : Fin m × Fin m, (e u p.1 * e u p.2) * Q p =
        ∑ j, e u j * ∑ k, e u k * Q (j, k) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e1]
    have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => e u j)
      (fun j => ∑ k, e u k * Q (j, k))
    have h1 : ∑ j, e u j ^ 2 ≤ 1 := hn u
    have h0 : 0 ≤ ∑ j, (∑ k, e u k * Q (j, k)) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    nlinarith
  have bj : ∀ j, BM (fun u => (∑ k, e u k * Q (j, k)) ^ 2) := fun j =>
    (bm_sum Finset.univ fun k _ => (he k).mul (BM.const (Q (j, k)))).sq
  have bL : BM (fun u => (∑ p : Fin m × Fin m, (e u p.1 * e u p.2) * Q p) ^ 2) :=
    (bm_sum Finset.univ fun p _ => ((he p.1).mul (he p.2)).mul (BM.const (Q p))).sq
  calc ∫ u, (∑ p : Fin m × Fin m, (e u p.1 * e u p.2) * Q p) ^ 2 ∂μ
      ≤ ∫ u, ∑ j, (∑ k, e u k * Q (j, k)) ^ 2 ∂μ :=
        integral_mono (bL.integrable μ)
          ((bm_sum Finset.univ fun j _ => bj j).integrable μ) pt
    _ = ∑ j, ∫ u, (∑ k, e u k * Q (j, k)) ^ 2 ∂μ :=
        integral_finsetSum _ fun j _ => (bj j).integrable μ
    _ ≤ ∑ j, L * ∑ k, Q (j, k) ^ 2 := Finset.sum_le_sum fun j _ => hL fun k => Q (j, k)
    _ = L * ∑ p, Q p ^ 2 := by rw [← Finset.mul_sum, Fintype.sum_prod_type]

end frame

/-! ## The pair distribution -/

lemma abs_dot_le_one {e e' : Fin m → ℝ} (he : normSq e = 1) (he' : normSq e' = 1) :
    |∑ j, e j * e' j| ≤ 1 := by
  unfold normSq at he he'
  have h1 : 0 ≤ ∑ j, (e j - e' j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have h2 : 0 ≤ ∑ j, (e j + e' j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have e1 : ∑ j, (e j - e' j) ^ 2 = ∑ j, e j ^ 2 + ∑ j, e' j ^ 2 - 2 * ∑ j, e j * e' j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ j, (e j + e' j) ^ 2 = ∑ j, e j ^ 2 + ∑ j, e' j ^ 2 + 2 * ∑ j, e j * e' j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [abs_le]
  constructor <;> linarith

lemma rowMat_self {e : Fin m → ℝ} (he : normSq e = 1) :
    rowMat n e * (rowMat n e).transpose = 1 := by
  classical
  ext i i'
  rw [rowMat_mul_transpose, Matrix.one_apply]
  have : ∑ j, e j * e j = 1 := by rw [← he]; exact Finset.sum_congr rfl fun j _ => (sq _).symm
  rw [this]

/-- For a unit vector `e`, `G e` is a standard Gaussian vector of `ℝⁿ`. -/
theorem row_law {e : Fin m → ℝ} (he : normSq e = 1) :
    (stdGauss (Fin n × Fin m)).map (fun ξ => (rowMat n e).mulVec ξ) = stdGauss (Fin n) := by
  classical
  have h := gaussLin105 _ _ _ (rowMat n e) (1 : Matrix (Fin n) (Fin n) ℝ)
    (by rw [rowMat_self he, Matrix.transpose_one, Matrix.mul_one])
  rw [h]
  have : (fun ξ : Fin n → ℝ => (1 : Matrix (Fin n) (Fin n) ℝ).mulVec ξ) = id := by
    funext ξ; simp
  rw [this, Measure.map_id]

/-- **The pair distribution.** For unit vectors `e`, `e'` of `ℝ^m` and a standard Gaussian
`n × m` matrix `G`: `(G e, G e')` has the distribution of `(X, ρ X + √(1−ρ²) Z)`, `ρ = ⟨e, e'⟩`,
`X`, `Z` independent standard Gaussian vectors of `ℝⁿ`. -/
theorem pair_law {e e' : Fin m → ℝ} (he : normSq e = 1) (he' : normSq e' = 1) :
    (stdGauss (Fin n × Fin m)).map
        (fun ξ => ((rowMat n e).mulVec ξ, (rowMat n e').mulVec ξ)) =
      ((stdGauss (Fin n)).prod (stdGauss (Fin n))).map
        (fun p => (p.1, (∑ j, e j * e' j) • p.1 + sC (∑ j, e j * e' j) • p.2)) := by
  classical
  set ρ := ∑ j, e j * e' j with hρ
  have hA : Matrix.fromRows (rowMat n e) (rowMat n e') *
      (Matrix.fromRows (rowMat n e) (rowMat n e')).transpose =
      Matrix.fromBlocks 1 (ρ • 1) (ρ • 1) 1 := by
    rw [Matrix.transpose_fromRows, Matrix.fromRows_mul_fromCols, rowMat_self he, rowMat_self he']
    congr 1
    · ext i i'
      rw [rowMat_mul_transpose, Matrix.smul_apply, Matrix.one_apply]
      split_ifs <;> simp [hρ]
    · ext i i'
      rw [rowMat_mul_transpose, Matrix.smul_apply, Matrix.one_apply]
      have : ∑ j, e' j * e j = ρ := by
        rw [hρ]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      split_ifs <;> simp [this]
  have h := ouPair_of_cov (abs_dot_le_one he he') _ hA
  rw [← h]
  rfl

end BstLean.Part134

open BstLean.Part134 in
#print axioms frame_bound
open BstLean.Part134 in
#print axioms frame_tensor
open BstLean.Part134 in
#print axioms pair_law
