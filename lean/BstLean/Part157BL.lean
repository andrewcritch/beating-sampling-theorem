import BstLean.Part157Gp
import BstLean.Part105Law

/-!
# Part 157, item 5: the Gaussian inequality for a finite frame

Do not use `sorry`, `native_decide` or `axiom`.

Paper: `theorem7-02-world.tex`, "The Gaussian geometric Brascamp–Lieb inequality"
(Chen, Dafnis, Paouris, Advances in Mathematics 280 (2015), Theorem 1(i), equation (1.4)).

* `GaussBLFinite`: the statement for a finite family of unit vectors `e_i` with
  `Σ c_i e_i e_iᵀ ≼ I`: `E ∏ f_i(⟨G, e_i⟩)^{c_i} ≤ ∏ (E f_i(g))^{c_i}`. A NAMED HYPOTHESIS; it is
  NOT proved in Lean.
* `jensen_rpow`: `E f^c ≤ (E f)^c` for `0 ≤ c ≤ 1`.
* `gauss_bl_coord`: the inequality for the coordinate vectors (independence and Jensen).
* **`gauss_bl_orthonormal`**: the inequality for ORTHONORMAL `e_i` (the rows of a matrix `E`
  with `E Eᵀ = 1`) and `0 ≤ c_i ≤ 1`. PROVED. For orthonormal vectors the frame condition
  `Σ c_i e_i e_iᵀ ≼ I` is the condition `c_i ≤ 1`.
-/

namespace BstLean.Part157

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part105 (gaussLin105)

/-- **The geometric Brascamp–Lieb inequality for the Gaussian measure, finite family (a named
hypothesis).** `e_i` (the rows of `E`) are unit vectors of `ℝ^ι`, `c_i > 0`, and
`Σ_i c_i ⟨e_i, w⟩² ≤ |w|²` for every `w`. Then for measurable `f_i ≥ 0` with `E f_i(g) < ∞`:
`E ∏_i f_i(⟨G, e_i⟩)^{c_i} ≤ ∏_i (E f_i(g))^{c_i}`, `G` standard Gaussian in `ℝ^ι`, `g` standard
Gaussian in `ℝ`.

Paper statement: `theorem7-02-world.tex`, the display before Lemma `t7:p02:GP` (the case of
rank-one maps `B_i = e_iᵀ`), cited from Chen–Dafnis–Paouris, Theorem 1(i). -/
def GaussBLFinite : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (E : Matrix κ ι ℝ) (c : κ → ℝ) (f : κ → ℝ → ℝ),
    (∀ i, ∑ j, E i j ^ 2 = 1) → (∀ i, 0 < c i) →
    (∀ w : ι → ℝ, ∑ i, c i * (E.mulVec w i) ^ 2 ≤ ∑ j, w j ^ 2) →
    (∀ i, Measurable (f i)) → (∀ i y, 0 ≤ f i y) →
    (∀ i, Integrable (f i) (gaussianReal 0 1)) →
    ∫ G, ∏ i, f i (E.mulVec G i) ^ c i ∂stdGauss ι ≤
      ∏ i, (∫ y, f i y ∂gaussianReal 0 1) ^ c i

/-- **Jensen's inequality for a power `0 ≤ c ≤ 1`**: `E f^c ≤ (E f)^c`. -/
theorem jensen_rpow {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f μ) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : ∫ x, f x ^ c ∂μ ≤ (∫ x, f x ∂μ) ^ c := by
  have hgi : Integrable (fun x => f x ^ c) μ := by
    refine ((integrable_const (1 : ℝ)).add hfi).mono' (hf.pow_const c).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hf0 x) c)]
    change f x ^ c ≤ 1 + f x
    rcases le_total (f x) 1 with h | h
    · have := Real.rpow_le_one (hf0 x) h hc0
      linarith [hf0 x]
    · have := Real.rpow_le_rpow_of_exponent_le h hc1
      rw [Real.rpow_one] at this
      linarith
  exact (Real.concaveOn_rpow hc0 hc1).le_map_integral
    (Real.continuous_rpow_const hc0).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall hf0) hfi hgi

/-- **The inequality for the coordinate vectors.** `E ∏_i f_i(G_i)^{c_i} ≤ ∏_i (E f_i(g))^{c_i}`
for `0 ≤ c_i ≤ 1`: the coordinates of a standard Gaussian vector are independent. -/
theorem gauss_bl_coord {κ : Type*} [Fintype κ] (f : κ → ℝ → ℝ) (c : κ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hf0 : ∀ i y, 0 ≤ f i y)
    (hfi : ∀ i, Integrable (f i) (gaussianReal 0 1)) (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1) :
    ∫ x, ∏ i, f i (x i) ^ c i ∂stdGauss κ ≤ ∏ i, (∫ y, f i y ∂gaussianReal 0 1) ^ c i := by
  unfold stdGauss
  rw [integral_fintype_prod_eq_prod (fun i y => f i y ^ c i)]
  exact Finset.prod_le_prod₀
    (fun i _ => integral_nonneg fun y => Real.rpow_nonneg (hf0 i y) _)
    (fun i _ => jensen_rpow (gaussianReal 0 1) (hf i) (hf0 i) (hfi i) (hc0 i) (hc1 i))

/-- The image of a standard Gaussian vector under a matrix with orthonormal rows is a standard
Gaussian vector. -/
theorem stdGauss_map_orthonormal {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (E : Matrix κ ι ℝ) (hE : E * E.transpose = 1) :
    (stdGauss ι).map (fun ξ => E.mulVec ξ) = stdGauss κ := by
  have h := gaussLin105 ι κ κ E (1 : Matrix κ κ ℝ) (by simp [hE])
  have e : (fun ξ : κ → ℝ => (1 : Matrix κ κ ℝ).mulVec ξ) = id := by
    funext ξ; simp
  rw [e, Measure.map_id] at h
  exact h

/-- **The Gaussian inequality for ORTHONORMAL vectors (proved).** `e_i` are the rows of `E`, with
`E Eᵀ = 1` (orthonormal), and `0 ≤ c_i ≤ 1`. For measurable `f_i ≥ 0` with `E f_i(g) < ∞`:
`E ∏_i f_i(⟨G, e_i⟩)^{c_i} ≤ ∏_i (E f_i(g))^{c_i}`. -/
theorem gauss_bl_orthonormal {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (E : Matrix κ ι ℝ) (hE : E * E.transpose = 1) (f : κ → ℝ → ℝ) (c : κ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hf0 : ∀ i y, 0 ≤ f i y)
    (hfi : ∀ i, Integrable (f i) (gaussianReal 0 1)) (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1) :
    ∫ G, ∏ i, f i (E.mulVec G i) ^ c i ∂stdGauss ι ≤
      ∏ i, (∫ y, f i y ∂gaussianReal 0 1) ^ c i := by
  have mg : Measurable (fun x : κ → ℝ => ∏ i, f i (x i) ^ c i) :=
    Finset.measurable_prod _ fun i _ => ((hf i).comp (measurable_pi_apply i)).pow_const _
  have mE : Measurable (fun ξ : ι → ℝ => E.mulVec ξ) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have h := integral_map (μ := stdGauss ι) mE.aemeasurable mg.aestronglyMeasurable
  rw [stdGauss_map_orthonormal E hE] at h
  rw [← h]
  exact gauss_bl_coord f c hf hf0 hfi hc0 hc1

end BstLean.Part157

open BstLean.Part157 in
#print axioms jensen_rpow
open BstLean.Part157 in
#print axioms gauss_bl_coord
open BstLean.Part157 in
#print axioms gauss_bl_orthonormal
