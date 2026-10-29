import BstLean.Part171Row

/-!
# Part 171 (file `Swap`): averaging the transverse matrix row by row

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, "conditioning the transverse row gives the two biases". Given `v`,
`(N w(v))_j` is a centred Gaussian with variance `t|w(v)|²` (`gaussMat_mulVec`), so
`E_N φ(α + (N w)_j) = E_Z φ(α + √t|w| Z)`; Fubini swaps `E_N` and `E_v`.

* `mulVec_coord_le`: `|(M y)_j| ≤ (Σ_{i,k} M_{ik}² + |y|²)/2`.
* `int_gaussMat_coord`: `∫ φ(α + (N y)_j) dN = ∫ φ(α + √t√|y|² z) dγ(z)`.
* **`swap_row`**: `∫_N ∫_v φ(α(v) + (N w(v))_j) = ∫_v ∫_z φ(α(v) + √t√|w(v)|² z)`, with the
  integrability in `N`.
-/

namespace BstLean.Part171

open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (relu normSq gaussMat gaussMat_mulVec)
open BstLean.Part131 (frob frob_nonneg continuous_frob frob_sq_integrable)

variable {V : Type*} [MeasurableSpace V] {μ : Measure V} {m : ℕ}

lemma mulVec_coord_sq_le (M : Matrix (Fin m) (Fin m) ℝ) (y : Fin m → ℝ) (j : Fin m) :
    (M *ᵥ y) j ^ 2 ≤ frob M * normSq y := by
  have hcs : (∑ k, M j k * y k) ^ 2 ≤ (∑ k, M j k ^ 2) * (∑ k, y k ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hrow : ∑ k, M j k ^ 2 ≤ frob M := by
    unfold frob
    exact Finset.single_le_sum (f := fun i => ∑ k, M i k ^ 2)
      (fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _) (Finset.mem_univ j)
  have hy : 0 ≤ ∑ k, y k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  calc (M *ᵥ y) j ^ 2 = (∑ k, M j k * y k) ^ 2 := by rfl
    _ ≤ (∑ k, M j k ^ 2) * (∑ k, y k ^ 2) := hcs
    _ ≤ frob M * normSq y := by unfold normSq; gcongr

lemma frob_integrable (t : ℝ) : Integrable (fun M : Matrix (Fin m) (Fin m) ℝ => frob M)
    (gaussMat m m t) := by
  refine Integrable.mono' (((frob_sq_integrable m m t).add (integrable_const 1)).div_const 2)
    continuous_frob.measurable.aestronglyMeasurable (Eventually.of_forall fun M => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (frob_nonneg M)]
  show frob M ≤ (frob M ^ 2 + 1) / 2
  nlinarith [sq_nonneg (frob M - 1)]

/-- `E_N φ(α + (N y)_j) = E_Z φ(α + √t√|y|² Z)`. -/
lemma int_gaussMat_coord {φ : ℝ → ℝ} (hφ : Continuous φ) (α t : ℝ) (y : Fin m → ℝ) (j : Fin m) :
    ∫ N, φ (α + (N *ᵥ y) j) ∂gaussMat m m t =
      ∫ z, φ (α + √t * √(normSq y) * z) ∂gaussianReal 0 1 := by
  set σ := √t * √(normSq y)
  have hm : Measurable (fun N : Matrix (Fin m) (Fin m) ℝ => N *ᵥ y) :=
    (Continuous.matrix_mulVec continuous_id continuous_const).measurable
  have hc1 : Continuous (fun x : Fin m → ℝ => φ (α + x j)) :=
    hφ.comp (continuous_const.add (continuous_apply j))
  have e1 : ∫ N, φ (α + (N *ᵥ y) j) ∂gaussMat m m t =
      ∫ x, φ (α + x j) ∂(gaussMat m m t).map (fun N => N *ᵥ y) := by
    rw [integral_map hm.aemeasurable hc1.aestronglyMeasurable]
  rw [e1, gaussMat_mulVec]
  have hm2 : Measurable (fun ξ : Fin m → ℝ => σ • ξ) := by
    have : Continuous (fun ξ : Fin m → ℝ => σ • ξ) := by fun_prop
    exact this.measurable
  rw [integral_map hm2.aemeasurable hc1.aestronglyMeasurable]
  have hm3 : Measurable (fun ξ : Fin m → ℝ => ξ ⬝ᵥ Pi.single j 1) :=
    (continuous_id.dotProduct continuous_const).measurable
  have hc3 : Continuous (fun z : ℝ => φ (α + σ * z)) :=
    hφ.comp (continuous_const.add (continuous_const.mul continuous_id))
  have e3 : ∫ ξ, φ (α + (σ • ξ) j) ∂stdGauss (Fin m) =
      ∫ z, φ (α + σ * z) ∂(stdGauss (Fin m)).map (fun ξ => ξ ⬝ᵥ Pi.single j 1) := by
    rw [integral_map hm3.aemeasurable hc3.aestronglyMeasurable]
    congr 1; funext ξ
    simp [dotProduct_single]
  rw [e3, BstLean.Part131.stdGauss_dot]
  simp [dotProduct_single]

/-- **Fubini for one row**: `∫_N ∫_v φ(α(v) + (N w(v))_j) = ∫_v ∫_z φ(α(v) + √t√|w(v)|² z)`. -/
lemma swap_row [IsProbabilityMeasure μ] {φ : ℝ → ℝ} (hφ : Continuous φ) {A : ℝ}
    (hφb : ∀ x, |φ x| ≤ A + x ^ 2) {α : V → ℝ} (hα : Measurable α) {C : ℝ}
    (hαb : ∀ v, |α v| ≤ C) {w : V → Fin m → ℝ} (hw : Measurable w) {K : ℝ}
    (hwb : ∀ v, normSq (w v) ≤ K) (_hK0 : 0 ≤ K) (t : ℝ) (j : Fin m) :
    Integrable (fun N => ∫ v, φ (α v + (N *ᵥ w v) j) ∂μ) (gaussMat m m t) ∧
    ∫ N, ∫ v, φ (α v + (N *ᵥ w v) j) ∂μ ∂gaussMat m m t =
      ∫ v, ∫ z, φ (α v + √t * √(normSq (w v)) * z) ∂gaussianReal 0 1 ∂μ := by
  set F : Matrix (Fin m) (Fin m) ℝ × V → ℝ := fun p => φ (α p.2 + (p.1 *ᵥ w p.2) j) with hF
  have mF : Measurable F := by
    have h1 : Measurable (fun p : Matrix (Fin m) (Fin m) ℝ × V => (p.1 *ᵥ w p.2) j) :=
      (measurable_pi_apply j).comp (BstLean.Part149.measurable_mulVec_joint.comp
        (measurable_fst.prodMk (hw.comp measurable_snd)))
    exact hφ.measurable.comp ((hα.comp measurable_snd).add h1)
  have hbd : ∀ p : Matrix (Fin m) (Fin m) ℝ × V, |F p| ≤ A + 2 * C ^ 2 + 2 * K * frob p.1 := by
    intro p
    refine (hφb _).trans ?_
    have h1 : (α p.2 + (p.1 *ᵥ w p.2) j) ^ 2 ≤ 2 * α p.2 ^ 2 + 2 * (p.1 *ᵥ w p.2) j ^ 2 := by
      nlinarith [sq_nonneg (α p.2 - (p.1 *ᵥ w p.2) j)]
    have h2 : α p.2 ^ 2 ≤ C ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hαb _) 2
    have h3 := mulVec_coord_sq_le p.1 (w p.2) j
    have h4 : frob p.1 * normSq (w p.2) ≤ frob p.1 * K :=
      mul_le_mul_of_nonneg_left (hwb _) (frob_nonneg _)
    nlinarith
  have iB : Integrable (fun p : Matrix (Fin m) (Fin m) ℝ × V => A + 2 * C ^ 2 + 2 * K * frob p.1)
      ((gaussMat m m t).prod μ) :=
    (integrable_const _).add (((frob_integrable t).comp_fst μ).const_mul _)
  have iF : Integrable F ((gaussMat m m t).prod μ) :=
    Integrable.mono' iB mF.aestronglyMeasurable (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]; exact hbd p)
  refine ⟨iF.integral_prod_left, ?_⟩
  rw [integral_integral_swap iF]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  exact int_gaussMat_coord hφ (α v) t (w v) j

end BstLean.Part171
