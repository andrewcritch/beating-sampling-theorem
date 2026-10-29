import BstLean.Part134Split
import BstLean.Part105Law
import BstLean.Part153PP
import BstLean.Part153Dec
import BstLean.Part153PPs

/-!
# Part 182 (file `EBlk`): groundwork for Lemma TI — the second-layer E block, upper singular values only

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `proofs/option-n/theorem7-04-frame-numerator.tex`, proof of Lemma `t7:p04:ti`, the E block.
This file avoids the Davidson–Szarek LOWER singular value (not in Lean): the main bilinear term is
bounded by polarization with the upper bound only ("TI-lite"; it costs the factor
`(ℓ² + L₁₁)/2` in place of `K₂⁺ L₁₁ + r₂ ℓ²`).

* `eb_colsplit`: for an orthogonal projection `P`, `A P` and `A (1 − P)` are independent under
  `gaussMat M k v` (column-block independence).
* `eb_rot`: `Rᵀ A U ~ gaussMat K d v` if `Rᵀ R = 1`, `Uᵀ U = 1`.
* `eb_cond_gordon`: `Pr(√v(√K + √d + υ) ≤ ‖(R Rᵀ) A (U Uᵀ)‖) ≤ e^{−υ²/2}`.
* `eb_polar`: `|XᵀMY| ≤ (s/4)(|X|² + |Y|² + 2|X·Y|)` for symmetric PSD `M ≼ sI`.
* `eb_polar_opN`: `‖𝔏ᵀ𝔑ᵀ𝔑𝔏'‖ ≤ ‖𝔑‖²(ℓ² + L₁₁)/2`.
* `eb_Eblock`: `‖(T + 𝔑𝔏)ᵀ(T' + 𝔑𝔏')‖ ≤ ‖𝔑‖²(ℓ² + L₁₁)/2 + 2τ₁c + τ₁²`.
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open BstLean.Part153 (nrm opN_mul_le)

variable {M k : ℕ}

/-- Flat vector to matrix. -/
def eb_toM {p q : ℕ} (η : Fin p × Fin q → ℝ) : Matrix (Fin p) (Fin q) ℝ := Matrix.of fun i j => η (i, j)

lemma eb_measurable_toM {p q : ℕ} : Measurable (eb_toM (p := p) (q := q)) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  exact measurable_pi_apply (i, j)

/-- The flat matrix of `A ↦ A * P` (with the scale `√v`). -/
noncomputable def eb_L (v : ℝ) (P : Matrix (Fin k) (Fin k) ℝ) :
    Matrix (Fin M × Fin k) (Fin M × Fin k) ℝ :=
  Matrix.of fun a b => √v * (if a.1 = b.1 then P b.2 a.2 else 0)

lemma eb_L_mulVec (v : ℝ) (P : Matrix (Fin k) (Fin k) ℝ) (ξ : Fin M × Fin k → ℝ) :
    (Matrix.of fun i j => √v * ξ (i, j) : Matrix (Fin M) (Fin k) ℝ) * P =
      eb_toM ((eb_L v P : Matrix (Fin M × Fin k) (Fin M × Fin k) ℝ) *ᵥ ξ) := by
  ext i j
  simp only [eb_toM, eb_L, Matrix.mul_apply, Matrix.of_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · refine Finset.sum_congr rfl fun j' _ => ?_
    simp; ring
  · intro b _ hb
    refine Finset.sum_eq_zero fun j' _ => ?_
    simp [Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma eb_L_orth (v : ℝ) (P : Matrix (Fin k) (Fin k) ℝ) (hPs : Pᵀ = P) (hPi : P * P = P) :
    (eb_L (M := M) v P) * (eb_L (M := M) v (1 - P))ᵀ = 0 := by
  have hz : Pᵀ * (1 - P) = 0 := by rw [hPs, Matrix.mul_sub, Matrix.mul_one, hPi, sub_self]
  ext a c
  simp only [eb_L, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Fintype.sum_prod_type, Matrix.zero_apply]
  rw [Finset.sum_eq_single a.1]
  · by_cases hac : c.1 = a.1
    · have h := congrFun (congrFun hz a.2) c.2
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply] at h
      rw [Finset.sum_congr rfl (g := fun j => (√v * √v) * (P j a.2 * (1 - P) j c.2))
        (fun j _ => by rw [if_pos rfl, if_pos hac]; ring)]
      rw [← Finset.mul_sum, h, mul_zero]
    · refine Finset.sum_eq_zero fun j _ => ?_
      simp [hac]
  · intro b _ hb
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Column-block independence of a Gaussian matrix**: for an orthogonal projection `P`
(`Pᵀ = P`, `P² = P`), `A * P` and `A * (1 − P)` are independent under `gaussMat M k v`. -/
theorem eb_colsplit (v : ℝ) (P : Matrix (Fin k) (Fin k) ℝ) (hPs : Pᵀ = P) (hPi : P * P = P) :
    (gaussMat M k v).map (fun A => (A * P, A * (1 - P))) =
      ((gaussMat M k v).map (fun A => A * P)).prod ((gaussMat M k v).map (fun A => A * (1 - P))) := by
  have hF : Measurable (fun ξ : Fin M × Fin k → ℝ =>
      (Matrix.of fun i j => √v * ξ (i, j) : Matrix (Fin M) (Fin k) ℝ)) := measurable_ofFlat _
  have hg : Measurable (fun A : Matrix (Fin M) (Fin k) ℝ => (A * P, A * (1 - P))) := by
    refine Measurable.prodMk ?_ ?_ <;>
    exact (continuous_id.matrix_mul continuous_const).measurable
  have hg1 : Measurable (fun A : Matrix (Fin M) (Fin k) ℝ => A * P) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hg2 : Measurable (fun A : Matrix (Fin M) (Fin k) ℝ => A * (1 - P)) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have mLP : Measurable (fun ξ : Fin M × Fin k → ℝ => (eb_L (M := M) v P) *ᵥ ξ) :=
    measurable_mulVec_left _
  have mLQ : Measurable (fun ξ : Fin M × Fin k → ℝ => (eb_L (M := M) v (1 - P)) *ᵥ ξ) :=
    measurable_mulVec_left _
  have hT := eb_measurable_toM (p := M) (q := k)
  unfold gaussMat
  rw [Measure.map_map hg hF, Measure.map_map hg1 hF, Measure.map_map hg2 hF]
  have e1 : (fun A : Matrix (Fin M) (Fin k) ℝ => (A * P, A * (1 - P))) ∘
      (fun ξ : Fin M × Fin k → ℝ => (Matrix.of fun i j => √v * ξ (i, j) : Matrix (Fin M) (Fin k) ℝ)) =
      (Prod.map eb_toM eb_toM) ∘ (fun ξ => ((eb_L (M := M) v P) *ᵥ ξ, (eb_L (M := M) v (1 - P)) *ᵥ ξ)) := by
    funext ξ
    simp only [Function.comp_apply, Prod.map_apply, eb_L_mulVec]
  have e2 : (fun A : Matrix (Fin M) (Fin k) ℝ => A * P) ∘
      (fun ξ : Fin M × Fin k → ℝ => (Matrix.of fun i j => √v * ξ (i, j) : Matrix (Fin M) (Fin k) ℝ)) =
      eb_toM ∘ (fun ξ => (eb_L (M := M) v P) *ᵥ ξ) := by
    funext ξ; simp only [Function.comp_apply, eb_L_mulVec]
  have e3 : (fun A : Matrix (Fin M) (Fin k) ℝ => A * (1 - P)) ∘
      (fun ξ : Fin M × Fin k → ℝ => (Matrix.of fun i j => √v * ξ (i, j) : Matrix (Fin M) (Fin k) ℝ)) =
      eb_toM ∘ (fun ξ => (eb_L (M := M) v (1 - P)) *ᵥ ξ) := by
    funext ξ; simp only [Function.comp_apply, eb_L_mulVec]
  rw [e1, e2, e3, ← Measure.map_map (hT.prodMap hT) (mLP.prodMk mLQ), ← Measure.map_map hT mLP,
    ← Measure.map_map hT mLQ, BstLean.Part134.stdGauss_indep_of_orth _ _ (eb_L_orth v P hPs hPi)]
  have : IsProbabilityMeasure (stdGauss (Fin M × Fin k)) := inferInstance
  rw [Measure.map_prod_map _ _ hT hT]

/-! ## Rotated blocks and the conditional Gordon bound -/

/-- The flat matrix of `A ↦ Rᵀ * A * U` (with the scale `√v`). -/
noncomputable def eb_LR {K d : ℕ} (v : ℝ) (R : Matrix (Fin M) (Fin K) ℝ) (U : Matrix (Fin k) (Fin d) ℝ) :
    Matrix (Fin K × Fin d) (Fin M × Fin k) ℝ :=
  Matrix.of fun a b => √v * (R b.1 a.1 * U b.2 a.2)

/-- The flat matrix of the scale `√v`. -/
noncomputable def eb_D {K d : ℕ} (v : ℝ) : Matrix (Fin K × Fin d) (Fin K × Fin d) ℝ :=
  Matrix.of fun a b => √v * (if a = b then 1 else 0)

lemma eb_LR_mulVec {K d : ℕ} (v : ℝ) (R : Matrix (Fin M) (Fin K) ℝ) (U : Matrix (Fin k) (Fin d) ℝ)
    (ξ : Fin M × Fin k → ℝ) :
    Rᵀ * (Matrix.of fun i j => √v * ξ (i, j) : Matrix (Fin M) (Fin k) ℝ) * U =
      eb_toM ((eb_LR v R U) *ᵥ ξ) := by
  ext a b
  simp only [eb_toM, eb_LR, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma eb_D_mulVec {K d : ℕ} (v : ℝ) (η : Fin K × Fin d → ℝ) :
    (Matrix.of fun i j => √v * η (i, j) : Matrix (Fin K) (Fin d) ℝ) = eb_toM ((eb_D v) *ᵥ η) := by
  ext a b
  simp only [eb_toM, eb_D, Matrix.of_apply, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (a, b)]
  · simp
  · intro c _ hc
    rw [if_neg (Ne.symm hc)]; ring
  · intro h; exact absurd (Finset.mem_univ _) h

lemma eb_LR_gram {K d : ℕ} (v : ℝ) (hv : 0 ≤ v) (R : Matrix (Fin M) (Fin K) ℝ) (U : Matrix (Fin k) (Fin d) ℝ)
    (hR : Rᵀ * R = 1) (hU : Uᵀ * U = 1) :
    (eb_LR v R U) * (eb_LR v R U)ᵀ = (eb_D (K := K) (d := d) v) * (eb_D v)ᵀ := by
  ext a a'
  have h1 := congrFun (congrFun hR a.1) a'.1
  have h2 := congrFun (congrFun hU a.2) a'.2
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at h1 h2
  have hvv : √v * √v = v := Real.mul_self_sqrt hv
  have eL : ((eb_LR v R U) * (eb_LR v R U)ᵀ) a a' =
      v * ((∑ i, R i a.1 * R i a'.1) * (∑ j, U j a.2 * U j a'.2)) := by
    simp only [eb_LR, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      Fintype.sum_prod_type]
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    linear_combination (R i a.1 * R i a'.1 * (U j a.2 * U j a'.2)) * hvv
  have eD : ((eb_D (K := K) (d := d) v : Matrix (Fin K × Fin d) (Fin K × Fin d) ℝ) *
      (eb_D (K := K) (d := d) v)ᵀ) a a' = v * (if a = a' then 1 else 0) := by
    simp only [eb_D, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    rw [Finset.sum_eq_single a]
    · by_cases h : a = a'
      · subst h; simpa using hvv
      · simp [h, Ne.symm h]
    · intro c _ hc; simp [Ne.symm hc]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [eL, eD, h1, h2]
  by_cases h : a = a'
  · subst h; simp
  · have : a.1 ≠ a'.1 ∨ a.2 ≠ a'.2 := by
      by_contra hc; push_neg at hc; exact h (Prod.ext hc.1 hc.2)
    rcases this with h' | h' <;> simp [Matrix.one_apply, h', h]

/-- **A Gaussian matrix in orthonormal coordinates**: if `Rᵀ R = 1` and `Uᵀ U = 1`, then
`Rᵀ A U` is a Gaussian matrix with the same entry variance. -/
theorem eb_rot {K d : ℕ} {v : ℝ} (hv : 0 ≤ v) (R : Matrix (Fin M) (Fin K) ℝ) (U : Matrix (Fin k) (Fin d) ℝ)
    (hR : Rᵀ * R = 1) (hU : Uᵀ * U = 1) :
    (gaussMat M k v).map (fun A => Rᵀ * A * U) = gaussMat K d v := by
  have hF : Measurable (fun ξ : Fin M × Fin k → ℝ =>
      (Matrix.of fun i j => √v * ξ (i, j) : Matrix (Fin M) (Fin k) ℝ)) := measurable_ofFlat _
  have hg : Measurable (fun A : Matrix (Fin M) (Fin k) ℝ => Rᵀ * A * U) :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable
  have hT := eb_measurable_toM (p := K) (q := d)
  unfold gaussMat
  rw [Measure.map_map hg hF]
  have e1 : (fun A : Matrix (Fin M) (Fin k) ℝ => Rᵀ * A * U) ∘
      (fun ξ : Fin M × Fin k → ℝ => (Matrix.of fun i j => √v * ξ (i, j) : Matrix (Fin M) (Fin k) ℝ)) =
      eb_toM ∘ (fun ξ => (eb_LR v R U) *ᵥ ξ) := by
    funext ξ; simp only [Function.comp_apply, eb_LR_mulVec]
  have e2 : (fun η : Fin K × Fin d → ℝ => (Matrix.of fun i j => √v * η (i, j) : Matrix (Fin K) (Fin d) ℝ)) =
      eb_toM ∘ (fun η => (eb_D v) *ᵥ η) := by
    funext η; simp only [Function.comp_apply, eb_D_mulVec]
  rw [e1, e2, ← Measure.map_map hT (measurable_mulVec_left _),
    ← Measure.map_map hT (measurable_mulVec_left _),
    BstLean.Part105.gaussLin105 _ _ _ _ _ (eb_LR_gram v hv R U hR hU)]

lemma eb_opN_le_one {K : ℕ} (R : Matrix (Fin M) (Fin K) ℝ) (hR : Rᵀ * R = 1) : opN R ≤ 1 := by
  refine BstLean.Part153.opN_le_of_forall R zero_le_one fun w => ?_
  have e : normSq (R *ᵥ w) = normSq w := by
    have h1 : normSq (R *ᵥ w) = (R *ᵥ w) ⬝ᵥ (R *ᵥ w) := by
      simp [normSq, dotProduct, sq]
    have h2 : normSq w = w ⬝ᵥ w := by simp [normSq, dotProduct, sq]
    rw [h1, h2, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, ← Matrix.mulVec_transpose, hR,
      Matrix.transpose_one, Matrix.one_mulVec, dotProduct_comm]
  rw [one_mul]
  unfold nrm
  rw [e]

/-- **Conditional Gordon bound**: for `S = R Rᵀ` (`Rᵀ R = 1`, `K` columns: at most `K` "active
rows") and `Q = U Uᵀ` (`Uᵀ U = 1`, `d` columns: a subspace of dimension `d`),
`Pr(√v(√K + √d + υ) ≤ ‖S A Q‖) ≤ e^{−υ²/2}` under `gaussMat M k v`. -/
theorem eb_cond_gordon {K d : ℕ} {v : ℝ} (hv : 0 < v) (R : Matrix (Fin M) (Fin K) ℝ)
    (U : Matrix (Fin k) (Fin d) ℝ) (hR : Rᵀ * R = 1) (hU : Uᵀ * U = 1) {υ : ℝ} (hυ : 0 ≤ υ) :
    (gaussMat M k v).real {A | √v * (√(K : ℝ) + √(d : ℝ) + υ) ≤ opN ((R * Rᵀ) * A * (U * Uᵀ))} ≤
      Real.exp (-υ ^ 2 / 2) := by
  have hg : Measurable (fun A : Matrix (Fin M) (Fin k) ℝ => Rᵀ * A * U) :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable
  have hS : MeasurableSet {B : Matrix (Fin K) (Fin d) ℝ | √v * (√(K : ℝ) + √(d : ℝ) + υ) ≤ opN B} :=
    measurableSet_le measurable_const opN_continuous.measurable
  have hsub : {A : Matrix (Fin M) (Fin k) ℝ | √v * (√(K : ℝ) + √(d : ℝ) + υ) ≤
      opN ((R * Rᵀ) * A * (U * Uᵀ))} ⊆
      (fun A => Rᵀ * A * U) ⁻¹' {B | √v * (√(K : ℝ) + √(d : ℝ) + υ) ≤ opN B} := by
    intro A hA
    simp only [Set.mem_setOf_eq, Set.mem_preimage] at hA ⊢
    refine hA.trans ?_
    have e : (R * Rᵀ) * A * (U * Uᵀ) = R * (Rᵀ * A * U) * Uᵀ := by
      simp only [Matrix.mul_assoc]
    rw [e]
    have h1 := opN_mul_le (R * (Rᵀ * A * U)) Uᵀ
    have h2 := opN_mul_le R (Rᵀ * A * U)
    have hR1 := eb_opN_le_one R hR
    have hU1 : opN Uᵀ ≤ 1 := by rw [BstLean.Part153.opN_transpose]; exact eb_opN_le_one U hU
    have h0 := opN_nonneg (Rᵀ * A * U)
    have h0' := opN_nonneg (R * (Rᵀ * A * U))
    calc opN (R * (Rᵀ * A * U) * Uᵀ) ≤ opN (R * (Rᵀ * A * U)) * opN Uᵀ := h1
      _ ≤ opN (R * (Rᵀ * A * U)) * 1 := mul_le_mul_of_nonneg_left hU1 h0'
      _ ≤ opN R * opN (Rᵀ * A * U) := by rw [mul_one]; exact h2
      _ ≤ 1 * opN (Rᵀ * A * U) := mul_le_mul_of_nonneg_right hR1 h0
      _ = opN (Rᵀ * A * U) := one_mul _
  have hP : IsProbabilityMeasure (gaussMat M k v) := by unfold gaussMat; infer_instance
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  rw [← map_measureReal_apply hg hS, eb_rot hv.le R U hR hU]
  exact opN_tail' (p := K) (q := d) hv hυ

/-! ## The polarization step (deterministic) -/

lemma eb_bil_symm {p : ℕ} (Mt : Matrix (Fin p) (Fin p) ℝ) (hsym : Mtᵀ = Mt) (X Y : Fin p → ℝ) :
    Y ⬝ᵥ Mt *ᵥ X = X ⬝ᵥ Mt *ᵥ Y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, dotProduct_comm]

lemma eb_normSq_add {p : ℕ} (X Y : Fin p → ℝ) :
    normSq (X + Y) = normSq X + normSq Y + 2 * (X ⬝ᵥ Y) := by
  simp only [normSq, dotProduct, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma eb_normSq_sub {p : ℕ} (X Y : Fin p → ℝ) :
    normSq (X - Y) = normSq X + normSq Y - 2 * (X ⬝ᵥ Y) := by
  simp only [normSq, dotProduct, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **Polarization with only an upper bound**: for a symmetric PSD matrix `M ≼ s·I`,
`|Xᵀ M Y| ≤ (s/4)(|X|² + |Y|² + 2|X·Y|)`. -/
theorem eb_polar {p : ℕ} (Mt : Matrix (Fin p) (Fin p) ℝ) (hsym : Mtᵀ = Mt)
    (hpsd : ∀ z, 0 ≤ z ⬝ᵥ Mt *ᵥ z) {s : ℝ} (hs0 : 0 ≤ s) (hs : ∀ z, z ⬝ᵥ Mt *ᵥ z ≤ s * normSq z)
    (X Y : Fin p → ℝ) :
    |X ⬝ᵥ Mt *ᵥ Y| ≤ s / 4 * (normSq X + normSq Y + 2 * |X ⬝ᵥ Y|) := by
  have hYX := eb_bil_symm Mt hsym X Y
  have ep : (X + Y) ⬝ᵥ Mt *ᵥ (X + Y) =
      X ⬝ᵥ Mt *ᵥ X + 2 * (X ⬝ᵥ Mt *ᵥ Y) + Y ⬝ᵥ Mt *ᵥ Y := by
    simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct]; rw [hYX]; ring
  have em : (X - Y) ⬝ᵥ Mt *ᵥ (X - Y) =
      X ⬝ᵥ Mt *ᵥ X - 2 * (X ⬝ᵥ Mt *ᵥ Y) + Y ⬝ᵥ Mt *ᵥ Y := by
    simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]; rw [hYX]; ring
  have h1 := hs (X + Y)
  have h2 := hs (X - Y)
  have h3 := hpsd (X + Y)
  have h4 := hpsd (X - Y)
  rw [eb_normSq_add] at h1
  rw [eb_normSq_sub] at h2
  have hab := abs_nonneg (X ⬝ᵥ Y)
  have hle := le_abs_self (X ⬝ᵥ Y)
  have hge := neg_abs_le (X ⬝ᵥ Y)
  rw [abs_le]
  constructor <;> nlinarith

/-- `opN M ≤ C` from a bound of the bilinear form on the unit spheres. -/
lemma eb_opN_le_of_bil {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ u : Fin p → ℝ, ∀ w : Fin q → ℝ, ∑ i, u i ^ 2 = 1 → ∑ j, w j ^ 2 = 1 →
      u ⬝ᵥ M *ᵥ w ≤ C) : opN M ≤ C := by
  by_cases hne : (opSet M).Nonempty
  · refine csSup_le hne ?_
    rintro x ⟨u, w, hu, hw, rfl⟩
    exact h u w hu hw
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    unfold opN
    rw [hne, Real.sSup_empty]
    exact hC

lemma eb_dot_transpose_mulVec {p q : ℕ} (B : Matrix (Fin p) (Fin q) ℝ) (u : Fin q → ℝ)
    (z : Fin p → ℝ) : u ⬝ᵥ Bᵀ *ᵥ z = (B *ᵥ u) ⬝ᵥ z := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

lemma eb_abs_bil_le {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) (u : Fin p → ℝ) (w : Fin q → ℝ)
    (hu : ∑ i, u i ^ 2 = 1) (hw : ∑ j, w j ^ 2 = 1) : |u ⬝ᵥ M *ᵥ w| ≤ opN M := by
  have h1 := bil_le_opN_mul M u w
  have h2 := bil_le_opN_mul M (-u) w
  have hu' : ∑ i, (-u) i ^ 2 = 1 := by simpa using hu
  rw [hu, hw, Real.sqrt_one, mul_one, mul_one] at h1
  rw [hu', hw, Real.sqrt_one, mul_one, mul_one, neg_dotProduct] at h2
  rw [abs_le]; constructor <;> linarith

lemma eb_normSq_mulVec_le {p q : ℕ} (B : Matrix (Fin p) (Fin q) ℝ) (u : Fin q → ℝ) :
    normSq (B *ᵥ u) ≤ opN B ^ 2 * normSq u := by
  have h := BstLean.Part153.nrm_mulVec_le B u
  have h0 := BstLean.Part153.nrm_nonneg (B *ᵥ u)
  have h2 : nrm (B *ᵥ u) ^ 2 ≤ (opN B * nrm u) ^ 2 := pow_le_pow_left₀ h0 h 2
  have e1 : nrm (B *ᵥ u) ^ 2 = normSq (B *ᵥ u) := Real.sq_sqrt (normSq_nonneg _)
  have e2 : nrm u ^ 2 = normSq u := Real.sq_sqrt (normSq_nonneg _)
  rw [e1, mul_pow, e2] at h2
  exact h2

/-- **The E-block main term without the lower singular value**: for `𝔑` (any matrix) and
`𝔏, 𝔏'` with `‖𝔏‖, ‖𝔏'‖ ≤ ℓ` and `‖𝔏ᵀ𝔏'‖ ≤ L₁₁`:
`‖𝔏ᵀ 𝔑ᵀ𝔑 𝔏'‖ ≤ ‖𝔑‖²(ℓ² + L₁₁)/2`. -/
theorem eb_polar_opN {r q a a' : ℕ} (Nm : Matrix (Fin r) (Fin q) ℝ) (L : Matrix (Fin q) (Fin a) ℝ)
    (L' : Matrix (Fin q) (Fin a') ℝ) {ℓ L11 : ℝ} (hL : opN L ≤ ℓ) (hL' : opN L' ≤ ℓ)
    (hLL : opN (Lᵀ * L') ≤ L11) :
    opN (Lᵀ * (Nmᵀ * Nm) * L') ≤ opN Nm ^ 2 * (ℓ ^ 2 + L11) / 2 := by
  have hℓ : 0 ≤ ℓ := (opN_nonneg L).trans hL
  have hL110 : 0 ≤ L11 := (opN_nonneg _).trans hLL
  have hs0 : 0 ≤ opN Nm ^ 2 := sq_nonneg _
  have hsym : (Nmᵀ * Nm)ᵀ = Nmᵀ * Nm := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hq : ∀ z : Fin q → ℝ, z ⬝ᵥ (Nmᵀ * Nm) *ᵥ z = normSq (Nm *ᵥ z) := by
    intro z
    rw [← Matrix.mulVec_mulVec, eb_dot_transpose_mulVec]
    simp [normSq, dotProduct, sq]
  have hpsd : ∀ z : Fin q → ℝ, 0 ≤ z ⬝ᵥ (Nmᵀ * Nm) *ᵥ z := fun z => by
    rw [hq]; exact normSq_nonneg _
  have hs : ∀ z : Fin q → ℝ, z ⬝ᵥ (Nmᵀ * Nm) *ᵥ z ≤ opN Nm ^ 2 * normSq z := fun z => by
    rw [hq]; exact eb_normSq_mulVec_le Nm z
  refine eb_opN_le_of_bil _ (by positivity) fun u w hu hw => ?_
  have e : u ⬝ᵥ (Lᵀ * (Nmᵀ * Nm) * L') *ᵥ w = (L *ᵥ u) ⬝ᵥ (Nmᵀ * Nm) *ᵥ (L' *ᵥ w) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, eb_dot_transpose_mulVec]
  rw [e]
  have hP := eb_polar (Nmᵀ * Nm) hsym hpsd hs0 hs (L *ᵥ u) (L' *ᵥ w)
  have hnu : normSq u = 1 := hu
  have hnw : normSq w = 1 := hw
  have hX : normSq (L *ᵥ u) ≤ ℓ ^ 2 := by
    have := eb_normSq_mulVec_le L u
    rw [hnu, mul_one] at this
    exact this.trans (pow_le_pow_left₀ (opN_nonneg L) hL 2)
  have hY : normSq (L' *ᵥ w) ≤ ℓ ^ 2 := by
    have := eb_normSq_mulVec_le L' w
    rw [hnw, mul_one] at this
    exact this.trans (pow_le_pow_left₀ (opN_nonneg L') hL' 2)
  have hXY : |(L *ᵥ u) ⬝ᵥ (L' *ᵥ w)| ≤ L11 := by
    have e2 : (L *ᵥ u) ⬝ᵥ (L' *ᵥ w) = u ⬝ᵥ (Lᵀ * L') *ᵥ w := by
      rw [← Matrix.mulVec_mulVec, eb_dot_transpose_mulVec]
    rw [e2]
    exact (eb_abs_bil_le _ u w hu hw).trans hLL
  have hbound : normSq (L *ᵥ u) + normSq (L' *ᵥ w) + 2 * |(L *ᵥ u) ⬝ᵥ (L' *ᵥ w)| ≤
      2 * ℓ ^ 2 + 2 * L11 := by linarith
  calc (L *ᵥ u) ⬝ᵥ (Nmᵀ * Nm) *ᵥ (L' *ᵥ w)
      ≤ |(L *ᵥ u) ⬝ᵥ (Nmᵀ * Nm) *ᵥ (L' *ᵥ w)| := le_abs_self _
    _ ≤ opN Nm ^ 2 / 4 * (normSq (L *ᵥ u) + normSq (L' *ᵥ w) + 2 * |(L *ᵥ u) ⬝ᵥ (L' *ᵥ w)|) := hP
    _ ≤ opN Nm ^ 2 / 4 * (2 * ℓ ^ 2 + 2 * L11) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = opN Nm ^ 2 * (ℓ ^ 2 + L11) / 2 := by ring

/-- **The E-block assembly (deterministic)**: if the second-layer image splits as
`X = T + 𝔑𝔏`, `X' = T' + 𝔑𝔏'` (paper: `S₂A₂𝔏 = S₂A₂P_{U₂}𝔏 + 𝔑 Q_proj 𝔏`) with `‖T‖, ‖T'‖ ≤ τ₁`
(the projection terms), `‖𝔑𝔏‖, ‖𝔑𝔏'‖ ≤ c` (the cross factors), `‖𝔏‖, ‖𝔏'‖ ≤ ℓ` and
`‖𝔏ᵀ𝔏'‖ ≤ L₁₁`, then `‖XᵀX'‖ ≤ ‖𝔑‖²(ℓ² + L₁₁)/2 + 2τ₁c + τ₁²`. -/
theorem eb_Eblock {r q a a' : ℕ} (T : Matrix (Fin r) (Fin a) ℝ) (T' : Matrix (Fin r) (Fin a') ℝ)
    (Nm : Matrix (Fin r) (Fin q) ℝ) (L : Matrix (Fin q) (Fin a) ℝ) (L' : Matrix (Fin q) (Fin a') ℝ)
    {ℓ L11 τ₁ cx : ℝ} (hT : opN T ≤ τ₁) (hT' : opN T' ≤ τ₁) (hNL : opN (Nm * L) ≤ cx)
    (hNL' : opN (Nm * L') ≤ cx) (hL : opN L ≤ ℓ) (hL' : opN L' ≤ ℓ) (hLL : opN (Lᵀ * L') ≤ L11) :
    opN ((T + Nm * L)ᵀ * (T' + Nm * L')) ≤ opN Nm ^ 2 * (ℓ ^ 2 + L11) / 2 + 2 * τ₁ * cx + τ₁ ^ 2 := by
  have hτ : 0 ≤ τ₁ := (opN_nonneg T).trans hT
  have e : (T + Nm * L)ᵀ * (T' + Nm * L') =
      (Tᵀ * T' + Tᵀ * (Nm * L')) + ((Nm * L)ᵀ * T' + Lᵀ * (Nmᵀ * Nm) * L') := by
    rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [e]
  have hm : ∀ {p1 p2 p3 : ℕ} (A : Matrix (Fin p2) (Fin p1) ℝ) (B : Matrix (Fin p2) (Fin p3) ℝ)
      {α β : ℝ}, opN A ≤ α → opN B ≤ β → opN (Aᵀ * B) ≤ α * β := by
    intro p1 p2 p3 A B α β hA hB
    refine (opN_mul_le Aᵀ B).trans ?_
    rw [BstLean.Part153.opN_transpose]
    exact mul_le_mul hA hB (opN_nonneg B) ((opN_nonneg A).trans hA)
  have h1 := hm T T' hT hT'
  have h2 := hm T (Nm * L') hT hNL'
  have h3 := hm (Nm * L) T' hNL hT'
  have h4 := eb_polar_opN Nm L L' hL hL' hLL
  refine (BstLean.Part153.opN_add_le' _ _).trans ?_
  have hA := BstLean.Part153.opN_add_le' (Tᵀ * T') (Tᵀ * (Nm * L'))
  have hB := BstLean.Part153.opN_add_le' ((Nm * L)ᵀ * T') (Lᵀ * (Nmᵀ * Nm) * L')
  nlinarith

end BstLean.Part182

open BstLean.Part182 in
#print axioms eb_colsplit
open BstLean.Part182 in
#print axioms eb_rot
open BstLean.Part182 in
#print axioms eb_cond_gordon
open BstLean.Part182 in
#print axioms eb_polar
open BstLean.Part182 in
#print axioms eb_polar_opN
open BstLean.Part182 in
#print axioms eb_Eblock
