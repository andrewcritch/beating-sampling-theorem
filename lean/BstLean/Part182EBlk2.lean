import BstLean.Part182EBlk
import BstLean.Part182Blk
import BstLean.Part182Mask2
import BstLean.Part182OBlk

/-!
# Part 182 (file `EBlk2`): the probabilistic E-block step of Lemma TI (TI-lite, upper singular values)

No proof is left open; no `native_decide` or `axiom` is used.

* `e2_rank_gordon`: row-selected Gordon on a `D`-dimensional subspace (`Uᵀ U = 1`).
* `e2_split_gordon`: the same when the row selection depends only on `A·P` and `P·U = 0`
  (column split `eb_colsplit`, Fubini).
* **`e2_joint`**: under `nuA n`, with measurable choices `P(A₁)` (projection, `P a = a`, `P a' = a'`)
  and `U(A₁)` (orthonormal columns, `P U = 0`):
  `Pr(tr S₂ ≤ K ∧ √t(√K + √D + υ) ≤ opN(S₂·A₂·U)) ≤ e^{−υ²/2}`.
* `e2_pair_eq`: `(J_xP_E)ᵀ(J_{x'}P_E) = (S₂A₂L)ᵀ(S₂A₂L')`, `L = D₁A₁P_E`.
* **`e2_Eblock_det`**: the E-block assembly via `eb_Eblock` with `T = S₂A₂PmL`, `𝔑 = S₂A₂U`,
  `𝔏 = Uᵀ(1 − Pm)L`.
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open BstLean.Part151 (mask measurable_mask)

variable {M k D : ℕ}

/-- **Row-selected Gordon on a `D`-dimensional subspace**: for a fixed `{0,1}` diagonal `d` with
`∑ d ≤ K` and `U` with orthonormal columns (`Uᵀ U = 1`):
`Pr(√v(√K + √D + υ) ≤ opN(diag d · A · U)) ≤ e^{−υ²/2}`. -/
theorem e2_rank_gordon {v : ℝ} (hv : 0 < v) (d : Fin M → ℝ) (hd : ∀ i, d i = 0 ∨ d i = 1)
    (U : Matrix (Fin k) (Fin D) ℝ) (hU : Uᵀ * U = 1) {K υ : ℝ} (hK : ∑ i, d i ≤ K) (hυ : 0 ≤ υ) :
    (gaussMat M k v) {A | √v * (√K + √(D : ℝ) + υ) ≤ opN (Matrix.diagonal d * (A * U))} ≤
      ENNReal.ofReal (exp (-υ ^ 2 / 2)) := by
  have hrot := eb_rot (M := M) (k := k) (K := M) (d := D) hv.le (1 : Matrix (Fin M) (Fin M) ℝ) U
    (by simp) hU
  have hg : Measurable (fun A : Matrix (Fin M) (Fin k) ℝ => (1 : Matrix (Fin M) (Fin M) ℝ)ᵀ * A * U) :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable
  have hS : MeasurableSet {G : Matrix (Fin M) (Fin D) ℝ |
      √v * (√K + √(D : ℝ) + √(2 * (υ ^ 2 / 2))) ≤ opN (Matrix.diagonal d * (G * (1 : Matrix (Fin D) (Fin D) ℝ)))} :=
    measurableSet_le measurable_const
      (opN_continuous.comp (continuous_const.matrix_mul
        (continuous_id.matrix_mul continuous_const))).measurable
  have hυ2 : √(2 * (υ ^ 2 / 2)) = υ := by
    rw [show 2 * (υ ^ 2 / 2) = υ ^ 2 by ring, Real.sqrt_sq hυ]
  have h := bk_rowsel_tail (p := M) (n := D) hv d hd (1 : Matrix (Fin D) (Fin D) ℝ) (by
      refine BstLean.Part153.opN_le_of_bound _ zero_le_one fun w => ?_
      simp) hK (by positivity : (0 : ℝ) ≤ υ ^ 2 / 2)
  rw [← hrot, Measure.map_apply hg hS] at h
  have e : (fun A : Matrix (Fin M) (Fin k) ℝ => (1 : Matrix (Fin M) (Fin M) ℝ)ᵀ * A * U) ⁻¹'
      {G | √v * (√K + √(D : ℝ) + √(2 * (υ ^ 2 / 2))) ≤ opN (Matrix.diagonal d * (G * (1 : Matrix (Fin D) (Fin D) ℝ)))} =
      {A | √v * (√K + √(D : ℝ) + υ) ≤ opN (Matrix.diagonal d * (A * U))} := by
    ext A
    simp only [Set.mem_preimage, Set.mem_setOf_eq, transpose_one, Matrix.one_mul, Matrix.mul_one,
      hυ2]
  rw [e] at h
  rwa [show -(υ ^ 2 / 2) = -υ ^ 2 / 2 by ring] at h

lemma e2_mulU_eq (P : Matrix (Fin k) (Fin k) ℝ) (U : Matrix (Fin k) (Fin D) ℝ) (hPU : P * U = 0)
    (A : Matrix (Fin M) (Fin k) ℝ) : A * (1 - P) * U = A * U := by
  rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hPU, sub_zero]

lemma e2_cont_diag :
    Continuous (fun q : (Fin M → ℝ) × Matrix (Fin M) (Fin D) ℝ => Matrix.diagonal q.1 * q.2) := by
  have h : Continuous (fun f : Fin M → ℝ => Matrix.diagonal f) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.diagonal_apply]
    split_ifs with h
    · subst h; exact continuous_apply i
    · exact continuous_const
  exact (h.comp continuous_fst).matrix_mul continuous_snd

/-- **Conditional Gordon after a column split**: if the `{0,1}` row selection depends only on
`A·P` (`P` an orthogonal projection) and `P·U = 0` (`U` with orthonormal columns), then
`Pr(∑ d ≤ K ∧ √v(√K + √D + υ) ≤ opN(diag d · A · U)) ≤ e^{−υ²/2}`. -/
theorem e2_split_gordon {v : ℝ} (hv : 0 < v) (P : Matrix (Fin k) (Fin k) ℝ) (hPs : Pᵀ = P)
    (hPi : P * P = P) (U : Matrix (Fin k) (Fin D) ℝ) (hU : Uᵀ * U = 1) (hPU : P * U = 0)
    (dF : Matrix (Fin M) (Fin k) ℝ → Fin M → ℝ) (hdF : Measurable dF)
    (hd01 : ∀ B i, dF B i = 0 ∨ dF B i = 1) {K υ : ℝ} (hυ : 0 ≤ υ) :
    (gaussMat M k v) {A | ∑ i, dF (A * P) i ≤ K ∧
      √v * (√K + √(D : ℝ) + υ) ≤ opN (Matrix.diagonal (dF (A * P)) * (A * U))} ≤
      ENNReal.ofReal (exp (-υ ^ 2 / 2)) := by
  classical
  have hPμ : IsProbabilityMeasure (gaussMat M k v) := by unfold gaussMat; infer_instance
  have hg1 : Measurable (fun A : Matrix (Fin M) (Fin k) ℝ => A * P) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hg2 : Measurable (fun A : Matrix (Fin M) (Fin k) ℝ => A * (1 - P)) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hg : Measurable (fun A : Matrix (Fin M) (Fin k) ℝ => (A * P, A * (1 - P))) :=
    hg1.prodMk hg2
  set S : Set (Matrix (Fin M) (Fin k) ℝ × Matrix (Fin M) (Fin k) ℝ) :=
    {q | ∑ i, dF q.1 i ≤ K ∧ √v * (√K + √(D : ℝ) + υ) ≤
      opN (Matrix.diagonal (dF q.1) * (q.2 * U))} with hSd
  have hSm : MeasurableSet S := by
    have h1 : Measurable (fun q : Matrix (Fin M) (Fin k) ℝ × Matrix (Fin M) (Fin k) ℝ =>
        ∑ i, dF q.1 i) :=
      Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).comp (hdF.comp measurable_fst)
    have h2 : Measurable (fun q : Matrix (Fin M) (Fin k) ℝ × Matrix (Fin M) (Fin k) ℝ =>
        opN (Matrix.diagonal (dF q.1) * (q.2 * U))) := by
      have hc : Measurable (fun q : Matrix (Fin M) (Fin k) ℝ × Matrix (Fin M) (Fin k) ℝ =>
          (dF q.1, q.2 * U)) :=
        (hdF.comp measurable_fst).prodMk
          ((continuous_snd.matrix_mul continuous_const).measurable)
      have hco : Measurable (fun q : (Fin M → ℝ) × Matrix (Fin M) (Fin D) ℝ =>
          opN (Matrix.diagonal q.1 * q.2)) :=
        (opN_continuous.comp (e2_cont_diag (M := M) (D := D))).measurable
      have := hco.comp hc
      simpa only [Function.comp_def] using this
    exact (measurableSet_le h1 measurable_const).inter (measurableSet_le measurable_const h2)
  have e : {A : Matrix (Fin M) (Fin k) ℝ | ∑ i, dF (A * P) i ≤ K ∧
      √v * (√K + √(D : ℝ) + υ) ≤ opN (Matrix.diagonal (dF (A * P)) * (A * U))} =
      (fun A => (A * P, A * (1 - P))) ⁻¹' S := by
    ext A
    simp only [hSd, Set.mem_preimage, Set.mem_setOf_eq, e2_mulU_eq P U hPU]
  rw [e, ← Measure.map_apply hg hSm, eb_colsplit v P hPs hPi]
  set μ₁ := (gaussMat M k v).map (fun A => A * P)
  set μ₂ := (gaussMat M k v).map (fun A => A * (1 - P))
  have : IsProbabilityMeasure μ₁ := inferInstance
  have : IsProbabilityMeasure μ₂ := inferInstance
  rw [Measure.prod_apply hSm]
  have hle : ∀ B, μ₂ (Prod.mk B ⁻¹' S) ≤ ENNReal.ofReal (exp (-υ ^ 2 / 2)) := by
    intro B
    by_cases hB : ∑ i, dF B i ≤ K
    · have hT : MeasurableSet {C : Matrix (Fin M) (Fin k) ℝ | √v * (√K + √(D : ℝ) + υ) ≤
          opN (Matrix.diagonal (dF B) * (C * U))} :=
        measurableSet_le measurable_const
          (opN_continuous.comp (continuous_const.matrix_mul
            (continuous_id.matrix_mul continuous_const))).measurable
      have e1 : Prod.mk B ⁻¹' S = {C : Matrix (Fin M) (Fin k) ℝ | √v * (√K + √(D : ℝ) + υ) ≤
          opN (Matrix.diagonal (dF B) * (C * U))} := by
        ext C; simp [hSd, hB]
      rw [e1, Measure.map_apply hg2 hT]
      have e2 : (fun A : Matrix (Fin M) (Fin k) ℝ => A * (1 - P)) ⁻¹'
          {C | √v * (√K + √(D : ℝ) + υ) ≤ opN (Matrix.diagonal (dF B) * (C * U))} =
          {A | √v * (√K + √(D : ℝ) + υ) ≤ opN (Matrix.diagonal (dF B) * (A * U))} := by
        ext A; simp only [Set.mem_preimage, Set.mem_setOf_eq, e2_mulU_eq P U hPU]
      rw [e2]
      exact e2_rank_gordon hv (dF B) (hd01 B) U hU hB hυ
    · have e1 : Prod.mk B ⁻¹' S = ∅ := by
        ext C; simp [hSd, hB]
      rw [e1, measure_empty]; exact bot_le
  calc ∫⁻ B, μ₂ (Prod.mk B ⁻¹' S) ∂μ₁ ≤ ∫⁻ _B, ENNReal.ofReal (exp (-υ ^ 2 / 2)) ∂μ₁ :=
        lintegral_mono hle
    _ = ENNReal.ofReal (exp (-υ ^ 2 / 2)) := by rw [lintegral_const, measure_univ, mul_one]

section joint

variable {n : ℕ}

/-- The second-layer overlap selection `S₂ = diag(mask(A₂a)·mask(A₂a'))` as a vector. -/
noncomputable def e2_sel (x x' : Fin n → ℝ) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) : Fin (mA n) → ℝ :=
  fun i => mask ((A₂ *ᵥ reluV (A₁ *ᵥ x)) i) * mask ((A₂ *ᵥ reluV (A₁ *ᵥ x')) i)

lemma e2_sel01 (x x' : Fin n → ℝ) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (i : Fin (mA n)) :
    e2_sel x x' A₁ A₂ i = 0 ∨ e2_sel x x' A₁ A₂ i = 1 := by
  unfold e2_sel
  rcases bk_mask01 ((A₂ *ᵥ reluV (A₁ *ᵥ x)) i) with h | h <;>
  rcases bk_mask01 ((A₂ *ᵥ reluV (A₁ *ᵥ x')) i) with h' | h' <;> simp [h, h']

lemma e2_sum_sel (x x' : Fin n → ℝ) (θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
    Matrix (Fin (mA n)) (Fin (mA n)) ℝ) : ∑ i, e2_sel x x' θ.1 θ.2 i = cnt2 x x' θ := rfl

/-- **The E-block Gordon tail under the joint Agent distribution** (TI-lite, second layer): for
measurable choices `P(A₁)` of an orthogonal projection with `P a = a`, `P a' = a'`
(`a = ReLU(A₁x)`, `a' = ReLU(A₁x')`, so `range P ⊇ U₂`) and `U(A₁)` with orthonormal columns and
`P U = 0` (`D` columns, an orthonormal basis of a space containing `Q·(range 𝔏 + range 𝔏')`):
`Pr_{nuA}(tr S₂ ≤ K ∧ √t(√K + √D + υ) ≤ opN(S₂·A₂·U)) ≤ e^{−υ²/2}`, `t = 2/m`. -/
theorem e2_joint (x x' : Fin n → ℝ)
    (Pf : Matrix (Fin (mA n)) (Fin n) ℝ → Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (Uf : Matrix (Fin (mA n)) (Fin n) ℝ → Matrix (Fin (mA n)) (Fin D) ℝ)
    (hUm : Measurable Uf)
    (hPs : ∀ A, (Pf A)ᵀ = Pf A) (hPi : ∀ A, Pf A * Pf A = Pf A)
    (hU : ∀ A, (Uf A)ᵀ * Uf A = 1) (hPU : ∀ A, Pf A * Uf A = 0)
    (ha : ∀ A, Pf A *ᵥ reluV (A *ᵥ x) = reluV (A *ᵥ x))
    (ha' : ∀ A, Pf A *ᵥ reluV (A *ᵥ x') = reluV (A *ᵥ x'))
    {K υ : ℝ} (hυ : 0 ≤ υ) (hm : 0 < mA n) :
    (BstLean.Part153.nuA n).real {θ | cnt2 x x' θ ≤ K ∧
      √(2 / ((mA n : ℕ) : ℝ)) * (√K + √(D : ℝ) + υ) ≤
        opN (Matrix.diagonal (e2_sel x x' θ.1 θ.2) * (θ.2 * Uf θ.1))} ≤ exp (-υ ^ 2 / 2) := by
  classical
  have hP1 : IsProbabilityMeasure (gaussMat (mA n) n (2 / (n : ℝ))) := by
    unfold gaussMat; infer_instance
  have hP2 : IsProbabilityMeasure (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) := by
    unfold gaussMat; infer_instance
  have hv : (0 : ℝ) < 2 / ((mA n : ℕ) : ℝ) := by
    have : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by exact_mod_cast hm
    positivity
  set S := {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      cnt2 x x' θ ≤ K ∧ √(2 / ((mA n : ℕ) : ℝ)) * (√K + √(D : ℝ) + υ) ≤
        opN (Matrix.diagonal (e2_sel x x' θ.1 θ.2) * (θ.2 * Uf θ.1))} with hSd
  have hsel : Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ => e2_sel x x' θ.1 θ.2) := by
    refine measurable_pi_iff.mpr fun i => ?_
    have h1 : Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
        Matrix (Fin (mA n)) (Fin (mA n)) ℝ => (θ.2 *ᵥ reluV (θ.1 *ᵥ x)) i) := by
      unfold reluV relu; simp only [Matrix.mulVec, dotProduct]; fun_prop
    have h2 : Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
        Matrix (Fin (mA n)) (Fin (mA n)) ℝ => (θ.2 *ᵥ reluV (θ.1 *ᵥ x')) i) := by
      unfold reluV relu; simp only [Matrix.mulVec, dotProduct]; fun_prop
    exact (measurable_mask.comp h1).mul (measurable_mask.comp h2)
  have hSm : MeasurableSet S := by
    have hc : Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
        Matrix (Fin (mA n)) (Fin (mA n)) ℝ => (e2_sel x x' θ.1 θ.2, θ.2 * Uf θ.1)) :=
      hsel.prodMk ((continuous_fst.matrix_mul continuous_snd).measurable.comp
        (measurable_snd.prodMk (hUm.comp measurable_fst)))
    have hco : Measurable (fun q : (Fin (mA n) → ℝ) × Matrix (Fin (mA n)) (Fin D) ℝ =>
        opN (Matrix.diagonal q.1 * q.2)) :=
      (opN_continuous.comp (e2_cont_diag (M := mA n) (D := D))).measurable
    have h2 := hco.comp hc
    exact (measurableSet_le (measurable_cnt2 x x') measurable_const).inter
      (measurableSet_le measurable_const (by simpa only [Function.comp_def] using h2))
  have hB : 0 ≤ exp (-υ ^ 2 / 2) := (exp_pos _).le
  rw [Measure.real]
  unfold BstLean.Part153.nuA
  rw [Measure.prod_apply hSm]
  have hle : ∀ A₁, (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) (Prod.mk A₁ ⁻¹' S) ≤
      ENNReal.ofReal (exp (-υ ^ 2 / 2)) := by
    intro A₁
    set dF : Matrix (Fin (mA n)) (Fin (mA n)) ℝ → Fin (mA n) → ℝ :=
      fun B i => mask ((B *ᵥ reluV (A₁ *ᵥ x)) i) * mask ((B *ᵥ reluV (A₁ *ᵥ x')) i) with hdF
    have hdFm : Measurable dF := by
      refine measurable_pi_iff.mpr fun i => ?_
      have h1 : Measurable (fun B : Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
          (B *ᵥ reluV (A₁ *ᵥ x)) i) := by
        simp only [Matrix.mulVec, dotProduct]; fun_prop
      have h2 : Measurable (fun B : Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
          (B *ᵥ reluV (A₁ *ᵥ x')) i) := by
        simp only [Matrix.mulVec, dotProduct]; fun_prop
      exact (measurable_mask.comp h1).mul (measurable_mask.comp h2)
    have hd01 : ∀ B i, dF B i = 0 ∨ dF B i = 1 := by
      intro B i
      simp only [hdF]
      rcases bk_mask01 ((B *ᵥ reluV (A₁ *ᵥ x)) i) with h | h <;>
      rcases bk_mask01 ((B *ᵥ reluV (A₁ *ᵥ x')) i) with h' | h' <;> simp [h, h']
    have hdP : ∀ A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ, dF (A₂ * Pf A₁) = e2_sel x x' A₁ A₂ := by
      intro A₂
      funext i
      simp only [hdF, e2_sel, ← Matrix.mulVec_mulVec, ha A₁, ha' A₁]
    have h := e2_split_gordon hv (Pf A₁) (hPs A₁) (hPi A₁) (Uf A₁) (hU A₁) (hPU A₁) dF hdFm hd01
      (K := K) hυ
    have e : Prod.mk A₁ ⁻¹' S = {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
        ∑ i, dF (A₂ * Pf A₁) i ≤ K ∧ √(2 / ((mA n : ℕ) : ℝ)) * (√K + √(D : ℝ) + υ) ≤
          opN (Matrix.diagonal (dF (A₂ * Pf A₁)) * (A₂ * Uf A₁))} := by
      ext A₂
      simp only [hSd, Set.mem_preimage, Set.mem_setOf_eq, hdP]
      rfl
    rw [e]; exact h
  calc (∫⁻ A₁, (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) (Prod.mk A₁ ⁻¹' S)
        ∂gaussMat (mA n) n (2 / (n : ℝ))).toReal
      ≤ (∫⁻ _A₁, ENNReal.ofReal (exp (-υ ^ 2 / 2)) ∂gaussMat (mA n) n (2 / (n : ℝ))).toReal :=
        ENNReal.toReal_mono (by rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.ofReal_ne_top)
          (lintegral_mono hle)
    _ = exp (-υ ^ 2 / 2) := by
        rw [lintegral_const, measure_univ, mul_one, ENNReal.toReal_ofReal hB]

end joint

section det

variable {n D : ℕ}

/-- The pair Jacobian product as a product of the row-selected second layer. -/
lemma e2_pair_eq (x x' : Fin n → ℝ) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (PE : Matrix (Fin n) (Fin n) ℝ) :
    (BstLean.Part151.jac A₁ A₂ x * PE)ᵀ * (BstLean.Part151.jac A₁ A₂ x' * PE) =
      (Matrix.diagonal (e2_sel x x' A₁ A₂) * A₂ * (obD (A₁ *ᵥ x) * A₁ * PE))ᵀ *
        (Matrix.diagonal (e2_sel x x' A₁ A₂) * A₂ * (obD (A₁ *ᵥ x') * A₁ * PE)) := by
  rw [ob_jac_eq, ob_jac_eq]
  set D2 := obD (A₂ *ᵥ reluV (A₁ *ᵥ x))
  set D2' := obD (A₂ *ᵥ reluV (A₁ *ᵥ x'))
  have hD2 : D2ᵀ = D2 := by simp [D2, obD]
  have hSt : (Matrix.diagonal (e2_sel x x' A₁ A₂))ᵀ * Matrix.diagonal (e2_sel x x' A₁ A₂) =
      D2ᵀ * D2' := by
    rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, hD2]
    simp only [D2, D2', obD, Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    simp only [e2_sel]
    rcases bk_mask01 ((A₂ *ᵥ reluV (A₁ *ᵥ x)) i) with h | h <;>
    rcases bk_mask01 ((A₂ *ᵥ reluV (A₁ *ᵥ x')) i) with h' | h' <;> simp [h, h']
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((Matrix.diagonal (e2_sel x x' A₁ A₂))ᵀ), hSt]
  simp only [Matrix.mul_assoc]

/-- **E block, deterministic assembly in the TI-lite form**: with `L = D₁A₁P_E`, `L' = D₁'A₁P_E`,
`S₂ = diag(e2_sel)`, a projection-like `Pm` (onto `U₂`) and `U` with `U Uᵀ (1 − Pm) L = (1 − Pm) L`
(and the same for `L'`): writing `T = S₂A₂PmL`, `𝔑 = S₂A₂U`, `𝔏 = Uᵀ(1 − Pm)L`,
`opN((J_xP_E)ᵀ(J_{x'}P_E)) ≤ opN(𝔑)²(ℓ² + L₁₁)/2 + 2τ₁·cx + τ₁²` under the norm hypotheses. -/
theorem e2_Eblock_det (x x' : Fin n → ℝ) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (PE : Matrix (Fin n) (Fin n) ℝ)
    (Pm : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (U : Matrix (Fin (mA n)) (Fin D) ℝ)
    (hUL : U * Uᵀ * ((1 - Pm) * (obD (A₁ *ᵥ x) * A₁ * PE)) = (1 - Pm) * (obD (A₁ *ᵥ x) * A₁ * PE))
    (hUL' : U * Uᵀ * ((1 - Pm) * (obD (A₁ *ᵥ x') * A₁ * PE)) =
      (1 - Pm) * (obD (A₁ *ᵥ x') * A₁ * PE))
    {ℓ L11 τ₁ cx : ℝ}
    (hT : opN (Matrix.diagonal (e2_sel x x' A₁ A₂) * A₂ * (Pm * (obD (A₁ *ᵥ x) * A₁ * PE))) ≤ τ₁)
    (hT' : opN (Matrix.diagonal (e2_sel x x' A₁ A₂) * A₂ * (Pm * (obD (A₁ *ᵥ x') * A₁ * PE))) ≤ τ₁)
    (hNL : opN ((Matrix.diagonal (e2_sel x x' A₁ A₂) * A₂ * U) *
      (Uᵀ * ((1 - Pm) * (obD (A₁ *ᵥ x) * A₁ * PE)))) ≤ cx)
    (hNL' : opN ((Matrix.diagonal (e2_sel x x' A₁ A₂) * A₂ * U) *
      (Uᵀ * ((1 - Pm) * (obD (A₁ *ᵥ x') * A₁ * PE)))) ≤ cx)
    (hL : opN (Uᵀ * ((1 - Pm) * (obD (A₁ *ᵥ x) * A₁ * PE))) ≤ ℓ)
    (hL' : opN (Uᵀ * ((1 - Pm) * (obD (A₁ *ᵥ x') * A₁ * PE))) ≤ ℓ)
    (hLL : opN ((Uᵀ * ((1 - Pm) * (obD (A₁ *ᵥ x) * A₁ * PE)))ᵀ *
      (Uᵀ * ((1 - Pm) * (obD (A₁ *ᵥ x') * A₁ * PE)))) ≤ L11) :
    opN ((BstLean.Part151.jac A₁ A₂ x * PE)ᵀ * (BstLean.Part151.jac A₁ A₂ x' * PE)) ≤
      opN (Matrix.diagonal (e2_sel x x' A₁ A₂) * A₂ * U) ^ 2 * (ℓ ^ 2 + L11) / 2 +
        2 * τ₁ * cx + τ₁ ^ 2 := by
  set S := Matrix.diagonal (e2_sel x x' A₁ A₂)
  set L := obD (A₁ *ᵥ x) * A₁ * PE
  set L' := obD (A₁ *ᵥ x') * A₁ * PE
  have hsplit : ∀ L₀ : Matrix (Fin (mA n)) (Fin n) ℝ, U * Uᵀ * ((1 - Pm) * L₀) = (1 - Pm) * L₀ →
      S * A₂ * L₀ = S * A₂ * (Pm * L₀) + (S * A₂ * U) * (Uᵀ * ((1 - Pm) * L₀)) := by
    intro L₀ h
    have e1 : (S * A₂ * U) * (Uᵀ * ((1 - Pm) * L₀)) = S * A₂ * ((1 - Pm) * L₀) := by
      have e0 : (S * A₂ * U) * (Uᵀ * ((1 - Pm) * L₀)) = S * A₂ * (U * Uᵀ * ((1 - Pm) * L₀)) := by
        simp only [Matrix.mul_assoc]
      rw [e0, h]
    rw [e1, ← Matrix.mul_add, ← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
  rw [e2_pair_eq, hsplit L hUL, hsplit L' hUL']
  exact eb_Eblock _ _ _ _ _ hT hT' hNL hNL' hL hL' hLL

end det

end BstLean.Part182

open BstLean.Part182 in
#print axioms e2_rank_gordon
open BstLean.Part182 in
#print axioms e2_split_gordon
open BstLean.Part182 in
#print axioms e2_joint
open BstLean.Part182 in
#print axioms e2_Eblock_det
