import BstLean.Part153PPs
import BstLean.Part182MS

/-!
# Part 182 (file `Blk`): first-layer operator bounds of Lemma TI on `E = span(x, x')^⊥`

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `proofs/option-n/theorem7-04-frame-numerator.tex`, Lemma `t7:p04:ti`, the three tails
"`‖D₁B₁‖, ‖D₁'B₁‖ ≤ ℓ`; `‖D₁D₁'B₁‖² ≤ L₁₁`". Here `B₁ = A₁ P_E` (`P_E = PEm x x'`, file `MS`),
`D₁ = diag(mask(A₁x))`, `D₁' = diag(mask(A₁x'))`, `A₁ ~ gaussMat m n (2/n)`.

Route: the decomposition of a Gaussian matrix along a unit vector (Part 153 `gaussMat_decomp`),
used along `x` and then along `e = eTan x x'`; the block `A₁ P_E` is then an independent Gaussian
matrix times `P_E`, the masks are fixed, and Gordon's tail (Part 152 `opN_tail`) applies to the
selected rows (Part 153 `opN_diag_le_submatrix`, `gaussMat_submatrix_rows`).

* `bk_rowsel_tail`: fixed `{0,1}` diagonal with trace `≤ K`, `‖P‖ ≤ 1`:
  `Pr(√v(√K + √n + √(2τ)) ≤ ‖diag(d) M P‖) ≤ e^{−τ}`.
* `blk_single`, `blk_double`: the conditional statements for general `P`.
* **`blk_ell`, `blk_ell'`, `blk_L11`**: the paper's tails with `γ = 2/n`, `υ = √(2τ)`, any `K`
  (in the paper `K = K₁⁺` resp. `K₁₁⁺`, whose own tails are in file `Mask`). The event uses
  `≤` (a superset of the paper's strict event).
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open BstLean.Part151 (mask measurable_mask)
open BstLean.Part153 (projT opN_mul_le opN_projT_le opN_diag_le_submatrix gaussMat_submatrix_rows
  measurable_submatrix_rows gaussMat_decomp mask_mul_pos)

variable {m n p : ℕ}

lemma bk_mask01 (t : ℝ) : mask t = 0 ∨ mask t = 1 := by
  unfold mask; split_ifs <;> simp

/-- **Conditional Gordon step**: a fixed `{0,1}` diagonal with trace `≤ K`, a Gaussian `p × n`
matrix `M` and a matrix `P` with `opN P ≤ 1`:
`Pr(√v(√K + √n + √(2τ)) ≤ opN(diag d · M · P)) ≤ e^{−τ}`. -/
theorem bk_rowsel_tail {v : ℝ} (hv : 0 < v) (d : Fin p → ℝ) (hd : ∀ i, d i = 0 ∨ d i = 1)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : opN P ≤ 1) {K τ : ℝ} (hK : ∑ i, d i ≤ K)
    (hτ : 0 ≤ τ) :
    (gaussMat p n v) {M | √v * (√K + √(n : ℝ) + √(2 * τ)) ≤
      opN (Matrix.diagonal d * (M * P))} ≤ ENNReal.ofReal (exp (-τ)) := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin p), ∀ i, i ∈ S ↔ d i = 1 :=
    ⟨Finset.univ.filter fun i => d i = 1, by simp⟩
  have hd' : ∀ i, d i = if i ∈ S then 1 else 0 := by
    intro i
    rcases hd i with h | h
    · have : i ∉ S := by rw [hS, h]; norm_num
      simp [this, h]
    · simp [(hS i).2 h, h]
  have hsum : ∑ i, d i = (S.card : ℝ) := by
    simp only [hd']
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    simp
  obtain ⟨K', hK'⟩ : ∃ K', S.card = K' := ⟨_, rfl⟩
  rw [hsum, hK'] at hK
  have hsv : 0 < √v := Real.sqrt_pos.2 hv
  set σ := S.orderEmbOfFin hK' with hσ
  have hsub : {M : Matrix (Fin p) (Fin n) ℝ | √v * (√K + √(n : ℝ) + √(2 * τ)) ≤
      opN (Matrix.diagonal d * (M * P))} ⊆
      (fun A : Matrix (Fin p) (Fin n) ℝ => A.submatrix σ id) ⁻¹'
        {M' | √v * (√(K' : ℝ) + √(n : ℝ)) + √v * √(2 * τ) ≤ opN M'} := by
    intro M hM
    simp only [mem_setOf_eq, mem_preimage] at hM ⊢
    have h1 : opN (Matrix.diagonal d * (M * P)) ≤ opN (Matrix.diagonal d * M) := by
      rw [← Matrix.mul_assoc]
      refine (opN_mul_le _ _).trans ?_
      calc opN (Matrix.diagonal d * M) * opN P ≤ opN (Matrix.diagonal d * M) * 1 :=
            mul_le_mul_of_nonneg_left hP (opN_nonneg _)
        _ = _ := mul_one _
    have h2 := opN_diag_le_submatrix d S hd' hK' M
    have h3 : √(K' : ℝ) ≤ √K := Real.sqrt_le_sqrt hK
    have h4 : √v * (√(K' : ℝ) + √(n : ℝ)) + √v * √(2 * τ) ≤
        √v * (√K + √(n : ℝ) + √(2 * τ)) := by nlinarith
    linarith
  refine (measure_mono hsub).trans ?_
  have hS' : MeasurableSet {M' : Matrix (Fin K') (Fin n) ℝ |
      √v * (√(K' : ℝ) + √(n : ℝ)) + √v * √(2 * τ) ≤ opN M'} :=
    measurableSet_le measurable_const opN_continuous.measurable
  rw [← Measure.map_apply (measurable_submatrix_rows σ) hS',
    gaussMat_submatrix_rows v σ σ.injective]
  have ht := opN_tail (p := K') (q := n) hv.le (t := √v * √(2 * τ)) (by positivity)
  have e : -(√v * √(2 * τ)) ^ 2 / (2 * v) = -τ := by
    rw [mul_pow, Real.sq_sqrt hv.le, Real.sq_sqrt (by linarith)]
    field_simp
  rw [e] at ht
  have hfin : IsFiniteMeasure (gaussMat K' n v) := by
    unfold gaussMat; infer_instance
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal ht

lemma bk_lint_ind {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    {S : Set β} (hS : MeasurableSet S) {f : α → β} (hf : Measurable f) :
    ∫⁻ a, S.indicator 1 (f a) ∂μ = μ (f ⁻¹' S) := by
  rw [← lintegral_indicator_one (hf hS)]
  rfl

lemma bk_meas_set (P : Matrix (Fin n) (Fin n) ℝ) (b K : ℝ)
    (dd : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ → Fin m → ℝ) (hdd : Measurable dd) :
    MeasurableSet {q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ |
      ∑ i, dd q i ≤ K ∧ b ≤ opN (Matrix.diagonal (dd q) * (q.2 * P))} := by
  have h1 : Measurable (fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ => ∑ i, dd q i) :=
    Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).comp hdd
  have h2 : Measurable (fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ =>
      Matrix.diagonal (dd q) * (q.2 * P)) := by
    refine measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun l => ?_
    have e : (fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ =>
        (Matrix.diagonal (dd q) * (q.2 * P)) j l) =
        fun q => dd q j * ∑ k, q.2 j k * P k l := by
      funext q; rw [Matrix.diagonal_mul, Matrix.mul_apply]
    show Measurable (fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ =>
        (Matrix.diagonal (dd q) * (q.2 * P)) j l)
    rw [e]
    refine ((measurable_pi_apply j).comp hdd).mul ?_
    refine Finset.measurable_sum Finset.univ fun k _ => ?_
    have h1 : Measurable fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ => q.2 j k :=
      (measurable_pi_apply k).comp ((measurable_pi_apply j).comp measurable_snd)
    exact h1.mul measurable_const
  exact (measurableSet_le h1 measurable_const).inter
    (measurableSet_le measurable_const (opN_continuous.measurable.comp h2))

/-- **The first-layer bound `‖D₁ B‖`** for one input: for a unit `x` and a matrix `P` with
`Π_x P = P` and `‖P‖ ≤ 1` (e.g. `P = P_E`), the Gaussian `m × n` matrix `A` (variance `v`)
satisfies `Pr(tr D ≤ K ∧ √v(√K + √n + √(2τ)) ≤ ‖D A P‖) ≤ e^{−τ}`, `D = diag(mask(A x))`. -/
theorem blk_single {v : ℝ} (hv : 0 < v) {x : Fin n → ℝ} (hx : normSq x = 1)
    (P : Matrix (Fin n) (Fin n) ℝ) (hPx : projT x * P = P) (hP : opN P ≤ 1) {K τ : ℝ}
    (hτ : 0 ≤ τ) :
    (gaussMat m n v) {A | ∑ i, mask ((A *ᵥ x) i) ≤ K ∧ √v * (√K + √(n : ℝ) + √(2 * τ)) ≤
      opN (Matrix.diagonal (fun i => mask ((A *ᵥ x) i)) * (A * P))} ≤
      ENNReal.ofReal (exp (-τ)) := by
  set b := √v * (√K + √(n : ℝ) + √(2 * τ)) with hb
  have hdd : Measurable (fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ => fun i => mask (q.1 i)) :=
    measurable_pi_iff.mpr fun i => measurable_mask.comp ((measurable_pi_apply i).comp measurable_fst)
  set S2 := {q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ |
      ∑ i, (fun i => mask (q.1 i)) i ≤ K ∧
        b ≤ opN (Matrix.diagonal (fun i => mask (q.1 i)) * (q.2 * P))} with hS2
  have hS2m : MeasurableSet S2 := bk_meas_set P b K (fun q i => mask (q.1 i)) hdd
  have hf : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => (A *ᵥ x, A * projT x)) :=
    (continuous_id.matrix_mulVec continuous_const).measurable.prodMk
      (BstLean.Part153.measurable_mul_const _)
  have hset : {A : Matrix (Fin m) (Fin n) ℝ | ∑ i, mask ((A *ᵥ x) i) ≤ K ∧ b ≤
      opN (Matrix.diagonal (fun i => mask ((A *ᵥ x) i)) * (A * P))} =
      (fun A : Matrix (Fin m) (Fin n) ℝ => (A *ᵥ x, A * projT x)) ⁻¹' S2 := by
    ext A
    simp only [mem_setOf_eq, mem_preimage, hS2, Matrix.mul_assoc, hPx]
  rw [hset, ← bk_lint_ind _ hS2m hf,
    gaussMat_decomp hx hv.le ((measurable_one.indicator hS2m))]
  have hsv : 0 < √v := Real.sqrt_pos.2 hv
  have inner : ∀ g : Fin m → ℝ, ∫⁻ M, S2.indicator 1 (√v • g, M * projT x) ∂gaussMat m n v ≤
      ENNReal.ofReal (exp (-τ)) := by
    intro g
    have hm : Measurable (fun M : Matrix (Fin m) (Fin n) ℝ => (√v • g, M * projT x)) :=
      measurable_const.prodMk (BstLean.Part153.measurable_mul_const _)
    rw [bk_lint_ind _ hS2m hm]
    have hmk : (fun i => mask ((√v • g) i)) = fun i => mask (g i) := by
      funext i; rw [Pi.smul_apply, smul_eq_mul, mask_mul_pos hsv]
    by_cases hK : ∑ i, mask (g i) ≤ K
    · refine (measure_mono ?_).trans (bk_rowsel_tail hv (fun i => mask (g i))
        (fun i => bk_mask01 _) P hP hK hτ)
      intro M hM
      simp only [mem_preimage, hS2, mem_setOf_eq, hmk, Matrix.mul_assoc, hPx] at hM
      exact hM.2
    · have e : (fun M : Matrix (Fin m) (Fin n) ℝ => (√v • g, M * projT x)) ⁻¹' S2 = ∅ := by
        ext M
        simp only [mem_preimage, hS2, mem_setOf_eq, hmk, mem_empty_iff_false, iff_false, not_and]
        intro h; exact absurd h hK
      rw [e, measure_empty]; exact bot_le
  have hP1 : IsProbabilityMeasure (stdGauss (Fin m)) := by unfold stdGauss; infer_instance
  calc ∫⁻ g, ∫⁻ M, S2.indicator 1 (√v • g, M * projT x) ∂gaussMat m n v ∂stdGauss (Fin m)
      ≤ ∫⁻ _g, ENNReal.ofReal (exp (-τ)) ∂stdGauss (Fin m) := lintegral_mono inner
    _ = ENNReal.ofReal (exp (-τ)) := by rw [lintegral_const, measure_univ, mul_one]

lemma bk_projT_mulVec_orth {x e : Fin n → ℝ} (hxe : x ⬝ᵥ e = 0) : projT x *ᵥ e = e := by
  rw [BstLean.Part153.projT_mulVec, hxe, zero_smul, sub_zero]

lemma bk_mul_projT_mulVec {x e : Fin n → ℝ} (hxe : x ⬝ᵥ e = 0) (M : Matrix (Fin m) (Fin n) ℝ) :
    (M * projT x) *ᵥ e = M *ᵥ e := by
  rw [← Matrix.mulVec_mulVec, bk_projT_mulVec_orth hxe]

/-- **The first-layer bound `‖D₁ D₁' B‖`** for a pair of inputs: `x`, `e` orthonormal,
`x' = c x + s e`, `P` with `Π_x P = P`, `Π_e P = P`, `‖P‖ ≤ 1` (e.g. `P = P_E`); `A` a Gaussian
`m × n` matrix (variance `v`), `d_i = mask((A x)_i)·mask((A x')_i)`:
`Pr(∑ d ≤ K ∧ √v(√K + √n + √(2τ)) ≤ ‖diag(d) A P‖) ≤ e^{−τ}`. -/
theorem blk_double {v : ℝ} (hv : 0 < v) {x e : Fin n → ℝ} (hx : normSq x = 1)
    (he : normSq e = 1) (hxe : x ⬝ᵥ e = 0) (c s : ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (hPx : projT x * P = P) (hPe : projT e * P = P)
    (hP : opN P ≤ 1) {K τ : ℝ} (hτ : 0 ≤ τ) :
    (gaussMat m n v) {A | ∑ i, mask ((A *ᵥ x) i) * mask ((A *ᵥ (c • x + s • e)) i) ≤ K ∧
      √v * (√K + √(n : ℝ) + √(2 * τ)) ≤ opN (Matrix.diagonal
        (fun i => mask ((A *ᵥ x) i) * mask ((A *ᵥ (c • x + s • e)) i)) * (A * P))} ≤
      ENNReal.ofReal (exp (-τ)) := by
  set b := √v * (√K + √(n : ℝ) + √(2 * τ)) with hb
  have hsv : 0 < √v := Real.sqrt_pos.2 hv
  -- first decomposition, along `x`
  set dd₁ : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ → Fin m → ℝ :=
    fun q i => mask (q.1 i) * mask ((c • q.1 + s • (q.2 *ᵥ e)) i) with hdd₁
  have hdd₁m : Measurable dd₁ := by
    refine measurable_pi_iff.mpr fun i => ?_
    have h1 : Measurable fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ =>
        (c • q.1 + s • (q.2 *ᵥ e)) i :=
      (measurable_pi_apply i).comp ((measurable_fst.const_smul c).add
        (((continuous_id.matrix_mulVec continuous_const).measurable.comp measurable_snd).const_smul s))
    exact (measurable_mask.comp ((measurable_pi_apply i).comp measurable_fst)).mul
      (measurable_mask.comp h1)
  set S2 := {q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ |
      ∑ i, dd₁ q i ≤ K ∧ b ≤ opN (Matrix.diagonal (dd₁ q) * (q.2 * P))} with hS2
  have hS2m : MeasurableSet S2 := bk_meas_set P b K dd₁ hdd₁m
  have hf : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => (A *ᵥ x, A * projT x)) :=
    (continuous_id.matrix_mulVec continuous_const).measurable.prodMk
      (BstLean.Part153.measurable_mul_const _)
  have hAx' : ∀ A : Matrix (Fin m) (Fin n) ℝ,
      A *ᵥ (c • x + s • e) = c • (A *ᵥ x) + s • ((A * projT x) *ᵥ e) := by
    intro A
    rw [bk_mul_projT_mulVec hxe, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  have hset : {A : Matrix (Fin m) (Fin n) ℝ |
      ∑ i, mask ((A *ᵥ x) i) * mask ((A *ᵥ (c • x + s • e)) i) ≤ K ∧ b ≤ opN (Matrix.diagonal
        (fun i => mask ((A *ᵥ x) i) * mask ((A *ᵥ (c • x + s • e)) i)) * (A * P))} =
      (fun A : Matrix (Fin m) (Fin n) ℝ => (A *ᵥ x, A * projT x)) ⁻¹' S2 := by
    ext A
    simp only [mem_setOf_eq, mem_preimage, hS2, hdd₁, Matrix.mul_assoc, hPx, hAx']
  rw [hset, ← bk_lint_ind _ hS2m hf, gaussMat_decomp hx hv.le (measurable_one.indicator hS2m)]
  -- the inner integral, for a fixed `g`
  have inner : ∀ g : Fin m → ℝ, ∫⁻ M, S2.indicator 1 (√v • g, M * projT x) ∂gaussMat m n v ≤
      ENNReal.ofReal (exp (-τ)) := by
    intro g
    set a := √v • g with ha
    have hm : Measurable (fun M : Matrix (Fin m) (Fin n) ℝ => (a, M * projT x)) :=
      measurable_const.prodMk (BstLean.Part153.measurable_mul_const _)
    rw [bk_lint_ind _ hS2m hm]
    -- second decomposition, along `e`
    set dd₂ : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ → Fin m → ℝ :=
      fun q i => mask (a i) * mask ((c • a + s • q.1) i) with hdd₂
    have hdd₂m : Measurable dd₂ := by
      refine measurable_pi_iff.mpr fun i => ?_
      have h1 : Measurable fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ => (c • a + s • q.1) i :=
        (measurable_pi_apply i).comp (measurable_const.add (measurable_fst.const_smul s))
      exact measurable_const.mul (measurable_mask.comp h1)
    set T := {q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ |
        ∑ i, dd₂ q i ≤ K ∧ b ≤ opN (Matrix.diagonal (dd₂ q) * (q.2 * P))} with hT
    have hTm : MeasurableSet T := bk_meas_set P b K dd₂ hdd₂m
    have hf₂ : Measurable (fun M : Matrix (Fin m) (Fin n) ℝ => (M *ᵥ e, M * projT e)) :=
      (continuous_id.matrix_mulVec continuous_const).measurable.prodMk
        (BstLean.Part153.measurable_mul_const _)
    have hset2 : (fun M : Matrix (Fin m) (Fin n) ℝ => (a, M * projT x)) ⁻¹' S2 =
        (fun M : Matrix (Fin m) (Fin n) ℝ => (M *ᵥ e, M * projT e)) ⁻¹' T := by
      ext M
      simp only [mem_preimage, hS2, hT, mem_setOf_eq, hdd₁, hdd₂, bk_mul_projT_mulVec hxe,
        Matrix.mul_assoc, hPx, hPe]
    rw [hset2, ← bk_lint_ind _ hTm hf₂, gaussMat_decomp he hv.le (measurable_one.indicator hTm)]
    have inner2 : ∀ h : Fin m → ℝ, ∫⁻ M', T.indicator 1 (√v • h, M' * projT e)
        ∂gaussMat m n v ≤ ENNReal.ofReal (exp (-τ)) := by
      intro h
      have hm' : Measurable (fun M' : Matrix (Fin m) (Fin n) ℝ => (√v • h, M' * projT e)) :=
        measurable_const.prodMk (BstLean.Part153.measurable_mul_const _)
      rw [bk_lint_ind _ hTm hm']
      set d : Fin m → ℝ := fun i => mask (a i) * mask ((c • a + s • (√v • h)) i) with hd
      have hd01 : ∀ i, d i = 0 ∨ d i = 1 := by
        intro i
        show mask (a i) * mask ((c • a + s • (√v • h)) i) = 0 ∨
          mask (a i) * mask ((c • a + s • (√v • h)) i) = 1
        rcases bk_mask01 (a i) with h1 | h1 <;> rcases bk_mask01 ((c • a + s • (√v • h)) i) with
          h2 | h2 <;> rw [h1, h2] <;> norm_num
      by_cases hK : ∑ i, d i ≤ K
      · refine (measure_mono ?_).trans (bk_rowsel_tail hv d hd01 P hP hK hτ)
        intro M' hM'
        simp only [mem_preimage, hT, mem_setOf_eq, hdd₂, Matrix.mul_assoc, hPe] at hM'
        exact hM'.2
      · have e0 : (fun M' : Matrix (Fin m) (Fin n) ℝ => (√v • h, M' * projT e)) ⁻¹' T = ∅ := by
          ext M'
          simp only [mem_preimage, hT, mem_setOf_eq, hdd₂, mem_empty_iff_false, iff_false,
            not_and]
          intro h'; exact absurd h' hK
        rw [e0, measure_empty]; exact bot_le
    have hP1 : IsProbabilityMeasure (stdGauss (Fin m)) := by unfold stdGauss; infer_instance
    calc ∫⁻ h, ∫⁻ M', T.indicator 1 (√v • h, M' * projT e) ∂gaussMat m n v ∂stdGauss (Fin m)
        ≤ ∫⁻ _h, ENNReal.ofReal (exp (-τ)) ∂stdGauss (Fin m) := lintegral_mono inner2
      _ = ENNReal.ofReal (exp (-τ)) := by rw [lintegral_const, measure_univ, mul_one]
  have hP1 : IsProbabilityMeasure (stdGauss (Fin m)) := by unfold stdGauss; infer_instance
  calc ∫⁻ g, ∫⁻ M, S2.indicator 1 (√v • g, M * projT x) ∂gaussMat m n v ∂stdGauss (Fin m)
      ≤ ∫⁻ _g, ENNReal.ofReal (exp (-τ)) ∂stdGauss (Fin m) := lintegral_mono inner
    _ = ENNReal.ofReal (exp (-τ)) := by rw [lintegral_const, measure_univ, mul_one]

/-! ## The instance `P = P_E` for a pair of unit inputs -/

lemma bk_projT_PEm {x x' y : Fin n → ℝ} (hy : ∀ w, y ⬝ᵥ (PEm x x' *ᵥ w) = 0) :
    projT y * PEm x x' = PEm x x' := by
  classical
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [← Matrix.mulVec_mulVec, BstLean.Part153.projT_mulVec, hy, zero_smul, sub_zero]

section pair
variable {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
  (hc : (x ⬝ᵥ x') ^ 2 < 1)
include hx hx' hc

lemma bk_dot_PEm (w : Fin n → ℝ) :
    x ⬝ᵥ (PEm x x' *ᵥ w) = 0 ∧ eTan x x' ⬝ᵥ (PEm x x' *ᵥ w) = 0 := by
  have h1 := eTan_dot_x hx hx' hc
  have h2 := eTan_dot_self hx hx' hc
  have hxx : x ⬝ᵥ x = 1 := by rw [ms_dot_self, hx]
  rw [PEm_mulVec]
  constructor
  · simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, hxx, dotProduct_comm x (eTan x x'),
      h1]
    ring
  · simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, h1, h2]
    ring

omit hx hx' in
lemma bk_sigma_pos : 0 < √(1 - (x ⬝ᵥ x') ^ 2) := Real.sqrt_pos.2 (by linarith)

lemma bk_x'_eq : x' = (x ⬝ᵥ x') • x + √(1 - (x ⬝ᵥ x') ^ 2) • eTan x x' := by
  have hs := bk_sigma_pos hc
  unfold eTan
  rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  abel

lemma bk_projT_x_PEm : projT x * PEm x x' = PEm x x' :=
  bk_projT_PEm fun w => (bk_dot_PEm hx hx' hc w).1

lemma bk_projT_e_PEm : projT (eTan x x') * PEm x x' = PEm x x' :=
  bk_projT_PEm fun w => (bk_dot_PEm hx hx' hc w).2

lemma bk_projT_x'_PEm : projT x' * PEm x x' = PEm x x' := by
  refine bk_projT_PEm fun w => ?_
  obtain ⟨h1, h2⟩ := bk_dot_PEm hx hx' hc w
  rw [congrArg (fun y => y ⬝ᵥ (PEm x x' *ᵥ w)) (bk_x'_eq hx hx' hc)]
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, h1, h2]
  simp

lemma bk_opN_PEm : opN (PEm x x') ≤ 1 := by
  have h1 := eTan_dot_x hx hx' hc
  have he : normSq (eTan x x') = 1 := by rw [← ms_dot_self]; exact eTan_dot_self hx hx' hc
  refine BstLean.Part153.opN_le_of_forall _ zero_le_one fun w => ?_
  have e : PEm x x' *ᵥ w = projT x *ᵥ (projT (eTan x x') *ᵥ w) := by
    rw [PEm_mulVec, BstLean.Part153.projT_mulVec, BstLean.Part153.projT_mulVec, dotProduct_sub,
      dotProduct_smul, dotProduct_comm x (eTan x x'), h1, smul_eq_mul, mul_zero, sub_zero]
    abel
  rw [e, one_mul]
  exact (BstLean.Part153.nrm_projT_le hx _).trans (BstLean.Part153.nrm_projT_le he _)

/-- **`‖D₁ B₁‖` (paper `ℓ`)**: `B₁ = A₁ P_E`, `D₁ = diag(mask(A₁ x))`, `A₁ ~ gaussMat m n (2/n)`:
`Pr(tr D₁ ≤ K ∧ √γ(√K + √n + √(2τ)) ≤ ‖D₁ B₁‖) ≤ e^{−τ}`, `γ = 2/n`. -/
theorem blk_ell (hn : 1 ≤ n) {K τ : ℝ} (hτ : 0 ≤ τ) :
    (gaussMat m n (2 / n)) {A | ∑ i, mask ((A *ᵥ x) i) ≤ K ∧
      √(2 / (n : ℝ)) * (√K + √(n : ℝ) + √(2 * τ)) ≤
        opN (Matrix.diagonal (fun i => mask ((A *ᵥ x) i)) * (A * PEm x x'))} ≤
      ENNReal.ofReal (exp (-τ)) := by
  have hv : (0 : ℝ) < 2 / n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  exact blk_single hv hx (PEm x x') (bk_projT_x_PEm hx hx' hc) (bk_opN_PEm hx hx' hc) hτ

/-- **`‖D₁' B₁‖` (paper `ℓ`, second input)**. -/
theorem blk_ell' (hn : 1 ≤ n) {K τ : ℝ} (hτ : 0 ≤ τ) :
    (gaussMat m n (2 / n)) {A | ∑ i, mask ((A *ᵥ x') i) ≤ K ∧
      √(2 / (n : ℝ)) * (√K + √(n : ℝ) + √(2 * τ)) ≤
        opN (Matrix.diagonal (fun i => mask ((A *ᵥ x') i)) * (A * PEm x x'))} ≤
      ENNReal.ofReal (exp (-τ)) := by
  have hv : (0 : ℝ) < 2 / n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  exact blk_single hv hx' (PEm x x') (bk_projT_x'_PEm hx hx' hc) (bk_opN_PEm hx hx' hc) hτ

/-- **`‖D₁ D₁' B₁‖` (paper `√L₁₁`)**: `Pr(tr D₁D₁' ≤ K ∧ √γ(√K + √n + √(2τ)) ≤ ‖D₁D₁'B₁‖) ≤ e^{−τ}`. -/
theorem blk_L11 (hn : 1 ≤ n) {K τ : ℝ} (hτ : 0 ≤ τ) :
    (gaussMat m n (2 / n)) {A | ∑ i, mask ((A *ᵥ x) i) * mask ((A *ᵥ x') i) ≤ K ∧
      √(2 / (n : ℝ)) * (√K + √(n : ℝ) + √(2 * τ)) ≤
        opN (Matrix.diagonal (fun i => mask ((A *ᵥ x) i) * mask ((A *ᵥ x') i)) *
          (A * PEm x x'))} ≤ ENNReal.ofReal (exp (-τ)) := by
  have hv : (0 : ℝ) < 2 / n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have he : normSq (eTan x x') = 1 := by rw [← ms_dot_self]; exact eTan_dot_self hx hx' hc
  have hxe : x ⬝ᵥ eTan x x' = 0 := by rw [dotProduct_comm]; exact eTan_dot_x hx hx' hc
  have h := blk_double (m := m) hv hx he hxe (x ⬝ᵥ x') (√(1 - (x ⬝ᵥ x') ^ 2)) (PEm x x')
    (bk_projT_x_PEm hx hx' hc) (bk_projT_e_PEm hx hx' hc) (bk_opN_PEm hx hx' hc) (K := K) hτ
  rwa [← bk_x'_eq hx hx' hc] at h

end pair

end BstLean.Part182

open BstLean.Part182 in
#print axioms bk_rowsel_tail
open BstLean.Part182 in
#print axioms blk_ell
open BstLean.Part182 in
#print axioms blk_ell'
open BstLean.Part182 in
#print axioms blk_L11
