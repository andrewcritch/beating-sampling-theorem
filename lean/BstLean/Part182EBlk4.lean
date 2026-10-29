import BstLean.Part182EBlk3
import BstLean.Part182Blk
import BstLean.Part182SBlk3

/-!
# Part 182 (file `EBlk4`): the `π₁` tail, the first-layer set `G₁`, and the E block of Lemma TI

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-04-frame-numerator.tex`, Lemma `t7:p04:ti`, tail "`‖P_{U₂}D₁B₁‖ ≤ π₁`" and the E
block, in the upper-singular-value ("TI-lite") form of files `EBlk`–`EBlk3`.

* `e4_proj_tail`: fixed left factor `Q` of rank `≤ 2` (with a frame): Gordon on `UᵀM`.
* `e4_double_tail`: the same with `Q = Qf(Ax, Ax')` (decomposition along `x`, then `e`).
* `e4_Q a b` (explicit Gram–Schmidt projection onto `span(a, b)`, measurable): `e4_Q_a`, `e4_Q_b`,
  `e4_Q_symm`, `e4_Q_rk2`, `e4_measurable_Q`.
* `e4_Q1`, `e4_Q2` (projections onto `span(a, D₁a')`, `span(D₁'a, a')`); `e4_pi1_of`, `e4_pi2_of`:
  the measurable event `‖Qᵢ A P_E‖ ≤ π₁` implies the `π₁` condition of `e3_good1`;
  **`e4_pi1_tail`, `e4_pi2_tail`**: `Pr(√γ(√2 + √n + √(2τ)) ≤ ‖Qᵢ A P_E‖) ≤ e^{−τ}`.
* `e4_G1` (measurable, `e4_measurableSet_G1`), `e4_good_of_G1`; **`e4_G1_charge`**:
  `Pr(A₁ ∉ G₁) ≤ 3e^{−2η²m} + 5e^{−τ}`.
* **`e4_Eblock`**: `Pr_{nuA}(‖P_E Jᵀ J' P_E‖ > e3_bound …) ≤ 12e^{−τ} + 4e^{−2η²m}` (the `KE`
  hypothesis of `ms_opN`).
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open BstLean.Part151 (mask measurable_mask jac)
open BstLean.Part153 (projT nrm nrm_mulVec_le opN_mul_le opN_le_of_bound gaussMat_decomp)

variable {m n : ℕ}

/-- Fixed left factor of rank `≤ 2`. -/
theorem e4_proj_tail {v : ℝ} (hv : 0 < v) (Q : Matrix (Fin m) (Fin m) ℝ) {r : ℕ} (hr : r ≤ 2)
    (U : Matrix (Fin m) (Fin r) ℝ) (hU : Uᵀ * U = 1) (hQU : Q * U * Uᵀ = Q)
    (hQ1 : opN (Q * U) ≤ 1) (P : Matrix (Fin n) (Fin n) ℝ) (hP : opN P ≤ 1) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    (gaussMat m n v) {M | √v * (√2 + √(n : ℝ) + √(2 * τ)) ≤ opN (Q * (M * P))} ≤
      ENNReal.ofReal (exp (-τ)) := by
  have hsub : {M : Matrix (Fin m) (Fin n) ℝ | √v * (√2 + √(n : ℝ) + √(2 * τ)) ≤
      opN (Q * (M * P))} ⊆ (fun A : Matrix (Fin m) (Fin n) ℝ => Uᵀ * A * (1 : Matrix (Fin n) (Fin n) ℝ)) ⁻¹'
        {M' | √v * (√(r : ℝ) + √(n : ℝ) + √(2 * τ)) ≤ opN M'} := by
    intro M hM
    simp only [mem_setOf_eq, mem_preimage, Matrix.mul_one] at hM ⊢
    have e : Q * (M * P) = (Q * U) * ((Uᵀ * M) * P) := by
      calc Q * (M * P) = (Q * U * Uᵀ) * (M * P) := by rw [hQU]
        _ = (Q * U) * ((Uᵀ * M) * P) := by simp only [Matrix.mul_assoc]
    have h1 : opN (Q * (M * P)) ≤ opN (Uᵀ * M) := by
      rw [e]
      refine (opN_mul_le _ _).trans ?_
      refine (mul_le_mul hQ1 (opN_mul_le _ _) (opN_nonneg _) zero_le_one).trans ?_
      rw [one_mul]
      calc opN (Uᵀ * M) * opN P ≤ opN (Uᵀ * M) * 1 :=
            mul_le_mul_of_nonneg_left hP (opN_nonneg _)
        _ = _ := mul_one _
    have h3 : √(r : ℝ) ≤ √2 := Real.sqrt_le_sqrt (by exact_mod_cast hr)
    have hsv : 0 ≤ √v := Real.sqrt_nonneg _
    have : √v * (√(r : ℝ) + √(n : ℝ) + √(2 * τ)) ≤ √v * (√2 + √(n : ℝ) + √(2 * τ)) := by
      nlinarith
    linarith
  refine (measure_mono hsub).trans ?_
  have hS' : MeasurableSet {M' : Matrix (Fin r) (Fin n) ℝ |
      √v * (√(r : ℝ) + √(n : ℝ) + √(2 * τ)) ≤ opN M'} :=
    measurableSet_le measurable_const opN_continuous.measurable
  have hfm : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ =>
      Uᵀ * A * (1 : Matrix (Fin n) (Fin n) ℝ)) :=
    (Continuous.matrix_mul (continuous_const.matrix_mul continuous_id) continuous_const).measurable
  rw [← Measure.map_apply hfm hS', eb_rot hv.le U (1 : Matrix (Fin n) (Fin n) ℝ) hU
    (by simp)]
  have ht := opN_tail' (p := r) (q := n) hv (u := √(2 * τ)) (Real.sqrt_nonneg _)
  have e : -(√(2 * τ)) ^ 2 / 2 = -τ := by
    rw [Real.sq_sqrt (by linarith)]; ring
  rw [e] at ht
  have hfin : IsFiniteMeasure (gaussMat r n v) := by unfold gaussMat; infer_instance
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal ht

lemma e4_meas_set (P : Matrix (Fin n) (Fin n) ℝ) (b : ℝ)
    (G : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ → Matrix (Fin m) (Fin m) ℝ) (hG : Measurable G) :
    MeasurableSet {q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ | b ≤ opN (G q * (q.2 * P))} := by
  have hc : Continuous (fun z : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ =>
      z.1 * (z.2 * P)) := continuous_fst.matrix_mul (continuous_snd.matrix_mul continuous_const)
  have h2 : Measurable (fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ => G q * (q.2 * P)) :=
    hc.measurable.comp (hG.prodMk measurable_snd)
  exact measurableSet_le measurable_const (opN_continuous.measurable.comp h2)

/-- The property of a left factor used by the tail: rank `≤ 2` with a frame. -/
def e4_Rk2 (Q : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  ∃ r : ℕ, r ≤ 2 ∧ ∃ U : Matrix (Fin m) (Fin r) ℝ, Uᵀ * U = 1 ∧ Q * U * Uᵀ = Q ∧ opN (Q * U) ≤ 1

/-- **The `π₁` tail for a left factor depending on `(A x, A x')`**: `x`, `e` orthonormal,
`x' = c x + s e`, `Π_x P = P`, `Π_e P = P`, `‖P‖ ≤ 1`, and `Qf y y'` of rank `≤ 2` (with a frame)
for all `y`, `y'`: `Pr(√v(√2 + √n + √(2τ)) ≤ ‖Qf(Ax, Ax')·A·P‖) ≤ e^{−τ}`. -/
theorem e4_double_tail {v : ℝ} (hv : 0 < v) {x e : Fin n → ℝ} (hx : normSq x = 1)
    (he : normSq e = 1) (hxe : x ⬝ᵥ e = 0) (c s : ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (hPx : projT x * P = P) (hPe : projT e * P = P)
    (hP : opN P ≤ 1) (Qf : (Fin m → ℝ) → (Fin m → ℝ) → Matrix (Fin m) (Fin m) ℝ)
    (hQm : Measurable (fun q : (Fin m → ℝ) × (Fin m → ℝ) => Qf q.1 q.2))
    (hQ : ∀ y y', e4_Rk2 (Qf y y')) {τ : ℝ} (hτ : 0 ≤ τ) :
    (gaussMat m n v) {A | √v * (√2 + √(n : ℝ) + √(2 * τ)) ≤
      opN (Qf (A *ᵥ x) (A *ᵥ (c • x + s • e)) * (A * P))} ≤ ENNReal.ofReal (exp (-τ)) := by
  set b := √v * (√2 + √(n : ℝ) + √(2 * τ)) with hb
  have hmv : Continuous (fun M : Matrix (Fin m) (Fin n) ℝ => M *ᵥ e) :=
    continuous_id.matrix_mulVec continuous_const
  set G₁ : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ → Matrix (Fin m) (Fin m) ℝ :=
    fun q => Qf q.1 (c • q.1 + s • (q.2 *ᵥ e)) with hG₁
  have hG₁m : Measurable G₁ :=
    hQm.comp (measurable_fst.prodMk ((measurable_fst.const_smul c).add
      ((hmv.measurable.comp measurable_snd).const_smul s)))
  set S2 := {q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ | b ≤ opN (G₁ q * (q.2 * P))} with hS2
  have hS2m : MeasurableSet S2 := e4_meas_set P b G₁ hG₁m
  have hf : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => (A *ᵥ x, A * projT x)) :=
    (continuous_id.matrix_mulVec continuous_const).measurable.prodMk
      (BstLean.Part153.measurable_mul_const _)
  have hAx' : ∀ A : Matrix (Fin m) (Fin n) ℝ,
      A *ᵥ (c • x + s • e) = c • (A *ᵥ x) + s • ((A * projT x) *ᵥ e) := by
    intro A
    rw [bk_mul_projT_mulVec hxe, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  have hset : {A : Matrix (Fin m) (Fin n) ℝ | b ≤
      opN (Qf (A *ᵥ x) (A *ᵥ (c • x + s • e)) * (A * P))} =
      (fun A : Matrix (Fin m) (Fin n) ℝ => (A *ᵥ x, A * projT x)) ⁻¹' S2 := by
    ext A
    simp only [mem_setOf_eq, mem_preimage, hS2, hG₁, Matrix.mul_assoc, hPx, hAx']
  rw [hset, ← bk_lint_ind _ hS2m hf, gaussMat_decomp hx hv.le (measurable_one.indicator hS2m)]
  have inner : ∀ g : Fin m → ℝ, ∫⁻ M, S2.indicator 1 (√v • g, M * projT x) ∂gaussMat m n v ≤
      ENNReal.ofReal (exp (-τ)) := by
    intro g
    set a := √v • g with ha
    have hm : Measurable (fun M : Matrix (Fin m) (Fin n) ℝ => (a, M * projT x)) :=
      measurable_const.prodMk (BstLean.Part153.measurable_mul_const _)
    rw [bk_lint_ind _ hS2m hm]
    set G₂ : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ → Matrix (Fin m) (Fin m) ℝ :=
      fun q => Qf a (c • a + s • q.1) with hG₂
    have hG₂m : Measurable G₂ :=
      hQm.comp (measurable_const.prodMk (measurable_const.add (measurable_fst.const_smul s)))
    set T := {q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ | b ≤ opN (G₂ q * (q.2 * P))} with hT
    have hTm : MeasurableSet T := e4_meas_set P b G₂ hG₂m
    have hf₂ : Measurable (fun M : Matrix (Fin m) (Fin n) ℝ => (M *ᵥ e, M * projT e)) :=
      (continuous_id.matrix_mulVec continuous_const).measurable.prodMk
        (BstLean.Part153.measurable_mul_const _)
    have hset2 : (fun M : Matrix (Fin m) (Fin n) ℝ => (a, M * projT x)) ⁻¹' S2 =
        (fun M : Matrix (Fin m) (Fin n) ℝ => (M *ᵥ e, M * projT e)) ⁻¹' T := by
      ext M
      simp only [mem_preimage, hS2, hT, mem_setOf_eq, hG₁, hG₂, bk_mul_projT_mulVec hxe,
        Matrix.mul_assoc, hPx, hPe]
    rw [hset2, ← bk_lint_ind _ hTm hf₂, gaussMat_decomp he hv.le (measurable_one.indicator hTm)]
    have inner2 : ∀ h : Fin m → ℝ, ∫⁻ M', T.indicator 1 (√v • h, M' * projT e)
        ∂gaussMat m n v ≤ ENNReal.ofReal (exp (-τ)) := by
      intro h
      have hm' : Measurable (fun M' : Matrix (Fin m) (Fin n) ℝ => (√v • h, M' * projT e)) :=
        measurable_const.prodMk (BstLean.Part153.measurable_mul_const _)
      rw [bk_lint_ind _ hTm hm']
      obtain ⟨r, hr, U, hU, hQU, hQ1⟩ := hQ a (c • a + s • (√v • h))
      refine (measure_mono ?_).trans (e4_proj_tail hv _ hr U hU hQU hQ1 P hP hτ)
      intro M' hM'
      simp only [mem_preimage, hT, mem_setOf_eq, hG₂, Matrix.mul_assoc, hPe] at hM'
      exact hM'
    have hP1 : IsProbabilityMeasure (stdGauss (Fin m)) := by unfold stdGauss; infer_instance
    calc ∫⁻ h, ∫⁻ M', T.indicator 1 (√v • h, M' * projT e) ∂gaussMat m n v ∂stdGauss (Fin m)
        ≤ ∫⁻ _h, ENNReal.ofReal (exp (-τ)) ∂stdGauss (Fin m) := lintegral_mono inner2
      _ = ENNReal.ofReal (exp (-τ)) := by rw [lintegral_const, measure_univ, mul_one]
  have hP1 : IsProbabilityMeasure (stdGauss (Fin m)) := by unfold stdGauss; infer_instance
  calc ∫⁻ g, ∫⁻ M, S2.indicator 1 (√v • g, M * projT x) ∂gaussMat m n v ∂stdGauss (Fin m)
      ≤ ∫⁻ _g, ENNReal.ofReal (exp (-τ)) ∂stdGauss (Fin m) := lintegral_mono inner
    _ = ENNReal.ofReal (exp (-τ)) := by rw [lintegral_const, measure_univ, mul_one]

/-! ## The explicit projection onto `span(a, b)` (Gram–Schmidt) -/

/-- `v/|v|` (`0` if `v = 0`). -/
noncomputable def e4_u {k : ℕ} (v : Fin k → ℝ) : Fin k → ℝ := (nrm v)⁻¹ • v

noncomputable def e4_e2 {k : ℕ} (a b : Fin k → ℝ) : Fin k → ℝ :=
  e4_u (b - (b ⬝ᵥ e4_u a) • e4_u a)

/-- **The orthogonal projection onto `span(a, b)`**, `e₁e₁ᵀ + e₂e₂ᵀ`. -/
noncomputable def e4_Q {k : ℕ} (a b : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  vecMulVec (e4_u a) (e4_u a) + vecMulVec (e4_e2 a b) (e4_e2 a b)

lemma e4_vmv_mulVec {k : ℕ} (u w : Fin k → ℝ) : vecMulVec u u *ᵥ w = (u ⬝ᵥ w) • u := by
  ext i
  simp only [Matrix.mulVec, dotProduct, vecMulVec, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma e4_Q_mulVec {k : ℕ} (a b w : Fin k → ℝ) :
    e4_Q a b *ᵥ w = (e4_u a ⬝ᵥ w) • e4_u a + (e4_e2 a b ⬝ᵥ w) • e4_e2 a b := by
  rw [e4_Q, Matrix.add_mulVec, e4_vmv_mulVec, e4_vmv_mulVec]

lemma e4_dot_self {k : ℕ} (v : Fin k → ℝ) : v ⬝ᵥ v = normSq v := by
  unfold normSq dotProduct; simp [sq]

lemma e4_u_eq {k : ℕ} (v : Fin k → ℝ) : nrm v • e4_u v = v := by
  unfold e4_u
  by_cases h : nrm v = 0
  · have h0 : normSq v = 0 := by
      have := BstLean.Part153.nrm_sq v; rw [h] at this; simpa using this.symm
    have : v = 0 := BstLean.Part134.eq_zero_of_normSq h0
    simp [this]
  · rw [smul_smul, mul_inv_cancel₀ h, one_smul]

lemma e4_u_cases {k : ℕ} (v : Fin k → ℝ) : e4_u v ⬝ᵥ e4_u v = 1 ∨ e4_u v = 0 := by
  by_cases h : nrm v = 0
  · right; unfold e4_u; rw [h, _root_.inv_zero, zero_smul]
  · left
    unfold e4_u
    rw [smul_dotProduct, dotProduct_smul, e4_dot_self, ← BstLean.Part153.nrm_sq, smul_eq_mul,
      smul_eq_mul]
    field_simp

lemma e4_orth {k : ℕ} (a b : Fin k → ℝ) : e4_u a ⬝ᵥ e4_e2 a b = 0 := by
  unfold e4_e2
  set e1 := e4_u a
  have h : e1 ⬝ᵥ (b - (b ⬝ᵥ e1) • e1) = 0 := by
    rcases e4_u_cases a with h1 | h1
    · rw [dotProduct_sub, dotProduct_smul, h1, smul_eq_mul, mul_one, dotProduct_comm]; ring
    · simp [e1, h1]
  unfold e4_u
  rw [dotProduct_smul, h, smul_zero]

/-- `Q` fixes every combination of `e₁`, `e₂`. -/
lemma e4_Q_fix {k : ℕ} (a b : Fin k → ℝ) (α β : ℝ) :
    e4_Q a b *ᵥ (α • e4_u a + β • e4_e2 a b) = α • e4_u a + β • e4_e2 a b := by
  rw [e4_Q_mulVec]
  have ho := e4_orth a b
  have ho' : e4_e2 a b ⬝ᵥ e4_u a = 0 := by rw [dotProduct_comm]; exact ho
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, ho, ho', mul_zero, add_zero, zero_add]
  have h2 : e4_e2 a b ⬝ᵥ e4_e2 a b = 1 ∨ e4_e2 a b = 0 := e4_u_cases _
  rcases e4_u_cases a with h1 | h1 <;> rcases h2 with h2 | h2
  · rw [h1, h2]; simp
  · rw [h1, h2]; simp
  · rw [h1, h2]; simp
  · rw [h1, h2]; simp

lemma e4_Q_a {k : ℕ} (a b : Fin k → ℝ) : e4_Q a b *ᵥ a = a := by
  have h := e4_Q_fix a b (nrm a) 0
  rw [zero_smul, add_zero, e4_u_eq] at h
  exact h

lemma e4_Q_b {k : ℕ} (a b : Fin k → ℝ) : e4_Q a b *ᵥ b = b := by
  have hb : b = (b ⬝ᵥ e4_u a) • e4_u a + nrm (b - (b ⬝ᵥ e4_u a) • e4_u a) • e4_e2 a b := by
    unfold e4_e2; rw [e4_u_eq]; abel
  have h := e4_Q_fix a b (b ⬝ᵥ e4_u a) (nrm (b - (b ⬝ᵥ e4_u a) • e4_u a))
  rw [← hb] at h
  exact h

lemma e4_Q_symm {k : ℕ} (a b : Fin k → ℝ) : (e4_Q a b)ᵀ = e4_Q a b := by
  simp [e4_Q, Matrix.transpose_add, Matrix.transpose_vecMulVec]

lemma e4_Q_rk2 {k : ℕ} (a b : Fin k → ℝ) : e4_Rk2 (e4_Q a b) := by
  obtain ⟨r, hr, U, X, hU, hUW, hUX⟩ := e3_frame (e3_W2 (e4_u a) (e4_e2 a b))
  refine ⟨r, by simpa using hr, U, hU, ?_, ?_⟩
  · have hc1 : (U * Uᵀ) *ᵥ e4_u a = e4_u a := by
      have h := congrArg (fun M : Matrix (Fin k) (Fin 2) ℝ => M *ᵥ ![1, 0]) hUW
      simp only [← Matrix.mulVec_mulVec, e3_W2_mulVec] at h
      simpa using h
    have hc2 : (U * Uᵀ) *ᵥ e4_e2 a b = e4_e2 a b := by
      have h := congrArg (fun M : Matrix (Fin k) (Fin 2) ℝ => M *ᵥ ![0, 1]) hUW
      simp only [← Matrix.mulVec_mulVec, e3_W2_mulVec] at h
      simpa using h
    have hsym : (U * Uᵀ)ᵀ = U * Uᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    have hd : ∀ (y w : Fin k → ℝ), (U * Uᵀ) *ᵥ y = y → y ⬝ᵥ ((U * Uᵀ) *ᵥ w) = y ⬝ᵥ w := by
      intro y w hy
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, hy]
    refine Matrix.ext_of_mulVec_single fun i => ?_
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, e4_Q_mulVec, e4_Q_mulVec, hd _ _ hc1, hd _ _ hc2]
  · refine opN_le_of_bound _ zero_le_one fun w => ?_
    rw [one_mul, ← Matrix.mulVec_mulVec]
    have hUw : U *ᵥ w = (X *ᵥ w) 0 • e4_u a + (X *ᵥ w) 1 • e4_e2 a b := by
      rw [hUX, ← Matrix.mulVec_mulVec, e3_W2_mulVec]
    rw [hUw, e4_Q_fix, ← hUw]
    exact (nrm_mulVec_le U w).trans (by
      have := e3_opN_frame U hU
      have h0 := BstLean.Part153.nrm_nonneg w
      nlinarith)

lemma e4_measurable_Q {k : ℕ} :
    Measurable (fun q : (Fin k → ℝ) × (Fin k → ℝ) => e4_Q q.1 q.2) := by
  unfold e4_Q e4_e2 e4_u nrm normSq
  simp only [vecMulVec, dotProduct]
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  simp only [Matrix.add_apply, Matrix.of_apply]
  fun_prop

/-! ## The `π₁` events for the pair `(x, x')` -/

/-- `Q₁ = proj span(a, D₁a')`, `a = ReLU(A x)`, `D₁ = diag(mask(A x))`. -/
noncomputable def e4_Q1 (x x' : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  e4_Q (reluV (A *ᵥ x)) (obD (A *ᵥ x) *ᵥ reluV (A *ᵥ x'))

/-- `Q₂ = proj span(D₁'a, a')`. -/
noncomputable def e4_Q2 (x x' : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  e4_Q (obD (A *ᵥ x') *ᵥ reluV (A *ᵥ x)) (reluV (A *ᵥ x'))

lemma e4_obD_mulVec {k : ℕ} (y u : Fin k → ℝ) : obD y *ᵥ u = fun i => mask (y i) * u i := by
  ext i; simp [obD, Matrix.mulVec_diagonal]

lemma e4_obD_relu {k : ℕ} (y : Fin k → ℝ) : obD y *ᵥ reluV y = reluV y := by
  rw [e4_obD_mulVec]; ext i
  simp only [reluV, relu]
  by_cases h : 0 < y i
  · rw [BstLean.Part151.mask_of_pos h, one_mul]
  · rw [BstLean.Part151.mask_of_nonpos (not_lt.mp h), zero_mul, max_eq_left (not_lt.mp h)]

lemma e4_nrm_obD_le {k : ℕ} (y u : Fin k → ℝ) : nrm (obD y *ᵥ u) ≤ nrm u := by
  rw [e4_obD_mulVec]; exact BstLean.Part153.nrm_mask_mul_le y u

lemma e4_obD_symm {k : ℕ} (y : Fin k → ℝ) : (obD y)ᵀ = obD y := by
  simp [obD, Matrix.diagonal_transpose]

/-- **From the measurable event to the `π₁` condition** (generic left factor `Q` fixing `D a`,
`D a'`). -/
lemma e4_pi_of {D Q : Matrix (Fin m) (Fin m) ℝ} (A : Matrix (Fin m) (Fin n) ℝ)
    (PE : Matrix (Fin n) (Fin n) ℝ) (a a' : Fin m → ℝ) (hDs : Dᵀ = D)
    (hD : ∀ u, nrm (D *ᵥ u) ≤ nrm u) (hQs : Qᵀ = Q) (hQa : Q *ᵥ (D *ᵥ a) = D *ᵥ a)
    (hQa' : Q *ᵥ (D *ᵥ a') = D *ᵥ a') {π₁ : ℝ} (hπ : opN (Q * (A * PE)) ≤ π₁) (c₀ c₁ : ℝ) :
    nrm ((D * A * PE)ᵀ *ᵥ (c₀ • a + c₁ • a')) ≤ π₁ * nrm (c₀ • a + c₁ • a') := by
  have hDu : Q *ᵥ (D *ᵥ (c₀ • a + c₁ • a')) = D *ᵥ (c₀ • a + c₁ • a') := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul, hQa, hQa']
  have e : (D * A * PE)ᵀ *ᵥ (c₀ • a + c₁ • a') =
      (Q * (A * PE))ᵀ *ᵥ (D *ᵥ (c₀ • a + c₁ • a')) := by
    have e1 : (D * A * PE)ᵀ = (A * PE)ᵀ * D := by
      rw [Matrix.mul_assoc, Matrix.transpose_mul, hDs]
    have e2 : (Q * (A * PE))ᵀ = (A * PE)ᵀ * Q := by rw [Matrix.transpose_mul, hQs]
    rw [e1, e2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hDu]
  rw [e]
  have h1 := nrm_mulVec_le (Q * (A * PE))ᵀ (D *ᵥ (c₀ • a + c₁ • a'))
  rw [BstLean.Part153.opN_transpose] at h1
  have h0 : 0 ≤ nrm (D *ᵥ (c₀ • a + c₁ • a')) := BstLean.Part153.nrm_nonneg _
  have hπ0 : 0 ≤ π₁ := (opN_nonneg _).trans hπ
  calc _ ≤ opN (Q * (A * PE)) * nrm (D *ᵥ (c₀ • a + c₁ • a')) := h1
    _ ≤ π₁ * nrm (D *ᵥ (c₀ • a + c₁ • a')) := mul_le_mul_of_nonneg_right hπ h0
    _ ≤ π₁ * nrm (c₀ • a + c₁ • a') := mul_le_mul_of_nonneg_left (hD _) hπ0

lemma e4_pi1_of (x x' : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (PE : Matrix (Fin n) (Fin n) ℝ)
    {π₁ : ℝ} (hπ : opN (e4_Q1 x x' A * (A * PE)) ≤ π₁) (c₀ c₁ : ℝ) :
    nrm ((obD (A *ᵥ x) * A * PE)ᵀ *ᵥ (c₀ • reluV (A *ᵥ x) + c₁ • reluV (A *ᵥ x'))) ≤
      π₁ * nrm (c₀ • reluV (A *ᵥ x) + c₁ • reluV (A *ᵥ x')) :=
  e4_pi_of A PE _ _ (e4_obD_symm _) (e4_nrm_obD_le _) (e4_Q_symm _ _)
    (by rw [e4_obD_relu]; exact e4_Q_a _ _) (e4_Q_b _ _) hπ c₀ c₁

lemma e4_pi2_of (x x' : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (PE : Matrix (Fin n) (Fin n) ℝ)
    {π₁ : ℝ} (hπ : opN (e4_Q2 x x' A * (A * PE)) ≤ π₁) (c₀ c₁ : ℝ) :
    nrm ((obD (A *ᵥ x') * A * PE)ᵀ *ᵥ (c₀ • reluV (A *ᵥ x) + c₁ • reluV (A *ᵥ x'))) ≤
      π₁ * nrm (c₀ • reluV (A *ᵥ x) + c₁ • reluV (A *ᵥ x')) :=
  e4_pi_of A PE _ _ (e4_obD_symm _) (e4_nrm_obD_le _) (e4_Q_symm _ _) (e4_Q_a _ _)
    (by rw [e4_obD_relu]; exact e4_Q_b _ _) hπ c₀ c₁

lemma e4_measurable_obD_relu :
    Measurable (fun q : (Fin m → ℝ) × (Fin m → ℝ) => obD q.1 *ᵥ reluV q.2) := by
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [e4_obD_mulVec, reluV, relu]
  exact (measurable_mask.comp ((measurable_pi_apply i).comp measurable_fst)).mul
    (measurable_const.max ((measurable_pi_apply i).comp measurable_snd))

lemma e4_measurable_reluV : Measurable (fun y : Fin m → ℝ => reluV y) := by
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [reluV, relu]
  exact measurable_const.max (measurable_pi_apply i)

section pair
variable {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
  (hc : (x ⬝ᵥ x') ^ 2 < 1)
include hx hx' hc

/-- **The `π₁` tail, first input**: `Pr(√γ(√2 + √n + √(2τ)) ≤ ‖Q₁ A P_E‖) ≤ e^{−τ}`. -/
theorem e4_pi1_tail (hn : 1 ≤ n) {τ : ℝ} (hτ : 0 ≤ τ) :
    (gaussMat m n (2 / n)) {A | √(2 / (n : ℝ)) * (√2 + √(n : ℝ) + √(2 * τ)) ≤
      opN (e4_Q1 x x' A * (A * PEm x x'))} ≤ ENNReal.ofReal (exp (-τ)) := by
  have hv : (0 : ℝ) < 2 / n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have he : normSq (eTan x x') = 1 := by rw [← ms_dot_self]; exact eTan_dot_self hx hx' hc
  have hxe : x ⬝ᵥ eTan x x' = 0 := by rw [dotProduct_comm]; exact eTan_dot_x hx hx' hc
  have hQm : Measurable (fun q : (Fin m → ℝ) × (Fin m → ℝ) =>
      e4_Q (reluV q.1) (obD q.1 *ᵥ reluV q.2)) := by
    have h0 := (e4_measurable_Q (k := m)).comp
      ((e4_measurable_reluV (m := m)).comp measurable_fst |>.prodMk
        (e4_measurable_obD_relu (m := m)))
    exact h0
  have h := e4_double_tail (m := m) hv hx he hxe (x ⬝ᵥ x') (√(1 - (x ⬝ᵥ x') ^ 2)) (PEm x x')
    (bk_projT_x_PEm hx hx' hc) (bk_projT_e_PEm hx hx' hc) (bk_opN_PEm hx hx' hc)
    (fun y y' => e4_Q (reluV y) (obD y *ᵥ reluV y')) hQm (fun _ _ => e4_Q_rk2 _ _) hτ
  rw [← bk_x'_eq hx hx' hc] at h
  exact h

/-- **The `π₁` tail, second input**. -/
theorem e4_pi2_tail (hn : 1 ≤ n) {τ : ℝ} (hτ : 0 ≤ τ) :
    (gaussMat m n (2 / n)) {A | √(2 / (n : ℝ)) * (√2 + √(n : ℝ) + √(2 * τ)) ≤
      opN (e4_Q2 x x' A * (A * PEm x x'))} ≤ ENNReal.ofReal (exp (-τ)) := by
  have hv : (0 : ℝ) < 2 / n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have he : normSq (eTan x x') = 1 := by rw [← ms_dot_self]; exact eTan_dot_self hx hx' hc
  have hxe : x ⬝ᵥ eTan x x' = 0 := by rw [dotProduct_comm]; exact eTan_dot_x hx hx' hc
  have hQm : Measurable (fun q : (Fin m → ℝ) × (Fin m → ℝ) =>
      e4_Q (obD q.2 *ᵥ reluV q.1) (reluV q.2)) := by
    have h0 := (e4_measurable_Q (k := m)).comp
      (((e4_measurable_obD_relu (m := m)).comp measurable_swap).prodMk
        ((e4_measurable_reluV (m := m)).comp measurable_snd))
    exact h0
  have h := e4_double_tail (m := m) hv hx he hxe (x ⬝ᵥ x') (√(1 - (x ⬝ᵥ x') ^ 2)) (PEm x x')
    (bk_projT_x_PEm hx hx' hc) (bk_projT_e_PEm hx hx' hc) (bk_opN_PEm hx hx' hc)
    (fun y y' => e4_Q (obD y' *ᵥ reluV y) (reluV y')) hQm (fun _ _ => e4_Q_rk2 _ _) hτ
  rw [← bk_x'_eq hx hx' hc] at h
  exact h

end pair

/-! ## The first-layer set `G₁` and its charge -/

/-- `ℓ = √γ(√K + √n + √(2τ))` (also `√L₁₁` with `K = K₁₁`, and `π₁` with `K = 2`). -/
noncomputable def e4_b (n : ℕ) (K τ : ℝ) : ℝ := √(2 / (n : ℝ)) * (√K + √(n : ℝ) + √(2 * τ))

/-- **The first-layer set `G₁`** (strict inequalities; its complement is covered by the tails). -/
def e4_G1 (x x' : Fin n → ℝ) (K₁ K₁₁ τ : ℝ) : Set (Matrix (Fin m) (Fin n) ℝ) :=
  {A | opN (Matrix.diagonal (fun i => mask ((A *ᵥ x) i)) * (A * PEm x x')) < e4_b n K₁ τ ∧
    opN (Matrix.diagonal (fun i => mask ((A *ᵥ x') i)) * (A * PEm x x')) < e4_b n K₁ τ ∧
    opN (Matrix.diagonal (fun i => mask ((A *ᵥ x) i) * mask ((A *ᵥ x') i)) * (A * PEm x x')) <
      e4_b n K₁₁ τ ∧
    opN (e4_Q1 x x' A * (A * PEm x x')) < e4_b n 2 τ ∧
    opN (e4_Q2 x x' A * (A * PEm x x')) < e4_b n 2 τ}

lemma e4_measurable_mul {G : Matrix (Fin m) (Fin n) ℝ → Matrix (Fin m) (Fin m) ℝ}
    (hG : Measurable G) (P : Matrix (Fin n) (Fin n) ℝ) :
    Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => opN (G A * (A * P))) := by
  have hc : Continuous (fun z : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ =>
      z.1 * (z.2 * P)) := continuous_fst.matrix_mul (continuous_snd.matrix_mul continuous_const)
  exact opN_continuous.measurable.comp (hc.measurable.comp (hG.prodMk measurable_id))

lemma e4_measurable_diag (f : (Fin m → ℝ) → Fin m → ℝ) (hf : Measurable f) (y : Fin n → ℝ) :
    Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => Matrix.diagonal (f (A *ᵥ y))) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  simp only [Matrix.diagonal_apply]
  by_cases h : i = j
  · simp only [h, if_true]
    exact (measurable_pi_apply j).comp (hf.comp
      (continuous_id.matrix_mulVec continuous_const).measurable)
  · simp only [h, if_false]; exact measurable_const

lemma e4_measurable_Q1 (x x' : Fin n → ℝ) :
    Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => e4_Q1 x x' A) := by
  have hv : ∀ y : Fin n → ℝ, Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => A *ᵥ y) :=
    fun y => (continuous_id.matrix_mulVec continuous_const).measurable
  have h0 := (e4_measurable_Q (k := m)).comp
    (((e4_measurable_reluV (m := m)).comp (hv x)).prodMk
      ((e4_measurable_obD_relu (m := m)).comp ((hv x).prodMk (hv x'))))
  exact h0

lemma e4_measurable_Q2 (x x' : Fin n → ℝ) :
    Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => e4_Q2 x x' A) := by
  have hv : ∀ y : Fin n → ℝ, Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => A *ᵥ y) :=
    fun y => (continuous_id.matrix_mulVec continuous_const).measurable
  have h0 := (e4_measurable_Q (k := m)).comp
    (((e4_measurable_obD_relu (m := m)).comp ((hv x').prodMk (hv x))).prodMk
      ((e4_measurable_reluV (m := m)).comp (hv x')))
  exact h0

lemma e4_measurableSet_G1 (x x' : Fin n → ℝ) (K₁ K₁₁ τ : ℝ) :
    MeasurableSet (e4_G1 (m := m) x x' K₁ K₁₁ τ) := by
  have hmask : Measurable (fun u : Fin m → ℝ => fun i => mask (u i)) :=
    measurable_pi_iff.mpr fun i => measurable_mask.comp (measurable_pi_apply i)
  have h1 := e4_measurable_mul (e4_measurable_diag _ hmask x) (PEm x x')
  have h2 := e4_measurable_mul (e4_measurable_diag _ hmask x') (PEm x x')
  have hd3 : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ =>
      Matrix.diagonal (fun i => mask ((A *ᵥ x) i) * mask ((A *ᵥ x') i))) := by
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    simp only [Matrix.diagonal_apply]
    by_cases h : i = j
    · simp only [h, if_true]
      have hv : ∀ y : Fin n → ℝ, Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => (A *ᵥ y) j) :=
        fun y => (measurable_pi_apply j).comp
          (continuous_id.matrix_mulVec continuous_const).measurable
      exact (measurable_mask.comp (hv x)).mul (measurable_mask.comp (hv x'))
    · simp only [h, if_false]; exact measurable_const
  have h3 := e4_measurable_mul hd3 (PEm x x')
  have h4 := e4_measurable_mul (e4_measurable_Q1 (m := m) x x') (PEm x x')
  have h5 := e4_measurable_mul (e4_measurable_Q2 (m := m) x x') (PEm x x')
  exact (measurableSet_lt h1 measurable_const).inter ((measurableSet_lt h2 measurable_const).inter
    ((measurableSet_lt h3 measurable_const).inter ((measurableSet_lt h4 measurable_const).inter
      (measurableSet_lt h5 measurable_const))))

/-- **`e3_good1` on `G₁`**, with `ℓ = e4_b K₁`, `L₁₁ = (e4_b K₁₁)²`, `π₁ = e4_b 2`. -/
lemma e4_good_of_G1 (x x' : Fin n → ℝ) (K₁ K₁₁ τ : ℝ) {A : Matrix (Fin (mA n)) (Fin n) ℝ}
    (hA : A ∈ e4_G1 (m := mA n) x x' K₁ K₁₁ τ) :
    e3_good1 x x' (PEm x x') (e4_b n K₁ τ) (e4_b n K₁₁ τ ^ 2) (e4_b n 2 τ) A := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hA
  refine ⟨?_, ?_, ?_, fun c₀ c₁ => e4_pi1_of x x' A _ h4.le c₀ c₁,
    fun c₀ c₁ => e4_pi2_of x x' A _ h5.le c₀ c₁⟩
  · rw [e3_L_eq]; exact h1.le
  · rw [e3_L_eq]; exact h2.le
  · refine (e3_LL_le x x' A (PEm x x')).trans ?_
    exact pow_le_pow_left₀ (opN_nonneg _) h3.le 2

lemma e4_toReal {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {S : Set α}
    {t : ℝ} (h : μ S ≤ ENNReal.ofReal t) (ht : 0 ≤ t) : μ.real S ≤ t := by
  rw [Measure.real]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans (ENNReal.toReal_ofReal ht).le

lemma e4_PEm_symm (x x' : Fin n → ℝ) : (PEm x x')ᵀ = PEm x x' := by
  simp [PEm, Matrix.transpose_sub, Matrix.transpose_vecMulVec]

section pair2
variable {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
  (hc : (x ⬝ᵥ x') ^ 2 < 1)
include hx hx' hc

/-- **The charge of `G₁`**: with `K₁ = m(1/2 + η)`, `K₁₁ = m(κ̇(c₊)/2 + η)`, `x·x' ≤ c₊ ≤ 1`:
`Pr(A ∉ G₁) ≤ 3e^{−2η²m} + 5e^{−τ}`. -/
theorem e4_G1_charge (hn : 1 ≤ n) {cp η τ : ℝ} (hcp : x ⬝ᵥ x' ≤ cp) (hcp1 : cp ≤ 1)
    (hη : 0 ≤ η) (hτ : 0 ≤ τ) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real
      (e4_G1 (m := mA n) x x' (((mA n : ℕ) : ℝ) * (1 / 2 + η))
        (((mA n : ℕ) : ℝ) * (kdot cp / 2 + η)) τ)ᶜ ≤
      3 * exp (-2 * η ^ 2 * (mA n : ℕ)) + 5 * exp (-τ) := by
  set μ := gaussMat (mA n) n (2 / (n : ℝ)) with hμ
  have hP : IsProbabilityMeasure μ := by rw [hμ]; unfold gaussMat; infer_instance
  have hv : (0 : ℝ) < 2 / n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have hne : ∀ y : Fin n → ℝ, normSq y = 1 → y ≠ 0 := by
    intro y hy h0; rw [h0] at hy; simp [normSq] at hy
  set K₁ := ((mA n : ℕ) : ℝ) * (1 / 2 + η) with hK₁
  set K₁₁ := ((mA n : ℕ) : ℝ) * (kdot cp / 2 + η) with hK₁₁
  set S1 := {A : Matrix (Fin (mA n)) (Fin n) ℝ | K₁ < ∑ i, mask ((A *ᵥ x) i)}
  set S2 := {A : Matrix (Fin (mA n)) (Fin n) ℝ | K₁ < ∑ i, mask ((A *ᵥ x') i)}
  set S3 := {A : Matrix (Fin (mA n)) (Fin n) ℝ | K₁₁ < ∑ i, mask ((A *ᵥ x) i) * mask ((A *ᵥ x') i)}
  set B1 := {A : Matrix (Fin (mA n)) (Fin n) ℝ | ∑ i, mask ((A *ᵥ x) i) ≤ K₁ ∧
      √(2 / (n : ℝ)) * (√K₁ + √(n : ℝ) + √(2 * τ)) ≤
        opN (Matrix.diagonal (fun i => mask ((A *ᵥ x) i)) * (A * PEm x x'))}
  set B2 := {A : Matrix (Fin (mA n)) (Fin n) ℝ | ∑ i, mask ((A *ᵥ x') i) ≤ K₁ ∧
      √(2 / (n : ℝ)) * (√K₁ + √(n : ℝ) + √(2 * τ)) ≤
        opN (Matrix.diagonal (fun i => mask ((A *ᵥ x') i)) * (A * PEm x x'))}
  set B3 := {A : Matrix (Fin (mA n)) (Fin n) ℝ | ∑ i, mask ((A *ᵥ x) i) * mask ((A *ᵥ x') i) ≤ K₁₁ ∧
      √(2 / (n : ℝ)) * (√K₁₁ + √(n : ℝ) + √(2 * τ)) ≤
        opN (Matrix.diagonal (fun i => mask ((A *ᵥ x) i) * mask ((A *ᵥ x') i)) * (A * PEm x x'))}
  set P1 := {A : Matrix (Fin (mA n)) (Fin n) ℝ | √(2 / (n : ℝ)) * (√2 + √(n : ℝ) + √(2 * τ)) ≤
      opN (e4_Q1 x x' A * (A * PEm x x'))}
  set P2 := {A : Matrix (Fin (mA n)) (Fin n) ℝ | √(2 / (n : ℝ)) * (√2 + √(n : ℝ) + √(2 * τ)) ≤
      opN (e4_Q2 x x' A * (A * PEm x x'))}
  have hsub : (e4_G1 (m := mA n) x x' K₁ K₁₁ τ)ᶜ ⊆
      S1 ∪ B1 ∪ S2 ∪ B2 ∪ S3 ∪ B3 ∪ P1 ∪ P2 := by
    intro A hA
    simp only [e4_G1, Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or, not_lt, e4_b] at hA
    simp only [Set.mem_union, Set.mem_setOf_eq, S1, S2, S3, B1, B2, B3, P1, P2]
    rcases hA with h | h | h | h | h
    · by_cases hk : ∑ i, mask ((A *ᵥ x) i) ≤ K₁
      · tauto
      · left; left; left; left; left; left; left; exact not_le.mp hk
    · by_cases hk : ∑ i, mask ((A *ᵥ x') i) ≤ K₁
      · tauto
      · left; left; left; left; left; right; exact not_le.mp hk
    · by_cases hk : ∑ i, mask ((A *ᵥ x) i) * mask ((A *ᵥ x') i) ≤ K₁₁
      · tauto
      · left; left; left; right; exact not_le.mp hk
    · left; right; exact h
    · right; exact h
  have t1 : μ.real S1 ≤ exp (-2 * η ^ 2 * (mA n : ℕ)) := single_tail hv (hne x hx) hη
  have t2 : μ.real S2 ≤ exp (-2 * η ^ 2 * (mA n : ℕ)) := single_tail hv (hne x' hx') hη
  have t3 : μ.real S3 ≤ exp (-2 * η ^ 2 * (mA n : ℕ)) :=
    mask_first hx hx' (by simpa [dotProduct] using hcp) hcp1 hη
  have tb1 : μ.real B1 ≤ exp (-τ) :=
    e4_toReal (blk_ell hx hx' hc hn (K := K₁) hτ) (exp_pos _).le
  have tb2 : μ.real B2 ≤ exp (-τ) :=
    e4_toReal (blk_ell' hx hx' hc hn (K := K₁) hτ) (exp_pos _).le
  have tb3 : μ.real B3 ≤ exp (-τ) :=
    e4_toReal (blk_L11 hx hx' hc hn (K := K₁₁) hτ) (exp_pos _).le
  have tp1 : μ.real P1 ≤ exp (-τ) :=
    e4_toReal (e4_pi1_tail hx hx' hc hn hτ) (exp_pos _).le
  have tp2 : μ.real P2 ≤ exp (-τ) :=
    e4_toReal (e4_pi2_tail hx hx' hc hn hτ) (exp_pos _).le
  have hu : ∀ X Y : Set (Matrix (Fin (mA n)) (Fin n) ℝ), μ.real (X ∪ Y) ≤ μ.real X + μ.real Y :=
    fun X Y => measureReal_union_le X Y
  calc μ.real (e4_G1 (m := mA n) x x' K₁ K₁₁ τ)ᶜ
      ≤ μ.real (S1 ∪ B1 ∪ S2 ∪ B2 ∪ S3 ∪ B3 ∪ P1 ∪ P2) := measureReal_mono hsub
    _ ≤ μ.real S1 + μ.real B1 + μ.real S2 + μ.real B2 + μ.real S3 + μ.real B3 + μ.real P1 +
        μ.real P2 := by
        have := hu (S1 ∪ B1 ∪ S2 ∪ B2 ∪ S3 ∪ B3 ∪ P1) P2
        have := hu (S1 ∪ B1 ∪ S2 ∪ B2 ∪ S3 ∪ B3) P1
        have := hu (S1 ∪ B1 ∪ S2 ∪ B2 ∪ S3) B3
        have := hu (S1 ∪ B1 ∪ S2 ∪ B2) S3
        have := hu (S1 ∪ B1 ∪ S2) B2
        have := hu (S1 ∪ B1) S2
        have := hu S1 B1
        linarith
    _ ≤ 3 * exp (-2 * η ^ 2 * (mA n : ℕ)) + 5 * exp (-τ) := by linarith

end pair2

section pair3
variable {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
  (hc : (x ⬝ᵥ x') ^ 2 < 1)
include hx hx' hc

/-- **The E block of Lemma TI (TI-lite form), one statement under `nuA`**: with
`K₁ = m(1/2 + η)`, `K₁₁ = m(κ̇(c₊)/2 + η)`, `K₂ = m(κ̇(c₁⁺)/2 + η)` (`c₁⁺ = s3c1 n τ (x·x')`),
`ℓ = √γ(√K₁ + √n + √(2τ))`, `L₁₁ = γ(√K₁₁ + √n + √(2τ))²`, `π₁ = √γ(√2 + √n + √(2τ))`,
`υ = √(2τ)`: `Pr(‖P_E Jᵀ J' P_E‖ > e3_bound n K₂ υ ℓ L₁₁ π₁) ≤ 12e^{−τ} + 4e^{−2η²m}`. The
left side is exactly the `KE` hypothesis of `ms_opN` with `J = jac A₁ A₂ x`, `J' = jac A₁ A₂ x'`. -/
theorem e4_Eblock (hn : 1 ≤ n) {cp η τ : ℝ} (hcp : x ⬝ᵥ x' ≤ cp) (hcp1 : cp ≤ 1)
    (hη : 0 ≤ η) (hτ : 0 ≤ τ)
    (ham : 0 < s3am n τ) (hdm : 0 ≤ s3dm n τ (x ⬝ᵥ x'))
    (h6 : s3dm n τ (x ⬝ᵥ x') ^ 2 ≤ 2 * s3ap n τ ^ 2) (hc1 : s3c1 n τ (x ⬝ᵥ x') ≤ 1) :
    (BstLean.Part153.nuA n).real {θ |
      e3_bound n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n τ (x ⬝ᵥ x')) / 2 + η)) (√(2 * τ))
        (e4_b n (((mA n : ℕ) : ℝ) * (1 / 2 + η)) τ)
        (e4_b n (((mA n : ℕ) : ℝ) * (kdot cp / 2 + η)) τ ^ 2) (e4_b n 2 τ) <
      opN (PEm x x' * ((jac θ.1 θ.2 x)ᵀ * jac θ.1 θ.2 x') * PEm x x')} ≤
      12 * exp (-τ) + 4 * exp (-2 * η ^ 2 * (mA n : ℕ)) := by
  classical
  have hP1 : IsProbabilityMeasure (gaussMat (mA n) n (2 / (n : ℝ))) := by
    unfold gaussMat; infer_instance
  have hP2 : IsProbabilityMeasure (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) := by
    unfold gaussMat; infer_instance
  set K₁ := ((mA n : ℕ) : ℝ) * (1 / 2 + η)
  set K₁₁ := ((mA n : ℕ) : ℝ) * (kdot cp / 2 + η)
  set K₂ := ((mA n : ℕ) : ℝ) * (kdot (s3c1 n τ (x ⬝ᵥ x')) / 2 + η)
  set G₁ := e4_G1 (m := mA n) x x' K₁ K₁₁ τ
  have hG₁m : MeasurableSet G₁ := e4_measurableSet_G1 x x' K₁ K₁₁ τ
  have hm : 0 < mA n := by unfold mA; positivity
  set bd := e3_bound n K₂ (√(2 * τ)) (e4_b n K₁ τ) (e4_b n K₁₁ τ ^ 2) (e4_b n 2 τ)
  have hPE : ∀ J J' : Matrix (Fin (mA n)) (Fin n) ℝ,
      PEm x x' * (Jᵀ * J') * PEm x x' = (J * PEm x x')ᵀ * (J' * PEm x x') := by
    intro J J'
    rw [Matrix.transpose_mul, e4_PEm_symm]; simp only [Matrix.mul_assoc]
  have hsub : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      bd < opN (PEm x x' * ((jac θ.1 θ.2 x)ᵀ * jac θ.1 θ.2 x') * PEm x x')} ⊆
      ((G₁ᶜ ×ˢ Set.univ) ∪ {θ | K₂ < cnt2 x x' θ}) ∪
        {θ | θ.1 ∈ G₁ ∧ cnt2 x x' θ ≤ K₂ ∧
          bd < opN ((jac θ.1 θ.2 x * PEm x x')ᵀ * (jac θ.1 θ.2 x' * PEm x x'))} := by
    intro θ hθ
    simp only [Set.mem_setOf_eq, hPE] at hθ
    by_cases h1 : θ.1 ∈ G₁
    · by_cases h2 : cnt2 x x' θ ≤ K₂
      · right; exact ⟨h1, h2, hθ⟩
      · left; right; exact not_le.mp h2
    · left; left; exact ⟨h1, Set.mem_univ _⟩
  have hprod : (BstLean.Part153.nuA n).real (G₁ᶜ ×ˢ Set.univ) =
      (gaussMat (mA n) n (2 / (n : ℝ))).real G₁ᶜ := by
    unfold BstLean.Part153.nuA
    rw [Measure.real, Measure.prod_prod, measure_univ, mul_one]
    rfl
  have tG := e4_G1_charge hx hx' hc hn hcp hcp1 hη hτ
  have tM : (BstLean.Part153.nuA n).real {θ | K₂ < cnt2 x x' θ} ≤
      5 * exp (-τ) + exp (-2 * η ^ 2 * (mA n : ℕ)) :=
    mask_second_tail hn hx hx' hτ hη ham hdm h6 hc1
  have tJ := e3_joint x x' (PEm x x') (ℓ := e4_b n K₁ τ) (L11 := e4_b n K₁₁ τ ^ 2)
    (π₁ := e4_b n 2 τ) (K := K₂) (υ := √(2 * τ)) (by unfold e4_b; positivity)
    (by unfold e4_b; positivity) (Real.sqrt_nonneg _) hm G₁ hG₁m
    (fun A hA => e4_good_of_G1 x x' K₁ K₁₁ τ hA)
  have e2 : -(√(2 * τ)) ^ 2 / 2 = -τ := by rw [Real.sq_sqrt (by linarith)]; ring
  rw [e2] at tJ
  calc _ ≤ (BstLean.Part153.nuA n).real (((G₁ᶜ ×ˢ Set.univ) ∪ {θ | K₂ < cnt2 x x' θ}) ∪
        {θ | θ.1 ∈ G₁ ∧ cnt2 x x' θ ≤ K₂ ∧
          bd < opN ((jac θ.1 θ.2 x * PEm x x')ᵀ * (jac θ.1 θ.2 x' * PEm x x'))}) :=
        measureReal_mono hsub
    _ ≤ (BstLean.Part153.nuA n).real (G₁ᶜ ×ˢ Set.univ) +
        (BstLean.Part153.nuA n).real {θ | K₂ < cnt2 x x' θ} +
        (BstLean.Part153.nuA n).real {θ | θ.1 ∈ G₁ ∧ cnt2 x x' θ ≤ K₂ ∧
          bd < opN ((jac θ.1 θ.2 x * PEm x x')ᵀ * (jac θ.1 θ.2 x' * PEm x x'))} := by
        have a1 := measureReal_union_le (μ := BstLean.Part153.nuA n)
          ((G₁ᶜ ×ˢ Set.univ) ∪ {θ | K₂ < cnt2 x x' θ})
          {θ | θ.1 ∈ G₁ ∧ cnt2 x x' θ ≤ K₂ ∧
            bd < opN ((jac θ.1 θ.2 x * PEm x x')ᵀ * (jac θ.1 θ.2 x' * PEm x x'))}
        have a2 := measureReal_union_le (μ := BstLean.Part153.nuA n)
          (G₁ᶜ ×ˢ Set.univ) {θ | K₂ < cnt2 x x' θ}
        linarith
    _ ≤ 12 * exp (-τ) + 4 * exp (-2 * η ^ 2 * (mA n : ℕ)) := by
        rw [hprod]; linarith

end pair3

end BstLean.Part182

open BstLean.Part182 in
#print axioms e4_pi1_tail
open BstLean.Part182 in
#print axioms e4_pi2_tail
open BstLean.Part182 in
#print axioms e4_G1_charge
open BstLean.Part182 in
#print axioms e4_Eblock
