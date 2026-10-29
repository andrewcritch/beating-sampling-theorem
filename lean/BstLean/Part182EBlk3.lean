import BstLean.Part182EBlk2

/-!
# Part 182 (file `EBlk3`): the E block of Lemma TI as one probabilistic statement (TI-lite)

No proof is left open; no `native_decide` or `axiom` is used.

* `e3_frame`: an orthonormal frame `U` (`r ≤ #columns`, `UᵀU = 1`) of the column span of any matrix
  `W`, with `UUᵀW = W` and `U = W X` (from `stdOrthonormalBasis` of the span).
* `e3_proj2`: the projection `Pm = U₂U₂ᵀ` onto `span(a, a')` (`r₂ ≤ 2`).
* `e3_opN_diag01`, `e3_opN_frame`, `e3_opN_frameT`, `e3_opN_neg`, `e3_opN_frame_mul`: operator-norm
  facts.
* `e3_bound n K υ ℓ L₁₁ π₁ = σ²(ℓ² + L₁₁ + π₁²)/2 + 2τ₁σℓ + τ₁²`, `σ = √t(√K + √(2n) + υ)`,
  `τ₁ = √t(√m + √2 + υ)·π₁`, `t = 2/m`.
* `e3_good1`: the first-layer conditions at a fixed `A₁` (`‖L‖, ‖L'‖ ≤ ℓ`, `‖LᵀL'‖ ≤ L₁₁`, and
  `|Lᵀu|, |L'ᵀu| ≤ π₁|u|` on `span(a, a')`), `L = D₁A₁P_E`, `L' = D₁'A₁P_E`.
* **`e3_cond`**: at a fixed `A₁` in `e3_good1`, under `A₂ ~ gaussMat m m t`:
  `Pr(tr S₂ ≤ K ∧ opN((J_xP_E)ᵀ(J_{x'}P_E)) > e3_bound) ≤ 2e^{−υ²/2}` (the frames are chosen per `A₁`;
  two Gordon tails: `𝔑 = S₂A₂U` and `A₂U₂`).
* **`e3_joint`**: the same under `nuA n` on a measurable set `G₁` of first layers in `e3_good1`.
* `e3_L_eq`, `e3_LL_le`: the links of `ℓ` and `L₁₁` to Part182Blk's `blk_ell`, `blk_L11`.
Not done here: the first-layer tail for `π₁` (projection of `L` onto `span(a, a')`).
-/

open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open BstLean.Part151 (mask measurable_mask jac)
open BstLean.Part153 (projT nrm nrm_mulVec_le opN_mul_le opN_le_of_bound)

namespace BstLean.Part182

theorem e3_frame {k : ℕ} {ι : Type*} [Fintype ι] (W : Matrix (Fin k) ι ℝ) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧ ∃ U : Matrix (Fin k) (Fin r) ℝ, ∃ X : Matrix ι (Fin r) ℝ,
      Uᵀ * U = 1 ∧ U * Uᵀ * W = W ∧ U = W * X := by
  classical
  set cols : ι → EuclideanSpace ℝ (Fin k) := fun j => WithLp.toLp 2 (fun i => W i j) with hcols
  set S := Submodule.span ℝ (Set.range cols)
  set b := stdOrthonormalBasis ℝ S
  have hr : Module.finrank ℝ S ≤ Fintype.card ι := finrank_range_le_card _
  refine ⟨Module.finrank ℝ S, hr, Matrix.of fun i l => ((b l : S) : EuclideanSpace ℝ (Fin k)).ofLp i, ?_⟩
  have hmem : ∀ l, ∃ c : ι → ℝ, ∑ j, c j • cols j = ((b l : S) : EuclideanSpace ℝ (Fin k)) :=
    fun l => (Submodule.mem_span_range_iff_exists_fun ℝ).1 (b l).2
  choose c hc using hmem
  refine ⟨Matrix.of fun j l => c l j, ?_, ?_, ?_⟩
  · ext l l'
    have h := b.orthonormal
    rw [orthonormal_iff_ite] at h
    have h2 := h l l'
    rw [Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct] at h2
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
    rw [← h2]
    simp only [dotProduct, star_trivial]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · ext i j
    have hw : cols j ∈ S := Submodule.subset_span ⟨j, rfl⟩
    have h := b.sum_repr' (⟨cols j, hw⟩ : S)
    have h2 := congrArg (fun z : S => ((z : EuclideanSpace ℝ (Fin k)).ofLp i)) h
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner, WithLp.ofLp_sum,
      WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      EuclideanSpace.inner_eq_star_dotProduct, hcols] at h2
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    rw [← h2]
    simp only [dotProduct, star_trivial, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    refine Finset.sum_congr rfl fun j' _ => ?_
    ring
  · ext i l
    have h2 := congrArg (fun z : EuclideanSpace ℝ (Fin k) => z.ofLp i) (hc l)
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      hcols] at h2
    simp only [Matrix.mul_apply, Matrix.of_apply]
    rw [← h2]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _


lemma e3_opN_diag01 {p : ℕ} (d : Fin p → ℝ) (hd : ∀ i, d i = 0 ∨ d i = 1) :
    opN (Matrix.diagonal d) ≤ 1 := by
  refine opN_le_of_bound _ zero_le_one fun v => ?_
  rw [one_mul]
  unfold nrm normSq
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  rw [Matrix.mulVec_diagonal]
  rcases hd i with h | h <;> simp [h, sq_nonneg]

lemma e3_opN_frame {k r : ℕ} (U : Matrix (Fin k) (Fin r) ℝ) (hU : Uᵀ * U = 1) : opN U ≤ 1 := by
  refine opN_le_of_bound _ zero_le_one fun v => ?_
  rw [one_mul]
  unfold nrm
  refine le_of_eq (congrArg Real.sqrt ?_)
  have h : normSq (U *ᵥ v) = (U *ᵥ v) ⬝ᵥ (U *ᵥ v) := by
    unfold normSq dotProduct; simp [sq]
  have h2 : (U *ᵥ v) ⬝ᵥ (U *ᵥ v) = v ⬝ᵥ ((Uᵀ * U) *ᵥ v) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  rw [h, h2, hU, Matrix.one_mulVec]
  unfold normSq dotProduct; simp [sq]

lemma e3_opN_frameT {k r : ℕ} (U : Matrix (Fin k) (Fin r) ℝ) (hU : Uᵀ * U = 1) : opN Uᵀ ≤ 1 := by
  rw [BstLean.Part153.opN_transpose]; exact e3_opN_frame U hU

/-- The `m × 2` matrix with columns `a`, `a'`. -/
def e3_W2 {m : ℕ} (a a' : Fin m → ℝ) : Matrix (Fin m) (Fin 2) ℝ :=
  Matrix.of fun i j => ![a i, a' i] j

lemma e3_W2_mulVec {m : ℕ} (a a' : Fin m → ℝ) (c : Fin 2 → ℝ) :
    e3_W2 a a' *ᵥ c = c 0 • a + c 1 • a' := by
  ext i
  simp [e3_W2, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]

/-- **The projection onto `span(a, a')` with an orthonormal frame**. -/
lemma e3_proj2 {m : ℕ} (a a' : Fin m → ℝ) :
    ∃ r : ℕ, r ≤ 2 ∧ ∃ U₂ : Matrix (Fin m) (Fin r) ℝ, U₂ᵀ * U₂ = 1 ∧
      (U₂ * U₂ᵀ) *ᵥ a = a ∧ (U₂ * U₂ᵀ) *ᵥ a' = a' ∧
      ∀ v, ∃ c₀ c₁ : ℝ, U₂ *ᵥ v = c₀ • a + c₁ • a' := by
  obtain ⟨r, hr, U₂, X, hU, hUW, hUX⟩ := e3_frame (e3_W2 a a')
  refine ⟨r, by simpa using hr, U₂, hU, ?_, ?_, ?_⟩
  · have h := congrArg (fun M : Matrix (Fin m) (Fin 2) ℝ => M *ᵥ ![1, 0]) hUW
    simp only [← Matrix.mulVec_mulVec, e3_W2_mulVec] at h
    simpa using h
  · have h := congrArg (fun M : Matrix (Fin m) (Fin 2) ℝ => M *ᵥ ![0, 1]) hUW
    simp only [← Matrix.mulVec_mulVec, e3_W2_mulVec] at h
    simpa using h
  · intro v
    refine ⟨(X *ᵥ v) 0, (X *ᵥ v) 1, ?_⟩
    rw [hUX, ← Matrix.mulVec_mulVec, e3_W2_mulVec]

section cond

variable {n : ℕ}

lemma e3_opN_neg {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) : opN (-M) ≤ opN M := by
  refine opN_le_of_bound _ (opN_nonneg _) fun v => ?_
  have e : nrm ((-M) *ᵥ v) = nrm (M *ᵥ v) := by
    unfold nrm normSq; simp [Matrix.neg_mulVec]
  rw [e]; exact nrm_mulVec_le _ _

/-- The E-block bound `n·k_E` in the TI-lite form:
`σ²(ℓ² + L₁₁ + π₁²)/2 + 2τ₁σℓ + τ₁²` with `σ = √t(√K + √(2n) + υ)`,
`τ₁ = √t(√m + √2 + υ)·π₁`, `t = 2/m`, `m = n²`. -/
noncomputable def e3_bound (n : ℕ) (K υ ℓ L11 π₁ : ℝ) : ℝ :=
  (√(2 / ((mA n : ℕ) : ℝ)) * (√K + √(2 * (n : ℝ)) + υ)) ^ 2 * (ℓ ^ 2 + (L11 + π₁ ^ 2)) / 2 +
    2 * (√(2 / ((mA n : ℕ) : ℝ)) * (√((mA n : ℕ) : ℝ) + √2 + υ) * π₁) *
      ((√(2 / ((mA n : ℕ) : ℝ)) * (√K + √(2 * (n : ℝ)) + υ)) * ℓ) +
    (√(2 / ((mA n : ℕ) : ℝ)) * (√((mA n : ℕ) : ℝ) + √2 + υ) * π₁) ^ 2

/-- The first-layer conditions of the E block at a fixed `A₁` (with `L = D₁A₁P_E`,
`L' = D₁'A₁P_E`, `a = ReLU(A₁x)`, `a' = ReLU(A₁x')`). -/
def e3_good1 (x x' : Fin n → ℝ) (PE : Matrix (Fin n) (Fin n) ℝ) (ℓ L11 π₁ : ℝ)
    (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) : Prop :=
  opN (obD (A₁ *ᵥ x) * A₁ * PE) ≤ ℓ ∧ opN (obD (A₁ *ᵥ x') * A₁ * PE) ≤ ℓ ∧
  opN ((obD (A₁ *ᵥ x) * A₁ * PE)ᵀ * (obD (A₁ *ᵥ x') * A₁ * PE)) ≤ L11 ∧
  (∀ c₀ c₁ : ℝ, nrm ((obD (A₁ *ᵥ x) * A₁ * PE)ᵀ *ᵥ (c₀ • reluV (A₁ *ᵥ x) + c₁ • reluV (A₁ *ᵥ x'))) ≤
    π₁ * nrm (c₀ • reluV (A₁ *ᵥ x) + c₁ • reluV (A₁ *ᵥ x'))) ∧
  (∀ c₀ c₁ : ℝ, nrm ((obD (A₁ *ᵥ x') * A₁ * PE)ᵀ *ᵥ (c₀ • reluV (A₁ *ᵥ x) + c₁ • reluV (A₁ *ᵥ x'))) ≤
    π₁ * nrm (c₀ • reluV (A₁ *ᵥ x) + c₁ • reluV (A₁ *ᵥ x')))

lemma e3_opN_frame_mul {r : ℕ} (L : Matrix (Fin (mA n)) (Fin n) ℝ) (a a' : Fin (mA n) → ℝ)
    (U₂ : Matrix (Fin (mA n)) (Fin r) ℝ) (hU : U₂ᵀ * U₂ = 1)
    (hsp : ∀ v, ∃ c₀ c₁ : ℝ, U₂ *ᵥ v = c₀ • a + c₁ • a') {π₁ : ℝ} (hπ0 : 0 ≤ π₁)
    (hπ : ∀ c₀ c₁ : ℝ, nrm (Lᵀ *ᵥ (c₀ • a + c₁ • a')) ≤ π₁ * nrm (c₀ • a + c₁ • a')) :
    opN (U₂ᵀ * L) ≤ π₁ := by
  rw [← BstLean.Part153.opN_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
  refine opN_le_of_bound _ hπ0 fun v => ?_
  obtain ⟨c₀, c₁, hc⟩ := hsp v
  rw [← Matrix.mulVec_mulVec, hc]
  refine (hπ c₀ c₁).trans ?_
  rw [← hc]
  exact mul_le_mul_of_nonneg_left ((nrm_mulVec_le _ _).trans
    (by have := e3_opN_frame U₂ hU; have := BstLean.Part153.nrm_nonneg v; nlinarith)) hπ0

/-- **The E block at a fixed first layer** (TI-lite): if `A₁` satisfies the first-layer
conditions `e3_good1` (bounds `ℓ`, `L₁₁`, `π₁`), then under `A₂ ~ gaussMat m m (2/m)`:
`Pr(tr S₂ ≤ K ∧ opN((J_xP_E)ᵀ(J_{x'}P_E)) > e3_bound) ≤ 2e^{−υ²/2}` (two Gordon tails). -/
theorem e3_cond (x x' : Fin n → ℝ) (PE : Matrix (Fin n) (Fin n) ℝ) {ℓ L11 π₁ K υ : ℝ}
    (hℓ0 : 0 ≤ ℓ) (hπ0 : 0 ≤ π₁) (hυ : 0 ≤ υ) (hm : 0 < mA n)
    (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (hg : e3_good1 x x' PE ℓ L11 π₁ A₁) :
    (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) {A₂ | ∑ i, e2_sel x x' A₁ A₂ i ≤ K ∧
      e3_bound n K υ ℓ L11 π₁ < opN ((jac A₁ A₂ x * PE)ᵀ * (jac A₁ A₂ x' * PE))} ≤
      ENNReal.ofReal (2 * exp (-υ ^ 2 / 2)) := by
  classical
  obtain ⟨hℓ, hℓ', hLL, hπ, hπ'⟩ := hg
  set a := reluV (A₁ *ᵥ x) with hadef
  set a' := reluV (A₁ *ᵥ x') with ha'def
  set L := obD (A₁ *ᵥ x) * A₁ * PE with hLd
  set L' := obD (A₁ *ᵥ x') * A₁ * PE with hL'd
  have hv : (0 : ℝ) < 2 / ((mA n : ℕ) : ℝ) := by
    have : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by exact_mod_cast hm
    positivity
  obtain ⟨r₂, hr₂, U₂, hU₂, ha, ha', hsp⟩ := e3_proj2 a a'
  set Pm := U₂ * U₂ᵀ with hPmd
  have hPs : Pmᵀ = Pm := by rw [hPmd, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hPi : Pm * Pm = Pm := by
    rw [hPmd, Matrix.mul_assoc, ← Matrix.mul_assoc U₂ᵀ, hU₂, Matrix.one_mul]
  set W := Matrix.fromCols ((1 - Pm) * L) ((1 - Pm) * L') with hWd
  obtain ⟨r, hr, U, X, hU, hUW, hUX⟩ := e3_frame W
  have hr' : (r : ℝ) ≤ 2 * (n : ℝ) := by
    have : r ≤ n + n := by simpa using hr
    have : (r : ℝ) ≤ ((n + n : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  have hPW : Pm * W = 0 := by
    have h0 : Pm * (1 - Pm) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hPi, sub_self]
    rw [hWd, Matrix.mul_fromCols]
    simp only [← Matrix.mul_assoc, h0, Matrix.zero_mul]
    exact Matrix.fromCols_zero
  have hPU : Pm * U = 0 := by rw [hUX, ← Matrix.mul_assoc, hPW, Matrix.zero_mul]
  have hUL2 : U * Uᵀ * ((1 - Pm) * L) = (1 - Pm) * L ∧ U * Uᵀ * ((1 - Pm) * L') = (1 - Pm) * L' := by
    rw [hWd, Matrix.mul_fromCols] at hUW
    exact Matrix.fromCols_inj hUW
  -- the selection depends on `A₂ * Pm` only
  set dF : Matrix (Fin (mA n)) (Fin (mA n)) ℝ → Fin (mA n) → ℝ :=
    fun B i => mask ((B *ᵥ a) i) * mask ((B *ᵥ a') i) with hdF
  have hdFm : Measurable dF := by
    refine measurable_pi_iff.mpr fun i => ?_
    have h1 : Measurable (fun B : Matrix (Fin (mA n)) (Fin (mA n)) ℝ => (B *ᵥ a) i) := by
      simp only [Matrix.mulVec, dotProduct]; fun_prop
    have h2 : Measurable (fun B : Matrix (Fin (mA n)) (Fin (mA n)) ℝ => (B *ᵥ a') i) := by
      simp only [Matrix.mulVec, dotProduct]; fun_prop
    exact (measurable_mask.comp h1).mul (measurable_mask.comp h2)
  have hd01 : ∀ B i, dF B i = 0 ∨ dF B i = 1 := by
    intro B i
    simp only [hdF]
    rcases bk_mask01 ((B *ᵥ a) i) with h | h <;>
    rcases bk_mask01 ((B *ᵥ a') i) with h' | h' <;> simp [h, h']
  have hdP : ∀ A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ, dF (A₂ * Pm) = e2_sel x x' A₁ A₂ := by
    intro A₂
    funext i
    simp only [hdF, e2_sel, ← Matrix.mulVec_mulVec]
    rw [ha, ha']
  have hE1 := e2_split_gordon hv Pm hPs hPi U hU hPU dF hdFm hd01 (K := K) hυ
  have hE2 := e2_rank_gordon (M := mA n) hv (fun _ => (1 : ℝ)) (fun _ => Or.inr rfl) U₂ hU₂
    (K := ((mA n : ℕ) : ℝ)) (by simp) hυ
  set t := 2 / ((mA n : ℕ) : ℝ) with htd
  set σ := √t * (√K + √(2 * (n : ℝ)) + υ) with hσd
  set τ₁ := √t * (√((mA n : ℕ) : ℝ) + √2 + υ) * π₁ with hτd
  have hsub : {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ | ∑ i, e2_sel x x' A₁ A₂ i ≤ K ∧
      e3_bound n K υ ℓ L11 π₁ < opN ((jac A₁ A₂ x * PE)ᵀ * (jac A₁ A₂ x' * PE))} ⊆
      {A₂ | ∑ i, dF (A₂ * Pm) i ≤ K ∧ √t * (√K + √(r : ℝ) + υ) ≤
        opN (Matrix.diagonal (dF (A₂ * Pm)) * (A₂ * U))} ∪
      {A₂ | √t * (√((mA n : ℕ) : ℝ) + √(r₂ : ℝ) + υ) ≤
        opN (Matrix.diagonal (fun _ => (1 : ℝ)) * (A₂ * U₂))} := by
    intro A₂ hA
    obtain ⟨hK, hB⟩ := hA
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_and, not_le, hdP] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hN := h1 hK
    have hS1 : opN (Matrix.diagonal (e2_sel x x' A₁ A₂)) ≤ 1 :=
      e3_opN_diag01 _ (e2_sel01 x x' A₁ A₂)
    have ht0 : 0 ≤ √t := Real.sqrt_nonneg _
    have hσ0 : 0 ≤ σ := by
      rw [hσd]; exact mul_nonneg ht0 (by positivity)
    have hNσ : opN (Matrix.diagonal (e2_sel x x' A₁ A₂) * A₂ * U) ≤ σ := by
      rw [Matrix.mul_assoc]
      refine hN.le.trans ?_
      rw [hσd]
      refine mul_le_mul_of_nonneg_left ?_ ht0
      have := Real.sqrt_le_sqrt hr'
      linarith
    have hA2 : opN (A₂ * U₂) ≤ √t * (√((mA n : ℕ) : ℝ) + √2 + υ) := by
      have hd1 := e3_opN_diag01 (fun _ : Fin (mA n) => (1 : ℝ)) (fun _ => Or.inr rfl)
      have h3 : opN (A₂ * U₂) ≤ opN (Matrix.diagonal (fun _ : Fin (mA n) => (1 : ℝ)) * (A₂ * U₂)) := by
        have e1 : Matrix.diagonal (fun _ : Fin (mA n) => (1 : ℝ)) * (A₂ * U₂) = A₂ * U₂ := by
          ext i j; simp [Matrix.diagonal_mul]
        rw [e1]
      refine h3.trans (h2.le.trans (mul_le_mul_of_nonneg_left ?_ ht0))
      have : √(r₂ : ℝ) ≤ √2 := Real.sqrt_le_sqrt (by exact_mod_cast hr₂)
      linarith
    have hUP : Uᵀ * Pm = 0 := by
      have : (Pm * U)ᵀ = Uᵀ * Pm := by rw [Matrix.transpose_mul, hPs]
      rw [← this, hPU, Matrix.transpose_zero]
    have hUtP : ∀ M : Matrix (Fin (mA n)) (Fin n) ℝ, Uᵀ * ((1 - Pm) * M) = Uᵀ * M := by
      intro M
      rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hUP, sub_zero]
    have hU2L := e3_opN_frame_mul L a a' U₂ hU₂ hsp hπ0 hπ
    have hU2L' := e3_opN_frame_mul L' a a' U₂ hU₂ hsp hπ0 hπ'
    have hτ0 : 0 ≤ √t * (√((mA n : ℕ) : ℝ) + √2 + υ) := mul_nonneg ht0 (by positivity)
    have hTgen : ∀ M : Matrix (Fin (mA n)) (Fin n) ℝ, opN (U₂ᵀ * M) ≤ π₁ →
        opN (Matrix.diagonal (e2_sel x x' A₁ A₂) * A₂ * (Pm * M)) ≤ τ₁ := by
      intro M hM
      have e : Matrix.diagonal (e2_sel x x' A₁ A₂) * A₂ * (Pm * M) =
          Matrix.diagonal (e2_sel x x' A₁ A₂) * ((A₂ * U₂) * (U₂ᵀ * M)) := by
        simp only [hPmd, Matrix.mul_assoc]
      rw [e]
      refine (opN_mul_le _ _).trans ?_
      refine (mul_le_mul hS1 (opN_mul_le _ _) (opN_nonneg _) zero_le_one).trans ?_
      rw [one_mul, hτd]
      exact mul_le_mul hA2 hM (opN_nonneg _) hτ0
    have hLgen : ∀ M : Matrix (Fin (mA n)) (Fin n) ℝ, opN M ≤ ℓ →
        opN (Uᵀ * ((1 - Pm) * M)) ≤ ℓ := by
      intro M hM
      rw [hUtP]
      refine (opN_mul_le _ _).trans ?_
      have := e3_opN_frameT U hU
      nlinarith [opN_nonneg M, opN_nonneg Uᵀ]
    have hNLgen : ∀ M : Matrix (Fin (mA n)) (Fin n) ℝ, opN M ≤ ℓ →
        opN ((Matrix.diagonal (e2_sel x x' A₁ A₂) * A₂ * U) * (Uᵀ * ((1 - Pm) * M))) ≤ σ * ℓ := by
      intro M hM
      refine (opN_mul_le _ _).trans ?_
      exact mul_le_mul hNσ (hLgen M hM) (opN_nonneg _) hσ0
    have hLL' : opN ((Uᵀ * ((1 - Pm) * L))ᵀ * (Uᵀ * ((1 - Pm) * L'))) ≤ L11 + π₁ ^ 2 := by
      have hUUL : U * Uᵀ * L' = L' - Pm * L' := by
        have h := hUL2.2
        rw [Matrix.mul_assoc, hUtP, ← Matrix.mul_assoc] at h
        rw [h, Matrix.sub_mul, Matrix.one_mul]
      have e : (Uᵀ * ((1 - Pm) * L))ᵀ * (Uᵀ * ((1 - Pm) * L')) =
          Lᵀ * L' + -((U₂ᵀ * L)ᵀ * (U₂ᵀ * L')) := by
        rw [hUtP, hUtP, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
          ← Matrix.mul_assoc U, hUUL, Matrix.mul_sub, Matrix.transpose_mul, hPmd]
        simp only [Matrix.mul_assoc, sub_eq_add_neg]
        congr 2
        simp only [hLd, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      rw [e]
      refine (BstLean.Part153.opN_add_le' _ _).trans ?_
      refine add_le_add hLL ((e3_opN_neg _).trans ?_)
      refine (opN_mul_le _ _).trans ?_
      rw [BstLean.Part153.opN_transpose, sq]
      exact mul_le_mul hU2L hU2L' (opN_nonneg _) hπ0
    have hdet := e2_Eblock_det x x' A₁ A₂ PE Pm U hUL2.1 hUL2.2 (ℓ := ℓ) (L11 := L11 + π₁ ^ 2)
      (τ₁ := τ₁) (cx := σ * ℓ) (hTgen L hU2L) (hTgen L' hU2L') (hNLgen L hℓ) (hNLgen L' hℓ')
      (hLgen L hℓ) (hLgen L' hℓ') hLL'
    have hL11 : 0 ≤ ℓ ^ 2 + (L11 + π₁ ^ 2) := by
      have := (opN_nonneg _).trans hLL
      positivity
    have hfin : opN (Matrix.diagonal (e2_sel x x' A₁ A₂) * A₂ * U) ^ 2 * (ℓ ^ 2 + (L11 + π₁ ^ 2)) / 2 +
        2 * τ₁ * (σ * ℓ) + τ₁ ^ 2 ≤ e3_bound n K υ ℓ L11 π₁ := by
      have h2' : opN (Matrix.diagonal (e2_sel x x' A₁ A₂) * A₂ * U) ^ 2 ≤ σ ^ 2 :=
        pow_le_pow_left₀ (opN_nonneg _) hNσ 2
      have eb : e3_bound n K υ ℓ L11 π₁ =
          σ ^ 2 * (ℓ ^ 2 + (L11 + π₁ ^ 2)) / 2 + 2 * τ₁ * (σ * ℓ) + τ₁ ^ 2 := rfl
      rw [eb]
      have := mul_le_mul_of_nonneg_right h2' hL11
      linarith
    linarith
  have hm2 : (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) {A₂ | ∑ i, e2_sel x x' A₁ A₂ i ≤ K ∧
      e3_bound n K υ ℓ L11 π₁ < opN ((jac A₁ A₂ x * PE)ᵀ * (jac A₁ A₂ x' * PE))} ≤
      ENNReal.ofReal (exp (-υ ^ 2 / 2)) + ENNReal.ofReal (exp (-υ ^ 2 / 2)) :=
    (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add hE1 hE2))
  refine hm2.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (exp_pos _).le (exp_pos _).le]
  ring_nf
lemma e3_measurable_jac (x : Fin n → ℝ) :
    Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
      jac θ.1 θ.2 x) := by
  refine measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun l => ?_
  simp only [jac, Matrix.of_apply, Matrix.mulVec, dotProduct, reluV, relu]
  have hmask := measurable_mask
  fun_prop

lemma e3_measurable_pair (x x' : Fin n → ℝ) (PE : Matrix (Fin n) (Fin n) ℝ) :
    Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
      opN ((jac θ.1 θ.2 x * PE)ᵀ * (jac θ.1 θ.2 x' * PE))) := by
  have hc : Continuous (fun z : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin n) ℝ =>
      opN ((z.1 * PE)ᵀ * (z.2 * PE))) :=
    opN_continuous.comp ((continuous_fst.matrix_mul continuous_const).matrix_transpose.matrix_mul
      (continuous_snd.matrix_mul continuous_const))
  have h := hc.measurable.comp ((e3_measurable_jac (n := n) x).prodMk (e3_measurable_jac x'))
  simpa only [Function.comp_def] using h

/-- **The E block of Lemma TI under the joint Agent distribution** (TI-lite): for a measurable set
`G₁` of first layers on which `e3_good1` holds,
`Pr_{nuA}(A₁ ∈ G₁ ∧ tr S₂ ≤ K ∧ opN((J_xP_E)ᵀ(J_{x'}P_E)) > e3_bound) ≤ 2e^{−υ²/2}`. -/
theorem e3_joint (x x' : Fin n → ℝ) (PE : Matrix (Fin n) (Fin n) ℝ) {ℓ L11 π₁ K υ : ℝ}
    (hℓ0 : 0 ≤ ℓ) (hπ0 : 0 ≤ π₁) (hυ : 0 ≤ υ) (hm : 0 < mA n)
    (G₁ : Set (Matrix (Fin (mA n)) (Fin n) ℝ)) (hG₁ : MeasurableSet G₁)
    (hG : ∀ A₁ ∈ G₁, e3_good1 x x' PE ℓ L11 π₁ A₁) :
    (BstLean.Part153.nuA n).real {θ | θ.1 ∈ G₁ ∧ cnt2 x x' θ ≤ K ∧
      e3_bound n K υ ℓ L11 π₁ < opN ((jac θ.1 θ.2 x * PE)ᵀ * (jac θ.1 θ.2 x' * PE))} ≤
      2 * exp (-υ ^ 2 / 2) := by
  classical
  have hP1 : IsProbabilityMeasure (gaussMat (mA n) n (2 / (n : ℝ))) := by
    unfold gaussMat; infer_instance
  have hP2 : IsProbabilityMeasure (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) := by
    unfold gaussMat; infer_instance
  set S := {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      θ.1 ∈ G₁ ∧ cnt2 x x' θ ≤ K ∧
      e3_bound n K υ ℓ L11 π₁ < opN ((jac θ.1 θ.2 x * PE)ᵀ * (jac θ.1 θ.2 x' * PE))} with hSd
  have hSm : MeasurableSet S :=
    (measurable_fst hG₁).inter ((measurableSet_le (measurable_cnt2 x x') measurable_const).inter
      (measurableSet_lt measurable_const (e3_measurable_pair x x' PE)))
  have hB : 0 ≤ 2 * exp (-υ ^ 2 / 2) := by positivity
  rw [Measure.real]
  unfold BstLean.Part153.nuA
  rw [Measure.prod_apply hSm]
  have hle : ∀ A₁, (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) (Prod.mk A₁ ⁻¹' S) ≤
      ENNReal.ofReal (2 * exp (-υ ^ 2 / 2)) := by
    intro A₁
    by_cases hA : A₁ ∈ G₁
    · have e : Prod.mk A₁ ⁻¹' S = {A₂ | ∑ i, e2_sel x x' A₁ A₂ i ≤ K ∧
          e3_bound n K υ ℓ L11 π₁ < opN ((jac A₁ A₂ x * PE)ᵀ * (jac A₁ A₂ x' * PE))} := by
        ext A₂
        simp only [hSd, Set.mem_preimage, Set.mem_setOf_eq]
        constructor
        · intro h; exact ⟨h.2.1, h.2.2⟩
        · intro h; exact ⟨hA, h.1, h.2⟩
      rw [e]
      exact e3_cond x x' PE hℓ0 hπ0 hυ hm A₁ (hG A₁ hA)
    · have e : Prod.mk A₁ ⁻¹' S = ∅ := by
        ext A₂
        simp only [hSd, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h; exact hA h.1
      rw [e, measure_empty]; exact bot_le
  calc (∫⁻ A₁, (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) (Prod.mk A₁ ⁻¹' S)
        ∂gaussMat (mA n) n (2 / (n : ℝ))).toReal
      ≤ (∫⁻ _A₁, ENNReal.ofReal (2 * exp (-υ ^ 2 / 2)) ∂gaussMat (mA n) n (2 / (n : ℝ))).toReal :=
        ENNReal.toReal_mono (by rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.ofReal_ne_top)
          (lintegral_mono hle)
    _ = 2 * exp (-υ ^ 2 / 2) := by
        rw [lintegral_const, measure_univ, mul_one, ENNReal.toReal_ofReal hB]
/-- `L = D₁A₁P_E` is the masked matrix of Part182Blk (`blk_ell`), up to associativity. -/
lemma e3_L_eq (x : Fin n → ℝ) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (PE : Matrix (Fin n) (Fin n) ℝ) :
    obD (A₁ *ᵥ x) * A₁ * PE = Matrix.diagonal (fun i => mask ((A₁ *ᵥ x) i)) * (A₁ * PE) := by
  rw [Matrix.mul_assoc]; rfl

/-- `‖LᵀL'‖ ≤ ‖D₁D₁'A₁P_E‖²` (the paper's `L₁₁`, bounded by `blk_L11`). -/
lemma e3_LL_le (x x' : Fin n → ℝ) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (PE : Matrix (Fin n) (Fin n) ℝ) :
    opN ((obD (A₁ *ᵥ x) * A₁ * PE)ᵀ * (obD (A₁ *ᵥ x') * A₁ * PE)) ≤
      opN (Matrix.diagonal (fun i => mask ((A₁ *ᵥ x) i) * mask ((A₁ *ᵥ x') i)) * (A₁ * PE)) ^ 2 := by
  set N := Matrix.diagonal (fun i => mask ((A₁ *ᵥ x) i) * mask ((A₁ *ᵥ x') i)) * (A₁ * PE)
  have e : (obD (A₁ *ᵥ x) * A₁ * PE)ᵀ * (obD (A₁ *ᵥ x') * A₁ * PE) = Nᵀ * N := by
    have hd : (obD (A₁ *ᵥ x))ᵀ * obD (A₁ *ᵥ x') =
        (Matrix.diagonal (fun i => mask ((A₁ *ᵥ x) i) * mask ((A₁ *ᵥ x') i)))ᵀ *
          Matrix.diagonal (fun i => mask ((A₁ *ᵥ x) i) * mask ((A₁ *ᵥ x') i)) := by
      simp only [obD, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
      congr 1; funext i
      rcases bk_mask01 ((A₁ *ᵥ x) i) with h | h <;>
      rcases bk_mask01 ((A₁ *ᵥ x') i) with h' | h' <;> simp [h, h']
    simp only [N, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (obD (A₁ *ᵥ x))ᵀ, hd]
    simp only [Matrix.mul_assoc]
  rw [e]
  refine (opN_mul_le _ _).trans ?_
  rw [BstLean.Part153.opN_transpose, sq]

end cond

end BstLean.Part182

open BstLean.Part182 in
#print axioms e3_frame
open BstLean.Part182 in
#print axioms e3_cond
open BstLean.Part182 in
#print axioms e3_joint
open BstLean.Part182 in
#print axioms e3_LL_le
