import BstLean.Part246RowGram
import BstLean.Part244EDet

/-! Part 244: **the sharp E block at a fixed first layer** (Lemma `t7:p04:ti`, E block).
Four second-layer tails: two singular-value tails (Gram), `‖A₂|U₂‖`, and the projection of
`A₂|V_E` onto `S₂A₂(U₂)`. The constant is the paper's
`t K (L₁₁ + π₁²) + t r₂ ℓ² + 2 τ₁ ζ ℓ + τ₁²`, with `r₂` replaced by
the paper's `2√K(√(2n)+υ) + (√(2n)+υ)²` (exact). -/
namespace BstLean.Part246
open MeasureTheory ProbabilityTheory Real Matrix Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part152
open BstLean.Part151 (mask measurable_mask jac)
open BstLean.Part153 (projT nrm nrm_mulVec_le opN_mul_le opN_le_of_bound)
open BstLean.Part182 (e2_sel e2_sel01 bk_mask01 e3_good1 e3_proj2 e3_frame e3_opN_diag01
  e3_opN_frameT e3_opN_frame_mul e3_opN_neg e2_rank_gordon e2_pair_eq obD e4_Q e4_Q_a e4_Q_b
  e4_measurable_Q e4_Q_symm)
open BstLean.Part244 (gramDev split_proj_tail eb_Eblock_sharp e4_Q_mul_diag)

variable {n : ℕ}

/-- The sharp E-block constant (`t = 2/m`, `m = n²`). -/
noncomputable def e3s_bound (n : ℕ) (K υ ℓ L11 π₁ : ℝ) : ℝ :=
  (√(2 / ((mA n : ℕ) : ℝ)) * (√((mA n : ℕ) : ℝ) + √2 + υ) * π₁) ^ 2 +
    2 * (√(2 / ((mA n : ℕ) : ℝ)) * (√((mA n : ℕ) : ℝ) + √2 + υ) * π₁) *
      (√(2 / ((mA n : ℕ) : ℝ)) * (√2 + √(2 * (n : ℝ)) + υ)) * ℓ +
    2 / ((mA n : ℕ) : ℝ) * (2 * √K * (√(2 * (n : ℝ)) + υ) + (√(2 * (n : ℝ)) + υ) ^ 2) *
      ℓ ^ 2 +
    2 / ((mA n : ℕ) : ℝ) * K * (L11 + π₁ ^ 2)

lemma gramRad_le_R2 {K' K D N υ : ℝ} (h1 : 1 ≤ K') (hK : K' ≤ K) (hD0 : 0 ≤ D) (hD : D ≤ N)
    (hυ : 0 ≤ υ) :
    gramRad K' D υ ≤ 2 * √K * (√N + υ) + (√N + υ) ^ 2 := by
  unfold gramRad
  have hsK : √K' ≤ √K := Real.sqrt_le_sqrt hK
  have hsD : √D ≤ √N := Real.sqrt_le_sqrt hD
  have h0 : 0 ≤ √K' := Real.sqrt_nonneg _
  have h2 : 2 * √K' * (√D + υ) ≤ 2 * √K * (√N + υ) := by
    have := Real.sqrt_nonneg D
    nlinarith
  have h3 : (√D + υ) ^ 2 ≤ (√N + υ) ^ 2 := by
    have := Real.sqrt_nonneg D
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  linarith

/-- **The sharp E block at a fixed first layer.** -/
theorem e3_cond_sharp (x x' : Fin n → ℝ) (PE : Matrix (Fin n) (Fin n) ℝ) {ℓ L11 π₁ K υ : ℝ}
    (hℓ0 : 0 ≤ ℓ) (hπ0 : 0 ≤ π₁) (hυ : 0 ≤ υ) (hm : 0 < mA n)
    (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (hg : e3_good1 x x' PE ℓ L11 π₁ A₁) :
    (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) {A₂ | ∑ i, e2_sel x x' A₁ A₂ i ≤ K ∧
      e3s_bound n K υ ℓ L11 π₁ < opN ((jac A₁ A₂ x * PE)ᵀ * (jac A₁ A₂ x' * PE))} ≤
      ENNReal.ofReal (4 * exp (-υ ^ 2 / 2)) := by
  classical
  obtain ⟨hℓ, hℓ', hLL, hπ, hπ'⟩ := hg
  set a := reluV (A₁ *ᵥ x) with hadef
  set a' := reluV (A₁ *ᵥ x') with ha'def
  set L := obD (A₁ *ᵥ x) * A₁ * PE with hLd
  set L' := obD (A₁ *ᵥ x') * A₁ * PE with hL'd
  set t := 2 / ((mA n : ℕ) : ℝ) with htd
  have hv : (0 : ℝ) < t := by
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
  -- the selection and the two spanning vectors depend on `A₂ * Pm` only
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
  set zF : Matrix (Fin (mA n)) (Fin (mA n)) ℝ → (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) :=
    fun B => (Matrix.diagonal (dF B) *ᵥ (B *ᵥ a), Matrix.diagonal (dF B) *ᵥ (B *ᵥ a')) with hzF
  have hzFm : Measurable zF := by
    have hdiag : Measurable (fun B : Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
        Matrix.diagonal (dF B)) := by
      refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
      simp only [Matrix.diagonal_apply]
      split_ifs with h
      · subst h; exact (measurable_pi_apply i).comp hdFm
      · exact measurable_const
    have hmv : ∀ w : Fin (mA n) → ℝ, Measurable (fun B : Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
        Matrix.diagonal (dF B) *ᵥ (B *ᵥ w)) := by
      intro w
      have hc : Continuous (fun q : Matrix (Fin (mA n)) (Fin (mA n)) ℝ ×
          Matrix (Fin (mA n)) (Fin (mA n)) ℝ => q.1 *ᵥ (q.2 *ᵥ w)) :=
        Continuous.matrix_mulVec continuous_fst (Continuous.matrix_mulVec continuous_snd
          continuous_const)
      exact hc.measurable.comp (hdiag.prodMk measurable_id)
    exact (hmv a).prodMk (hmv a')
  -- the four tails
  have hE1 : (gaussMat (mA n) (mA n) t) {A₂ | t * gramRad (∑ i, dF (A₂ * Pm) i) r υ <
      gramDev t (dF (A₂ * Pm)) U A₂} ≤ ENNReal.ofReal (2 * exp (-υ ^ 2 / 2)) := by
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · have hE : IsEmpty (Fin r) := by rw [hr0]; infer_instance
      have he : {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ | t * gramRad (∑ i, dF (A₂ * Pm) i) r υ <
          gramDev t (dF (A₂ * Pm)) U A₂} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro A₂ hA
        simp only [mem_setOf_eq] at hA
        have h0 : gramDev t (dF (A₂ * Pm)) U A₂ = 0 := by
          unfold gramDev
          apply le_antisymm _ (opN_nonneg _)
          refine opN_le_of_bound _ le_rfl fun w => ?_
          have : w = 0 := funext fun i => isEmptyElim i
          subst this
          simp [BstLean.Part153.nrm, normSq]
        rw [h0] at hA
        exact absurd hA (not_lt.mpr (mul_nonneg hv.le (gramRad_nonneg hυ)))
      rw [he, measure_empty]; exact bot_le
    · have h := split_gram_tail (M := mA n) (k := mA n) (D := r) hrpos hv hυ Pm hPs hPi U hU hPU dF
        hdFm hd01
      rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal h
  have hE2 := e2_rank_gordon (M := mA n) hv (fun _ => (1 : ℝ)) (fun _ => Or.inr rfl) U₂ hU₂
    (K := ((mA n : ℕ) : ℝ)) (by simp) hυ
  have hE3 := split_proj_tail (M := mA n) (k := mA n) (D := r) hv hυ Pm hPs hPi U hU hPU zF hzFm
  set ζ := √t * (√2 + √(2 * (n : ℝ)) + υ) with hζd
  set τ₁ := √t * (√((mA n : ℕ) : ℝ) + √2 + υ) * π₁ with hτd
  set R2 := 2 * √K * (√(2 * (n : ℝ)) + υ) + (√(2 * (n : ℝ)) + υ) ^ 2 with hR2d
  have hsub : {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ | ∑ i, e2_sel x x' A₁ A₂ i ≤ K ∧
      e3s_bound n K υ ℓ L11 π₁ < opN ((jac A₁ A₂ x * PE)ᵀ * (jac A₁ A₂ x' * PE))} ⊆
      ({A₂ | t * gramRad (∑ i, dF (A₂ * Pm) i) r υ < gramDev t (dF (A₂ * Pm)) U A₂} ∪
      {A₂ | √t * (√((mA n : ℕ) : ℝ) + √(r₂ : ℝ) + υ) ≤
        opN (Matrix.diagonal (fun _ => (1 : ℝ)) * (A₂ * U₂))}) ∪
      {A₂ | √t * (√2 + √(r : ℝ) + υ) ≤
        opN (e4_Q (zF (A₂ * Pm)).1 (zF (A₂ * Pm)).2 * (A₂ * U))} := by
    intro A₂ hA
    obtain ⟨hK, hB⟩ := hA
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt, not_le, hdP] at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    set S := Matrix.diagonal (e2_sel x x' A₁ A₂) with hSd
    have ht0 : 0 ≤ √t := Real.sqrt_nonneg _
    -- the bound is nonnegative
    have hL110 : 0 ≤ L11 := (opN_nonneg _).trans hLL
    have hbound0 : 0 ≤ e3s_bound n K υ ℓ L11 π₁ := by
      have hK0 : 0 ≤ K := (Finset.sum_nonneg fun i _ => by
        rcases e2_sel01 x x' A₁ A₂ i with h | h <;> rw [h] <;> norm_num).trans hK
      unfold e3s_bound
      positivity
    by_cases htr : ∑ i, e2_sel x x' A₁ A₂ i = 0
    · -- no active rows: the product vanishes
      have hS0 : S = 0 := by
        have hall : ∀ i, e2_sel x x' A₁ A₂ i = 0 := by
          have hnn : ∀ i ∈ Finset.univ, 0 ≤ e2_sel x x' A₁ A₂ i := fun i _ => by
            rcases e2_sel01 x x' A₁ A₂ i with h | h <;> rw [h] <;> norm_num
          intro i
          exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 htr i (Finset.mem_univ i)
        rw [hSd, show e2_sel x x' A₁ A₂ = 0 from funext hall]
        ext i j; simp [Matrix.diagonal]
      have hz : (jac A₁ A₂ x * PE)ᵀ * (jac A₁ A₂ x' * PE) = 0 := by
        rw [e2_pair_eq, ← hSd, hS0]; simp
      rw [hz] at hB
      have : opN (0 : Matrix (Fin n) (Fin n) ℝ) = 0 :=
        le_antisymm (opN_le_of_bound _ le_rfl fun w => by simp [BstLean.Part153.nrm, normSq])
          (opN_nonneg _)
      linarith
    have htr1 : 1 ≤ ∑ i, e2_sel x x' A₁ A₂ i := by
      have hnat : ∀ i, e2_sel x x' A₁ A₂ i = (if e2_sel x x' A₁ A₂ i = 1 then (1 : ℝ) else 0) := by
        intro i; rcases e2_sel01 x x' A₁ A₂ i with h | h <;> simp [h]
      rw [Finset.sum_congr rfl fun i _ => hnat i] at htr ⊢
      rw [Finset.sum_boole] at htr ⊢
      have : (Finset.univ.filter fun i => e2_sel x x' A₁ A₂ i = 1).card ≠ 0 := by
        intro h0; apply htr; rw [h0]; simp
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
    -- the norm bounds of the TI-lite proof
    have hA2 : opN (A₂ * U₂) ≤ √t * (√((mA n : ℕ) : ℝ) + √2 + υ) := by
      have h3' : opN (A₂ * U₂) ≤ opN (Matrix.diagonal (fun _ : Fin (mA n) => (1 : ℝ)) * (A₂ * U₂)) := by
        have e1 : Matrix.diagonal (fun _ : Fin (mA n) => (1 : ℝ)) * (A₂ * U₂) = A₂ * U₂ := by
          ext i j; simp [Matrix.diagonal_mul]
        rw [e1]
      refine h3'.trans (h2.le.trans (mul_le_mul_of_nonneg_left ?_ ht0))
      have : √(r₂ : ℝ) ≤ √2 := Real.sqrt_le_sqrt (by exact_mod_cast hr₂)
      linarith
    have hS1 : opN S ≤ 1 := e3_opN_diag01 _ (e2_sel01 x x' A₁ A₂)
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
        opN (S * A₂ * (Pm * M)) ≤ τ₁ := by
      intro M hM
      have e : S * A₂ * (Pm * M) = S * ((A₂ * U₂) * (U₂ᵀ * M)) := by
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
    -- the rank-two projection and its properties
    set z₁ := S *ᵥ (A₂ *ᵥ a) with hz₁
    set z₂ := S *ᵥ (A₂ *ᵥ a') with hz₂
    have hzF : zF (A₂ * Pm) = (z₁, z₂) := by
      simp only [hzF, hdP, ← Matrix.mulVec_mulVec, ha, ha', hz₁, hz₂, hSd]
    rw [hzF] at h3
    set Q := e4_Q z₁ z₂ with hQd
    have hSidem : ∀ w, S *ᵥ (S *ᵥ w) = S *ᵥ w := by
      intro w
      rw [Matrix.mulVec_mulVec, hSd, Matrix.diagonal_mul_diagonal]
      congr 2
      funext i
      rcases e2_sel01 x x' A₁ A₂ i with h | h <;> simp [h]
    have hQS : Q * S = Q := e4_Q_mul_diag _ z₁ z₂ (hSidem _) (hSidem _)
    have hQN : opN (Q * (S * A₂ * U)) ≤ ζ := by
      have e : Q * (S * A₂ * U) = Q * (A₂ * U) := by
        rw [Matrix.mul_assoc S, ← Matrix.mul_assoc Q, hQS]
      rw [e]
      refine h3.le.trans (mul_le_mul_of_nonneg_left ?_ ht0)
      have := Real.sqrt_le_sqrt hr'
      linarith
    have hQfix : ∀ c₀ c₁ : ℝ, Q *ᵥ (c₀ • z₁ + c₁ • z₂) = c₀ • z₁ + c₁ • z₂ := by
      intro c₀ c₁
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hQd, e4_Q_a, e4_Q_b]
    have hQT0 : Q * (S * A₂ * U₂) = S * A₂ * U₂ := by
      refine Matrix.ext_of_mulVec_single fun j => ?_
      rw [← Matrix.mulVec_mulVec]
      obtain ⟨c₀, c₁, hc⟩ := hsp (Pi.single j 1)
      have e : (S * A₂ * U₂) *ᵥ Pi.single j 1 = c₀ • z₁ + c₁ • z₂ := by
        rw [show (S * A₂ * U₂) *ᵥ Pi.single j 1 = S *ᵥ (A₂ *ᵥ (U₂ *ᵥ Pi.single j 1)) by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc], hc]
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hz₁, hz₂]
      rw [e, hQfix]
    have hQT : ∀ M : Matrix (Fin (mA n)) (Fin n) ℝ, Q * (S * A₂ * (Pm * M)) = S * A₂ * (Pm * M) := by
      intro M
      have e : S * A₂ * (Pm * M) = (S * A₂ * U₂) * (U₂ᵀ * M) := by
        simp only [hPmd, Matrix.mul_assoc]
      rw [e, ← Matrix.mul_assoc, hQT0]
    -- the Gram deviation
    have hgram : opN ((S * A₂ * U)ᵀ * (S * A₂ * U) -
        (t * ∑ i, e2_sel x x' A₁ A₂ i) • (1 : Matrix (Fin r) (Fin r) ℝ)) ≤ t * R2 := by
      have h1' := h1
      unfold gramDev at h1'
      have e : S * A₂ * U = Matrix.diagonal (e2_sel x x' A₁ A₂) * (A₂ * U) := by
        rw [hSd, Matrix.mul_assoc]
      rw [e]
      refine h1'.trans (mul_le_mul_of_nonneg_left ?_ hv.le)
      exact gramRad_le_R2 htr1 hK (Nat.cast_nonneg r) hr' hυ
    have hc0 : 0 ≤ t * ∑ i, e2_sel x x' A₁ A₂ i := by positivity
    have hsplit : ∀ L₀ : Matrix (Fin (mA n)) (Fin n) ℝ, U * Uᵀ * ((1 - Pm) * L₀) = (1 - Pm) * L₀ →
        S * A₂ * L₀ = S * A₂ * (Pm * L₀) + (S * A₂ * U) * (Uᵀ * ((1 - Pm) * L₀)) := by
      intro L₀ h
      have e1 : (S * A₂ * U) * (Uᵀ * ((1 - Pm) * L₀)) = S * A₂ * ((1 - Pm) * L₀) := by
        have e0 : (S * A₂ * U) * (Uᵀ * ((1 - Pm) * L₀)) = S * A₂ * (U * Uᵀ * ((1 - Pm) * L₀)) := by
          simp only [Matrix.mul_assoc]
        rw [e0, h]
      rw [e1, ← Matrix.mul_add, ← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
    have hpair : (jac A₁ A₂ x * PE)ᵀ * (jac A₁ A₂ x' * PE) =
        (S * A₂ * (Pm * L) + (S * A₂ * U) * (Uᵀ * ((1 - Pm) * L)))ᵀ *
          (S * A₂ * (Pm * L') + (S * A₂ * U) * (Uᵀ * ((1 - Pm) * L'))) := by
      rw [e2_pair_eq, ← hSd, ← hLd, ← hL'd, ← hsplit L hUL2.1, ← hsplit L' hUL2.2]
    have hdet := eb_Eblock_sharp (S * A₂ * (Pm * L)) (S * A₂ * (Pm * L')) (S * A₂ * U)
      (Uᵀ * ((1 - Pm) * L)) (Uᵀ * ((1 - Pm) * L')) Q (by rw [hQd]; exact e4_Q_symm _ _)
      (hQT L) (hQT L') hc0 (hTgen L hU2L) (hTgen L' hU2L') hQN (hLgen L hℓ) (hLgen L' hℓ')
      hgram hLL'
    rw [hpair] at hB
    have hfin : τ₁ ^ 2 + 2 * τ₁ * ζ * ℓ + t * R2 * ℓ ^ 2 +
        (t * ∑ i, e2_sel x x' A₁ A₂ i) * (L11 + π₁ ^ 2) ≤ e3s_bound n K υ ℓ L11 π₁ := by
      have hl0 : 0 ≤ L11 + π₁ ^ 2 := by positivity
      have h4 : (t * ∑ i, e2_sel x x' A₁ A₂ i) * (L11 + π₁ ^ 2) ≤ t * K * (L11 + π₁ ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK hv.le) hl0
      have eb : e3s_bound n K υ ℓ L11 π₁ =
          τ₁ ^ 2 + 2 * τ₁ * ζ * ℓ + t * R2 * ℓ ^ 2 + t * K * (L11 + π₁ ^ 2) := by
        rw [e3s_bound]
      rw [eb]
      linarith
    linarith
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
        (add_le_add hE1 hE2)) hE3)
    _ = ENNReal.ofReal (4 * exp (-υ ^ 2 / 2)) := by
        rw [← ENNReal.ofReal_add (by positivity) (exp_pos _).le,
          ← ENNReal.ofReal_add (by positivity) (exp_pos _).le]
        ring_nf

end BstLean.Part246
