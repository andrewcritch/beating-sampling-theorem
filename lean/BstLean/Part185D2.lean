import BstLean.Part185D1
import BstLean.Part182EBlk3

/-!
# Part 185 (file `D2`): the two-sided E block of Lemma TI at a fixed first layer

No proof is left open; no `native_decide` or `axiom` is used.

* `d2_two_sided_opN`: if `lo|z|² ≤ |𝔑z|² ≤ hi|z|²` then
  `‖𝔏ᵀ𝔑ᵀ𝔑𝔏'‖ ≤ ((hi + lo)/2)L₁₁ + ((hi − lo)/2)ℓ²` (`‖𝔏‖, ‖𝔏'‖ ≤ ℓ`, `‖𝔏ᵀ𝔏'‖ ≤ L₁₁`).
* `d2_Eblock`, `d2_Eblock_det`: the deterministic assemblies of Part 182 with this main term.
* `d2_net_mono`: `(2⌈√r/ε⌉ + 1)^r ≤ (2⌈√R/ε⌉ + 1)^R` for `r ≤ R`.
* `e3_bound2 n K Klo υ ℓ L₁₁ π₁ δ ε = ((hi + lo)/2)(L₁₁ + π₁²) + ((hi − lo)/2)ℓ² + 2τ₁σℓ + τ₁²`,
  `σ = √t(√K + √(2n) + υ)`, `hi = σ²`, `lo = (√((1 − δ)tK_lo)(1 − ε) − σε)²`.
* **`d2_cond`**: at a fixed `A₁` in `e3_good1`, under `A₂ ~ gaussMat m m t`:
  `Pr(K_lo ≤ tr S₂ ≤ K ∧ opN((J_xP_E)ᵀ(J_{x'}P_E)) > e3_bound2) ≤ 3e^{−υ²/2} + net`,
  `net = (2⌈√(2n)/ε⌉ + 1)^{2n} e^{−K_lo δ²/4}`.
* **`d2_joint`**: the same under `nuA n` on a measurable set `G₁` of first layers in `e3_good1`.
-/

open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open BstLean.Part151 (mask measurable_mask jac)
open BstLean.Part153 (projT nrm nrm_mulVec_le opN_mul_le opN_le_of_bound)
open BstLean.Part182
open BstLean.Part184 (gridN gram_two_sided)

namespace BstLean.Part185

/-- **The two-sided E-block main term.** -/
theorem d2_two_sided_opN {r q a a' : ℕ} (Nm : Matrix (Fin r) (Fin q) ℝ)
    (L : Matrix (Fin q) (Fin a) ℝ) (L' : Matrix (Fin q) (Fin a') ℝ) {ℓ L11 lo hi : ℝ}
    (hL : opN L ≤ ℓ) (hL' : opN L' ≤ ℓ) (hLL : opN (Lᵀ * L') ≤ L11)
    (hlo : ∀ z, lo * normSq z ≤ normSq (Nm *ᵥ z)) (hhi : ∀ z, normSq (Nm *ᵥ z) ≤ hi * normSq z)
    (hlo0 : 0 ≤ lo) (hlohi : lo ≤ hi) :
    opN (Lᵀ * (Nmᵀ * Nm) * L') ≤ (hi + lo) / 2 * L11 + (hi - lo) / 2 * ℓ ^ 2 := by
  have hℓ : 0 ≤ ℓ := (opN_nonneg L).trans hL
  have hL110 : 0 ≤ L11 := (opN_nonneg _).trans hLL
  refine eb_opN_le_of_bil _ (by nlinarith) fun u w hu hw => ?_
  have e : u ⬝ᵥ (Lᵀ * (Nmᵀ * Nm) * L') *ᵥ w = (Nm *ᵥ (L *ᵥ u)) ⬝ᵥ (Nm *ᵥ (L' *ᵥ w)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, eb_dot_transpose_mulVec,
      ← Matrix.mulVec_mulVec, eb_dot_transpose_mulVec]
  rw [e]
  have hG := gram_two_sided Nm hlo hhi (L *ᵥ u) (L' *ᵥ w)
  have hnu : normSq u = 1 := hu
  have hnw : normSq w = 1 := hw
  have hX : √(normSq (L *ᵥ u)) ≤ ℓ := by
    have := eb_normSq_mulVec_le L u
    rw [hnu, mul_one] at this
    rw [Real.sqrt_le_left hℓ]
    exact this.trans (pow_le_pow_left₀ (opN_nonneg L) hL 2)
  have hY : √(normSq (L' *ᵥ w)) ≤ ℓ := by
    have := eb_normSq_mulVec_le L' w
    rw [hnw, mul_one] at this
    rw [Real.sqrt_le_left hℓ]
    exact this.trans (pow_le_pow_left₀ (opN_nonneg L') hL' 2)
  have hXY : |(L *ᵥ u) ⬝ᵥ (L' *ᵥ w)| ≤ L11 := by
    have e2 : (L *ᵥ u) ⬝ᵥ (L' *ᵥ w) = u ⬝ᵥ (Lᵀ * L') *ᵥ w := by
      rw [← Matrix.mulVec_mulVec, eb_dot_transpose_mulVec]
    rw [e2]
    exact (eb_abs_bil_le _ u w hu hw).trans hLL
  have hc0 : 0 ≤ (hi + lo) / 2 := by linarith
  have hh0 : 0 ≤ (hi - lo) / 2 := by linarith
  have h1 : (hi + lo) / 2 * ((L *ᵥ u) ⬝ᵥ (L' *ᵥ w)) ≤ (hi + lo) / 2 * L11 :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans hXY) hc0
  have h2 : (hi - lo) / 2 * √(normSq (L *ᵥ u)) * √(normSq (L' *ᵥ w)) ≤ (hi - lo) / 2 * ℓ ^ 2 := by
    rw [mul_assoc, sq]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hX hY (Real.sqrt_nonneg _) hℓ) hh0
  have h3 := (abs_le.mp hG).2
  linarith

/-- **The E-block assembly (deterministic) with a given main-term bound `B`.** -/
theorem d2_Eblock {r q a a' : ℕ} (T : Matrix (Fin r) (Fin a) ℝ) (T' : Matrix (Fin r) (Fin a') ℝ)
    (Nm : Matrix (Fin r) (Fin q) ℝ) (L : Matrix (Fin q) (Fin a) ℝ) (L' : Matrix (Fin q) (Fin a') ℝ)
    {τ₁ cx B : ℝ} (hT : opN T ≤ τ₁) (hT' : opN T' ≤ τ₁) (hNL : opN (Nm * L) ≤ cx)
    (hNL' : opN (Nm * L') ≤ cx) (hB : opN (Lᵀ * (Nmᵀ * Nm) * L') ≤ B) :
    opN ((T + Nm * L)ᵀ * (T' + Nm * L')) ≤ B + 2 * τ₁ * cx + τ₁ ^ 2 := by
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
  refine (BstLean.Part153.opN_add_le' _ _).trans ?_
  have hA := BstLean.Part153.opN_add_le' (Tᵀ * T') (Tᵀ * (Nm * L'))
  have hB' := BstLean.Part153.opN_add_le' ((Nm * L)ᵀ * T') (Lᵀ * (Nmᵀ * Nm) * L')
  nlinarith

variable {n D : ℕ}

/-- **E block, deterministic assembly with a main-term bound `B`** (copy of `e2_Eblock_det`). -/
theorem d2_Eblock_det (x x' : Fin n → ℝ) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (PE : Matrix (Fin n) (Fin n) ℝ)
    (Pm : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (U : Matrix (Fin (mA n)) (Fin D) ℝ)
    (hUL : U * Uᵀ * ((1 - Pm) * (obD (A₁ *ᵥ x) * A₁ * PE)) = (1 - Pm) * (obD (A₁ *ᵥ x) * A₁ * PE))
    (hUL' : U * Uᵀ * ((1 - Pm) * (obD (A₁ *ᵥ x') * A₁ * PE)) =
      (1 - Pm) * (obD (A₁ *ᵥ x') * A₁ * PE))
    {τ₁ cx B : ℝ}
    (hT : opN (Matrix.diagonal (e2_sel x x' A₁ A₂) * A₂ * (Pm * (obD (A₁ *ᵥ x) * A₁ * PE))) ≤ τ₁)
    (hT' : opN (Matrix.diagonal (e2_sel x x' A₁ A₂) * A₂ * (Pm * (obD (A₁ *ᵥ x') * A₁ * PE))) ≤ τ₁)
    (hNL : opN ((Matrix.diagonal (e2_sel x x' A₁ A₂) * A₂ * U) *
      (Uᵀ * ((1 - Pm) * (obD (A₁ *ᵥ x) * A₁ * PE)))) ≤ cx)
    (hNL' : opN ((Matrix.diagonal (e2_sel x x' A₁ A₂) * A₂ * U) *
      (Uᵀ * ((1 - Pm) * (obD (A₁ *ᵥ x') * A₁ * PE)))) ≤ cx)
    (hB : opN ((Uᵀ * ((1 - Pm) * (obD (A₁ *ᵥ x) * A₁ * PE)))ᵀ *
      ((Matrix.diagonal (e2_sel x x' A₁ A₂) * A₂ * U)ᵀ * (Matrix.diagonal (e2_sel x x' A₁ A₂) * A₂ * U)) *
      (Uᵀ * ((1 - Pm) * (obD (A₁ *ᵥ x') * A₁ * PE)))) ≤ B) :
    opN ((BstLean.Part151.jac A₁ A₂ x * PE)ᵀ * (BstLean.Part151.jac A₁ A₂ x' * PE)) ≤
      B + 2 * τ₁ * cx + τ₁ ^ 2 := by
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
  exact d2_Eblock _ _ _ _ _ hT hT' hNL hNL' hB

/-- Monotonicity of the net cardinality bound in the dimension. -/
lemma d2_net_mono {r R : ℕ} (h : r ≤ R) {ε : ℝ} (hε : 0 < ε) :
    (2 * (gridN r ε : ℝ) + 1) ^ r ≤ (2 * (gridN R ε : ℝ) + 1) ^ R := by
  have hg : gridN r ε ≤ gridN R ε := by
    unfold gridN
    exact Nat.ceil_mono (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (by exact_mod_cast h)) hε.le)
  have hg' : (gridN r ε : ℝ) ≤ gridN R ε := by exact_mod_cast hg
  have h0 : (0 : ℝ) ≤ gridN r ε := Nat.cast_nonneg _
  calc (2 * (gridN r ε : ℝ) + 1) ^ r ≤ (2 * (gridN R ε : ℝ) + 1) ^ r :=
        pow_le_pow_left₀ (by positivity) (by linarith) r
    _ ≤ (2 * (gridN R ε : ℝ) + 1) ^ R := pow_le_pow_right₀ (by linarith) h


/-- `σ = √t(√K + √(2n) + υ)`, `t = 2/m`. -/
noncomputable def e3_sig (n : ℕ) (K υ : ℝ) : ℝ :=
  √(2 / ((mA n : ℕ) : ℝ)) * (√K + √(2 * (n : ℝ)) + υ)

/-- The lower singular-value level `√((1 − δ)tK_lo)(1 − ε) − σε`. -/
noncomputable def e3_bl (n : ℕ) (K Klo υ δ ε : ℝ) : ℝ :=
  √((1 - δ) * (2 / ((mA n : ℕ) : ℝ)) * Klo) * (1 - ε) - e3_sig n K υ * ε

/-- **The two-sided E-block bound.** -/
noncomputable def e3_bound2 (n : ℕ) (K Klo υ ℓ L11 π₁ δ ε : ℝ) : ℝ :=
  (e3_sig n K υ ^ 2 + e3_bl n K Klo υ δ ε ^ 2) / 2 * (L11 + π₁ ^ 2) +
    (e3_sig n K υ ^ 2 - e3_bl n K Klo υ δ ε ^ 2) / 2 * ℓ ^ 2 +
    2 * (√(2 / ((mA n : ℕ) : ℝ)) * (√((mA n : ℕ) : ℝ) + √2 + υ) * π₁) * (e3_sig n K υ * ℓ) +
    (√(2 / ((mA n : ℕ) : ℝ)) * (√((mA n : ℕ) : ℝ) + √2 + υ) * π₁) ^ 2

/-- Scaling of a lower bound on the unit sphere. -/
lemma d2_lo_scale {p q : ℕ} (N : Matrix (Fin p) (Fin q) ℝ) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ w : Fin q → ℝ, normSq w = 1 → b ≤ √(normSq (N *ᵥ w))) (z : Fin q → ℝ) :
    b ^ 2 * normSq z ≤ normSq (N *ᵥ z) := by
  have hz0 : 0 ≤ normSq z := normSq_nonneg z
  rcases hz0.lt_or_eq with hpos | hzero
  · set c := (√(normSq z))⁻¹ with hc
    have hs : 0 < √(normSq z) := Real.sqrt_pos.mpr hpos
    have hw : normSq (c • z) = 1 := by
      rw [BstLean.Part184.normSq_smul', hc, inv_pow, Real.sq_sqrt hz0, inv_mul_cancel₀ hpos.ne']
    have h1 := h _ hw
    rw [Matrix.mulVec_smul, BstLean.Part184.normSq_smul', Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (by rw [hc]; positivity)] at h1
    have h2 : b * √(normSq z) ≤ √(normSq (N *ᵥ z)) := by
      rw [hc] at h1
      rw [inv_mul_eq_div, le_div_iff₀ hs] at h1
      linarith
    have h3 := mul_le_mul h2 h2 (by positivity) (Real.sqrt_nonneg _)
    rw [Real.mul_self_sqrt (normSq_nonneg _)] at h3
    nlinarith [Real.sq_sqrt hz0]
  · rw [← hzero, mul_zero]; exact normSq_nonneg _

lemma d2_bl_le_sig {n : ℕ} {K Klo υ δ ε : ℝ} (hKlo0 : 0 ≤ Klo) (hKK : Klo ≤ K) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hε0 : 0 < ε) (hε1 : ε < 1) (hυ : 0 ≤ υ) :
    e3_bl n K Klo υ δ ε ≤ e3_sig n K υ := by
  unfold e3_bl
  set t := 2 / ((mA n : ℕ) : ℝ) with htd
  have ht' : (0 : ℝ) ≤ t := by rw [htd]; positivity
  have ht0 : 0 ≤ √t := Real.sqrt_nonneg _
  have hσe : e3_sig n K υ = √t * (√K + √(2 * (n : ℝ)) + υ) := rfl
  have hσ0 : 0 ≤ e3_sig n K υ := by rw [hσe]; positivity
  have h1' : √((1 - δ) * t * Klo) ≤ e3_sig n K υ := by
    rw [hσe]
    have : √((1 - δ) * t * Klo) ≤ √t * √K := by
      rw [← Real.sqrt_mul ht' K]
      apply Real.sqrt_le_sqrt
      have h1 : (1 - δ) * Klo ≤ K := by
        have : (1 - δ) * Klo ≤ Klo := by nlinarith
        linarith
      have e2 : (1 - δ) * t * Klo = t * ((1 - δ) * Klo) := by ring
      rw [e2]
      exact mul_le_mul_of_nonneg_left h1 ht'
    have : √t * √K ≤ √t * (√K + √(2 * (n : ℝ)) + υ) :=
      mul_le_mul_of_nonneg_left (by have := Real.sqrt_nonneg (2 * (n : ℝ)); linarith) ht0
    linarith
  have h2 : √((1 - δ) * t * Klo) * (1 - ε) ≤ e3_sig n K υ * (1 - ε) :=
    mul_le_mul_of_nonneg_right h1' (by linarith)
  have h3 : 0 ≤ e3_sig n K υ * ε := mul_nonneg hσ0 hε0.le
  nlinarith

/-- **The two-sided E block at a fixed first layer.** -/
theorem d2_cond (x x' : Fin n → ℝ) (PE : Matrix (Fin n) (Fin n) ℝ) {ℓ L11 π₁ K Klo υ δ ε : ℝ}
    (hℓ0 : 0 ≤ ℓ) (hπ0 : 0 ≤ π₁) (hυ : 0 ≤ υ) (hm : 0 < mA n) (hKlo0 : 0 ≤ Klo)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hbl : 0 ≤ e3_bl n K Klo υ δ ε)
    (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (hg : e3_good1 x x' PE ℓ L11 π₁ A₁) :
    (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) {A₂ | Klo ≤ ∑ i, e2_sel x x' A₁ A₂ i ∧
      ∑ i, e2_sel x x' A₁ A₂ i ≤ K ∧
      e3_bound2 n K Klo υ ℓ L11 π₁ δ ε < opN ((jac A₁ A₂ x * PE)ᵀ * (jac A₁ A₂ x' * PE))} ≤
      ENNReal.ofReal (3 * exp (-υ ^ 2 / 2) +
        (2 * (gridN (2 * n) ε : ℝ) + 1) ^ (2 * n) * exp (-(Klo * δ ^ 2 / 4))) := by
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
  set σ := e3_sig n K υ with hσd
  have hσe : σ = √t * (√K + √(2 * (n : ℝ)) + υ) := rfl
  set τ₁ := √t * (√((mA n : ℕ) : ℝ) + √2 + υ) * π₁ with hτd
  set bl := e3_bl n K Klo υ δ ε with hbld
  set br := √((1 - δ) * t * Klo) * (1 - ε) - √t * (√K + √(r : ℝ) + υ) * ε with hbrd
  have ht0 : 0 ≤ √t := Real.sqrt_nonneg _
  have hrs : √(r : ℝ) ≤ √(2 * (n : ℝ)) := Real.sqrt_le_sqrt hr'
  have hblr : bl ≤ br := by
    have e : bl = √((1 - δ) * t * Klo) * (1 - ε) - σ * ε := rfl
    rw [e, hbrd, hσe]
    have : √t * (√K + √(r : ℝ) + υ) ≤ √t * (√K + √(2 * (n : ℝ)) + υ) :=
      mul_le_mul_of_nonneg_left (by linarith) ht0
    nlinarith
  set E3 := {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ | Klo ≤ ∑ i, dF (A₂ * Pm) i ∧
      ∑ i, dF (A₂ * Pm) i ≤ K ∧ ∃ z : Fin r → ℝ, normSq z = 1 ∧
        √(normSq ((Matrix.diagonal (dF (A₂ * Pm)) * (A₂ * U)) *ᵥ z)) <
          √((1 - δ) * t * Klo) * (1 - ε) - √t * (√K + √(r : ℝ) + υ) * ε} with hE3
  have hsub : {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ | Klo ≤ ∑ i, e2_sel x x' A₁ A₂ i ∧
      ∑ i, e2_sel x x' A₁ A₂ i ≤ K ∧
      e3_bound2 n K Klo υ ℓ L11 π₁ δ ε < opN ((jac A₁ A₂ x * PE)ᵀ * (jac A₁ A₂ x' * PE))} ⊆
      ({A₂ | ∑ i, dF (A₂ * Pm) i ≤ K ∧ √t * (√K + √(r : ℝ) + υ) ≤
        opN (Matrix.diagonal (dF (A₂ * Pm)) * (A₂ * U))} ∪
      {A₂ | √t * (√((mA n : ℕ) : ℝ) + √(r₂ : ℝ) + υ) ≤
        opN (Matrix.diagonal (fun _ => (1 : ℝ)) * (A₂ * U₂))}) ∪ E3 := by
    intro A₂ hA
    obtain ⟨hKl, hK, hB⟩ := hA
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_and, not_le, hdP, hE3, not_exists,
      not_lt] at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    have hN := h1 hK
    have hlow := h3 hKl hK
    have hS1 : opN (Matrix.diagonal (e2_sel x x' A₁ A₂)) ≤ 1 :=
      e3_opN_diag01 _ (e2_sel01 x x' A₁ A₂)
    have hσ0 : 0 ≤ σ := by
      rw [hσe]; exact mul_nonneg ht0 (by positivity)
    have hNσ : opN (Matrix.diagonal (e2_sel x x' A₁ A₂) * A₂ * U) ≤ σ := by
      rw [Matrix.mul_assoc]
      refine hN.le.trans ?_
      rw [hσe]
      refine mul_le_mul_of_nonneg_left ?_ ht0
      linarith
    have hA2 : opN (A₂ * U₂) ≤ √t * (√((mA n : ℕ) : ℝ) + √2 + υ) := by
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
    -- the two-sided bounds on `𝔑 = S₂A₂U`
    set Nm := Matrix.diagonal (e2_sel x x' A₁ A₂) * A₂ * U with hNm
    have hNm' : Nm = Matrix.diagonal (dF (A₂ * Pm)) * (A₂ * U) := by
      rw [hNm, hdP, Matrix.mul_assoc]
    have hhi : ∀ z, normSq (Nm *ᵥ z) ≤ σ ^ 2 * normSq z := fun z =>
      (eb_normSq_mulVec_le Nm z).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (opN_nonneg _) hNσ 2) (normSq_nonneg _))
    have hlo : ∀ z, bl ^ 2 * normSq z ≤ normSq (Nm *ᵥ z) := by
      intro z
      refine d2_lo_scale Nm hbl (fun w hw => ?_) z
      have := hlow w hw
      have e : Nm = Matrix.diagonal (e2_sel x x' A₁ A₂) * (A₂ * U) := by rw [hNm, Matrix.mul_assoc]
      rw [← e] at this
      linarith
    have hblσ : bl ≤ σ := d2_bl_le_sig hKlo0 (hKl.trans hK) hδ0 hδ1 hε0 hε1 hυ
    have hB2 := d2_two_sided_opN Nm (Uᵀ * ((1 - Pm) * L)) (Uᵀ * ((1 - Pm) * L'))
      (hLgen L hℓ) (hLgen L' hℓ') hLL' hlo hhi (sq_nonneg _)
      (pow_le_pow_left₀ hbl hblσ 2)
    have hdet := d2_Eblock_det x x' A₁ A₂ PE Pm U hUL2.1 hUL2.2 (τ₁ := τ₁) (cx := σ * ℓ)
      (hTgen L hU2L) (hTgen L' hU2L') (hNLgen L hℓ) (hNLgen L' hℓ') hB2
    have eb : e3_bound2 n K Klo υ ℓ L11 π₁ δ ε =
        (σ ^ 2 + bl ^ 2) / 2 * (L11 + π₁ ^ 2) + (σ ^ 2 - bl ^ 2) / 2 * ℓ ^ 2 +
          2 * τ₁ * (σ * ℓ) + τ₁ ^ 2 := rfl
    rw [eb] at hB
    linarith
  -- the three charges
  have hE3m : (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) E3 ≤
      ENNReal.ofReal ((2 * (gridN (2 * n) ε : ℝ) + 1) ^ (2 * n) * exp (-(Klo * δ ^ 2 / 4)) +
        exp (-υ ^ 2 / 2)) := by
    rcases Nat.eq_zero_or_pos r with hr0 | hr1
    · have : E3 = ∅ := by
        ext A₂
        simp only [hE3, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨-, -, z, hz, -⟩
        subst hr0
        simp [normSq] at hz
      rw [this, measure_empty]; exact bot_le
    · have h := d1_split_smin hv Pm hPs hPi U hU hPU dF hdFm hd01 hr1 hKlo0 hδ0 hδ1 hε0 hε1 hυ
        (Klo := Klo) (Khi := K)
      refine h.trans (ENNReal.ofReal_le_ofReal ?_)
      have hr2 : r ≤ 2 * n := by
        have : r ≤ n + n := by simpa using hr
        omega
      have hnet := d2_net_mono hr2 hε0
      have := mul_le_mul_of_nonneg_right hnet (Real.exp_pos (-(Klo * δ ^ 2 / 4))).le
      push_cast
      linarith
  have hm2 := (measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add ((measure_union_le _ _).trans (add_le_add hE1 hE2)) hE3m))
  refine hm2.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (exp_pos _).le (exp_pos _).le,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

theorem d2_joint (x x' : Fin n → ℝ) (PE : Matrix (Fin n) (Fin n) ℝ) {ℓ L11 π₁ K Klo υ δ ε : ℝ}
    (hℓ0 : 0 ≤ ℓ) (hπ0 : 0 ≤ π₁) (hυ : 0 ≤ υ) (hm : 0 < mA n) (hKlo0 : 0 ≤ Klo)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hbl : 0 ≤ e3_bl n K Klo υ δ ε)
    (G₁ : Set (Matrix (Fin (mA n)) (Fin n) ℝ)) (hG₁ : MeasurableSet G₁)
    (hG : ∀ A₁ ∈ G₁, e3_good1 x x' PE ℓ L11 π₁ A₁) :
    (BstLean.Part153.nuA n).real {θ | θ.1 ∈ G₁ ∧ Klo ≤ cnt2 x x' θ ∧ cnt2 x x' θ ≤ K ∧
      e3_bound2 n K Klo υ ℓ L11 π₁ δ ε < opN ((jac θ.1 θ.2 x * PE)ᵀ * (jac θ.1 θ.2 x' * PE))} ≤
      (3 * exp (-υ ^ 2 / 2) + (2 * (gridN (2 * n) ε : ℝ) + 1) ^ (2 * n) * exp (-(Klo * δ ^ 2 / 4))) := by
  classical
  have hP1 : IsProbabilityMeasure (gaussMat (mA n) n (2 / (n : ℝ))) := by
    unfold gaussMat; infer_instance
  have hP2 : IsProbabilityMeasure (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) := by
    unfold gaussMat; infer_instance
  set S := {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      θ.1 ∈ G₁ ∧ Klo ≤ cnt2 x x' θ ∧ cnt2 x x' θ ≤ K ∧
      e3_bound2 n K Klo υ ℓ L11 π₁ δ ε < opN ((jac θ.1 θ.2 x * PE)ᵀ * (jac θ.1 θ.2 x' * PE))} with hSd
  have hSm : MeasurableSet S :=
    (measurable_fst hG₁).inter ((measurableSet_le measurable_const (measurable_cnt2 x x')).inter
      ((measurableSet_le (measurable_cnt2 x x') measurable_const).inter
      (measurableSet_lt measurable_const (e3_measurable_pair x x' PE))))
  have hB : 0 ≤ (3 * exp (-υ ^ 2 / 2) + (2 * (gridN (2 * n) ε : ℝ) + 1) ^ (2 * n) * exp (-(Klo * δ ^ 2 / 4))) := by positivity
  rw [Measure.real]
  unfold BstLean.Part153.nuA
  rw [Measure.prod_apply hSm]
  have hle : ∀ A₁, (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) (Prod.mk A₁ ⁻¹' S) ≤
      ENNReal.ofReal ((3 * exp (-υ ^ 2 / 2) + (2 * (gridN (2 * n) ε : ℝ) + 1) ^ (2 * n) * exp (-(Klo * δ ^ 2 / 4)))) := by
    intro A₁
    by_cases hA : A₁ ∈ G₁
    · have e : Prod.mk A₁ ⁻¹' S = {A₂ | Klo ≤ ∑ i, e2_sel x x' A₁ A₂ i ∧
          ∑ i, e2_sel x x' A₁ A₂ i ≤ K ∧
          e3_bound2 n K Klo υ ℓ L11 π₁ δ ε < opN ((jac A₁ A₂ x * PE)ᵀ * (jac A₁ A₂ x' * PE))} := by
        ext A₂
        simp only [hSd, Set.mem_preimage, Set.mem_ofPred_eq]
        constructor
        · intro h; exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
        · intro h; exact ⟨hA, h.1, h.2.1, h.2.2⟩
      rw [e]
      exact d2_cond x x' PE hℓ0 hπ0 hυ hm hKlo0 hδ0 hδ1 hε0 hε1 hbl A₁ (hG A₁ hA)
    · have e : Prod.mk A₁ ⁻¹' S = ∅ := by
        ext A₂
        simp only [hSd, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h; exact hA h.1
      rw [e, measure_empty]; exact bot_le
  calc (∫⁻ A₁, (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) (Prod.mk A₁ ⁻¹' S)
        ∂gaussMat (mA n) n (2 / (n : ℝ))).toReal
      ≤ (∫⁻ _A₁, ENNReal.ofReal ((3 * exp (-υ ^ 2 / 2) + (2 * (gridN (2 * n) ε : ℝ) + 1) ^ (2 * n) * exp (-(Klo * δ ^ 2 / 4)))) ∂gaussMat (mA n) n (2 / (n : ℝ))).toReal :=
        ENNReal.toReal_mono (by rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.ofReal_ne_top)
          (lintegral_mono hle)
    _ = (3 * exp (-υ ^ 2 / 2) + (2 * (gridN (2 * n) ε : ℝ) + 1) ^ (2 * n) * exp (-(Klo * δ ^ 2 / 4))) := by
        rw [lintegral_const, measure_univ, mul_one, ENNReal.toReal_ofReal hB]

end BstLean.Part185

open BstLean.Part185 in
#print axioms d2_cond
open BstLean.Part185 in
#print axioms d2_joint
