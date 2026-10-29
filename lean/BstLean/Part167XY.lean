import BstLean.Part167Asm

/-!
# Part 167 (file `XY`): `JM_hyp` from the two moment hypotheses `X` and `Y`

No proof is left open; no `native_decide` or `axiom` is used.

* `XY_hyp n X2 Y2`: for a World value in the window, an index `a` and a direction `v ≠ 0`:
  the plane moment `E_{A₁,ξ}|P_lat(D₁A₁)ᵀp|^{128} ≤ X2^{64}` for `y = b̂` and for `y = r̂`, and the
  masked Frobenius moment `E_{A₁}‖P_lat(D₁A₁)ᵀ‖_F^{128} ≤ Y2^{64}` (the paper's `X_ℓ`, `Y_ℓ`).
* `K2XY n X2 Y2 = (√(X2 + t_A Y2) + C√t_A Zop)²` (the paper's `K_ℓ²`).
* **`JM_of_XY`**: `XY_hyp n X2 Y2 → JM_hyp n (K2XY n X2 Y2)`.
* `JM_mono`: `JM_hyp` is monotone in `K2`.
-/

namespace BstLean.Part167

open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part160 BstLean.Part157
open BstLean.Part152 (opN opN_nonneg)
open BstLean.Part153 (nuA)
open BstLean.Part150 (hT)
open BstLean.Part151 (mask measurable_mask)
open BstLean.Part161 (Ix uHat xLat)
open BstLean.Part162 (dirW)
open BstLean.Part166 (winC bhat)
open BstLean.Part53 (unitF53 radF53)

variable {n : ℕ}

/-- The plane moment for an admissible direction `Yf`. -/
noncomputable def Xmom (c : Fin n → ℝ) (τ : ℝ) (a : Ix n) (v : Fin (n - 1) → ℝ)
    (Yf : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) → Fin (mA n) → ℝ) :
    ℝ≥0∞ :=
  ∫⁻ A₁, ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (latSq (vecMul (planeP (2 / ((mA n : ℕ) : ℝ))
      (reluV (A₁ *ᵥ xLat (rc c) (latitude (n := n) (√(normSq c)) τ a) (unitF53 v)))
      (hT n A₁ c τ) (gate (Yf A₁)) ξ₁ ξ₂)
      (D1A1 A₁ (xLat (rc c) (latitude (n := n) (√(normSq c)) τ a) (unitF53 v))))
      (uHat (rc c)) (dirW (rc c) (unitF53 v)) ^ 64)
    ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) ∂gaussMat (mA n) n (2 / (n : ℝ))

/-- The masked Frobenius moment. -/
noncomputable def Ymom (c : Fin n → ℝ) (τ : ℝ) (a : Ix n) (v : Fin (n - 1) → ℝ) : ℝ≥0∞ :=
  ∫⁻ A₁, ENNReal.ofReal (frobSq (Pmat (uHat (rc c)) (dirW (rc c) (unitF53 v)) *
      (D1A1 A₁ (xLat (rc c) (latitude (n := n) (√(normSq c)) τ a) (unitF53 v)))ᵀ) ^ 64)
    ∂gaussMat (mA n) n (2 / (n : ℝ))

/-- **The two moment hypotheses of Lemma LJ** (the paper's `X_ℓ` and `Y_ℓ`). -/
def XY_hyp (n : ℕ) (X2 Y2 : ℝ) : Prop :=
  ∀ (c : Fin n → ℝ) (τ : ℝ), winC c τ → ∀ (a : Ix n) (v : Fin (n - 1) → ℝ), v ≠ 0 →
    Xmom c τ a v (fun A₁ => YF A₁ c τ) ≤ ENNReal.ofReal (X2 ^ 64) ∧
    Xmom c τ a v (fun A₁ => YS A₁ c τ) ≤ ENNReal.ofReal (X2 ^ 64) ∧
    Ymom c τ a v ≤ ENNReal.ofReal (Y2 ^ 64)

/-- `K_ℓ²` from `X2`, `Y2` and the proved `Z` term. -/
noncomputable def K2XY (n : ℕ) (X2 Y2 : ℝ) : ℝ :=
  (√(X2 + 2 / ((mA n : ℕ) : ℝ) * Y2) + Cg * √(2 / ((mA n : ℕ) : ℝ)) * Zop n) ^ 2

lemma measurable_D1A1 (x : Fin n → ℝ) :
    Measurable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ => D1A1 A₁ x) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun l => ?_
  simp only [D1A1, Matrix.of_apply]
  refine (measurable_mask.comp ?_).mul (Continuous.measurable (by fun_prop))
  exact Continuous.measurable (by simp only [mulVec, dotProduct]; fun_prop)

lemma measurable_frob (u w x : Fin n → ℝ) :
    Measurable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ => frobSq (Pmat u w * (D1A1 A₁ x)ᵀ)) := by
  have hc : Continuous (fun D : Matrix (Fin (mA n)) (Fin n) ℝ => frobSq (Pmat u w * Dᵀ)) := by
    unfold frobSq
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    fun_prop
  exact hc.measurable.comp (measurable_D1A1 x)

lemma Zop_pos (hn : 1 ≤ n) : 0 < Zop n := by
  unfold Zop
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have := BstLean.Part152.gaussMomConst_nonneg 64
  have : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn0
  positivity

/-- **`JM_hyp` from `X` and `Y`.** -/
theorem JM_of_XY (hn : 1 ≤ n) {X2 Y2 : ℝ} (hX2 : 0 < X2) (hY2 : 0 < Y2) (h : XY_hyp n X2 Y2) :
    JM_hyp n (K2XY n X2 Y2) := by
  intro c τ hw a v hv
  obtain ⟨hXf, hXs, hY⟩ := h c τ hw a v hv
  obtain ⟨hu, hw1, huw⟩ := frame_orth hn (window_c_ne hn hw) hv
  have hm0 : (0 : ℝ) < 2 / ((mA n : ℕ) : ℝ) := by
    have : 0 < mA n := by unfold mA; positivity
    positivity
  have hpow : ENNReal.ofReal ((√(X2 + 2 / ((mA n : ℕ) : ℝ) * Y2) +
      Cg * √(2 / ((mA n : ℕ) : ℝ)) * Zop n) ^ 128) = ENNReal.ofReal (K2XY n X2 Y2 ^ 64) := by
    unfold K2XY; rw [← pow_mul]
  set x := xLat (rc c) (latitude (n := n) (√(normSq c)) τ a) (unitF53 v)
  have hF : Measurable (fun g : Fin n → ℝ =>
      ENNReal.ofReal (latSq g (uHat (rc c)) (dirW (rc c) (unitF53 v)) ^ 64)) := by
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    unfold latSq; fun_prop
  refine ⟨?_, ?_⟩
  · rw [JM_rep_f c τ x hF, ← hpow]
    exact asm_core hu hw1 huw x hm0 (fun A₁ => hT n A₁ c τ) (fun A₁ => YF A₁ c τ)
      (fun A₁ p => normSq_bhat_le _) _ hX2 hY2 (Zop_pos hn) hXf (measurable_frob _ _ x) hY Zop_mom
  · rw [JM_rep_s c τ x hF, ← hpow]
    exact asm_core hu hw1 huw x hm0 (fun A₁ => hT n A₁ c τ) (fun A₁ => YS A₁ c τ)
      (fun A₁ p => normSq_bhat_le _) _ hX2 hY2 (Zop_pos hn) hXs (measurable_frob _ _ x) hY Zop_mom

/-- `JM_hyp` is monotone in `K2`. -/
lemma JM_mono {K K' : ℝ} (hK : 0 ≤ K) (hKK : K ≤ K') (h : JM_hyp n K) : JM_hyp n K' := by
  intro c τ hw a v hv
  obtain ⟨h1, h2⟩ := h c τ hw a v hv
  have hle : ENNReal.ofReal (K ^ 64) ≤ ENNReal.ofReal (K' ^ 64) :=
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hK hKK 64)
  exact ⟨h1.trans hle, h2.trans hle⟩

end BstLean.Part167
