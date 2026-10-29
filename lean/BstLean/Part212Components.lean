import BstLean.Part167XY
import BstLean.Part212Assembly
import BstLean.Part212Jacobian

/-! The actual order-160 Jacobian moment follows from the component moments. -/
namespace BstLean.Part212
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

open BstLean.Part167
variable {n : ℕ}

noncomputable def planeMoment160 (c : Fin n → ℝ) (τ : ℝ) (a : Ix n) (v : Fin (n - 1) → ℝ)
    (Yf : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) → Fin (mA n) → ℝ) :
    ℝ≥0∞ :=
  ∫⁻ A₁, ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (latSq (vecMul (planeP (2 / ((mA n : ℕ) : ℝ))
      (reluV (A₁ *ᵥ xLat (rc c) (latitude (n := n) (√(normSq c)) τ a) (unitF53 v)))
      (hT n A₁ c τ) (gate (Yf A₁)) ξ₁ ξ₂)
      (D1A1 A₁ (xLat (rc c) (latitude (n := n) (√(normSq c)) τ a) (unitF53 v))))
      (uHat (rc c)) (dirW (rc c) (unitF53 v)) ^ 80)
    ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) ∂gaussMat (mA n) n (2 / (n : ℝ))

/-- The masked Frobenius moment. -/
noncomputable def frobMoment160 (c : Fin n → ℝ) (τ : ℝ) (a : Ix n) (v : Fin (n - 1) → ℝ) : ℝ≥0∞ :=
  ∫⁻ A₁, ENNReal.ofReal (frobSq (Pmat (uHat (rc c)) (dirW (rc c) (unitF53 v)) *
      (D1A1 A₁ (xLat (rc c) (latitude (n := n) (√(normSq c)) τ a) (unitF53 v)))ᵀ) ^ 80)
    ∂gaussMat (mA n) n (2 / (n : ℝ))

/-- **The two moment hypotheses of Lemma LJ** (the paper's `X_ℓ` and `Y_ℓ`). -/
def ComponentMoments160 (n : ℕ) (X2 Y2 : ℝ) : Prop :=
  ∀ (c : Fin n → ℝ) (τ : ℝ), winC c τ → ∀ (a : Ix n) (v : Fin (n - 1) → ℝ), v ≠ 0 →
    planeMoment160 c τ a v (fun A₁ => YF A₁ c τ) ≤ ENNReal.ofReal (X2 ^ 80) ∧
    planeMoment160 c τ a v (fun A₁ => YS A₁ c τ) ≤ ENNReal.ofReal (X2 ^ 80) ∧
    frobMoment160 c τ a v ≤ ENNReal.ofReal (Y2 ^ 80)

/-- `K_ℓ²` from `X2`, `Y2` and the proved `Z` term. -/
noncomputable def jacobianConstantSquared160 (n : ℕ) (X2 Y2 : ℝ) : ℝ :=
  (√(X2 + 2 / ((mA n : ℕ) : ℝ) * Y2) + transverseConstant160 * √(2 / ((mA n : ℕ) : ℝ)) * operatorEnvelope160 n) ^ 2

lemma operatorEnvelope_pos160 (hn : 1 ≤ n) : 0 < operatorEnvelope160 n := by
  unfold operatorEnvelope160
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have := BstLean.Part152.gaussMomConst_nonneg 80
  have : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn0
  positivity

theorem assemble_jacobian160 (hn : 1 ≤ n) {X2 Y2 : ℝ} (hX2 : 0 < X2) (hY2 : 0 < Y2) (h : ComponentMoments160 n X2 Y2) :
    JacobianMoment160 n (jacobianConstantSquared160 n X2 Y2) := by
  intro c τ hw a v hv
  obtain ⟨hXf, hXs, hY⟩ := h c τ hw a v hv
  obtain ⟨hu, hw1, huw⟩ := frame_orth hn (window_c_ne hn hw) hv
  have hm0 : (0 : ℝ) < 2 / ((mA n : ℕ) : ℝ) := by
    have : 0 < mA n := by unfold mA; positivity
    positivity
  have hpow : ENNReal.ofReal ((√(X2 + 2 / ((mA n : ℕ) : ℝ) * Y2) +
      transverseConstant160 * √(2 / ((mA n : ℕ) : ℝ)) * operatorEnvelope160 n) ^ 160) = ENNReal.ofReal (jacobianConstantSquared160 n X2 Y2 ^ 80) := by
    unfold jacobianConstantSquared160; rw [← pow_mul]
  set x := xLat (rc c) (latitude (n := n) (√(normSq c)) τ a) (unitF53 v)
  have hF : Measurable (fun g : Fin n → ℝ =>
      ENNReal.ofReal (latSq g (uHat (rc c)) (dirW (rc c) (unitF53 v)) ^ 80)) := by
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    unfold latSq; fun_prop
  refine ⟨?_, ?_⟩
  · rw [JM_rep_f c τ x hF, ← hpow]
    exact assemble_latitude160 hu hw1 huw x hm0 (fun A₁ => hT n A₁ c τ) (fun A₁ => YF A₁ c τ)
      (fun A₁ p => normSq_bhat_le _) _ hX2 hY2 (operatorEnvelope_pos160 hn) hXf (measurable_frob _ _ x) hY operator_moment160
  · rw [JM_rep_s c τ x hF, ← hpow]
    exact assemble_latitude160 hu hw1 huw x hm0 (fun A₁ => hT n A₁ c τ) (fun A₁ => YS A₁ c τ)
      (fun A₁ p => normSq_bhat_le _) _ hX2 hY2 (operatorEnvelope_pos160 hn) hXs (measurable_frob _ _ x) hY operator_moment160

/-- `JacobianMoment160` is monotone in `K2`. -/
lemma jacobian160_mono {K K' : ℝ} (hK : 0 ≤ K) (hKK : K ≤ K') (h : JacobianMoment160 n K) : JacobianMoment160 n K' := by
  intro c τ hw a v hv
  obtain ⟨h1, h2⟩ := h c τ hw a v hv
  have hle : ENNReal.ofReal (K ^ 80) ≤ ENNReal.ofReal (K' ^ 80) :=
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hK hKK 80)
  exact ⟨h1.trans hle, h2.trans hle⟩

end BstLean.Part212
