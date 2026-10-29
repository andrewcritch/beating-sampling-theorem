import BstLean.Part199Schur
import BstLean.Part199Pairs

/-! Part 199: the actual core and wide Schur reduction with scalar premises.
The input distribution is stdGauss (Fin n), followed by the same normalization at both levels. -/
namespace BstLean.Part199
open MeasureTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152 BstLean.Part160 BstLean.Part182
open BstLean.Part150 (thetaC)
open BstLean.Part153 (Xi4)

noncomputable def outsideBound (w : Window) : ℝ :=
  2 * exp (-w.t ^ 2 / 2) + 2 * exp (-w.z)

noncomputable def pairRowBound (w : Window) : ℝ := 2 * exp (-w.pair ^ 2 / 2)

noncomputable def exceptionalBound (w : Window) (b₀ b₁ : ℝ) : ℝ :=
  pairRowBound w + 2 * (b₀ + b₁)

noncomputable def exceptionalFactor (w : Window) (b₀ b₁ : ℝ) : ℝ :=
  2 * √(√(exceptionalBound w b₀ b₁)) + √(outsideBound w)

/-- Scalar coefficient for mA=n^2. The moment coefficient M is normalized by 2/n^2. -/
noncomputable def coreWideScalar (n : ℕ) (θ : ℝ) (w₀ w₁ : Window)
    (lam₀ lam₁ E M b₀ b₁ : ℝ) : ℝ :=
  θ * (lam₁ * E + lam₀ * (1 - radiusMinus n θ w₁)⁻¹ * pairRowBound w₁ +
    lam₀ * (1 - radiusMinus n θ w₀)⁻¹ * outsideBound w₁) +
    M * exceptionalFactor w₀ b₀ b₁

/-- Checked scalar cells bound the exact coefficient, with no charge over the cells. -/
theorem coreWide_scalar_of_cover {n : ℕ} {ι : Type*} {domain : Set ℝ}
    (C : BstLean.Part193.FiniteCover ℝ ι domain) (w₀ w₁ : Window)
    (lam₀ lam₁ E M b₀ b₁ : ℝ)
    (B : BstLean.Part193.CheckedBounds C
      (fun θ => coreWideScalar n θ w₀ w₁ lam₀ lam₁ E M b₀ b₁))
    {N : ℝ} (hN : ∀ i ∈ C.indices, (B.bound i).hi ≤ N) :
    ∀ θ ∈ domain, coreWideScalar n θ w₀ w₁ lam₀ lam₁ E M b₀ b₁ ≤ N :=
  BstLean.Part193.finite_cover_uniform_upper C B hN

/-- Core, shell and outside terms for fixed actual matrices.
The only numerical floor is the integrability guard n>=6. -/
theorem Dq_core_wide {n : ℕ} (hn : 6 ≤ n)
    (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) (w₀ w₁ : Window) (h10 : w₁.LE w₀)
    {lam₀ lam₁ E M b₀ b₁ : ℝ} (hl₀ : 0 ≤ lam₀) (hl₁ : 0 ≤ lam₁)
    (hM : 0 ≤ M) (hθ : thetaC c τ < 1)
    (hr₀ : radiusMinus n (thetaC c τ) w₀ < 1)
    (hr₁ : radiusMinus n (thetaC c τ) w₁ < 1)
    (hEw : ∫ ξ, wN c τ ξ ∂stdGauss (Fin n) ≤ E * thetaC c τ / n)
    (hX : Xi4 A₁ A₂ c τ ≤ M * (2 / (n : ℝ)) / n)
    (hb₀ : badMass n w₀.t w₀.z w₀.pair lam₀ ((c, τ), (A₁, A₂)) ≤ b₀)
    (hb₁ : badMass n w₁.t w₁.z w₁.pair lam₁ ((c, τ), (A₁, A₂)) ≤ b₁)
    (v : Fin (mA n) → ℝ) :
    Dq A₁ A₂ c τ v ≤ coreWideScalar n (thetaC c τ) w₀ w₁ lam₀ lam₁ E M b₀ b₁ *
      (2 / (n : ℝ)) / n * normSq v := by
  haveI : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hc := ne_zero_of_thetaC_lt hn0 hτ hθ
  have hθ0 : 0 ≤ thetaC c τ := by unfold thetaC; positivity
  let μ := stdGauss (Fin n)
  let Ω₀ := OmegaS c w₀.t w₀.z
  let Ω₁ := OmegaS c w₁.t w₁.z
  let B := pairFailure A₁ A₂ c τ w₀ lam₀ ∪ pairFailure A₁ A₂ c τ w₁ lam₁
  let G := commonGood c w₀ B
  let G₁ := G ∩ Ω₁ ×ˢ Ω₁
  have hΩ₀ := measurableSet_OmegaS c w₀.t w₀.z
  have hΩ₁ := measurableSet_OmegaS c w₁.t w₁.z
  have h01 : Ω₁ ⊆ Ω₀ := omega_subset c h10
  have hB : MeasurableSet B := (measurableSet_pairFailure A₁ A₂ c τ w₀ lam₀).union
    (measurableSet_pairFailure A₁ A₂ c τ w₁ lam₁)
  have hG := measurableSet_commonGood c w₀ hB
  have hG₁ : MeasurableSet G₁ := hG.inter (hΩ₁.prod hΩ₁)
  have hGs : ∀ a b, (a, b) ∈ G → (b, a) ∈ G := commonGood_swap c w₀ B
  have hGs₁ : ∀ a b, (a, b) ∈ G₁ → (b, a) ∈ G₁ :=
    fun a b h => ⟨hGs a b h.1, h.2.2, h.2.1⟩
  have hwide : ∀ a b, (a, b) ∈ G →
      opN ((BJ A₁ A₂ c τ a)ᵀ * BJ A₁ A₂ c τ b) ≤ (n : ℝ) * lam₀ :=
    fun _ _ h => commonGood_wide_pair A₁ A₂ c τ w₀ w₁ lam₀ lam₁ h
  have hcore : ∀ a b, (a, b) ∈ G₁ →
      opN ((BJ A₁ A₂ c τ a)ᵀ * BJ A₁ A₂ c τ b) ≤
        kern (coreKernelSet c w₁) ((n : ℝ) * lam₁) ((n : ℝ) * lam₀) a b :=
    fun _ _ h => commonGood_core_pair A₁ A₂ c τ w₀ w₁ lam₀ lam₁ h.1 h.2.1 h.2.2
  have hW : ∀ w : Window, radiusMinus n (thetaC c τ) w < 1 →
      ∀ ξ ∈ OmegaS c w.t w.z,
        wN c τ ξ ≤ (1 - radiusMinus n (thetaC c τ) w)⁻¹ * thetaC c τ / n := by
    intro w hr ξ hξ
    have h := omega_weight hn0 hc hτ w.t_nonneg w.z_nonneg hξ hr
    simpa only [wN, radiusMinus, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h
  have hW₀0 : 0 ≤ (1 - radiusMinus n (thetaC c τ) w₀)⁻¹ * thetaC c τ / n := by
    have : 0 < 1 - radiusMinus n (thetaC c τ) w₀ := by linarith
    positivity
  have hW₁0 : 0 ≤ (1 - radiusMinus n (thetaC c τ) w₁)⁻¹ * thetaC c τ / n := by
    have : 0 < 1 - radiusMinus n (thetaC c τ) w₁ := by linarith
    positivity
  have hPs : μ.real (Ω₀ \ Ω₁) ≤ outsideBound w₁ :=
    (measureReal_mono (fun _ h => h.2) (measure_ne_top _ _)).trans
      (omega_compl_le hn0 c w₁.t_nonneg w₁.z_nonneg)
  have hmain := Dq_le_two_weights hn A₁ A₂ c hτ h01 hΩ₀ hΩ₁ hl₁ hl₀
    (coreKernelSet c w₁) (measurableSet_coreKernelSet c w₁) (coreKernelSet_swap c w₁)
    G₁ hG₁ hGs₁ hcore G hG hGs hwide hEw hW₁0 hW₀0
    (hW w₁ hr₁) (hW w₀ hr₀) (coreKernelSet_row hn0 c w₁) hPs v
  have hb : (μ.prod μ).real B ≤ b₀ + b₁ :=
    (measureReal_union_le _ _).trans (add_le_add hb₀ hb₁)
  have hH := commonGood_exception hn0 c w₀ hB hb
  have hsub₁ : G₁ᶜ ∩ Ω₁ ×ˢ Ω₁ ⊆ Gᶜ ∩ Ω₀ ×ˢ Ω₀ := by
    rintro p ⟨hno, hp⟩
    exact ⟨fun h => hno ⟨h, hp⟩, h01 hp.1, h01 hp.2⟩
  have hsub₀ : Gᶜ ∩ (Ω₀ \ Ω₁) ×ˢ (Ω₀ \ Ω₁) ⊆ Gᶜ ∩ Ω₀ ×ˢ Ω₀ :=
    fun _ h => ⟨h.1, h.2.1.1, h.2.2.1⟩
  have hH₁ := (measureReal_mono hsub₁ (measure_ne_top _ _)).trans hH
  have hH₀ := (measureReal_mono hsub₀ (measure_ne_top _ _)).trans hH
  have hPo := omega_compl_le hn0 c w₀.t_nonneg w₀.z_nonneg
  have hF : √(√((μ.prod μ).real (G₁ᶜ ∩ Ω₁ ×ˢ Ω₁))) +
      √(√((μ.prod μ).real (Gᶜ ∩ (Ω₀ \ Ω₁) ×ˢ (Ω₀ \ Ω₁)))) +
      √(μ.real Ω₀ᶜ) ≤ exceptionalFactor w₀ b₀ b₁ := by
    have h1 := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hH₁)
    have h0 := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hH₀)
    have ho := Real.sqrt_le_sqrt hPo
    unfold exceptionalFactor exceptionalBound pairRowBound outsideBound
    linarith
  have hXF := mul_le_mul hX hF (by positivity) (by positivity)
  apply schur_scalar hn0
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ (normSq_nonneg v))
  exact add_le_add le_rfl hXF

end BstLean.Part199
