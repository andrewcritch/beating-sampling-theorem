import BstLean.Part235JointEvent
import BstLean.Part199CoreWide

/-! Part 235: core, shell and exceptional covariance terms on the actual joint event. -/
namespace BstLean.Part235
open MeasureTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152 BstLean.Part160 BstLean.Part182 BstLean.Part199
open BstLean.Part150 (thetaC)
open BstLean.Part153 (Xi4)

noncomputable def jointExceptionalFactor (w : Window) (b : ℝ) : ℝ :=
  2 * √(√(pairRowBound w + b)) + √(outsideBound w)

noncomputable def jointCovScalar (n : ℕ) (θ : ℝ) (w₀ w₁ : Window)
    (lam₀ lam₁ E M b : ℝ) : ℝ :=
  θ * (lam₁ * E + lam₀ * (1 - radiusMinus n θ w₁)⁻¹ * pairRowBound w₁ +
    lam₀ * (1 - radiusMinus n θ w₀)⁻¹ * outsideBound w₁) +
    M * jointExceptionalFactor w₀ b

/-- The actual operator failure is symmetric because the reversed matrix is its transpose. -/
theorem pairFailure_swap {n : ℕ}
    (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (w : Window) (lam : ℝ)
    {a b : Fin n → ℝ} (h : (a, b) ∈ pairFailure A₁ A₂ c τ w lam) :
    (b, a) ∈ pairFailure A₁ A₂ c τ w lam := by
  refine ⟨gammaS_swap h.1, ?_⟩
  have he : opN ((BstLean.Part153.jacT A₁ A₂ (sphPt (c + τ • b)))ᵀ *
      BstLean.Part153.jacT A₁ A₂ (sphPt (c + τ • a))) =
      opN ((BstLean.Part153.jacT A₁ A₂ (sphPt (c + τ • a)))ᵀ *
        BstLean.Part153.jacT A₁ A₂ (sphPt (c + τ • b))) := by
    rw [← BstLean.Part153.opN_transpose
      ((BstLean.Part153.jacT A₁ A₂ (sphPt (c + τ • b)))ᵀ *
        BstLean.Part153.jacT A₁ A₂ (sphPt (c + τ • a))),
      Matrix.transpose_mul, Matrix.transpose_transpose]
  change (n : ℝ) * lam < _
  rw [he]
  exact h.2

/-- Symmetric failures need no second payment for the reversed orientation. -/
theorem commonGood_exception_symmetric {n : ℕ} (hn : 0 < n)
    (c : Fin n → ℝ) (w : Window)
    {B : Set ((Fin n → ℝ) × (Fin n → ℝ))}
    (hBs : ∀ a b, (a, b) ∈ B → (b, a) ∈ B) {b : ℝ}
    (hb : ((stdGauss (Fin n)).prod (stdGauss (Fin n))).real B ≤ b) :
    ((stdGauss (Fin n)).prod (stdGauss (Fin n))).real
      ((commonGood c w B)ᶜ ∩ OmegaS c w.t w.z ×ˢ OmegaS c w.t w.z) ≤
      pairRowBound w + b := by
  haveI : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hswap : Prod.swap ⁻¹' B ⊆ B := fun p hp => hBs p.2 p.1 hp
  have hs : (commonGood c w B)ᶜ ∩ OmegaS c w.t w.z ×ˢ OmegaS c w.t w.z ⊆
      ((OmegaS c w.t w.z ×ˢ OmegaS c w.t w.z) \ GammaS c w.t w.z w.pair) ∪ B := by
    rintro p ⟨hno, hp⟩
    by_cases hΓ : p ∈ GammaS c w.t w.z w.pair
    · have hbad : p ∈ B ∪ Prod.swap ⁻¹' B := by
        by_contra hbad
        exact hno ⟨hΓ, hbad⟩
      exact Or.inr (hbad.elim id (fun h => hswap h))
    · exact Or.inl ⟨hp, hΓ⟩
  exact (measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add
      (pairs_out_gamma hn c w.z_nonneg w.pair_nonneg (t0 := w.t)) hb))

theorem Dq_core_wide_joint {n : ℕ} (hn : 6 ≤ n)
    (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) (w₀ w₁ : Window) (h10 : w₁.LE w₀)
    {lam₀ lam₁ E M b : ℝ} (hl₀ : 0 ≤ lam₀) (hl₁ : 0 ≤ lam₁)
    (hM : 0 ≤ M) (hθ : thetaC c τ < 1)
    (hr₀ : radiusMinus n (thetaC c τ) w₀ < 1)
    (hr₁ : radiusMinus n (thetaC c τ) w₁ < 1)
    (hEw : ∫ ξ, wN c τ ξ ∂stdGauss (Fin n) ≤ E * thetaC c τ / n)
    (hX : Xi4 A₁ A₂ c τ ≤ M * (2 / (n : ℝ)) / n)
    (hmass : jointBadMass n w₀ w₁ lam₀ lam₁ ((c, τ), (A₁, A₂)) ≤ b)
    (v : Fin (mA n) → ℝ) :
    Dq A₁ A₂ c τ v ≤ jointCovScalar n (thetaC c τ) w₀ w₁ lam₀ lam₁ E M b *
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
  have hb : (μ.prod μ).real B ≤ b := hmass
  have hBs : ∀ a b, (a, b) ∈ B → (b, a) ∈ B := by
    intro a b h
    rcases h with h | h
    · exact Or.inl (pairFailure_swap A₁ A₂ c τ w₀ lam₀ h)
    · exact Or.inr (pairFailure_swap A₁ A₂ c τ w₁ lam₁ h)
  have hH := commonGood_exception_symmetric hn0 c w₀ hBs hb
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
      √(μ.real Ω₀ᶜ) ≤ jointExceptionalFactor w₀ b := by
    have h1 := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hH₁)
    have h0 := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hH₀)
    have ho := Real.sqrt_le_sqrt hPo
    unfold jointExceptionalFactor
    calc
      _ ≤ (√(√(pairRowBound w₀ + b)) + √(√(pairRowBound w₀ + b))) +
          √(outsideBound w₀) := add_le_add (add_le_add h1 h0) ho
      _ = _ := by ring
  have hXF := mul_le_mul hX hF (by positivity) (by positivity)
  apply schur_scalar hn0
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ (normSq_nonneg v))
  exact add_le_add le_rfl hXF

end BstLean.Part235
