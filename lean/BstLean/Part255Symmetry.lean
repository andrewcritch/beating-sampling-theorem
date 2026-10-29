import BstLean.Part254GaussianJoint
import BstLean.Part254GaussianScalar
import BstLean.Part235Covariance

/-! The local mode event is symmetric in its two unit inputs. -/
namespace BstLean.Part255
open MeasureTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152 BstLean.Part157 BstLean.Part160 BstLean.Part182
open BstLean.Part208 BstLean.Part199 BstLean.Part238 BstLean.Part254
open BstLean.Part150 (thetaC)
open BstLean.Part153 (nrm Xi4 opN_transpose)

theorem modeBounds_swap {m n : ℕ} {J J' : Matrix (Fin m) (Fin n) ℝ}
    {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
    {kE ko ks cp : ℝ} (hcp : cp^2 < 1)
    (h : ModeBounds J J' kE ko ks cp x x') : ModeBounds J' J kE ko ks cp x' x := by
  have hp : PEm x x' = PEm x' x :=
    Matrix.ext_iff_mulVec.mpr (ta_PEm_symm hx hx' (h.1.trans_lt hcp))
  refine ⟨by simpa only [dotProduct_comm] using h.1, ?_, ?_, ?_, ?_⟩
  · have he : (PEm x x' * (Jᵀ * J') * PEm x x')ᵀ =
        PEm x' x * (J'ᵀ * J) * PEm x' x := by
      simp only [transpose_mul, transpose_transpose, e4_PEm_symm, hp, mul_assoc]
    rw [← he, opN_transpose]
    exact h.2.1
  · rw [← hp]
    exact h.2.2.2.1
  · rw [← hp]
    exact h.2.2.1
  · simpa only [dotProduct_comm] using h.2.2.2.2

theorem modeFailure_swap {n : ℕ} (hn : 1 ≤ n)
    (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (w : Window) (kE ko ks cp : ℝ) (hcp : cp^2 < 1)
    {a b : Fin n → ℝ} (h : (a,b) ∈ modeFailure A₁ A₂ c τ w kE ko ks cp) :
    (b,a) ∈ modeFailure A₁ A₂ c τ w kE ko ks cp := by
  refine ⟨gammaS_swap h.1, ?_⟩
  intro hg
  exact h.2 (modeBounds_swap (normSq_sphPt hn _) (normSq_sphPt hn _) hcp hg)

theorem commonGood_exception_gaussian_symmetric {n : ℕ} (hn : 0 < n)
    (c : Fin n → ℝ) (w : Window)
    {B : Set ((Fin n → ℝ) × (Fin n → ℝ))}
    (hBs : ∀ a b, (a,b) ∈ B → (b,a) ∈ B) {b : ℝ}
    (hb : ((stdGauss (Fin n)).prod (stdGauss (Fin n))).real B ≤ b) :
    ((stdGauss (Fin n)).prod (stdGauss (Fin n))).real
      ((commonGood c w B)ᶜ ∩ OmegaS c w.t w.z ×ˢ OmegaS c w.t w.z) ≤
      gaussianTail w.pair + b := by
  haveI : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  let μ := (stdGauss (Fin n)).prod (stdGauss (Fin n))
  have hswap : Prod.swap ⁻¹' B ⊆ B := fun p hp => hBs p.2 p.1 hp
  have hs : (commonGood c w B)ᶜ ∩ OmegaS c w.t w.z ×ˢ OmegaS c w.t w.z ⊆
      ((OmegaS c w.t w.z ×ˢ OmegaS c w.t w.z) \ GammaS c w.t w.z w.pair) ∪ B := by
    rintro p ⟨hno,hp⟩
    by_cases hΓ : p ∈ GammaS c w.t w.z w.pair
    · have hbad : p ∈ B ∪ Prod.swap ⁻¹' B := by
        by_contra hbad
        exact hno ⟨hΓ,hbad⟩
      exact Or.inr (hbad.elim id (fun h => hswap h))
    · exact Or.inl ⟨hp,hΓ⟩
  exact (measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (pairs_out_gamma_gaussian hn c w.z_nonneg w.pair_nonneg) hb))

theorem Dq_gaussian_symmetric {n : ℕ} (hn : 6 ≤ n)
    (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c u : Fin n → ℝ) {a τ : ℝ} (hcau : c = a • u) (ha : 0 < a) (hu : normSq u = 1)
    (hτ : 0 < τ) (w₀ w₁ : Window) (h10 : w₁.LE w₀)
    {kE ko ks lam₀ cp sm M b : ℝ} (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks)
    (hl₀ : 0 ≤ lam₀) (hM : 0 ≤ M) (hθ : thetaC c τ < 1)
    (hr₀ : radiusMinus n (thetaC c τ) w₀ < 1) (hr₁ : radiusMinus n (thetaC c τ) w₁ < 1)
    (hR : 0 < axialRadiusLower n a τ w₁.t w₁.z) (hcp : cp^2 < 1) (hsm1 : sm ≤ 1)
    (hsm : ∀ ξ ∈ OmegaS c w₁.t w₁.z, sm ≤ (u ⬝ᵥ sphPt (c + τ • ξ))^2)
    (hb : sharpBadMass n w₀ w₁ lam₀ kE ko ks cp ((c,τ),(A₁,A₂)) ≤ b)
    (hX : Xi4 A₁ A₂ c τ ≤ M * (2/(n : ℝ))/n) (v : Fin (mA n) → ℝ) :
    Dq A₁ A₂ c τ v ≤
      gaussianScalar n (thetaC c τ) w₀ w₁
        (min (sharpK kE ko ks (chiCore n a τ w₁.t w₁.z sm cp)) (ta_lam kE ko ks))
        lam₀ (1-4*thetaC c τ/n)⁻¹ M
        (gaussianTail w₀.pair+b) * (2/(n : ℝ))/n * normSq v := by
  let B := pairFailure A₁ A₂ c τ w₀ lam₀ ∪ modeFailure A₁ A₂ c τ w₁ kE ko ks cp
  have hBm : MeasurableSet B :=
    (measurableSet_pairFailure A₁ A₂ c τ w₀ lam₀).union
      (measurableSet_modeFailure A₁ A₂ c τ w₁ kE ko ks cp)
  have hBs : ∀ a b, (a,b) ∈ B → (b,a) ∈ B := by
    intro a b h
    exact h.elim (fun h => Or.inl (BstLean.Part235.pairFailure_swap A₁ A₂ c τ w₀ lam₀ h))
      (fun h => Or.inr (modeFailure_swap (by omega) A₁ A₂ c τ w₁ kE ko ks cp hcp h))
  let G := commonGood c w₀ B
  have hB : ((stdGauss (Fin n)).prod (stdGauss (Fin n))).real B ≤ b := hb
  apply Dq_core_wide_gaussian hn A₁ A₂ c u hcau ha hu hτ w₀ w₁ h10 hkE hko hks hl₀ hM hθ hr₀ hr₁
    hR hcp hsm1 hsm G (measurableSet_commonGood c w₀ hBm)
    (fun p hp => commonGood_swap c w₀ B p.1 p.2 hp)
    (fun p hp => ⟨hp.1.1,hp.1.2.1⟩)
    (fun p hp hp₁ => by
      by_contra hno
      exact hp.2 (Or.inl (Or.inr ⟨hp₁,hno⟩)))
    (fun p hp _ => by
      apply not_lt.mp
      intro hbad
      exact hp.2 (Or.inl (Or.inl ⟨hp.1,hbad⟩)))
    (commonGood_exception_gaussian_symmetric (by omega) c w₀ hBs hB) hX v

theorem gaussian_exceptional_single {b : ℝ} (hb : b ≤ 28/10^16) :
    2 * √(√(gaussianTail exampleWide.pair+b)) + √(gaussianOutside exampleWide) ≤
      (58249/10^8 : ℝ) := by
  have hp : gaussianTail exampleWide.pair ≤ (1244193/10^21 : ℝ) := gaussianTail_8.2
  have hq : √(√(gaussianTail exampleWide.pair+b)) ≤ (252208/10^9 : ℝ) := by
    apply BstLean.Part182.sqrt_sqrt_le_of (by norm_num)
    linarith only [hp,hb]
  have ho : √(gaussianOutside exampleWide) ≤ (78074/10^9 : ℝ) := by
    apply BstLean.Part182.sqrt_le_of_sq' (by norm_num)
    linarith only [gaussian_wide_outside_upper]
  linarith only [hq,ho]

end BstLean.Part255
