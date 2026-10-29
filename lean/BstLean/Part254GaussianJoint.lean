import BstLean.Part254GaussianAssembly

namespace BstLean.Part254
open MeasureTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152 BstLean.Part157 BstLean.Part160 BstLean.Part182
open BstLean.Part208 BstLean.Part199 BstLean.Part238
open BstLean.Part150 (thetaC)
open BstLean.Part153 (nrm Xi4)

theorem Dq_gaussian_joint {n : ℕ} (hn : 6 ≤ n)
    (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c u : Fin n → ℝ) {a τ : ℝ} (hcau : c = a • u) (ha : 0 < a) (hu : normSq u = 1)
    (hτ : 0 < τ) (w₀ w₁ : Window) (h10 : w₁.LE w₀)
    {kE ko ks lam₀ cp sm M b : ℝ} (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks)
    (hl₀ : 0 ≤ lam₀) (hM : 0 ≤ M) (hθ : thetaC c τ < 1)
    (hr₀ : radiusMinus n (thetaC c τ) w₀ < 1) (hr₁ : radiusMinus n (thetaC c τ) w₁ < 1)
    (hR : 0 < axialRadiusLower n a τ w₁.t w₁.z) (hcp : cp ^ 2 < 1) (hsm1 : sm ≤ 1)
    (hsm : ∀ ξ ∈ OmegaS c w₁.t w₁.z, sm ≤ (u ⬝ᵥ sphPt (c + τ • ξ)) ^ 2)
    (hb : sharpBadMass n w₀ w₁ lam₀ kE ko ks cp ((c, τ), (A₁, A₂)) ≤ b)
    (hX : Xi4 A₁ A₂ c τ ≤ M * (2 / (n : ℝ)) / n) (v : Fin (mA n) → ℝ) :
    Dq A₁ A₂ c τ v ≤
      gaussianScalar n (thetaC c τ) w₀ w₁
        (min (sharpK kE ko ks (chiCore n a τ w₁.t w₁.z sm cp)) (ta_lam kE ko ks))
        lam₀ (1 - 4 * thetaC c τ / n)⁻¹ M
        (gaussianTail w₀.pair + 2 * b) * (2 / (n : ℝ)) / n * normSq v := by
  have hn0 : 0 < n := by omega
  let B := pairFailure A₁ A₂ c τ w₀ lam₀ ∪ modeFailure A₁ A₂ c τ w₁ kE ko ks cp
  have hBm : MeasurableSet B :=
    (measurableSet_pairFailure A₁ A₂ c τ w₀ lam₀).union
      (measurableSet_modeFailure A₁ A₂ c τ w₁ kE ko ks cp)
  let G := commonGood c w₀ B
  have hB : ((stdGauss (Fin n)).prod (stdGauss (Fin n))).real B ≤ b := hb
  apply Dq_core_wide_gaussian hn A₁ A₂ c u hcau ha hu hτ w₀ w₁ h10 hkE hko hks hl₀ hM hθ hr₀ hr₁
    hR hcp hsm1 hsm G (measurableSet_commonGood c w₀ hBm)
    (fun p hp => commonGood_swap c w₀ B p.1 p.2 hp)
    (fun p hp => ⟨hp.1.1, hp.1.2.1⟩)
    (fun p hp hp₁ => by
      by_contra hno
      exact hp.2 (Or.inl (Or.inr ⟨hp₁, hno⟩)))
    (fun p hp _ => by
      apply not_lt.mp
      intro hbad
      exact hp.2 (Or.inl (Or.inl ⟨hp.1, hbad⟩)))
    (commonGood_exception_gaussian hn0 c w₀ hBm hB) hX v


end BstLean.Part254
