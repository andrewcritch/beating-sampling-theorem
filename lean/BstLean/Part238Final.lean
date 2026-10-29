import BstLean.Part238Centre

/-! Part 238: the network covariance transfer with the centre-projection premise discharged.
The remaining analytic premise is the fixed-pair three-mode TI hypothesis `TI3_hyp`. -/
namespace BstLean.Part238
open MeasureTheory Real Matrix Set
open BstLean.Part130 BstLean.Part152 BstLean.Part157 BstLean.Part160 BstLean.Part182
  BstLean.Part208
open BstLean.Part199 (Window radiusMinus)
open BstLean.Part150 (thetaC)
open BstLean.Part153 (nrm Xi4)

lemma centre_proj_lower' {n : ℕ} {c u : Fin n → ℝ} {a τ t0 z0 : ℝ} (hcau : c = a • u)
    (hu : normSq u = 1) (ha : 0 < a) (hτ : 0 < τ) (hat : τ * t0 ≤ a) :
    ∀ ξ ∈ OmegaS c t0 z0, axialProjLower n a τ t0 z0 ≤ (u ⬝ᵥ sphPt (c + τ • ξ)) ^ 2 := by
  subst hcau
  exact centre_proj_lower hu ha hτ hat

/-- **Sharp covariance transfer for a nonzero retained centre.** With `a = |ĉ|`, `u = ĉ/|ĉ|`,
`s₋ = axialProjLower`, and the guard `τ t₀ ≤ a`, the joint event and the sharp scalar bound imply
`COV_at D k N`. -/
theorem cov_at_sharp_centre {n : ℕ} (hn : 6 ≤ n) (D : Design n) (k : Ret n)
    (hτ : 0 < D.tau0 k) (hc : k.1.2 ≠ 0) (w₀ w₁ : Window) (h10 : w₁.LE w₀)
    {θlo θhi kE ko ks lam₀ cp M b N : ℝ} (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks)
    (hl₀ : 0 ≤ lam₀) (hM : 0 ≤ M)
    (hw : thetaC k.1.2 (D.tau0 k) ∈ Set.Icc θlo θhi) (hθhi : θhi < 1)
    (hr₀ : radiusMinus n (thetaC k.1.2 (D.tau0 k)) w₀ < 1)
    (hr₁ : radiusMinus n (thetaC k.1.2 (D.tau0 k)) w₁ < 1)
    (hat : D.tau0 k * w₁.t ≤ nrm k.1.2)
    (hR : 0 < axialRadiusLower n (nrm k.1.2) (D.tau0 k) w₁.t w₁.z) (hcp : cp ^ 2 < 1)
    (hX : Xi4 k.2.1.1.1 k.2.1.1.2 k.1.2 (D.tau0 k) ≤ M * (2 / (n : ℝ)) / n)
    (hC : ((k.1.2, D.tau0 k), (k.2.1.1.1, k.2.1.1.2)) ∈
      SharpCovEvent n w₀ w₁ θlo θhi lam₀ kE ko ks cp b)
    (hN : sharpScalar n (thetaC k.1.2 (D.tau0 k)) w₀ w₁
        (min (sharpK kE ko ks (chiCore n (nrm k.1.2) (D.tau0 k) w₁.t w₁.z
          (axialProjLower n (nrm k.1.2) (D.tau0 k) w₁.t w₁.z) cp)) (ta_lam kE ko ks))
        lam₀ (1 - 4 * thetaC k.1.2 (D.tau0 k) / n)⁻¹ M
        (2 * exp (-w₀.pair ^ 2 / 2) + 2 * b) ≤ N) : COV_at D k N := by
  obtain ⟨hcau, ha, hu⟩ := centre_decomp hc
  exact cov_at_sharp hn D k hτ (uC k.1.2) hcau ha hu w₀ w₁ h10 hkE hko hks hl₀ hM hw hθhi
    hr₀ hr₁ hR hcp (axialProjLower_le_one n ha hτ w₁.t_nonneg w₁.z_nonneg hat)
    (centre_proj_lower' hcau hu ha hτ hat) hX hC hN

end BstLean.Part238
