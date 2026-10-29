import BstLean.Part199CoreWide
import BstLean.Part199Supplies

/-! Part 199: the core and wide scalar coefficient supplies the actual covariance interface. -/
namespace BstLean.Part199
open MeasureTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part182
open BstLean.Part150 (thetaC)
open BstLean.Part153 (Xi4)

/-- One combined retained event pays each analytic source once. -/
theorem CovMoment_ret_charge {n p P : ℕ} (hp : 1 ≤ p) (hP : 1 ≤ P)
    (hn : 2 * p + 1 < n) (D : Design n) (hτ : TauWorld D) (w₀ w₁ : Window)
    {θlo θhi lo₀ hi₀ lo₁ hi₁ lam₀ lam₁ δ₀ δ₁ ε₀ ε₁ M η : ℝ}
    (hM : 0 < M) (hη : 0 ≤ η)
    (hδ₀ : 0 ≤ δ₀) (hδ₁ : 0 ≤ δ₁) (hε₀ : 0 < ε₀) (hε₁ : 0 < ε₁)
    (hg₀ : ∀ θ ∈ Set.Icc θlo θhi, OverlapGuard n θ w₀ lo₀ hi₀)
    (hg₁ : ∀ θ ∈ Set.Icc θlo θhi, OverlapGuard n θ w₁ lo₁ hi₁)
    (hTI₀ : TI_hyp n lo₀ hi₀ lam₀ δ₀) (hTI₁ : TI_hyp n lo₁ hi₁ lam₁ δ₁) :
    (retDist D.toCentres).real ((agentEv D (MomentEvent n p M)) ∩
      ((agentEv D (CovEvent n w₀ θlo θhi lam₀ (δ₀ / ε₀))) ∩
       (agentEv D (CovEvent n w₁ θlo θhi lam₁ (δ₁ / ε₁)))))ᶜ ≤
      (BstLean.Part153.jS n (p * P) η ^ 2 / M) ^ (p * P) + ε₀ + ε₁ := by
  rw [Set.compl_inter]
  have h := (measureReal_union_le _ _).trans (add_le_add
    (MomentEvent_ret_charge hp hP hn D hτ hM hη)
    (CovEvents_ret_charge (by omega) D hτ w₀ w₁ hδ₀ hδ₁ hε₀ hε₁ hg₀ hg₁ hTI₀ hTI₁))
  simpa only [add_assoc] using h

theorem Dq_core_wide_moment {n p : ℕ} (hp : 2 ≤ p) (hn : 2 * p + 1 < n)
    (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) (w₀ w₁ : Window) (h10 : w₁.LE w₀)
    {lam₀ lam₁ E M b₀ b₁ : ℝ} (hl₀ : 0 ≤ lam₀) (hl₁ : 0 ≤ lam₁)
    (hE : 0 < E) (hM : 0 < M) (hθ0 : 0 < thetaC c τ) (hθ1 : thetaC c τ < 1)
    (hr₀ : radiusMinus n (thetaC c τ) w₀ < 1)
    (hr₁ : radiusMinus n (thetaC c τ) w₁ < 1)
    (hW : WqN p c τ ≤ (E * thetaC c τ / n) ^ p)
    (hX : ((c, τ), (A₁, A₂)) ∈ MomentEvent n p M)
    (hb₀ : badMass n w₀.t w₀.z w₀.pair lam₀ ((c, τ), (A₁, A₂)) ≤ b₀)
    (hb₁ : badMass n w₁.t w₁.z w₁.pair lam₁ ((c, τ), (A₁, A₂)) ≤ b₁)
    (v : Fin (mA n) → ℝ) :
    Dq A₁ A₂ c τ v ≤
      coreWideScalar n (thetaC c τ) w₀ w₁ lam₀ lam₁ E (M * E * thetaC c τ) b₀ b₁ *
        (2 / (n : ℝ)) / n * normSq v := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmean := Wq_le_of_Wp (by omega) (show 1 ≤ p by omega) hn c hτ (by positivity) hW
  have hEw : ∫ ξ, wN c τ ξ ∂stdGauss (Fin n) ≤ E * thetaC c τ / n := by
    simpa only [WqN, pow_one, wN] using hmean
  exact Dq_core_wide (by omega) A₁ A₂ c hτ w₀ w₁ h10 hl₀ hl₁ (by positivity)
    hθ1 hr₀ hr₁ hEw (Xi4_on_MomentEvent hp hn A₁ A₂ c hτ hM hE hθ0 hW hX) hb₀ hb₁ v

/-- Actual retained events and a scalar upper bound give the original COV_at conclusion. -/
theorem cov_core_wide {n p : ℕ} (hp : 2 ≤ p) (hn : 2 * p + 1 < n)
    (D : Design n) (k : Ret n) (hτ : 0 < D.tau0 k) (w₀ w₁ : Window) (h10 : w₁.LE w₀)
    {θlo θhi lam₀ lam₁ E M b₀ b₁ N : ℝ}
    (hl₀ : 0 ≤ lam₀) (hl₁ : 0 ≤ lam₁) (hE : 0 < E) (hM : 0 < M)
    (hw : thetaC k.1.2 (D.tau0 k) ∈ Set.Icc θlo θhi)
    (hθlo : 0 < θlo) (hθhi : θhi < 1)
    (hr₀ : radiusMinus n (thetaC k.1.2 (D.tau0 k)) w₀ < 1)
    (hr₁ : radiusMinus n (thetaC k.1.2 (D.tau0 k)) w₁ < 1)
    (hW : WqN p k.1.2 (D.tau0 k) ≤ (E * thetaC k.1.2 (D.tau0 k) / n) ^ p)
    (hX : ((k.1.2, D.tau0 k), (k.2.1.1.1, k.2.1.1.2)) ∈ MomentEvent n p M)
    (hC₀ : ((k.1.2, D.tau0 k), (k.2.1.1.1, k.2.1.1.2)) ∈
      CovEvent n w₀ θlo θhi lam₀ b₀)
    (hC₁ : ((k.1.2, D.tau0 k), (k.2.1.1.1, k.2.1.1.2)) ∈
      CovEvent n w₁ θlo θhi lam₁ b₁)
    (hN : coreWideScalar n (thetaC k.1.2 (D.tau0 k)) w₀ w₁ lam₀ lam₁ E
      (M * E * thetaC k.1.2 (D.tau0 k)) b₀ b₁ ≤ N) : COV_at D k N := by
  refine cov_of_scalar (by omega) D k hτ hN fun v => ?_
  exact Dq_core_wide_moment hp hn k.2.1.1.1 k.2.1.1.2 k.1.2 hτ w₀ w₁ h10
    hl₀ hl₁ hE hM (hθlo.trans_le hw.1) (hw.2.trans_lt hθhi) hr₀ hr₁ hW hX
    (CovEvent_mass hw hC₀) (CovEvent_mass hw hC₁) v

end BstLean.Part199
