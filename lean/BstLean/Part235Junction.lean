import BstLean.Part235Covariance
import BstLean.Part235Evaluator
import BstLean.Part199Junction
import BstLean.Part208Junction

/-! Part 235: the checked coefficient supplies the original network covariance interface. -/
namespace BstLean.Part235
open MeasureTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part160 BstLean.Part182
open BstLean.Part199 BstLean.Part193
open BstLean.Part153 (Xi4)

theorem jointCovScalar_eq (n : ℕ) (θ : ℝ) (w₀ w₁ : Window)
    (lam₀ lam₁ E M b : ℝ) :
    jointCovScalar n θ w₀ w₁ lam₀ lam₁ E M b =
      coreWideScalar n θ w₀ w₁ lam₀ lam₁ E M (b / 4) (b / 4) := by
  simp only [jointCovScalar, coreWideScalar, jointExceptionalFactor,
    exceptionalFactor, exceptionalBound, show 2 * (b / 4 + b / 4) = b by ring]

/-- A proof tree checks the joint-event coefficient, without duplicating the bad mass. -/
theorem joint_certificate_sound {n : ℕ} {θ : ℝ} {w₀ w₁ : Window}
    {lam₀ lam₁ E M b N : ℝ} {I : Interval}
    (C : ExprCertificate (covarianceVars n θ w₀ w₁ lam₀ lam₁ E M (b / 4) (b / 4))
      covarianceExpr I) (hN : I.hi ≤ N) :
    jointCovScalar n θ w₀ w₁ lam₀ lam₁ E M b ≤ N := by
  rw [jointCovScalar_eq]
  exact covariance_certificate_sound C hN

theorem JointCovEvent_mass {n : ℕ} {w₀ w₁ : Window} {θlo θhi lam₀ lam₁ b : ℝ}
    {k : AgFam n} (hw : thetaC k.1.1 k.1.2 ∈ Set.Icc θlo θhi)
    (hk : k ∈ JointCovEvent n w₀ w₁ θlo θhi lam₀ lam₁ b) :
    jointBadMass n w₀ w₁ lam₀ lam₁ k ≤ b := by
  rcases hk with hk | hk
  · exact False.elim (hk hw)
  · exact hk

/-- The paper inverse-radius mean discharges the mean premise. The actual joint
event and the fourth-moment bound remain visible inputs. -/
theorem cov_at_joint {n : ℕ} (hn : 6 ≤ n) (D : Design n) (k : Ret n)
    (hτ : 0 < D.tau0 k) (w₀ w₁ : Window) (h10 : w₁.LE w₀)
    {θlo θhi lam₀ lam₁ M b N : ℝ} (hl₀ : 0 ≤ lam₀) (hl₁ : 0 ≤ lam₁)
    (hM : 0 ≤ M) (hw : thetaC k.1.2 (D.tau0 k) ∈ Set.Icc θlo θhi)
    (hθhi : θhi < 1)
    (hr₀ : radiusMinus n (thetaC k.1.2 (D.tau0 k)) w₀ < 1)
    (hr₁ : radiusMinus n (thetaC k.1.2 (D.tau0 k)) w₁ < 1)
    (hX : Xi4 k.2.1.1.1 k.2.1.1.2 k.1.2 (D.tau0 k) ≤ M * (2 / (n : ℝ)) / n)
    (hC : ((k.1.2, D.tau0 k), (k.2.1.1.1, k.2.1.1.2)) ∈
      JointCovEvent n w₀ w₁ θlo θhi lam₀ lam₁ b)
    (hN : jointCovScalar n (thetaC k.1.2 (D.tau0 k)) w₀ w₁ lam₀ lam₁
      (1 - 4 * thetaC k.1.2 (D.tau0 k) / n)⁻¹ M b ≤ N) : COV_at D k N := by
  refine cov_of_scalar hn D k hτ hN (fun v => ?_)
  apply Dq_core_wide_joint hn k.2.1.1.1 k.2.1.1.2 k.1.2 hτ w₀ w₁ h10
    hl₀ hl₁ hM (hw.2.trans_lt hθhi) hr₀ hr₁
    (hX := hX) (hmass := JointCovEvent_mass hw hC)
  have h := BstLean.Part208.Ew_paper (by omega) k.1.2 hτ
  convert h using 1 <;> ring

/-- The moment event and the covariance event each receive one complement payment. -/
theorem joint_moment_ret_charge {n p P : ℕ} (hp : 1 ≤ p) (hP : 1 ≤ P)
    (hn : 2 * p + 1 < n) (D : Design n) (hτ : TauWorld D)
    (w₀ w₁ : Window) (h10 : w₁.LE w₀)
    {θlo θhi lo₀ hi₀ lo₁ hi₁ lam₀ lam₁ δ ε M η : ℝ}
    (hlam : lam₁ ≤ lam₀) (hδ : 0 ≤ δ) (hε : 0 < ε) (hM : 0 < M) (hη : 0 ≤ η)
    (hg₀ : ∀ θ ∈ Set.Icc θlo θhi, OverlapGuard n θ w₀ lo₀ hi₀)
    (hg₁ : ∀ θ ∈ Set.Icc θlo θhi, OverlapGuard n θ w₁ lo₁ hi₁)
    (hTI₀ : TI_hyp n lo₀ hi₀ lam₀ δ) (hTI₁ : TI_hyp n lo₁ hi₁ lam₁ δ) :
    (retDist D.toCentres).real
      ((agentEv D (MomentEvent n p M)) ∩
        (agentEv D (JointCovEvent n w₀ w₁ θlo θhi lam₀ lam₁ (δ / ε))))ᶜ ≤
      (BstLean.Part153.jS n (p * P) η ^ 2 / M) ^ (p * P) + ε := by
  rw [Set.compl_inter]
  exact (measureReal_union_le _ _).trans (add_le_add
    (MomentEvent_ret_charge hp hP hn D hτ hM hη)
    (JointCovEvent_ret_charge (by omega) D hτ w₀ w₁ h10 hlam hδ hε hg₀ hg₁ hTI₀ hTI₁))

end BstLean.Part235
