import BstLean.Part193Expr
import BstLean.Part199CoreWide

/-! Part 235: an expression certificate for the exact Part199 covariance coefficient.
Exponential tail values enter as exact variables. Their enclosures need separate proofs. -/
namespace BstLean.Part235
open BstLean.Part193 BstLean.Part199

/-- Variables: theta, wide/core coefficients, mean, fourth moment, wide/core radii,
wide/core pair tails, wide/core outside tails, and wide/core bad masses. -/
noncomputable def covarianceVars (n : ℕ) (θ : ℝ) (w₀ w₁ : Window)
    (lam₀ lam₁ E M b₀ b₁ : ℝ) : ℕ → ℝ
  | 0 => θ
  | 1 => lam₀
  | 2 => lam₁
  | 3 => E
  | 4 => M
  | 5 => radiusMinus n θ w₀
  | 6 => radiusMinus n θ w₁
  | 7 => pairRowBound w₀
  | 8 => pairRowBound w₁
  | 9 => outsideBound w₀
  | 10 => outsideBound w₁
  | 11 => b₀
  | 12 => b₁
  | _ => 0

def inverseRadiusExpr (i : ℕ) : Expr :=
  .div (.const 1) (.add (.const 1) (.neg (.var i)))

def covarianceExpr : Expr :=
  .add
    (.mul (.var 0)
      (.add
        (.add (.mul (.var 2) (.var 3))
          (.mul (.mul (.var 1) (inverseRadiusExpr 6)) (.var 8)))
        (.mul (.mul (.var 1) (inverseRadiusExpr 5)) (.var 10))))
    (.mul (.var 4)
      (.add
        (.mul (.const 2)
          (.sqrt (.sqrt (.add (.var 7) (.mul (.const 2) (.add (.var 11) (.var 12)))))))
        (.sqrt (.var 9))))

theorem covarianceExpr_exact (n : ℕ) (θ : ℝ) (w₀ w₁ : Window)
    (lam₀ lam₁ E M b₀ b₁ : ℝ) :
    covarianceExpr.eval (covarianceVars n θ w₀ w₁ lam₀ lam₁ E M b₀ b₁) =
      coreWideScalar n θ w₀ w₁ lam₀ lam₁ E M b₀ b₁ := by
  simp [covarianceExpr, inverseRadiusExpr, Expr.eval, covarianceVars,
    coreWideScalar, exceptionalFactor, exceptionalBound, one_div, sub_eq_add_neg]

/-- The certificate checks the exact formula, including positive reciprocal denominators. -/
theorem covariance_certificate_sound {n : ℕ} {θ : ℝ} {w₀ w₁ : Window}
    {lam₀ lam₁ E M b₀ b₁ N : ℝ} {I : Interval}
    (C : ExprCertificate (covarianceVars n θ w₀ w₁ lam₀ lam₁ E M b₀ b₁)
      covarianceExpr I) (hN : I.hi ≤ N) :
    coreWideScalar n θ w₀ w₁ lam₀ lam₁ E M b₀ b₁ ≤ N := by
  rw [← covarianceExpr_exact]
  exact C.sound.2.trans hN

/-- A cover of theta cells checks the whole coefficient without a cell charge. -/
theorem covariance_cover_sound {n : ℕ} {ι : Type*} {domain : Set ℝ}
    (cover : FiniteCover ℝ ι domain) (w₀ w₁ : Window)
    (lam₀ lam₁ E M b₀ b₁ : ℝ) (I : ι → Interval) {N : ℝ}
    (C : ∀ i ∈ cover.indices, ∀ θ ∈ domain, θ ∈ cover.cell i →
      ExprCertificate (covarianceVars n θ w₀ w₁ lam₀ lam₁ E M b₀ b₁) covarianceExpr (I i))
    (hN : ∀ i ∈ cover.indices, (I i).hi ≤ N) :
    ∀ θ ∈ domain, coreWideScalar n θ w₀ w₁ lam₀ lam₁ E M b₀ b₁ ≤ N := by
  intro θ hθ
  obtain ⟨i, hi, hcell⟩ := cover.covers θ hθ
  exact covariance_certificate_sound (C i hi θ hθ hcell) (hN i hi)

end BstLean.Part235
