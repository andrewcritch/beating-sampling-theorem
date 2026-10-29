import BstLean.Part193Interval

/-! Part 193: proof-producing scalar formula certificates.
The expression semantics is an exact real function. Certificate constructors
check every enclosure and every positive-division guard. No float computation
supplies a proof. External analytic functions can enter as variables with
separately proved interval bounds. -/
namespace BstLean.Part193

inductive Expr where
  | const : ℚ → Expr
  | var : ℕ → Expr
  | add : Expr → Expr → Expr
  | neg : Expr → Expr
  | mul : Expr → Expr → Expr
  | div : Expr → Expr → Expr
  | sqrt : Expr → Expr
  | pow : Expr → ℕ → Expr
  | zpow : Expr → ℤ → Expr
  | max : Expr → Expr → Expr
  | min : Expr → Expr → Expr
  | nonnegBranch : Expr → Expr → Expr → Expr

noncomputable def Expr.eval (v : ℕ → ℝ) : Expr → ℝ
  | .const q => (q : ℝ)
  | .var i => v i
  | .add a b => a.eval v + b.eval v
  | .neg a => -a.eval v
  | .mul a b => a.eval v * b.eval v
  | .div a b => a.eval v / b.eval v
  | .sqrt a => Real.sqrt (a.eval v)
  | .pow a k => a.eval v ^ k
  | .zpow a k => a.eval v ^ k
  | .max a b => Max.max (a.eval v) (b.eval v)
  | .min a b => Min.min (a.eval v) (b.eval v)
  | .nonnegBranch c a b => if 0 ≤ c.eval v then a.eval v else b.eval v

/-- A finite proof tree certifies an interval for the exact expression. -/
inductive ExprCertificate (v : ℕ → ℝ) : Expr → Interval → Prop where
  | const (q : ℚ) : ExprCertificate v (.const q) (Interval.point (q : ℝ))
  | var (i : ℕ) (I : Interval) (h : I.Mem (v i)) : ExprCertificate v (.var i) I
  | add {a b I J} : ExprCertificate v a I → ExprCertificate v b J →
      ExprCertificate v (.add a b) (Interval.add I J)
  | neg {a I} : ExprCertificate v a I → ExprCertificate v (.neg a) (Interval.neg I)
  | mul {a b I J} : ExprCertificate v a I → ExprCertificate v b J →
      ExprCertificate v (.mul a b) (Interval.mul I J)
  | div {a b I J} (h : 0 < J.lo) :
      ExprCertificate v a I → ExprCertificate v b J →
      ExprCertificate v (.div a b) (Interval.divPos I J h)
  | sqrt {a I} : ExprCertificate v a I → ExprCertificate v (.sqrt a) (Interval.sqrt I)
  | sqrtBound {a I} (J : Interval) (hl : 0 ≤ J.lo) (hu : 0 ≤ J.hi)
      (hsqlo : J.lo ^ 2 ≤ I.lo) (hsqhi : I.hi ≤ J.hi ^ 2) :
      ExprCertificate v a I → ExprCertificate v (.sqrt a) J
  | pow {a I} (k : ℕ) : ExprCertificate v a I →
      ExprCertificate v (.pow a k) (Interval.pow I k)
  | zpow {a I} (k : ℤ) (h : 0 < I.lo) : ExprCertificate v a I →
      ExprCertificate v (.zpow a k) (Interval.zpowPos I h k)
  | max {a b I J} : ExprCertificate v a I → ExprCertificate v b J →
      ExprCertificate v (.max a b) (Interval.maxInterval I J)
  | min {a b I J} : ExprCertificate v a I → ExprCertificate v b J →
      ExprCertificate v (.min a b) (Interval.minInterval I J)
  | branchHull (c : Expr) {a b I J} : ExprCertificate v a I → ExprCertificate v b J →
      ExprCertificate v (.nonnegBranch c a b) (Interval.hull I J)
  | branchNonneg {c a b K I} (h : 0 ≤ K.lo) :
      ExprCertificate v c K → ExprCertificate v a I →
      ExprCertificate v (.nonnegBranch c a b) I
  | branchNeg {c a b K J} (h : K.hi < 0) :
      ExprCertificate v c K → ExprCertificate v b J →
      ExprCertificate v (.nonnegBranch c a b) J
  | weaken {a I} (J : Interval) (hl : J.lo ≤ I.lo) (hu : I.hi ≤ J.hi) :
      ExprCertificate v a I → ExprCertificate v a J

theorem ExprCertificate.sound {v : ℕ → ℝ} {a : Expr} {I : Interval}
    (C : ExprCertificate v a I) : I.Mem (a.eval v) := by
  induction C with
  | const q => exact Interval.mem_point _
  | var i I h => exact h
  | add _ _ ha hb => exact Interval.mem_add ha hb
  | neg _ ha => exact Interval.mem_neg ha
  | mul _ _ ha hb => exact Interval.mem_mul ha hb
  | div h _ _ ha hb => exact Interval.mem_divPos ha hb h
  | sqrt _ ha => exact Interval.mem_sqrt ha
  | sqrtBound J hl hu hsqlo hsqhi _ ha =>
      exact Interval.sqrt_bounds hl hu (hsqlo.trans ha.1) (ha.2.trans hsqhi)
  | pow k _ ha => exact Interval.mem_pow ha k
  | zpow k h _ ha => exact Interval.mem_zpowPos ha h k
  | max _ _ ha hb => exact Interval.mem_max ha hb
  | min _ _ ha hb => exact Interval.mem_min ha hb
  | branchHull c _ _ ha hb => exact Interval.mem_ite_hull ha hb
  | branchNonneg h _ _ hc ha =>
      simpa only [Expr.eval, ite_eq_left (h.trans hc.1)] using ha
  | branchNeg h _ _ hc hb =>
      simpa only [Expr.eval, ite_eq_right (not_le_of_gt (hc.2.trans_lt h))] using hb
  | weaken J hl hu _ ha => exact Interval.mem_weaken ha hl hu

end BstLean.Part193
