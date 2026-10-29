import BstLean.Part197Exp
import BstLean.Part197Log
import BstLean.Part197Erfc
import BstLean.Part197Kernel
import BstLean.Part193Certificate

/-! Part 197: exact polynomial syntax and analytic certificate adapters.
Every finite sum has Part193 arithmetic semantics. Each adapter adds a proved remainder. -/
namespace BstLean.Part197

open BstLean.Part193

def sumExpr : ℕ → (ℕ → Expr) → Expr
  | 0, _ => .const 0
  | N + 1, f => .add (sumExpr N f) (f N)

theorem eval_sumExpr (N : ℕ) (f : ℕ → Expr) (v : ℕ → ℝ) :
    (sumExpr N f).eval v = ∑ j ∈ Finset.range N, (f j).eval v := by
  induction N with
  | zero => simp [sumExpr, Expr.eval]
  | succ N h => simp [sumExpr, Expr.eval, h, Finset.sum_range_succ]

theorem sum_expr_certificate {v : ℕ → ℝ} (N : ℕ) (f : ℕ → Expr) (I : ℕ → Interval)
    (h : ∀ j ∈ Finset.range N, ExprCertificate v (f j) (I j)) :
    ExprCertificate v (sumExpr N f) (Interval.sum (Finset.range N) I) := by
  induction N with
  | zero =>
      convert ExprCertificate.const (v := v) 0 using 1 <;>
        simp [sumExpr, Interval.sum, Interval.point]
  | succ N ih =>
      have hprev : ∀ j ∈ Finset.range N, ExprCertificate v (f j) (I j) :=
        fun j hj => h j (Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans N.lt_succ_self))
      have hn := h N (Finset.mem_range.mpr N.lt_succ_self)
      have hc := ExprCertificate.add (ih hprev) hn
      convert hc using 1 <;>
        simp [sumExpr, Interval.sum, Interval.add, Finset.sum_range_succ]

def expSumExpr (N : ℕ) (a : Expr) : Expr :=
  sumExpr N fun j => .mul (.pow a j) (.const ((j.factorial : ℚ)⁻¹))

theorem eval_expSumExpr (N : ℕ) (a : Expr) (v : ℕ → ℝ) :
    (expSumExpr N a).eval v = expSum N (a.eval v) := by
  simp only [expSumExpr, eval_sumExpr, Expr.eval, expSum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [div_eq_mul_inv]

def logOneAddSumExpr (N : ℕ) (a : Expr) : Expr :=
  .neg (sumExpr N fun j => .mul (.pow (.neg a) (j + 1)) (.const (((j + 1 : ℕ) : ℚ)⁻¹)))

theorem eval_logOneAddSumExpr (N : ℕ) (a : Expr) (v : ℕ → ℝ) :
    (logOneAddSumExpr N a).eval v = logOneAddSum N (a.eval v) := by
  simp only [logOneAddSumExpr, Expr.eval, eval_sumExpr, logOneAddSum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp [div_eq_mul_inv]

def logRatioSumExpr (N : ℕ) (a : Expr) : Expr :=
  .mul (.const 2) (sumExpr N fun j =>
    .mul (.pow a (2 * j + 1)) (.const (((2 * j + 1 : ℕ) : ℚ)⁻¹)))

theorem eval_logRatioSumExpr (N : ℕ) (a : Expr) (v : ℕ → ℝ) :
    (logRatioSumExpr N a).eval v = logRatioSum N (a.eval v) := by
  simp only [logRatioSumExpr, Expr.eval, eval_sumExpr, logRatioSum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp [div_eq_mul_inv]

def logPositiveSumExpr (N : ℕ) (a : Expr) : Expr :=
  logRatioSumExpr N (.div (.add a (.const (-1))) (.add a (.const 1)))

theorem eval_logPositiveSumExpr (N : ℕ) (a : Expr) (v : ℕ → ℝ) :
    (logPositiveSumExpr N a).eval v =
      logRatioSum N ((a.eval v - 1) / (a.eval v + 1)) := by
  simp [logPositiveSumExpr, eval_logRatioSumExpr, Expr.eval, sub_eq_add_neg]

def atanSumExpr (N : ℕ) (a : Expr) : Expr :=
  sumExpr N fun j => .mul (.const ((-1 : ℚ) ^ j / (2 * j + 1))) (.pow a (2 * j + 1))

theorem eval_atanSumExpr (N : ℕ) (a : Expr) (v : ℕ → ℝ) :
    (atanSumExpr N a).eval v = atanSum N (a.eval v) := by
  simp only [atanSumExpr, eval_sumExpr, Expr.eval, atanSum]
  apply Finset.sum_congr rfl
  intro j hj
  push_cast
  ring

def erfSumExpr (N : ℕ) (a : Expr) : Expr :=
  sumExpr N fun j =>
    .mul (.const ((-1 : ℚ) ^ j / ((j.factorial : ℚ) * (2 * j + 1)))) (.pow a (2 * j + 1))

theorem eval_erfSumExpr (N : ℕ) (a : Expr) (v : ℕ → ℝ) :
    (erfSumExpr N a).eval v = erfSum N (a.eval v) := by
  simp only [erfSumExpr, eval_sumExpr, Expr.eval, erfSum]
  apply Finset.sum_congr rfl
  intro j hj
  push_cast
  ring

def erfcSumExpr (N : ℕ) (a piExpr : Expr) : Expr :=
  .add (.const 1) (.neg (.mul (.div (.const 2) (.sqrt piExpr)) (erfSumExpr N a)))

theorem eval_erfcSumExpr (N : ℕ) (a piExpr : Expr) (v : ℕ → ℝ)
    (hpi : piExpr.eval v = Real.pi) :
    (erfcSumExpr N a piExpr).eval v = erfcSum N (a.eval v) := by
  simp [erfcSumExpr, Expr.eval, eval_erfSumExpr, hpi, erfcSum, sub_eq_add_neg]

def angleRatioExpr (a : Expr) : Expr :=
  .sqrt (.div (.add (.const 1) (.neg a)) (.add (.const 1) a))

theorem eval_angleRatioExpr (a : Expr) (v : ℕ → ℝ) :
    (angleRatioExpr a).eval v = angleRatio (a.eval v) := by
  simp [angleRatioExpr, Expr.eval, angleRatio, sub_eq_add_neg]

def kernelSlopeSumExpr (N : ℕ) (a piExpr : Expr) : Expr :=
  .div (.add piExpr (.neg (.mul (.const 2) (atanSumExpr N (angleRatioExpr a))))) piExpr

theorem eval_kernelSlopeSumExpr (N : ℕ) (a piExpr : Expr) (v : ℕ → ℝ)
    (hpi : piExpr.eval v = Real.pi) :
    (kernelSlopeSumExpr N a piExpr).eval v = kernelSlopeSum N (a.eval v) := by
  simp [kernelSlopeSumExpr, Expr.eval, eval_atanSumExpr, eval_angleRatioExpr,
    hpi, kernelSlopeSum, sub_eq_add_neg]

def kernelSumExpr (N : ℕ) (a piExpr : Expr) : Expr :=
  .add (.div (.sqrt (.add (.const 1) (.neg (.pow a 2)))) piExpr)
    (.mul a (kernelSlopeSumExpr N a piExpr))

theorem eval_kernelSumExpr (N : ℕ) (a piExpr : Expr) (v : ℕ → ℝ)
    (hpi : piExpr.eval v = Real.pi) :
    (kernelSumExpr N a piExpr).eval v = kernelSum N (a.eval v) := by
  simp only [kernelSumExpr, Expr.eval, eval_kernelSlopeSumExpr N a piExpr v hpi, hpi]
  unfold kernelSum kernelSlopeSum
  push_cast
  ring

/-- A polynomial certificate and a certified residual bound enclose the exact function. -/
theorem remainder_certificate {v : ℕ → ℝ} {a : Expr} {P J : Interval} {y R : ℝ}
    (C : ExprCertificate v a P) (h : |y - a.eval v| ≤ R)
    (hl : J.lo ≤ P.lo - R) (hu : P.hi + R ≤ J.hi) : J.Mem y := by
  have hp := C.sound
  have hr := abs_le.mp h
  constructor <;> linarith [hp.1, hp.2, hr.1, hr.2]

theorem exp_expr_mem {v : ℕ → ℝ} {a : Expr} {P J : Interval} {b : ℝ} {N : ℕ}
    (hN : 0 < N) (hx : |a.eval v| ≤ b) (hb : b ≤ 1)
    (C : ExprCertificate v (expSumExpr N a) P)
    (hl : J.lo ≤ P.lo - expError N b) (hu : P.hi + expError N b ≤ J.hi) :
    J.Mem (Real.exp (a.eval v)) := by
  apply remainder_certificate C _ hl hu
  rw [eval_expSumExpr]
  exact exp_remainder hN hx hb

theorem log_one_add_expr_mem {v : ℕ → ℝ} {a : Expr} {P J : Interval} {N : ℕ}
    (hx : |a.eval v| < 1) (C : ExprCertificate v (logOneAddSumExpr N a) P)
    {R : ℝ} (hR : |a.eval v| ^ (N + 1) / (1 - |a.eval v|) ≤ R)
    (hl : J.lo ≤ P.lo - R) (hu : P.hi + R ≤ J.hi) :
    J.Mem (Real.log (1 + a.eval v)) := by
  apply remainder_certificate C _ hl hu
  rw [eval_logOneAddSumExpr]
  exact (log_one_add_remainder hx N).trans hR

theorem log_positive_expr_mem {v : ℕ → ℝ} {a : Expr} {P J : Interval} {N : ℕ}
    (hy : 0 < a.eval v) (C : ExprCertificate v (logPositiveSumExpr N a) P)
    {R : ℝ} (hR : 2 * (|(a.eval v - 1) / (a.eval v + 1)| ^ (2 * N + 1) /
      (1 - ((a.eval v - 1) / (a.eval v + 1)) ^ 2)) ≤ R)
    (hl : J.lo ≤ P.lo - R) (hu : P.hi + R ≤ J.hi) : J.Mem (Real.log (a.eval v)) := by
  apply remainder_certificate C _ hl hu
  rw [eval_logPositiveSumExpr]
  exact (log_positive_remainder hy N).trans hR

theorem erfc_expr_mem {v : ℕ → ℝ} {a piExpr : Expr} {P J : Interval} {n : ℕ}
    (hz : 0 ≤ a.eval v) (hpi : piExpr.eval v = Real.pi)
    (C : ExprCertificate v (erfcSumExpr (n + 1) a piExpr) P)
    {R : ℝ} (hR : erfcError (n + 1) (a.eval v) ≤ R)
    (hl : J.lo ≤ P.lo - R) (hu : P.hi + R ≤ J.hi) : J.Mem (erfc (a.eval v)) := by
  apply remainder_certificate C _ hl hu
  rw [eval_erfcSumExpr _ _ _ _ hpi]
  exact (erfc_remainder hz n).trans hR

theorem kernel_expr_mem {v : ℕ → ℝ} {a piExpr : Expr} {P J : Interval} {N : ℕ}
    (hc : 0 < a.eval v) (hc1 : a.eval v ≤ 1) (hpi : piExpr.eval v = Real.pi)
    (C : ExprCertificate v (kernelSumExpr N a piExpr) P)
    {R : ℝ} (hR : a.eval v * (2 * (angleRatio (a.eval v) ^ (2 * N + 1) /
      (2 * N + 1))) / Real.pi ≤ R)
    (hl : J.lo ≤ P.lo - R) (hu : P.hi + R ≤ J.hi) :
    J.Mem (BstLean.Part130.kappa (a.eval v)) := by
  apply remainder_certificate C _ hl hu
  rw [eval_kernelSumExpr _ _ _ _ hpi]
  exact (kernel_remainder hc hc1 N).trans hR

theorem kernel_slope_expr_mem {v : ℕ → ℝ} {a piExpr : Expr} {P J : Interval} {N : ℕ}
    (hc : 0 < a.eval v) (hc1 : a.eval v ≤ 1) (hpi : piExpr.eval v = Real.pi)
    (C : ExprCertificate v (kernelSlopeSumExpr N a piExpr) P)
    {R : ℝ} (hR : (2 * (angleRatio (a.eval v) ^ (2 * N + 1) /
      (2 * N + 1))) / Real.pi ≤ R)
    (hl : J.lo ≤ P.lo - R) (hu : P.hi + R ≤ J.hi) :
    J.Mem (kernelSlope (a.eval v)) := by
  apply remainder_certificate C _ hl hu
  rw [eval_kernelSlopeSumExpr _ _ _ _ hpi]
  exact (kernel_slope_remainder hc hc1 N).trans hR

end BstLean.Part197
