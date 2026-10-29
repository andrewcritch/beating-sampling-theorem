import BstLean.Part78Defs2

/-!
# Part 78, wave 3: interfaces for the sharper conditional variance bound

`wQ a H x = E_W (F_x − E_y F_y)²` is the pointwise (in `x`) mean of the squared centred output.
-/

namespace BstLean.Part78

open MeasureTheory
open BstLean.Part29 (stdGauss uniformSphere)

variable {n : ℕ}

/-- `w(x) = E_W (F_x(W) − E_y F_y(W))²`. -/
noncomputable def wQ (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ W, (FG a H W x - ∫ y, FG a H W y ∂uniformSphere n) ^ 2 ∂stdGauss (WIdx n)

/-- **Conditional variance bound, kernel form**:
`Var_W V ≤ (c/n) E_x[(‖a‖² + 4‖H‖² κ(x,x)) w(x)]`, with `w` continuous and `E_x w = E_W V`. -/
def VarBoundK (n : ℕ) (c : ℝ) : Prop :=
  ∀ (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ), H.IsSymm →
    Continuous (wQ a H) ∧
    ∫ x, wQ a H x ∂uniformSphere n = ∫ W, VG a H W ∂stdGauss (WIdx n) ∧
    ∫ W, (VG a H W - ∫ W', VG a H W' ∂stdGauss (WIdx n)) ^ 2 ∂stdGauss (WIdx n) ≤
      c / (n : ℝ) * ∫ x, (nsq a + 4 * frobH H * kap x x) * wQ a H x ∂uniformSphere n

/-- **The pointwise identity for `w`.** -/
def WQId (n : ℕ) : Prop :=
  ∀ (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ), H.IsSymm → ∀ x : Fin n → ℝ,
    wQ a H x = nsq a * (kap x x - 2 * ∫ y, kap x y ∂uniformSphere n + mm1 n) +
      trH H ^ 2 * (kap x x - tG n) ^ 2 +
      2 * frobH H * (kap x x ^ 2 - 2 * ∫ y, kap x y ^ 2 ∂uniformSphere n + ss2 n)

end BstLean.Part78
