import BstLean.Part78Defs

/-!
# Part 78, wave 2: one more interface — the fourth moment of a Gaussian polynomial of degree `≤ 2`
-/

namespace BstLean.Part78

open MeasureTheory
open BstLean.Part29 (stdGauss)

/-- **Fourth moment at degree two**: `E P⁴ ≤ K₂ (E P²)²` for every polynomial of total degree `≤ 2`
in independent standard Gaussians. -/
def Deg2Fourth (K2 : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (P : MvPolynomial ι ℝ), P.totalDegree ≤ 2 →
    ∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss ι ≤
      K2 * (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι) ^ 2

end BstLean.Part78
