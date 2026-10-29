import BstLean.Part78Defs3

/-!
# Part 78, wave 4: interfaces for the Poincaré inequality with the first chaos separated
-/

namespace BstLean.Part78

open MeasureTheory
open BstLean.Part29 (stdGauss uniformSphere)

variable {n : ℕ}

/-- **Gaussian Poincaré inequality with the first chaos separated**:
`Var P ≤ (1/2) Σ_α E (∂_α P)² + (1/2) Σ_α (E ∂_α P)²`. -/
def PoincareMv2 : Prop :=
  ∀ (ι : Type) [Fintype ι] (P : MvPolynomial ι ℝ),
    ∫ z, (MvPolynomial.eval z P - ∫ w, MvPolynomial.eval w P ∂stdGauss ι) ^ 2 ∂stdGauss ι ≤
      1 / 2 * ∑ α, ∫ z, (MvPolynomial.eval z (MvPolynomial.pderiv α P)) ^ 2 ∂stdGauss ι +
      1 / 2 * ∑ α, (∫ z, MvPolynomial.eval z (MvPolynomial.pderiv α P) ∂stdGauss ι) ^ 2

/-- `r_i(x) = E_W[Q_x T_i(x)] = a_i tr H (κ(x,x) − tG) + 2 (Ha)_i (κ(x,x) − E_y κ(x,y))`. -/
noncomputable def rT (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  a i * (trH H * (kap x x - tG n)) +
    2 * (∑ k, H i k * a k) * (kap x x - ∫ y, kap x y ∂uniformSphere n)

/-- **Conditional variance bound, kernel form, first chaos separated**:
`Var_W V ≤ (1/2)(c/n) E_x[(‖a‖² + 4‖H‖² κ(x,x)) w(x)] + (1/2)(c'/n) E_x Σ_i r_i(x)²`. -/
def VarBoundK2 (n : ℕ) (c c' : ℝ) : Prop :=
  ∀ (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ), H.IsSymm →
    ∫ W, (VG a H W - ∫ W', VG a H W' ∂stdGauss (WIdx n)) ^ 2 ∂stdGauss (WIdx n) ≤
      1 / 2 * (c / (n : ℝ) *
        ∫ x, (nsq a + 4 * frobH H * kap x x) * wQ a H x ∂uniformSphere n) +
      1 / 2 * (c' / (n : ℝ) * ∫ x, ∑ i, rT a H i x ^ 2 ∂uniformSphere n)

end BstLean.Part78
