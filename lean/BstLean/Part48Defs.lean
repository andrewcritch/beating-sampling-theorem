import BstLean.Part44Defs

/-!
# Part 48, wave 0: frozen definitions — Theorem G for every degree with no Fradelizi hypothesis

Source: `delegations/answers/omQ4-codex-prover.md` §2–§4 (interpolation on the circle, a
dimension-free fourth moment, Gaussian rotation). Specification: `delegations/answers/p48-spec-opus.md`.
This file holds definitions only. Provers must not edit it, and must not use `native_decide` or
`axiom` anywhere.

Conventions. Part 41, 43 and 44 names are reused. `k = d_f`, `d = d_M`. The small-ball level is a
parameter `t` of the budget: every theorem that needs a level takes `SBLevel (2 * k) p t` as a
hypothesis, and the headline obtains a positive `t` from `sb_level_exists`.

* **Trigonometric polynomials.** `IsTrig h F`: `F s = Σ_{j ≤ h} (a_j cos(j s) + b_j sin(j s))`.
* **Rotation.** `rotX s x y = cos s · x + sin s · y`, `rotY s x y = −sin s · x + cos s · y`.
  `circ` is Lebesgue measure on `(0, 2π]` (total mass `2π`, not normalized).
* **Small-ball level.** `SBLevel h p t`: for every finite `ι` and every nonnegative real polynomial
  `P` of total degree `≤ h`, `γ{P < t·E_γ P} ≤ p` (`γ` the standard Gaussian on `ℝ^ι`).
* **Budget.** `gam48`, `Phi48`, `BudgetOK48` are Part 43's `gam43`, `Phi43` and Part 44's
  `BudgetOK44` with `tsb k q.psb` replaced by the level `t`, and without the conjunct
  `q.psb < 1 − e^{−1}` (Part 43 needed it only for Fradelizi).
-/

namespace BstLean.Part48

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part41 (thetaT Kc etaR etaK GamP Lk Bfix Pn)
open BstLean.Part43 (Params43 tau43 xi43 nu43)

/-! ## §1 Trigonometric polynomials and rotation -/

/-- `F` is a real trigonometric polynomial of degree `≤ h`. -/
def IsTrig (h : ℕ) (F : ℝ → ℝ) : Prop :=
  ∃ a b : ℕ → ℝ, ∀ s : ℝ,
    F s = ∑ j ∈ Finset.range (h + 1), (a j * Real.cos (j * s) + b j * Real.sin (j * s))

/-- Lebesgue measure on the angle interval `(0, 2π]`. -/
noncomputable def circ : Measure ℝ := volume.restrict (Set.Ioc 0 (2 * Real.pi))

/-- `X_s = cos s · X + sin s · Y`. -/
noncomputable def rotX {ι : Type*} (s : ℝ) (x y : ι → ℝ) : ι → ℝ :=
  fun i => Real.cos s * x i + Real.sin s * y i

/-- `Y_s = −sin s · X + cos s · Y`. -/
noncomputable def rotY {ι : Type*} (s : ℝ) (x y : ι → ℝ) : ι → ℝ :=
  fun i => -Real.sin s * x i + Real.cos s * y i

/-! ## §2 The small-ball level -/

/-- `t` is a small-ball level at degree `h` and probability `p`: every nonnegative polynomial `P` of
total degree `≤ h` in standard Gaussians has `γ{P < t E P} ≤ p`. -/
def SBLevel (h : ℕ) (p t : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (P : MvPolynomial ι ℝ), P.totalDegree ≤ h →
    (∀ z, 0 ≤ MvPolynomial.eval z P) →
    stdGauss ι {z | MvPolynomial.eval z P < t * ∫ z', MvPolynomial.eval z' P ∂stdGauss ι} ≤
      ENNReal.ofReal p

/-! ## §3 Budget at level `t` -/

/-- `γ = √(t/K_c) − η_k √(Γ'/β)`. -/
noncomputable def gam48 (n d k : ℕ) (q : Params43) (t : ℝ) : ℝ :=
  Real.sqrt (t / Kc n d k q.eta) - etaK n d k q.x * Real.sqrt (GamP n d k / q.beta)

/-- `Φ(n) = p_sb + 2e^{−x} + β + L τ / ((1 − ξ)² γ²)`. -/
noncomputable def Phi48 (n d k : ℕ) (q : Params43) (t : ℝ) : ℝ :=
  q.psb + 2 * Real.exp (-q.x) + q.beta + Lk k * tau43 n d k / ((1 - xi43) ^ 2 * gam48 n d k q t ^ 2)

/-- The conditions of the proof of Theorem G at `n`, failure budget `δ`, small-ball level `t`. -/
def BudgetOK48 (n d k : ℕ) (q : Params43) (δ t : ℝ) : Prop :=
  2 ≤ n ∧ 1 ≤ d ∧ 0 < tau43 n d k ∧
  0 < q.psb ∧ 0 < q.x ∧ 0 < q.beta ∧ 0 < q.eta ∧
  (1 + 1 / q.eta) * thetaT n d k < 1 ∧ etaR n d q.x < 1 ∧ 0 < Kc n d k q.eta ∧
  0 < gam48 n d k q t ∧ 455 / 1000 * Bfix n k < (1 - nu43) * (91 / 100) * Pn n d ∧
  Phi48 n d k q t ≤ δ

end BstLean.Part48
