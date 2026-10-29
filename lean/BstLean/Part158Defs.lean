import BstLean.Part157Mgf
import BstLean.Part152SF
import BstLean.Part148GC

/-!
# Part 158 (file `Defs`): the objects of the interpolation proof of the inequality (GP)

Do not use `sorry`, `native_decide` or `axiom`.

Paper: `theorem7-02-world.tex`, Lemma `t7:p02:GP`. The Lean proof is the interpolation
`cos θ · ξ + sin θ · ξ'` of two independent standard Gaussian vectors (the Ornstein–Uhlenbeck
semigroup at the time `v = −log cos θ`), with Gaussian integration by parts.

`γ = stdGauss ι`. `F x : (ι → ℝ) → ℝ` is a family of functions on the Gaussian space, with
gradient `dF x`. For real `c`, `s`:

* `U F c s x ξ = E_{ξ'} F x (c ξ + s ξ')`;
* `Abar dF c s x ξ k = E_{ξ'} (dF x (c ξ + s ξ'))_k`;
* `wv = Abar / U` (the gradient of `log U`, without the factor `c`);
* `Vv μ L … ξ k = L⁻¹ ∫ wv … x ξ k dμ(x)`;
* `T μ L F c s ξ = L⁻¹ ∫ log (U F c s x ξ) dμ(x)`;
* `Psi μ L F c s = E_ξ exp (T μ L F c s ξ)`.
-/

namespace BstLean.Part158

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)

/-- The linear functional `v ↦ Σ_k a_k v_k`. -/
noncomputable def dotL {ι : Type} [Fintype ι] (a : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ k, a k • (ContinuousLinearMap.proj k : (ι → ℝ) →L[ℝ] ℝ)

lemma dotL_apply {ι : Type} [Fintype ι] (a v : ι → ℝ) : dotL a v = ∑ k, a k * v k := by
  simp [dotL]

/-- **A regular family**: `F x` is a function on `ℝ^ι` with values in `[a, b]`, `0 < a`,
differentiable with gradient `dF x`, every component of the gradient bounded by `C`; `F` and `dF`
are jointly measurable. -/
structure Fam {X : Type*} [MeasurableSpace X] {ι : Type} [Fintype ι]
    (F : X → (ι → ℝ) → ℝ) (dF : X → (ι → ℝ) → ι → ℝ) (a b C : ℝ) : Prop where
  mF : Measurable (fun p : X × (ι → ℝ) => F p.1 p.2)
  mdF : Measurable (fun p : X × (ι → ℝ) => dF p.1 p.2)
  ha : 0 < a
  lo : ∀ x ξ, a ≤ F x ξ
  hi : ∀ x ξ, F x ξ ≤ b
  hd : ∀ x ξ, HasFDerivAt (F x) (dotL (dF x ξ)) ξ
  hC : ∀ x ξ k, |dF x ξ k| ≤ C

variable {X : Type*} [MeasurableSpace X] {ι : Type} [Fintype ι]

/-- `U F c s x ξ = E_{ξ'} F x (c ξ + s ξ')`. -/
noncomputable def U (F : X → (ι → ℝ) → ℝ) (c s : ℝ) (x : X) (ξ : ι → ℝ) : ℝ :=
  ∫ ξ', F x (c • ξ + s • ξ') ∂stdGauss ι

/-- `Abar dF c s x ξ k = E_{ξ'} (dF x (c ξ + s ξ'))_k`. -/
noncomputable def Abar (dF : X → (ι → ℝ) → ι → ℝ) (c s : ℝ) (x : X) (ξ : ι → ℝ) (k : ι) : ℝ :=
  ∫ ξ', dF x (c • ξ + s • ξ') k ∂stdGauss ι

/-- `wv = Abar / U`. -/
noncomputable def wv (F : X → (ι → ℝ) → ℝ) (dF : X → (ι → ℝ) → ι → ℝ) (c s : ℝ) (x : X)
    (ξ : ι → ℝ) (k : ι) : ℝ :=
  Abar dF c s x ξ k / U F c s x ξ

/-- `Vv = L⁻¹ ∫ wv dμ(x)`. -/
noncomputable def Vv (μ : Measure X) (L : ℝ) (F : X → (ι → ℝ) → ℝ) (dF : X → (ι → ℝ) → ι → ℝ)
    (c s : ℝ) (ξ : ι → ℝ) (k : ι) : ℝ :=
  L⁻¹ * ∫ x, wv F dF c s x ξ k ∂μ

/-- `T = L⁻¹ ∫ log U dμ(x)`. -/
noncomputable def T (μ : Measure X) (L : ℝ) (F : X → (ι → ℝ) → ℝ) (c s : ℝ) (ξ : ι → ℝ) : ℝ :=
  L⁻¹ * ∫ x, log (U F c s x ξ) ∂μ

/-- `Psi = E_ξ exp T`. -/
noncomputable def Psi (μ : Measure X) (L : ℝ) (F : X → (ι → ℝ) → ℝ) (c s : ℝ) : ℝ :=
  ∫ ξ, exp (T μ L F c s ξ) ∂stdGauss ι

/-- The statement of the derivative formula of the interpolation (proved in `Part158Deriv`):
`d/dθ Psi(cos θ, sin θ) = sin θ cos θ · E_ξ [e^T · Σ_k (L⁻¹ ∫ w_k² dμ − V_k²)]`. -/
def PsiDerivStmt : Prop :=
  ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] {ι : Type} [Fintype ι]
    {F : X → (ι → ℝ) → ℝ} {dF : X → (ι → ℝ) → ι → ℝ} {a b C : ℝ}, Fam F dF a b C →
    ∀ (L θ : ℝ),
    HasDerivAt (fun θ => Psi μ L F (cos θ) (sin θ))
      (sin θ * cos θ * ∫ ξ, exp (T μ L F (cos θ) (sin θ) ξ) *
        ∑ k, (L⁻¹ * ∫ x, wv F dF (cos θ) (sin θ) x ξ k ^ 2 ∂μ -
          Vv μ L F dF (cos θ) (sin θ) ξ k ^ 2) ∂stdGauss ι) θ

/-- The statement of the inequality (GP) for a FINITE measure `μ`, unit vectors `e(x)` and
functions `f(x, ·)` that are differentiable with a bounded gradient (proved in
`Part158Smooth`). -/
def GPSmoothStmt : Prop :=
  ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] {q m : ℕ}
    (e : X → Fin m → ℝ), Measurable e → (∀ x, BstLean.Part130.normSq (e x) = 1) →
    ∀ (f : X × (Fin q → ℝ) → ℝ), Measurable f →
    ∀ (f' : X × (Fin q → ℝ) → Fin q → ℝ), Measurable f' →
    (∀ x z, HasFDerivAt (fun z => f (x, z)) (dotL (f' (x, z))) z) →
    ∀ a b C : ℝ, 0 < a → (∀ y, a ≤ f y) → (∀ y, f y ≤ b) → (∀ y i, |f' y i| ≤ C) →
    ∀ L : ℝ, 0 < L →
    (∀ w : Fin m → ℝ, ∫ x, (∑ j, e x j * w j) ^ 2 ∂μ ≤ L * ∑ j, w j ^ 2) →
    ∫ G, exp (1 / L * ∫ x, log (f (x, G.mulVec (e x))) ∂μ) ∂BstLean.Part130.gaussMat q m 1 ≤
      exp (1 / L * ∫ x, log (∫ z, f (x, z) ∂stdGauss (Fin q)) ∂μ)

end BstLean.Part158
