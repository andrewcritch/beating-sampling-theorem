import BstLean.Part71Defs

/-!
# Part 71: the interface statements of the Theorem 4 chain for `ChiLaw`

Copies of the `Part59Defs` §6 interfaces (`PropE59`, `PropF59`, `LemmaV59`, `RadialTail59`,
`PropT1_59`, `PropT2_59`) with `UpLaw n μ K` replaced by `ChiLaw n μ K`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part71

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part59
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM contr trL frob IsSymmT Tens TSymm fval Pn varU sdU mset)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part53 (sg c0 aH g0 heatA fvA Ncirc Reads53)

/-- **Prop E** (proxy error), distributions with `χ²(D‖σ) ≤ K`. -/
def PropE71 (d k : ℕ) (K C : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ μ : Measure (Fin n → ℝ), ChiLaw n μ K →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
      Integrable (fun Z => (BofQ μ k f0 T (sg n d • Z) - g0 n d k f0 T (sg n d • Z)) ^ 2)
          (stdGauss (CoefIdxD n d)) ∧
      ∫ Z, (BofQ μ k f0 T (sg n d • Z) - g0 n d k f0 T (sg n d • Z)) ^ 2
          ∂stdGauss (CoefIdxD n d) ≤ C / n * Ncirc n d k f0 T

/-- **Prop F** (proxy floor), distributions with `χ²(D‖σ) ≤ K`. -/
def PropF71 (d k : ℕ) (K : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ μ : Measure (Fin n → ℝ), ChiLaw n μ K →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
      Ncirc n d k f0 T / 8 ≤ ∫ Z, varFQ μ k f0 T (sg n d • Z) ∂stdGauss (CoefIdxD n d)

/-- **Lemma V** (proxy variance of any polynomial of degree `≤ k`), distributions with `χ²(D‖σ) ≤ K`. -/
def LemmaV71 (d k : ℕ) (K C : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ μ : Measure (Fin n → ℝ), ChiLaw n μ K →
    ∀ A : Tens n, (∀ j, IsSymmT (A j)) →
      Integrable (fun Z => varU μ (fun x => fvA k A (mapMD (sg n d • Z) x))) (stdGauss (CoefIdxD n d)) ∧
      ∫ Z, varU μ (fun x => fvA k A (mapMD (sg n d • Z) x)) ∂stdGauss (CoefIdxD n d) ≤ C * NcA n d k A

/-- **Radial tail** (the second event of Prop T2*): `Pr_Z{√(sN°) ≤ radDef(Z/‖Z‖, λ)} ≤ C/(ns)`. -/
def RadialTail71 (d k : ℕ) (K C : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ μ : Measure (Fin n → ℝ), ChiLaw n μ K →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) → ∀ s : ℝ, 0 < s →
      stdGauss (CoefIdxD n d) {Z | Real.sqrt (s * Ncirc n d k f0 T) ≤
        radDef59 μ k f0 T (unitOfD Z) (lam59 n d Z)} ≤ ENNReal.ofReal (C / (n * s))

/-- **Prop T1*** (error on the coefficient sphere, with Markov), distributions with `χ²(D‖σ) ≤ K`. -/
def PropT1_71 (d k : ℕ) (K C : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ μ : Measure (Fin n → ℝ), ChiLaw n μ K →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) → ∀ c : ℝ, 0 < c →
      stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
        c * Ncirc n d k f0 T ≤ (BofQ μ k f0 T (unitOfD Z) - g0 n d k f0 T (unitOfD Z)) ^ 2} ≤
        ENNReal.ofReal (C / (n * c))

/-- **Prop T2*** (floor on the coefficient sphere), distributions with `χ²(D‖σ) ≤ K`. -/
def PropT2_71 (d k : ℕ) (K p s C : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ μ : Measure (Fin n → ℝ), ChiLaw n μ K →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
      stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧ varFQ μ k f0 T (unitOfD Z) < s * Ncirc n d k f0 T} ≤
        ENNReal.ofReal (p + C / (n * s))

end BstLean.Part71
