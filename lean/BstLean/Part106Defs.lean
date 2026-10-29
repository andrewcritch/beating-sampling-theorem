import BstLean.Part105Final
import BstLean.Part105Cost

/-!
# Part 106, definitions: the program `g` and its random inputs

Role: `delegations/statements/p106-spec.md`. Paper source:
`delegations/answers/oaW2-opus-prover.md` (the program `g_k`, Theorem 0).

* `phiAF A F = F ∘ A` as a function on `ℝⁿ` (`A : ℝⁿ → ℝⁿ` of degree at most `d_A`,
  `F : ℝⁿ → ℝ` of degree at most `d_F`, both given by monomial coefficients).
* A *block* of random inputs of the program is a pair `(u, g)`: `u` a point of `ℝ^N` (uniform on
  the unit sphere) and `g` a point of `ℝⁿ` (standard Gaussian). The program uses `k` independent
  blocks: a point of `Fin k → (Fin N → ℝ) × (Fin n → ℝ)` with the measure
  `Measure.pi fun _ => (uniformSphere N).prod (stdGauss (Fin n))`.
* `standIn b0 τ (u, g) = y/|y|`, `y = W_0 + W_1 u + τ g`: one sample of the stand-in. It reads
  only the coefficients of degree `0` and `1` of `b0`.
* `gVal b0 τ φ ω = (1/k) Σ_i φ(standIn b0 τ (ω i))`: the value that the program returns.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part106

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105

/-- `φ = F ∘ A`: the composition of the Agent polynomial `A` and of `F`, on `ℝⁿ`. -/
noncomputable def phiAF {n dA dF : ℕ} (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  bwEval F (bwEval A x) 0

/-- One sample of the stand-in from one block `(u, g)` of random inputs:
`y/|y|`, `y = W_0 + W_1 u + τ g`. -/
noncomputable def standIn {N n d : ℕ} (b0 : CoefIdx N n d → ℝ) (τ : ℝ)
    (p : (Fin N → ℝ) × (Fin n → ℝ)) : Fin n → ℝ :=
  sphProj (bwEval (mixW b0 0) p.1 + τ • p.2)

/-- The value of the program `g`: the mean of `φ` over `k` samples of the stand-in. -/
noncomputable def gVal {N n d k : ℕ} (b0 : CoefIdx N n d → ℝ) (τ : ℝ) (φ : (Fin n → ℝ) → ℝ)
    (ω : Fin k → (Fin N → ℝ) × (Fin n → ℝ)) : ℝ :=
  (∑ i, φ (standIn b0 τ (ω i))) / (k : ℝ)

/-- The stand-in distribution `ν_W` is the distribution of `standIn` of one block. -/
theorem nuW_eq_map {N n d : ℕ} (b0 : CoefIdx N n d → ℝ) (τ : ℝ) :
    nuW b0 τ = ((uniformSphere N).prod (stdGauss (Fin n))).map (standIn b0 τ) := rfl

end BstLean.Part106
