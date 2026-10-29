import BstLean.Part174Wfl

/-!
# Part 183 (file `Def`): the centred energy allowance `WflV` and the statement `EnV_stmt`

No proof is left open; no `native_decide` or `axiom` is used.

Part 174's energy fluctuation allowance (`WflR`) bounds the gradient of the transverse energy
`Q(N)` by the FULL mean energy `√(t O²(m + 8))`. The gradient of `Q` is
`2E_v[R_j(v)w(v)] = 2E_v[(R_j(v) − c_j)w(v)]` (the transverse vector `w(v)` has mean zero), so only
the CENTRED energy enters: `Σ_j E_v(R_j − c_j)² ≤ |M₀(a − ā)|² + Σ_j (N w)_j²`, whose mean is
`t(m + 8)·E_v|a(v) − ā|²` at most, and `E_v|a(v) − ā|² ≤ (1 − s²)‖A₁‖_F²/(n − 2) ≤ q n O²/(n − 2)`.

* `WflV n O q = 2c₈L·(√(t(m + 8)·T) + c₈L)`, `L = √(tΛ)`, `Λ = qO²/(n − 2)`, `T = q n O²/(n − 2)`,
  `c₈ = 1.8·π/2` (Part 174: `WflR = a₁ + 2c₈L·√(tO²(m + 8))`; the ratio of the main terms is
  `√(q n/(n − 2)) ≈ 0.768` at `q = 0.5903`).
* `WflJ n O q = 2c₈L·(√(m t T/2) + c₈√t·O)`: the same with the Jensen factor `1/2`
  (`E_v ReLU(z·a(v)) ≥ ReLU(z·ā)`, so `E_z Var_v ReLU(z·a(v)) ≤ t·E_v|a − ā|²/2`); the ratio of the
  main terms to `WflR` is `√(q n/(2(n − 2)))` `≈ 0.543`.
* `EnJ_stmt`: Part 174's `exWn_mom_r` with `WflJ` in place of `WflR` (proved in file `EnJ`).
-/

namespace BstLean.Part183

open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170

/-- The centred energy fluctuation allowance (without the Jensen factor; not used by the chain):
`W_fl = 2c₈L(√(t(m + 8)T) + c₈L)`, `L = √(t·qO²/(n − 2))`, `T = q n O²/(n − 2)`. -/
noncomputable def WflV (n : ℕ) (O q : ℝ) : ℝ :=
  2 * (π / 2 * (18 / 10) * √(tA n * (q * O ^ 2 / ((n : ℝ) - 2)))) *
    (√(tA n * ((mA n : ℝ) + 8) * (q * n * O ^ 2 / ((n : ℝ) - 2))) +
      π / 2 * (18 / 10) * √(tA n * (q * O ^ 2 / ((n : ℝ) - 2))))

/-- **The centred energy fluctuation allowance with the Jensen factor** (used by the chain):
`W_fl = 2c₈L(√(m t T/2) + c₈√t·O)`, `L = √(t·qO²/(n − 2))`, `T = q n O²/(n − 2)`, `t = t_A`,
`m = m_A`, `c₈ = 1.8π/2`. The term `m t T/2` bounds `E_{A₂} Σ_j Var_v ReLU((A₂a(v))_j)`
(Jensen: `E_v ReLU(z·a(v)) ≥ ReLU(z·ā)`); `c₈√t·O` is the `L⁸` concentration of its square root
(Lipschitz constant `√t·O`). -/
noncomputable def WflJ (n : ℕ) (O q : ℝ) : ℝ :=
  2 * (π / 2 * (18 / 10) * √(tA n * (q * O ^ 2 / ((n : ℝ) - 2)))) *
    (√((mA n : ℝ) * tA n * (q * n * O ^ 2 / ((n : ℝ) - 2)) / 2) +
      π / 2 * (18 / 10) * (√(tA n) * O))

/-- **The centred energy** of a matrix `M`: `Σ_j Var_v ReLU((M a(v))_j)`. -/
noncomputable def Qvar {V : Type*} [MeasurableSpace V] (μ : Measure V) {m : ℕ}
    (a : V → Fin m → ℝ) (M : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ∑ j, (∫ v, relu ((M *ᵥ a v) j) ^ 2 ∂μ - (∫ v, relu ((M *ᵥ a v) j) ∂μ) ^ 2)

/-- **The centred energy at fixed plane coordinates**:
`Σ_j Var_v ReLU((M₀a(v))_j + (N w(v))_j)`, `w(v) = perp r (perp h (a v))`, `r = res h ā`
(the variance form of Part 170's `flQ`). -/
noncomputable def flQv {V : Type*} [MeasurableSpace V] (μ : Measure V) {m : ℕ}
    (a : V → Fin m → ℝ) (h : Fin m → ℝ) (M₀ N : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ∑ j, (∫ v, relu ((M₀ *ᵥ a v) j + (N *ᵥ BstLean.Part167.perp
      (BstLean.Part134.res h (vmean μ a)) (BstLean.Part167.perp h (a v))) j) ^ 2 ∂μ -
    (∫ v, relu ((M₀ *ᵥ a v) j + (N *ᵥ BstLean.Part167.perp
      (BstLean.Part134.res h (vmean μ a)) (BstLean.Part167.perp h (a v))) j) ∂μ) ^ 2)

/-- **The centred energy fluctuation bound** (statement): Part 174's `exWn_mom_r` with the
allowance `WflJ`. -/
def EnJ_stmt : Prop :=
  ∀ {n : ℕ}, 3 ≤ n → ∀ (c : Ret n) (g : ℕ), nodeS c g ^ 2 ≤ 1 → ∀ {O : ℝ}, 0 < O →
    OpB (A1 c) O → ∀ {q : ℝ}, 0 < q → 1 - nodeS c g ^ 2 ≤ q → ∀ {B : ℝ}, 0 < B →
    ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8) ∂stdGauss (Fin (mA n))
      ∂stdGauss (Fin (mA n)) ≤ ENNReal.ofReal (B ^ 8) →
    ∫⁻ M, ENNReal.ofReal (exWn (withA2 c M) g ^ 8) ∂gaussMat (mA n) (mA n) (tA n) ≤
      ENNReal.ofReal ((WflJ n O q + B) ^ 8)

end BstLean.Part183
