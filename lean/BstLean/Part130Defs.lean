import BstLean.Part105Defs
import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# Part 130, definitions: random ReLU MLPs with two hidden layers

Role: `delegations/statements/p130-spec.md`. Compare with `MM.md` (north star of 2026-10-08,
"The random MLP distribution"). This file holds definitions only.
Do not use `sorry`, `native_decide` or `axiom`.

## The network (compare `MM.md`: `N(z) = M_{L+1} ReLU(M_L ⋯ ReLU(M_1 z))`, here `L = 2`)

* `relu t = max 0 t`; `reluV v`: `relu` on each coordinate.
* A weight matrix with `m` rows and `k` columns is `Matrix (Fin m) (Fin k) ℝ`; `M *ᵥ z` is the
  product of the matrix `M` and the vector `z` (`Matrix.mulVec`).
* `mlp2 M₁ M₂ M₃ z = M₃ *ᵥ reluV (M₂ *ᵥ reluV (M₁ *ᵥ z))`. No biases.
* `MlpParam k m q`: the triple `(M₁, M₂, M₃)`, `M₁` is `m × k`, `M₂` is `m × m`, `M₃` is `q × m`.
  `mlpEval θ z = mlp2 θ.1 θ.2.1 θ.2.2 z`: the network `ℝ^k → ℝ^q` with weights `θ`.

## The weight distribution

* `gaussMat m k v`: every entry of an `m × k` matrix is an independent Gaussian with mean `0`
  and variance `v`. It is the image of the standard Gaussian on the index type `Fin m × Fin k`
  under `ξ ↦ (√v · ξ(i, j))_{i,j}`.
* `mlpGauss k m q`: the product of `gaussMat m k (2/k)`, `gaussMat m m (2/m)`,
  `gaussMat q m (2/m)`: variance `2/(number of columns)` in each matrix.

## The present question

* `sphPt y = y/|y|` for `y ≠ 0`, and the fixed point `e0 = (1, 0, …, 0)` for `y = 0`.
* `muWn W`: the distribution of `x = sphPt (W(u))`, `u` uniform on the unit sphere of `ℝ^{rn}`.
* `phiN A F x = F(A(x))`; `Bn W A F = ∫ F(A(x)) dμ_W`; `sdn W A F`: the standard deviation of
  `F(A(x))` under `μ_W`.
* The widths of the Focus: `mA n = n²`, `mF n = ⌈n^{3/2}⌉`, `mW n = ⌈n^{7/2}⌉`.
-/

namespace BstLean.Part130

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105 (sphProj)

/-! ## §1 The network -/

/-- `ReLU(t) = max(0, t)`. -/
noncomputable def relu (t : ℝ) : ℝ := max 0 t

/-- `ReLU` on each coordinate of a vector. -/
noncomputable def reluV {ι : Type*} (v : ι → ℝ) : ι → ℝ := fun i => relu (v i)

/-- `|y|² = Σ_i y_i²`. -/
def normSq {ι : Type*} [Fintype ι] (y : ι → ℝ) : ℝ := ∑ i, y i ^ 2

/-- **A ReLU MLP with two hidden layers and no biases**, as a function of its three weight
matrices: `z ↦ M₃ ReLU(M₂ ReLU(M₁ z))`. The matrices may have any sizes that fit. -/
noncomputable def mlp2 {k m₁ m₂ q : ℕ} (M₁ : Matrix (Fin m₁) (Fin k) ℝ)
    (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ) (M₃ : Matrix (Fin q) (Fin m₂) ℝ) (z : Fin k → ℝ) :
    Fin q → ℝ :=
  M₃.mulVec (reluV (M₂.mulVec (reluV (M₁.mulVec z))))

/-- The weights of a ReLU MLP `ℝ^k → ℝ^q` with two hidden layers of width `m`:
`M₁` (`m × k`), `M₂` (`m × m`), `M₃` (`q × m`). -/
abbrev MlpParam (k m q : ℕ) : Type :=
  Matrix (Fin m) (Fin k) ℝ × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin q) (Fin m) ℝ

/-- The network with weights `θ`. -/
noncomputable def mlpEval {k m q : ℕ} (θ : MlpParam k m q) (z : Fin k → ℝ) : Fin q → ℝ :=
  mlp2 θ.1 θ.2.1 θ.2.2 z

/-! ## §2 The weight distribution -/

/-- **A Gaussian matrix**: `m` rows, `k` columns, every entry an independent Gaussian with mean
`0` and variance `v` (for `v ≥ 0`; for `v < 0` the matrix is `0`, because `Real.sqrt v = 0`). -/
noncomputable def gaussMat (m k : ℕ) (v : ℝ) : Measure (Matrix (Fin m) (Fin k) ℝ) :=
  (stdGauss (Fin m × Fin k)).map (fun ξ => Matrix.of fun i j => Real.sqrt v * ξ (i, j))

/-- **The random MLP distribution** (`L = 2`): independent Gaussian weights with mean `0`; an
entry of `M₁` has variance `2/k`, an entry of `M₂` and of `M₃` has variance `2/m` (the number of
columns of each matrix). -/
noncomputable def mlpGauss (k m q : ℕ) : Measure (MlpParam k m q) :=
  (gaussMat m k (2 / (k : ℝ))).prod ((gaussMat m m (2 / (m : ℝ))).prod (gaussMat q m (2 / (m : ℝ))))

/-! ## §3 The present question -/

/-- The fixed point `(1, 0, …, 0)` of `S^{n−1}`. -/
def e0 (n : ℕ) : Fin n → ℝ := fun i => if i.val = 0 then 1 else 0

/-- `y/|y|` for `y ≠ 0`, and the fixed point `e0 n` for `y = 0`. -/
noncomputable def sphPt {n : ℕ} (y : Fin n → ℝ) : Fin n → ℝ :=
  if normSq y = 0 then e0 n else sphProj y

/-- `μ_W`: the distribution of `x = W(u)/|W(u)|` (`e0 n` if `W(u) = 0`), `u` uniform on the unit
sphere of `ℝ^N` (`N = r·n` in the present question). -/
noncomputable def muWn {N m n : ℕ} (W : MlpParam N m n) : Measure (Fin n → ℝ) :=
  (uniformSphere N).map (fun u => sphPt (mlpEval W u))

/-- `x ↦ F(A(x))`. -/
noncomputable def phiN {n mA mF : ℕ} (A : MlpParam n mA n) (F : MlpParam n mF 1)
    (x : Fin n → ℝ) : ℝ :=
  mlpEval F (mlpEval A x) 0

/-- **The target** `B(W, A, F) = E_u F(A(x))`, `x = W(u)/|W(u)|`. -/
noncomputable def Bn {N mW n mA mF : ℕ} (W : MlpParam N mW n) (A : MlpParam n mA n)
    (F : MlpParam n mF 1) : ℝ :=
  ∫ x, phiN A F x ∂muWn W

/-- **The realized spread**: the standard deviation of `F(A(x))` over the random `u`. -/
noncomputable def sdn {N mW n mA mF : ℕ} (W : MlpParam N mW n) (A : MlpParam n mA n)
    (F : MlpParam n mF 1) : ℝ :=
  Real.sqrt (Var[phiN A F; muWn W])

/-- The hidden width of the Agent network: `m_A = n²`. -/
def mA (n : ℕ) : ℕ := n ^ 2

/-- The hidden width of `F`: `m_F = ⌈n^{3/2}⌉`. -/
noncomputable def mF (n : ℕ) : ℕ := ⌈(n : ℝ) ^ ((3 : ℝ) / 2)⌉₊

/-- The hidden width of the World network: `m_W = ⌈n^{7/2}⌉`. -/
noncomputable def mW (n : ℕ) : ℕ := ⌈(n : ℝ) ^ ((7 : ℝ) / 2)⌉₊

/-- **The joint distribution of the three networks of the present question** at `r`, `n`, with
the widths of the Focus: `W`, `A`, `F` independent, each with the random MLP distribution. -/
noncomputable def mlpTriple (r n : ℕ) :
    Measure (MlpParam (r * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) :=
  (mlpGauss (r * n) (mW n) n).prod ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1))

end BstLean.Part130
