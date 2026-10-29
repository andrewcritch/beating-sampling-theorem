import BstLean.Part140Cost

/-!
# Part 141, definitions: the finite ReLU sum (atom sum) and the arithmetic centre

Role: `delegations/statements/p141-spec.md`. Paper sources: `onW8c-cx.md` §§2–3.

* `atomSum p z s x = Σ_ℓ p_ℓ·relu(x + s·z_ℓ)`: a finite ReLU sum with atoms `z_ℓ` and weights
  `p_ℓ`.
* `zQ q R`: the rational atoms `(ℓ − Rq)/q`, `ℓ = 0, …, 2Rq`: the grid of mesh `1/q` on `[−R, R]`.
* `quant q R z = ⌊clip(z)·q⌋`, `clip(z) = max(−R, min(R, z))`: the cell index of `z`.
* `pR q R ℓ`: the probability that a standard Gaussian number is in cell `ℓ` (a real number).
* `pQ q R D ℓ`: RATIONAL weights: `⌊D·pR ℓ⌋/D` for `ℓ ≠ 0`, and the weight at `ℓ = 0` is
  `1 −` (the sum of the other weights). They depend on `(q, R, D)` only.
* `aOf c θ = M₂·(c·|row_j(M₁)|)_j`, `sOf c θ = √(Σ_j|row_j|²·(1/(mN) − (2/m)c²))`: the values
  that the program `preProg` of Part 140 computes with a constant `c` in the place of `c_N`.
* `bOf c p z θ`: the centre `b_i = atomSum p z (sOf c θ) (aOf c θ i)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part141

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part136

/-- **A finite ReLU sum**: `Σ_ℓ p_ℓ·relu(x + s·z_ℓ)`. -/
noncomputable def atomSum {L : ℕ} (p z : Fin L → ℝ) (s x : ℝ) : ℝ :=
  ∑ ℓ, p ℓ * relu (x + s * z ℓ)

/-- The rational atoms: the grid of mesh `1/q` on `[−R, R]`. -/
def zQ (q R : ℕ) : Fin (2 * R * q + 1) → ℚ := fun ℓ => (((ℓ : ℕ) : ℚ) - (R * q : ℕ)) / (q : ℚ)

/-- The cell index of `z`: `⌊clip(z)·q⌋`, `clip(z) = max(−R, min(R, z))`. -/
noncomputable def quant (q R : ℕ) (z : ℝ) : ℤ := ⌊max (-(R : ℝ)) (min (R : ℝ) z) * (q : ℝ)⌋

/-- The probability of cell `ℓ` under the standard Gaussian distribution. -/
noncomputable def pR (q R : ℕ) : Fin (2 * R * q + 1) → ℝ := fun ℓ =>
  (gaussianReal 0 1).real {z | quant q R z = ((ℓ : ℕ) : ℤ) - ((R * q : ℕ) : ℤ)}

/-- **The rational weights**: `⌊D·pR ℓ⌋/D` for `ℓ ≠ 0`; the weight at `ℓ = 0` is `1` minus the
sum of the other weights. -/
noncomputable def pQ (q R D : ℕ) : Fin (2 * R * q + 1) → ℚ := fun ℓ =>
  if ℓ = 0 then 1 - ∑ ℓ' ∈ Finset.univ.erase (0 : Fin (2 * R * q + 1)),
      ((⌊(D : ℝ) * pR q R ℓ'⌋ : ℤ) : ℚ) / (D : ℚ)
  else ((⌊(D : ℝ) * pR q R ℓ⌋ : ℤ) : ℚ) / (D : ℚ)

section centre

variable {N m : ℕ}

/-- `a = M₂·(c·|row_j(M₁)|)_j`. -/
noncomputable def aOf (c : ℝ) (θ : HidParam N m) : Fin m → ℝ :=
  θ.2.mulVec (fun j => c * √(normSq (rowOf j θ.1)))

/-- `s = √(Σ_j|row_j(M₁)|²·(1/(mN) − (2/m)c²))`. -/
noncomputable def sOf (c : ℝ) (θ : HidParam N m) : ℝ :=
  √((∑ j, normSq (rowOf j θ.1)) * (1 / ((m : ℝ) * N) - 2 / (m : ℝ) * (c * c)))

/-- **The centre of a finite ReLU sum**: `b_i = Σ_ℓ p_ℓ·relu(a_i + s·z_ℓ)`. -/
noncomputable def bOf {L : ℕ} (c : ℝ) (p z : Fin L → ℝ) (θ : HidParam N m) : Fin m → ℝ :=
  fun i => atomSum p z (sOf c θ) (aOf c θ i)

end centre

end BstLean.Part141
