import BstLean.Part150Defs

/-!
# Part 150, item 3, definitions: the finite centre and the oracle centre of `A`

Role: `delegations/statements/p150-spec.md`, item 3. Paper source: `onW45-opus-prover.md` §1
("The oracle centre", "The finite centre").

`A₁ : m × n`, `A₂ : m × m`, `A₃ : n × m` are the three matrices of the Agent network `A`
(hidden width `m`); `c` and `τ` are the centre and the scalar of the `W` stage (`ĉ`, `τ_0`);
`t = 2/m`; `J₁`, `J₂` are the atom counts of the first and of the second layer.

* `mRow i = (A₁ c)_i`, `sRow i = τ·|row_i(A₁)|`.
* The FINITE centre (binomial sums): `hT`, `gT`, `sT2`, `sT`, `bT`, and `rhoC`, `cT`, `sigT`.
* The ORACLE centre (exact Gaussian means; a device of the proof): `hO`, `gO`, `sO2`, `sO`, `bO`.

**Difference with Part 149.** The oracle centre here is the one of the paper (`onW43`, `onW45`
§1): the Gaussian means `ψ_{s_i}(m_i)` of the stand-in input `ĉ + τ_0 g` WITHOUT normalization
to the sphere; the factor `1/ρ` is applied at the end (`cT`, `sigT`). The mean-field centre
`bMF` of Part 149 uses the exact means over the sphere-normalized inputs `sphPt (c + τγ)`. The
two are different functions.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Finset
open BstLean.Part130 BstLean.Part137

noncomputable section

variable {n m : ℕ}

/-- `m_i = (A₁ c)_i`. -/
def mRow (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (i : Fin m) : ℝ := (A₁.mulVec c) i

/-- `s_i = τ·|row_i(A₁)|`. -/
def sRow (A₁ : Matrix (Fin m) (Fin n) ℝ) (τ : ℝ) (i : Fin m) : ℝ := τ * √(∑ j, A₁ i j ^ 2)

/-- The squared Frobenius norm of `A₁`. -/
def froSq (A₁ : Matrix (Fin m) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, A₁ i j ^ 2

/-- The finite first-layer mean `h̃_i = E relu(m_i + s_i Z_{J₁})`. -/
def hT (J₁ : ℕ) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) : Fin m → ℝ :=
  fun i => binMean J₁ (fun z => relu (mRow A₁ c i + sRow A₁ τ i * z))

/-- The finite second moment `γ̃_Γ = t·Σ_i E relu(m_i + s_i Z_{J₁})²` (the same weights). -/
def gT (J₁ : ℕ) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  2 / (m : ℝ) * ∑ i, binMean J₁ (fun z => relu (mRow A₁ c i + sRow A₁ τ i * z) ^ 2)

/-- `s̃² = γ̃_Γ − t|h̃|²`. -/
def sT2 (J₁ : ℕ) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  gT J₁ A₁ c τ - 2 / (m : ℝ) * ∑ i, hT J₁ A₁ c τ i ^ 2

/-- `s̃ = √(s̃²)`. -/
def sT (J₁ : ℕ) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  √(sT2 J₁ A₁ c τ)

/-- **The finite centre** `b̃′_j = E relu((A₂ h̃)_j + s̃ Z_{J₂})`. -/
def bT (J₁ J₂ : ℕ) (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) : Fin m → ℝ :=
  fun j => binMean J₂ (fun z => relu ((A₂.mulVec (hT J₁ A₁ c τ)) j + sT J₁ A₁ c τ * z))

/-- The oracle first-layer mean `h̄_i = ψ_{s_i}(m_i)`. -/
def hO (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) : Fin m → ℝ :=
  fun i => psiS (sRow A₁ τ i) (mRow A₁ c i)

/-- The oracle second moment `γ_Γ = t·Σ_i E relu(m_i + s_i Z)²`. -/
def gO (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  2 / (m : ℝ) * ∑ i, ∫ z, relu (mRow A₁ c i + sRow A₁ τ i * z) ^ 2 ∂gaussianReal 0 1

/-- `s² = γ_Γ − t|h̄|²`. -/
def sO2 (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  gO A₁ c τ - 2 / (m : ℝ) * ∑ i, hO A₁ c τ i ^ 2

/-- `s = √(s²)`. -/
def sO (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) : ℝ := √(sO2 A₁ c τ)

/-- **The oracle centre** `b′_j = ψ_s((A₂ h̄)_j)`. -/
def bO (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) : Fin m → ℝ :=
  fun j => psiS (sO A₁ c τ) ((A₂.mulVec (hO A₁ c τ)) j)

/-- `ρ = √(|c|² + nτ²)`. -/
def rhoC (c : Fin n → ℝ) (τ : ℝ) : ℝ := √(normSq c + (n : ℝ) * τ ^ 2)

/-- `c̃_A = (A₃ b̃′)/ρ`. -/
def cT (J₁ J₂ : ℕ) (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (A₃ : Matrix (Fin n) (Fin m) ℝ) (c : Fin n → ℝ) (τ : ℝ) : Fin n → ℝ :=
  fun i => (A₃.mulVec (bT J₁ J₂ A₁ A₂ c τ)) i / rhoC c τ

/-- `σ̃_p = √(max(0, 2/n − t|b̃′|²/ρ²))`. -/
def sigT (J₁ J₂ : ℕ) (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  √(max 0 (2 / (n : ℝ) - 2 / (m : ℝ) * normSq (bT J₁ J₂ A₁ A₂ c τ) / rhoC c τ ^ 2))

end

end BstLean.Part150
