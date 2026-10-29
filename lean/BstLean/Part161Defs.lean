import BstLean.Part157All

/-!
# Part 161: shared definitions for the Agent replacement hypothesis

Role: `delegations/statements/p161-spec.md`. Do not use `sorry`, `native_decide` or `axiom`.

Paper: `proofs/option-n/theorem7-07-mixture-fluctuation.tex` (the latitude decomposition, the
Gaussian comparison lemmas).

* `gd1 μ v z`, `gdN μ v z`: the density of `N(μ, v·I)` with respect to the standard Gaussian
  distribution (one coordinate, and a vector).
* `hellG2 n d2 S₁ S₂`: the squared Hellinger distance of `N(m₁, S₁·I_n)` and `N(m₂, S₂·I_n)` with
  `d2 = |m₁ − m₂|²` (the value `2` when a scale is not positive).
* `consV z g`: the vector of `ℝⁿ` with first coordinate `z` and the other coordinates `g`.
* `hhMat u`: the reflection (a Householder matrix) that exchanges `e0 n` and the unit vector `u`.
* `uHat c = ĉ/|ĉ|`; `xLat c s v = s·u + √(1 − s²)·H(0, v)`: the point of latitude `s` and
  direction `v`.
* `lamX`, `sigX`: `λ(x)` and `σ(x) = √(2/m_A)·|r(x)|` of the Agent network at the input `x`.
-/

namespace BstLean.Part161

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part157

/-- The density of `N(μ, v)` with respect to `N(0, 1)` at `z` (for `v > 0`):
`v^{−1/2}·exp(−(z − μ)²/(2v) + z²/2)`. -/
noncomputable def gd1 (μ v z : ℝ) : ℝ := (√v)⁻¹ * exp (-(z - μ) ^ 2 / (2 * v) + z ^ 2 / 2)

/-- The density of `N(μ, v·I)` with respect to the standard Gaussian distribution of `ι → ℝ`. -/
noncomputable def gdN {ι : Type*} [Fintype ι] (μ : ι → ℝ) (v : ℝ) (z : ι → ℝ) : ℝ :=
  ∏ i, gd1 (μ i) v (z i)

/-- **The squared Hellinger distance of two Gaussian distributions with scalar covariance**,
`H²(N(m₁, S₁·I_n), N(m₂, S₂·I_n)) = 2 − 2·(2√(S₁S₂)/(S₁ + S₂))^{n/2}·exp(−d2/(4(S₁ + S₂)))`,
`d2 = |m₁ − m₂|²`, for `S₁ > 0` and `S₂ > 0`; the upper value `2` otherwise. -/
noncomputable def hellG2 (n : ℕ) (d2 S₁ S₂ : ℝ) : ℝ :=
  if 0 < S₁ ∧ 0 < S₂ then
    2 - 2 * (√(2 * √(S₁ * S₂) / (S₁ + S₂)) ^ n * exp (-d2 / (4 * (S₁ + S₂))))
  else 2

variable {n : ℕ}

/-- The vector of `ℝⁿ` with coordinate `0` equal to `z` and the other coordinates `g`. -/
def consV (z : ℝ) (g : Fin (n - 1) → ℝ) : Fin n → ℝ :=
  fun i => if h : (i : ℕ) = 0 then z else g ⟨(i : ℕ) - 1, by omega⟩

/-- The reflection that exchanges `e0 n` and the unit vector `u`:
`H = 1 − 2 w wᵀ/|w|²`, `w = e0 − u` (the unit matrix when `u = e0`). -/
noncomputable def hhMat (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - (2 * (normSq (e0 n - u))⁻¹) • Matrix.vecMulVec (e0 n - u) (e0 n - u)

/-- The unit vector `u = ĉ/|ĉ|` of the retained World centre value. -/
noncomputable def uHat (c : Ret n) : Fin n → ℝ := (√(normSq c.1.2))⁻¹ • c.1.2

/-- **The point of latitude `s` and direction `v`**: `H·(s, √(1 − s²)·v)`, which is
`s·u + √(1 − s²)·H(0, v)`; `H(0, v)` is orthogonal to `u`. -/
noncomputable def xLat (c : Ret n) (s : ℝ) (v : Fin (n - 1) → ℝ) : Fin n → ℝ :=
  (hhMat (uHat c)).mulVec (consV s (√(1 - s ^ 2) • v))

/-- `λ(x) = ⟨a₂(x), b⟩/|b|²` for the Agent network with retained data `c`. -/
noncomputable def lamX (D : Design n) (c : Ret n) (x : Fin n → ℝ) : ℝ :=
  lam (D.bA c.1 c.2.1.1) (hid2 c.2.1.1.1 c.2.1.1.2 x)

/-- `σ(x) = √(2/m_A)·|r(x)|` for the Agent network with retained data `c`. The paper's scale is
`S(x) = σ(x)²`. -/
noncomputable def sigX (D : Design n) (c : Ret n) (x : Fin n → ℝ) : ℝ :=
  sig (2 / (mA n : ℝ)) (D.bA c.1 c.2.1.1) (hid2 c.2.1.1.1 c.2.1.1.2 x)

lemma measurable_lamX (D : Design n) (c : Ret n) : Measurable (lamX D c) :=
  (measurable_lam _).comp (continuous_hid2 c.2.1.1.1 c.2.1.1.2).measurable

lemma measurable_sigX (D : Design n) (c : Ret n) : Measurable (sigX D c) :=
  (measurable_sig _ _).comp (continuous_hid2 c.2.1.1.1 c.2.1.1.2).measurable

lemma sigX_nonneg (D : Design n) (c : Ret n) (x : Fin n → ℝ) : 0 ≤ sigX D c x :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

lemma measurable_consV : Measurable (fun p : ℝ × (Fin (n - 1) → ℝ) => consV (n := n) p.1 p.2) := by
  refine measurable_pi_iff.mpr fun i => ?_
  unfold consV
  by_cases h : (i : ℕ) = 0
  · simp only [h, dite_true]; exact measurable_fst
  · simp only [h, dite_false]; exact (measurable_pi_apply _).comp measurable_snd

lemma measurable_xLat (c : Ret n) :
    Measurable (fun p : ℝ × (Fin (n - 1) → ℝ) => xLat c p.1 p.2) := by
  unfold xLat
  have h1 : Measurable (fun p : ℝ × (Fin (n - 1) → ℝ) => (p.1, √(1 - p.1 ^ 2) • p.2)) :=
    measurable_fst.prodMk
      (((measurable_const.sub (measurable_fst.pow_const 2)).sqrt).smul measurable_snd)
  have h2 : Measurable (fun w : Fin n → ℝ => (hhMat (uHat c)).mulVec w) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  exact h2.comp (measurable_consV.comp h1)

end BstLean.Part161
