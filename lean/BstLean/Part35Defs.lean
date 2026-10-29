import BstLean.Part33Defs

/-!
# Part 35, wave 0: frozen definitions for the explicit `(2,3)` theorem

Paper: `proofs/option-m/35-explicit-23-at-100.tex`. Specification:
`delegations/answers/p35-spec-opus.md`. This file holds definitions only. The theorems are stated in the
wave-1 files `Part35Index`, `Part35ExactFormula`, `Part35Branches`, `Part35Scale`, `Part35Wick`,
`Part35GaussQuad`, `Part35Traces`, `Part35Cov`, `Part35Overlap`, `Part35Parity`, `Part35Certificate`,
and assembled in `Part35Main` and `Part35Final`.

Conventions.
* `f(y) = f₀ + bᵀy + yᵀFy` is Part 29's `funF` (quadratic `f`, `d_f = 2`).
* `m(x) = M φ(x)` with `φ` the raw monomials of degree `≤ 3` (`d_M = 3`). The coefficient vector
  `M : CoefIdx3 n → ℝ` has four blocks: constants `c_k`, linear `L_{k,i}`, quadratic raw `q_{k,ij}` (`i ≤ j`),
  cubic raw `r_{k,ijl}` (`i ≤ j ≤ l`). The output index `k` is always the last component.
* The readers `a3Of`, `r3Of` return `0` off sorted index tuples, so `mapM3` sums over all tuples.
* `Dc3 n = card (CoefIdx3 n) = n · C(n+3,3)` (the paper's `D`).
* Name clashes: `P`, `CE`, `CH`, `CU` below are Part 35's. Part 29 and Part 33 names are opened selectively.
-/

namespace BstLean.Part35

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss qformι funF gaussMom frobSq)
open BstLean.Part33 (SphereProd floorW6 ch2 ch3 ch6 rho2 rho3)

variable {n : ℕ}

/-! ## §0 The coefficient space -/

/-- Coefficient index of a degree-3 map `ℝⁿ → ℝⁿ`: constant `k`; linear `(k, i)`; quadratic `(i, j, k)` with
`i ≤ j`; cubic `(i, j, l, k)` with `i ≤ j ≤ l`. -/
abbrev CoefIdx3 (n : ℕ) :=
  Fin n ⊕ (Fin n × Fin n) ⊕ {p : Fin n × Fin n × Fin n // p.1 ≤ p.2.1} ⊕
    {p : Fin n × Fin n × Fin n × Fin n // p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2.1}

/-- The index type of a full (unsorted) cubic coefficient array `G (i, j, l, k)`. -/
abbrev Arr4 (n : ℕ) := Fin n × Fin n × Fin n × Fin n

/-- `D = card (CoefIdx3 n)` as a real number. -/
noncomputable def Dc3 (n : ℕ) : ℝ := (Fintype.card (CoefIdx3 n) : ℝ)

/-- `‖Z‖²`. -/
noncomputable def nsq3 (Z : CoefIdx3 n → ℝ) : ℝ := ∑ α, Z α ^ 2

/-- `M = Z / ‖Z‖`. -/
noncomputable def unitOf3 (Z : CoefIdx3 n → ℝ) : CoefIdx3 n → ℝ := (1 / Real.sqrt (∑ i, Z i ^ 2)) • Z

/-! ## §1 Readers and the map -/

section readers
variable (M : CoefIdx3 n → ℝ)

/-- Constant column `c_k`. -/
noncomputable def c3Of : Fin n → ℝ := fun k => M (Sum.inl k)
/-- Linear part `L k i`. -/
noncomputable def L3Of : Matrix (Fin n) (Fin n) ℝ := fun k i => M (Sum.inr (Sum.inl (k, i)))
/-- Raw quadratic coefficient `q_{k,ij}` (`0` unless `i ≤ j`). -/
noncomputable def a3Of : Fin n → Fin n → Fin n → ℝ := fun k i j =>
  if h : i ≤ j then M (Sum.inr (Sum.inr (Sum.inl ⟨(i, j, k), h⟩))) else 0
/-- Raw cubic coefficient `r_{k,ijl}` (`0` unless `i ≤ j ≤ l`). -/
noncomputable def r3Of : Fin n → Fin n → Fin n → Fin n → ℝ := fun k i j l =>
  if h : i ≤ j ∧ j ≤ l then M (Sum.inr (Sum.inr (Sum.inr ⟨(i, j, l, k), h⟩))) else 0

/-- The raw cubic array `G (i, j, l, k) = r_{k,ijl}`. -/
noncomputable def rawC : Arr4 n → ℝ := fun p => r3Of M p.2.2.2 p.1 p.2.1 p.2.2.1

/-- The degree-3 map `m(x)_k`. -/
noncomputable def mapM3 (x : Fin n → ℝ) (k : Fin n) : ℝ :=
  c3Of M k + ∑ i, L3Of M k i * x i + ∑ i, ∑ j, a3Of M k i j * x i * x j
    + ∑ i, ∑ j, ∑ l, r3Of M k i j l * x i * x j * x l

/-- `s_k = Σᵢ q_{k,ii}`. -/
noncomputable def sOf : Fin n → ℝ := fun k => ∑ i, a3Of M k i i

/-- `τ_{k,i} = 3 r_{k,iii} + Σ_{l ≠ i} r_{k,{i,l,l}}`, in sorted raw coordinates. -/
noncomputable def tauOf : Fin n → Fin n → ℝ := fun k i =>
  ∑ j, r3Of M k j j i + ∑ l, r3Of M k i l l + r3Of M k i i i

end readers

/-- `β!` for a sorted quadratic monomial: `2` on squares, `1` otherwise. -/
noncomputable def fact2 (i j : Fin n) : ℝ := if i = j then 2 else 1

/-- `β!` for a sorted cubic monomial: `6`, `2` or `1`. -/
noncomputable def fact3 (i j l : Fin n) : ℝ :=
  if i = j ∧ j = l then 6 else if i = j ∨ j = l ∨ i = l then 2 else 1

section gram
variable (M : CoefIdx3 n → ℝ)

/-- `W₂[p,q] = Σ_{|β|=2} β! q_{pβ} q_{qβ}`. -/
noncomputable def W2Of : Fin n → Fin n → ℝ := fun p q =>
  ∑ i, ∑ j, fact2 i j * a3Of M p i j * a3Of M q i j

/-- `W₃[p,q] = Σ_{|β|=3} β! r_{pβ} r_{qβ}`. -/
noncomputable def W3Of : Fin n → Fin n → ℝ := fun p q =>
  ∑ i, ∑ j, ∑ l, fact3 i j l * r3Of M p i j l * r3Of M q i j l

/-- `μ = c + s/n`. -/
noncomputable def muOf : Fin n → ℝ := fun k => c3Of M k + sOf M k / n

/-- `G = E_x m(x) m(x)ᵀ` (Lemma 1). -/
noncomputable def GOf : Fin n → Fin n → ℝ := fun p q =>
  c3Of M p * c3Of M q + (c3Of M p * sOf M q + sOf M p * c3Of M q) / n
    + (∑ i, L3Of M p i * L3Of M q i) / n
    + (∑ i, (L3Of M p i * tauOf M q i + tauOf M p i * L3Of M q i)) / rho2 n
    + (sOf M p * sOf M q + W2Of M p q) / rho2 n
    + (∑ i, tauOf M p i * tauOf M q i + W3Of M p q) / rho3 n

end gram

/-- `w₂ = Σ_{|β|=2} β! = n(n+3)/2`. -/
noncomputable def w2 (x : ℝ) : ℝ := x * (x + 3) / 2
/-- `w₃ = Σ_{|β|=3} β! = n(n²+9n+26)/6`. -/
noncomputable def w3 (x : ℝ) : ℝ := x * (x ^ 2 + 9 * x + 26) / 6

/-! ## §2 `B`, the variance, and the three branch programs -/

section programs
variable (f0 : ℝ) (b : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (M : CoefIdx3 n → ℝ)

/-- `B(M) = E_x f(m_M(x))`. -/
noncomputable def Bof35 (μ : Measure (Fin n → ℝ)) : ℝ := ∫ x, funF f0 b F (mapM3 M x) ∂μ

/-- `sd(M)² = Var_x f(m_M(x))`. -/
noncomputable def varOf35 (μ : Measure (Fin n → ℝ)) : ℝ :=
  ∫ x, (funF f0 b F (mapM3 M x) - Bof35 f0 b F M μ) ^ 2 ∂μ

/-- `⟨F, W₂⟩`. -/
noncomputable def fW2 : ℝ := ∑ p, ∑ q, F p q * W2Of M p q
/-- `⟨F, W₃⟩`. -/
noncomputable def fW3 : ℝ := ∑ p, ∑ q, F p q * W3Of M p q

/-- Branch E: the right-hand side of Lemma 1. -/
noncomputable def Eof35 : ℝ := f0 + ∑ k, b k * muOf M k + ∑ p, ∑ q, F p q * GOf M p q

/-- Branch H (reading R1): E with the fully crossed term `⟨F,W₃⟩/ρ₃` replaced by its mean
`tr F · w₃ / (ρ₃ D)`. -/
noncomputable def Hof35 : ℝ :=
  Eof35 f0 b F M - fW3 F M / rho3 n + F.trace * w3 n / (rho3 n * Dc3 n)

/-- Branch U (reading R1): H with also `⟨F,W₂⟩/ρ₂` replaced by `tr F · w₂ / (ρ₂ D)`. -/
noncomputable def Uof35 : ℝ :=
  Hof35 f0 b F M - fW2 F M / rho2 n + F.trace * w2 n / (rho2 n * Dc3 n)

end programs

/-! ## §3 The error matrices (Lemma 2) -/

/-- `A_H = ρ₃⁻¹ F ⊗ diag(β!)` on the cubic columns, `0` elsewhere. -/
noncomputable def AH35 (F : Matrix (Fin n) (Fin n) ℝ) : Matrix (CoefIdx3 n) (CoefIdx3 n) ℝ := fun α β =>
  match α, β with
  | Sum.inr (Sum.inr (Sum.inr p)), Sum.inr (Sum.inr (Sum.inr q)) =>
      if p.1.1 = q.1.1 ∧ p.1.2.1 = q.1.2.1 ∧ p.1.2.2.1 = q.1.2.2.1 then
        F p.1.2.2.2 q.1.2.2.2 * fact3 p.1.1 p.1.2.1 p.1.2.2.1 / rho3 n
      else 0
  | _, _ => 0

/-- `ρ₂⁻¹ F ⊗ diag(β!)` on the quadratic columns, `0` elsewhere. -/
noncomputable def A2blk (F : Matrix (Fin n) (Fin n) ℝ) : Matrix (CoefIdx3 n) (CoefIdx3 n) ℝ := fun α β =>
  match α, β with
  | Sum.inr (Sum.inr (Sum.inl p)), Sum.inr (Sum.inr (Sum.inl q)) =>
      if p.1.1 = q.1.1 ∧ p.1.2.1 = q.1.2.1 then
        F p.1.2.2 q.1.2.2 * fact2 p.1.1 p.1.2.1 / rho2 n
      else 0
  | _, _ => 0

/-- `A_U = A_H + ρ₂⁻¹ F ⊗ diag(β!)_{|β|=2}`. -/
noncomputable def AU35 (F : Matrix (Fin n) (Fin n) ℝ) : Matrix (CoefIdx3 n) (CoefIdx3 n) ℝ :=
  AH35 F + A2blk F

/-- `‖A_H‖²/v = n(n²+21n+194)/(6ρ₃²)`. -/
noncomputable def aH (x : ℝ) : ℝ := x * (x ^ 2 + 21 * x + 194) / (6 * rho3 x ^ 2)
/-- `‖A_U‖²/v = ‖A_H‖²/v + n(n+7)/(2ρ₂²)`. -/
noncomputable def aU (x : ℝ) : ℝ := aH x + x * (x + 7) / (2 * rho2 x ^ 2)

/-- The centred error numerator in `Z`-units: `Zᵀ (A − (tr A / D) I) Z`. -/
noncomputable def EF3 (A : Matrix (CoefIdx3 n) (CoefIdx3 n) ℝ) (Z : CoefIdx3 n → ℝ) : ℝ :=
  qformι (A - (A.trace / Dc3 n) • (1 : Matrix (CoefIdx3 n) (CoefIdx3 n) ℝ)) Z

/-! ## §4 The level-6 parity floor (Lemmas 4 and 5) -/

/-- The 20 ordered splits `β ⊔ γ = Fin 6` into increasing triples (`β` in lexicographic order). -/
def triples20 : Fin 20 → (Fin 6 × Fin 6 × Fin 6) × (Fin 6 × Fin 6 × Fin 6) :=
  ![((0,1,2),(3,4,5)), ((0,1,3),(2,4,5)), ((0,1,4),(2,3,5)), ((0,1,5),(2,3,4)), ((0,2,3),(1,4,5)),
    ((0,2,4),(1,3,5)), ((0,2,5),(1,3,4)), ((0,3,4),(1,2,5)), ((0,3,5),(1,2,4)), ((0,4,5),(1,2,3)),
    ((1,2,3),(0,4,5)), ((1,2,4),(0,3,5)), ((1,2,5),(0,3,4)), ((1,3,4),(0,2,5)), ((1,3,5),(0,2,4)),
    ((1,4,5),(0,2,3)), ((2,3,4),(0,1,5)), ((2,3,5),(0,1,4)), ((2,4,5),(0,1,3)), ((3,4,5),(0,1,2))]

/-- `C_S = Σ_{β ⊂ S, |β|=3} G_{·β}ᵀ F G_{·,S∖β}` for a six-subset `S`, on a cubic array `G (i,j,l,k)`. -/
noncomputable def coefC35 (F : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) (hS : S.card = 6)
    (G : Arr4 n → ℝ) : ℝ :=
  let s := S.orderEmbOfFin hS
  ∑ m : Fin 20, ∑ a, ∑ b, F a b
    * G (s (triples20 m).1.1, s (triples20 m).1.2.1, s (triples20 m).1.2.2, a)
    * G (s (triples20 m).2.1, s (triples20 m).2.2.1, s (triples20 m).2.2.2, b)

/-- `C_S²`, extended by `0` off the six-subsets. -/
noncomputable def coefX35 (F : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) (G : Arr4 n → ℝ) : ℝ :=
  if hS : S.card = 6 then coefC35 F S hS G ^ 2 else 0

/-- The level-6 floor `Y = ρ₆⁻¹ Σ_{|S|=6} C_S²`. -/
noncomputable def floorY35 (F : Matrix (Fin n) (Fin n) ℝ) (G : Arr4 n → ℝ) : ℝ :=
  floorW6 n * ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard 6, coefX35 F S G

/-- `κ = n(n−1)⋯(n−5)/ρ₆`, so that `E Y = κ v / 18`. -/
noncomputable def kappa35 (x : ℝ) : ℝ :=
  x * (x - 1) * (x - 2) * (x - 3) * (x - 4) * (x - 5) /
    (x * (x + 2) * (x + 4) * (x + 6) * (x + 8) * (x + 10))

/-- `η₆`, the Chebyshev bound `4 Var Y / (E Y)²` at `θ = 1/2` after `r ≤ v²`. -/
noncomputable def eta6 (x : ℝ) : ℝ :=
  (52 / 5 + 8 / 5 * ch3 (x - 6) + 24 / 5 * ch2 (x - 6) + 24 / 5 * (x - 6)) / ch6 x

/-- `r = tr F⁴`, written as `‖F²‖_F²` (equal to `tr F⁴` for symmetric `F`). -/
noncomputable def trF4 (F : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ a, ∑ b, (∑ c, F a c * F c b) ^ 2

/-- The three labels of a triple, as a finset. -/
def tripleSet (β : Fin n × Fin n × Fin n) : Finset (Fin n) := {β.1, β.2.1, β.2.2}

/-- The matching matrix `E_S(β, γ)`: `1` iff `β`, `γ` are increasing triples with `β ⊔ γ = S`. -/
noncomputable def splitS (S : Finset (Fin n)) (β γ : Fin n × Fin n × Fin n) : ℝ :=
  if β.1 < β.2.1 ∧ β.2.1 < β.2.2 ∧ γ.1 < γ.2.1 ∧ γ.2.1 < γ.2.2 ∧
      Disjoint (tripleSet β) (tripleSet γ) ∧ tripleSet β ∪ tripleSet γ = S then 1 else 0

/-- `K_S = E_S ⊗ F` on the cubic array: `C_S(G) = Gᵀ K_S G`. -/
noncomputable def KS (F : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : Matrix (Arr4 n) (Arr4 n) ℝ :=
  fun p q => F p.2.2.2 q.2.2.2 * splitS S (p.1, p.2.1, p.2.2.1) (q.1, q.2.1, q.2.2.1)

/-! ## §5 Costs (Lemma 3, paper model) and thresholds -/

/-- Per-sample cost of `s_B`: `P = n(N−1) = n²(n²+6n+11)/6`. -/
noncomputable def P (x : ℝ) : ℝ := x ^ 2 * (x ^ 2 + 6 * x + 11) / 6
noncomputable def CU (x : ℝ) : ℝ := 5 * x ^ 3 + 10 * x ^ 2 + 10 * x + 300
noncomputable def CH (x : ℝ) : ℝ := CU x + (x + 1) * (2 * x ^ 3 + x ^ 2 + 2) / 2
noncomputable def CE (x : ℝ) : ℝ := CH x + (2 * x ^ 5 + 7 * x ^ 4 + 7 * x ^ 3 + 8 * x ^ 2 + 6) / 6

/-- `h² = 72 ‖A_H‖² / (κ v q)`. -/
noncomputable def hSq (x δ : ℝ) : ℝ := 72 * aH x / (kappa35 x * (δ - eta6 x))
/-- `u² = 72 ‖A_U‖² / (κ v q)`. -/
noncomputable def uSq (x δ : ℝ) : ℝ := 72 * aU x / (kappa35 x * (δ - eta6 x))

/-- The theorem's program: E if `ε² < h²`, H if `h² ≤ ε² < u²`, U otherwise. -/
noncomputable def gOf35 (δ ε f0 : ℝ) (b : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (M : CoefIdx3 n → ℝ) : ℝ :=
  if ε ^ 2 < hSq n δ then Eof35 f0 b F M
  else if ε ^ 2 < uSq n δ then Hof35 f0 b F M else Uof35 f0 b F M

/-- Its cost in the paper model. -/
noncomputable def costOf35 (n : ℕ) (δ ε : ℝ) : ℝ :=
  if ε ^ 2 < hSq n δ then CE n else if ε ^ 2 < uSq n δ then CH n else CU n

end BstLean.Part35
