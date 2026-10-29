import BstLean.Part35Defs
import Mathlib.Data.Sym.Card

/-!
# Part 36, wave 0: frozen definitions for the explicit `(2,d)` theorem (Route G, general `d`)

Paper: `proofs/option-m/36-explicit-2d.tex`. Specification: `delegations/answers/p36-spec-opus.md`.
This file holds definitions only. Provers must not edit it, and must not use `native_decide` anywhere.

Conventions.
* `f(y) = f₀ + bᵀy + yᵀFy` is Part 29's `funF` (quadratic `f`, `d_f = 2`).
* `m(x) = M φ(x)`, `φ` the raw monomials of degree `≤ d`. A degree-`i` monomial is a multiset
  `β : Sym (Fin n) i`; its value is `x^β = (β.map x).prod`; its exponent at `l` is `β.count l`.
  The coefficient vector is `M : CoefIdxD n d → ℝ`, with `CoefIdxD n d = Σ i : Fin (d+1), Sym (Fin n) i × Fin n`
  (output index last). Each raw monomial appears once, so `M = Z/‖Z‖` is uniform on `S^{D−1}`, `D = nN`.
* `coefD M i β p` reads the coefficient for `i : ℕ`, and is `0` for `i > d`; so every degree sum runs over
  `Finset.range (d + 1)`.
* `lapW β δ` is the coefficient of `x^δ` in `(Δ/2)^s x^β / s!`, `s = (|β| − |δ|)/2`, in closed form
  (a product over coordinates of `lap1`). `Hc M i k p δ = Σ_β M_{p,β} lapW β δ` is the paper's
  `H_{i→k}/s!`, so the paper's weights `1/(ρ s! t!)` become `1/ρ` here. `lapW_step` (file `Part36Lap`) ties
  `Hc` to the iterated half-Laplacian `halfLap`, which is what the program computes.
* Branch E is the level formula (Lemma 1). Branch H drops level `d` and adds its mean. Branch U also drops
  level `d − 1` and adds its mean; it keeps every level `k ≤ d − 2` exactly. This is reading R1.
* The cost functions `PD`, `CUD`, `CHD`, `CED` are schedule S2 of the paper (Lemma 6), taken as
  definitions (paper cost model), as in Parts 29 and 35. They are checked against `windows.py`.
* `Sbar x k` is Lemma 2's upper bound on `S_k = Σ_{|β|=k} (β!)²`; the certificates use it in place of `S_k`.
-/

namespace BstLean.Part36

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss qformι funF gaussMom frobSq)
open BstLean.Part33 (SphereProd)

variable {n d : ℕ}

/-! ## §0 The coefficient space -/

/-- Coefficient index of a degree-`d` map `ℝⁿ → ℝⁿ`: degree `i ≤ d`, a monomial `β : Sym (Fin n) i`,
and the output index. -/
abbrev CoefIdxD (n d : ℕ) := Σ i : Fin (d + 1), Sym (Fin n) i × Fin n

/-- The top block (degree exactly `d`): monomial and output index. -/
abbrev BlkD (n d : ℕ) := Sym (Fin n) d × Fin n

/-- `D = card (CoefIdxD n d)` as a real number. -/
noncomputable def DD (n d : ℕ) : ℝ := (Fintype.card (CoefIdxD n d) : ℝ)

/-- `‖Z‖²`. -/
noncomputable def nsqD (Z : CoefIdxD n d → ℝ) : ℝ := ∑ α, Z α ^ 2

/-- `M = Z / ‖Z‖`. -/
noncomputable def unitOfD (Z : CoefIdxD n d → ℝ) : CoefIdxD n d → ℝ :=
  (1 / Real.sqrt (∑ i, Z i ^ 2)) • Z

/-! ## §1 Readers, monomials and the map -/

/-- The coefficient `M_{p,β}` of the degree-`i` monomial `β` in output `p` (`0` if `i > d`). -/
noncomputable def coefD (M : CoefIdxD n d → ℝ) (i : ℕ) (β : Sym (Fin n) i) (p : Fin n) : ℝ :=
  if h : i < d + 1 then M ⟨⟨i, h⟩, (β, p)⟩ else 0

/-- The top block of `M`. -/
def blkOf (M : CoefIdxD n d → ℝ) : BlkD n d → ℝ := fun q => M ⟨Fin.last d, q⟩

/-- `x^β = ∏_{l ∈ β} x_l`. -/
noncomputable def monoVal (x : Fin n → ℝ) (s : Multiset (Fin n)) : ℝ := (s.map x).prod

/-- The degree-`d` map `m(x)_p = Σ_{i ≤ d} Σ_{|β| = i} M_{p,β} x^β`. -/
noncomputable def mapMD (M : CoefIdxD n d → ℝ) (x : Fin n → ℝ) (p : Fin n) : ℝ :=
  ∑ i ∈ Finset.range (d + 1), ∑ β : Sym (Fin n) i, coefD M i β p * monoVal x β.1

/-- `ρ_p = n(n+2)⋯(n+2p−2)`, `ρ₀ = 1` (the denominator of `SphereProd`). -/
noncomputable def rhoD (x : ℝ) (p : ℕ) : ℝ := ∏ j ∈ Finset.range p, (x + 2 * j)

/-- The Gaussian moment `E_g g^s = ∏_l (s_l − 1)!!` (`0` if some exponent is odd). -/
noncomputable def gpm (s : Multiset (Fin n)) : ℝ := ∏ l, gaussMom (s.count l)

/-- `β! = ∏_l (β_l)!`. -/
noncomputable def factM (s : Multiset (Fin n)) : ℝ := ∏ l, ((s.count l).factorial : ℝ)

/-- One coordinate of `e^{∂²/2}`: the coefficient of `t^c` in `e^{∂²/2} t^a`, that is
`a! / (c! 2^σ σ!)` with `a − c = 2σ`, and `0` unless `c ≤ a` and `a − c` is even. -/
noncomputable def lap1 (a c : ℕ) : ℝ :=
  if c ≤ a ∧ Even (a - c) then
    (a.factorial : ℝ) / ((c.factorial : ℝ) * 2 ^ ((a - c) / 2) * (((a - c) / 2).factorial : ℝ))
  else 0

/-- The coefficient of `x^δ` in `(Δ/2)^s x^β / s!` (`s = (|β| − |δ|)/2`), in closed form. -/
noncomputable def lapW (β δ : Multiset (Fin n)) : ℝ := ∏ l, lap1 (β.count l) (δ.count l)

/-- One half-Laplacian step on raw coefficients: `((Δ/2)u)_γ = Σ_l (γ_l+1)(γ_l+2)/2 · u_{γ+2e_l}`. -/
noncomputable def halfLap (k : ℕ) (u : Sym (Fin n) (k + 2) → ℝ) : Sym (Fin n) k → ℝ := fun γ =>
  ∑ l, ((γ.1.count l + 1 : ℝ) * (γ.1.count l + 2) / 2) * u (Sym.cons l (Sym.cons l γ))

section levels
variable (M : CoefIdxD n d → ℝ)

/-- `H_{i→k}/s!` in raw coefficients: `Hc M i k p δ = Σ_{|β|=i} M_{p,β} lapW β δ`. -/
noncomputable def Hc (i k : ℕ) (p : Fin n) (δ : Sym (Fin n) k) : ℝ :=
  ∑ β : Sym (Fin n) i, coefD M i β p * lapW β.1 δ.1

/-- `μ_p = E_x m(x)_p = Σ_{i ≤ d} Hc M i 0 p ∅ / ρ_{i/2}` (odd `i` give `0`). -/
noncomputable def muD (p : Fin n) : ℝ :=
  ∑ i ∈ Finset.range (d + 1), (rhoD n (i / 2))⁻¹ * Hc M i 0 p Sym.nil

/-- Level `k` of `⟨F, E_x m mᵀ⟩` (Lemma 1): `Σ_{i,j} ρ_{(i+j)/2}⁻¹ ⟨F, H_{i→k} Λ_k H_{j→k}ᵀ⟩`.
The pairs `(i, j)` that are not sources of `k` give `0`. -/
noncomputable def levelD (F : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : ℝ :=
  ∑ p, ∑ q, F p q * ∑ i ∈ Finset.range (d + 1), ∑ j ∈ Finset.range (d + 1),
    (rhoD n ((i + j) / 2))⁻¹ * ∑ δ : Sym (Fin n) k, factM δ.1 * Hc M i k p δ * Hc M j k q δ

/-- The moment form of `E_x m(x)_p` (before the level decomposition). -/
noncomputable def muMomD (p : Fin n) : ℝ :=
  ∑ i ∈ Finset.range (d + 1), ∑ β : Sym (Fin n) i, coefD M i β p * gpm β.1 / rhoD n (i / 2)

/-- The moment form of `E_x m(x)_p m(x)_q`. -/
noncomputable def GmomD (p q : Fin n) : ℝ :=
  ∑ i ∈ Finset.range (d + 1), ∑ j ∈ Finset.range (d + 1), ∑ β : Sym (Fin n) i, ∑ γ : Sym (Fin n) j,
    coefD M i β p * coefD M j γ q * gpm (β.1 + γ.1) / rhoD n ((i + j) / 2)

/-- The fully crossed term of the `(k, k)` block: `⟨F, X_k Λ_k X_kᵀ⟩ = Σ_{pq} F_pq Σ_{|δ|=k} δ! M_{pδ} M_{qδ}`. -/
noncomputable def fWD (F : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : ℝ :=
  ∑ p, ∑ q, F p q * ∑ δ : Sym (Fin n) k, factM δ.1 * coefD M k δ p * coefD M k δ q

end levels

/-- `w_k = Σ_{|β|=k} β!` (a hardcoded constant of the program). -/
noncomputable def wD (n k : ℕ) : ℝ := ∑ δ : Sym (Fin n) k, factM δ.1

/-- `S_k = Σ_{|β|=k} (β!)²`. -/
noncomputable def SsD (n k : ℕ) : ℝ := ∑ δ : Sym (Fin n) k, factM δ.1 ^ 2

/-! ## §2 `B`, the variance, and the three branch programs -/

section programs
variable (f0 : ℝ) (b : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (M : CoefIdxD n d → ℝ)

/-- `B(M) = E_x f(m_M(x))`. -/
noncomputable def BofD (μ : Measure (Fin n → ℝ)) : ℝ := ∫ x, funF f0 b F (mapMD M x) ∂μ

/-- `sd(M)² = Var_x f(m_M(x))`. -/
noncomputable def varOfD (μ : Measure (Fin n → ℝ)) : ℝ :=
  ∫ x, (funF f0 b F (mapMD M x) - BofD f0 b F M μ) ^ 2 ∂μ

/-- The moment form `f₀ + bᵀ E m + ⟨F, E m mᵀ⟩`. -/
noncomputable def EmomD : ℝ :=
  f0 + ∑ p, b p * muMomD M p + ∑ p, ∑ q, F p q * GmomD M p q

/-- Branch E: the level formula of Lemma 1, all levels `0, …, d`. -/
noncomputable def EofD : ℝ :=
  f0 + ∑ p, b p * muD M p + ∑ k ∈ Finset.range (d + 1), levelD M F k

/-- Branch H: levels `0, …, d − 1` exactly, level `d` replaced by its mean `tr F · w_d / (ρ_d D)`. -/
noncomputable def HofD : ℝ :=
  f0 + ∑ p, b p * muD M p + ∑ k ∈ Finset.range d, levelD M F k
    + F.trace * wD n d / (rhoD n d * DD n d)

/-- Branch U: levels `0, …, d − 2` exactly, levels `d − 1` and `d` replaced by their means. -/
noncomputable def UofD : ℝ :=
  f0 + ∑ p, b p * muD M p + ∑ k ∈ Finset.range (d - 1), levelD M F k
    + F.trace * wD n (d - 1) / (rhoD n (d - 1) * DD n d)
    + F.trace * wD n d / (rhoD n d * DD n d)

end programs

/-! ## §3 The error matrices (Lemma 2) -/

/-- `c · F ⊗ diag(β!)` on the degree-`k` columns, `0` elsewhere. -/
noncomputable def blockA (F : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (c : ℝ) :
    Matrix (CoefIdxD n d) (CoefIdxD n d) ℝ := fun α α' =>
  if (α.1 : ℕ) = k ∧ (α'.1 : ℕ) = k ∧ α.2.1.1 = α'.2.1.1 then
    c * F α.2.2 α'.2.2 * factM α.2.1.1
  else 0

/-- `A_H = ρ_d⁻¹ F ⊗ Λ_d`. -/
noncomputable def AHD (F : Matrix (Fin n) (Fin n) ℝ) : Matrix (CoefIdxD n d) (CoefIdxD n d) ℝ :=
  blockA F d (rhoD n d)⁻¹

/-- `A_U = A_H + ρ_{d−1}⁻¹ F ⊗ Λ_{d−1}`. -/
noncomputable def AUD (F : Matrix (Fin n) (Fin n) ℝ) : Matrix (CoefIdxD n d) (CoefIdxD n d) ℝ :=
  AHD F + blockA F (d - 1) (rhoD n (d - 1))⁻¹

/-- `‖A_H‖²/v = S_d / ρ_d²`. -/
noncomputable def aHD (n d : ℕ) : ℝ := SsD n d / rhoD n d ^ 2
/-- `‖A_U‖²/v = S_d / ρ_d² + S_{d−1} / ρ_{d−1}²`. -/
noncomputable def aUD (n d : ℕ) : ℝ := aHD n d + SsD n (d - 1) / rhoD n (d - 1) ^ 2

/-- The centred error numerator in `Z`-units: `Zᵀ (A − (tr A / D) I) Z`. -/
noncomputable def EFD (A : Matrix (CoefIdxD n d) (CoefIdxD n d) ℝ) (Z : CoefIdxD n d → ℝ) : ℝ :=
  qformι (A - (A.trace / DD n d) • (1 : Matrix (CoefIdxD n d) (CoefIdxD n d) ℝ)) Z

/-! ## §4 The level-`2d` parity floor (Lemmas 3 and 4) -/

/-- The matching matrix `E_S(β, γ)`: `1` iff `β + γ = S` as multisets (so `β`, `γ` are disjoint
`d`-subsets of `S`). -/
noncomputable def splitSD (S : Finset (Fin n)) (β γ : Sym (Fin n) d) : ℝ :=
  if β.1 + γ.1 = S.val then 1 else 0

/-- `K_S = E_S ⊗ F` on the top block. -/
noncomputable def KSD (F : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : Matrix (BlkD n d) (BlkD n d) ℝ :=
  fun p q => splitSD S p.1 q.1 * F p.2 q.2

/-- `C_S(G) = Σ_{β + γ = S} G_{·β}ᵀ F G_{·γ} = Gᵀ K_S G`. -/
noncomputable def coefCD (F : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) (G : BlkD n d → ℝ) : ℝ :=
  qformι (KSD F S) G

/-- The level-`2d` floor `Y = ρ_{2d}⁻¹ Σ_{|S| = 2d} C_S²`. -/
noncomputable def floorYD (F : Matrix (Fin n) (Fin n) ℝ) (G : BlkD n d → ℝ) : ℝ :=
  (rhoD n (2 * d))⁻¹ * ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (2 * d), coefCD F S G ^ 2

/-- The binomial coefficient as a polynomial: `C(x, k) = x(x−1)⋯(x−k+1)/k!`. -/
noncomputable def chooseR (x : ℝ) (k : ℕ) : ℝ := (∏ i ∈ Finset.range k, (x - i)) / (k.factorial : ℝ)

/-- `κ = n(n−1)⋯(n−2d+1)/ρ_{2d}`, so that `E Y = 2 κ v / (d!)²`. -/
noncomputable def kappaD (x : ℝ) (d : ℕ) : ℝ :=
  (∏ i ∈ Finset.range (2 * d), (x - i)) / rhoD x (2 * d)

/-- `η_{2d}`, the Chebyshev bound `4 Var Y / (E Y)²` at level `1/2` after `r ≤ v²` (Lemma 4). -/
noncomputable def etaD (x : ℝ) (d : ℕ) : ℝ :=
  (8 + 48 / ((2 * d).choose d : ℝ) + 32 / ((2 * d).choose d : ℝ) ^ 2 *
      ∑ j ∈ Finset.Ico d (2 * d), ((2 * d).choose j : ℝ) * (j.choose d : ℝ) * chooseR (x - 2 * d) (2 * d - j))
    / chooseR x (2 * d)

/-- Lemma 2's bound: `S_k ≤ Σ_{ℓ=1}^k C(n,ℓ) C(k−1,ℓ−1) ((k−ℓ+1)!)²`. -/
noncomputable def Sbar (x : ℝ) (k : ℕ) : ℝ :=
  ∑ l ∈ Finset.Icc 1 k, chooseR x l * ((k - 1).choose (l - 1) : ℝ) * (((k - l + 1).factorial : ℝ)) ^ 2

/-! ## §5 Costs (Lemma 6, schedule S2, paper model) and thresholds -/

/-- `N_k = C(n+k−1, k)`, the number of degree-`k` monomials. -/
noncomputable def NhR (x : ℝ) (k : ℕ) : ℝ := chooseR (x + k - 1) k

/-- `m_k = ⌊(d−k)/2⌋ + 1`, the number of sources of level `k`. -/
def mSrc (d k : ℕ) : ℕ := (d - k) / 2 + 1

/-- The trace cost: `Σ_{i=2}^d Σ_{k = i−2, i−4, … ≥ 0} n(n−1+k) N_k`. -/
noncomputable def tracesC (x : ℝ) (d : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 2 d, ∑ s ∈ Finset.range ((i - 2) / 2 + 1),
    x * (x - 1 + ((i - 2 - 2 * s : ℕ) : ℝ)) * NhR x (i - 2 - 2 * s)

/-- `T_d = Σ_{k ≤ d−2} m_k(m_k+1)/2`. -/
def TdC (d : ℕ) : ℕ := ∑ k ∈ Finset.range (d - 1), mSrc d k * (mSrc d k + 1) / 2

/-- The cost of level `k` with `m` sources under schedule S2. -/
noncomputable def gram2C (x : ℝ) (k m : ℕ) : ℝ :=
  (m : ℝ) * (2 * m - 1) * x * NhR x k + m * x * (NhR x k - chooseR x k)
    + x * (x + 1) / 2 * (2 * m * NhR x k - 1) + 3 / 2 * x * (x + 1)

/-- Per-sample cost of `s_B`: `P = n(N − 1)`, `N = C(n+d, d)`. -/
noncomputable def PD (x : ℝ) (d : ℕ) : ℝ := x * (chooseR (x + d) d - 1)
/-- Cost of branch U (S2). -/
noncomputable def CUD (x : ℝ) (d : ℕ) : ℝ :=
  tracesC x d + ∑ k ∈ Finset.range (d - 1), gram2C x k (mSrc d k) + 2 * x * (mSrc d 0 : ℝ)
    + (x ^ 2 + 3 * x + 294 + 2 * (TdC d : ℝ))
/-- Cost of branch H (S2). -/
noncomputable def CHD (x : ℝ) (d : ℕ) : ℝ := CUD x d + gram2C x (d - 1) 1 + 2
/-- Cost of branch E (S2). -/
noncomputable def CED (x : ℝ) (d : ℕ) : ℝ := CHD x d + gram2C x d 1 + 2

/-- `h² = 2(d!)² ‖A_H‖² / (κ v q)`. -/
noncomputable def hSqD (n d : ℕ) (δ : ℝ) : ℝ :=
  2 * (d.factorial : ℝ) ^ 2 * aHD n d / (kappaD n d * (δ - etaD n d))
/-- `u² = 2(d!)² ‖A_U‖² / (κ v q)`. -/
noncomputable def uSqD (n d : ℕ) (δ : ℝ) : ℝ :=
  2 * (d.factorial : ℝ) ^ 2 * aUD n d / (kappaD n d * (δ - etaD n d))

/-- The four windows of Lemma 7 (Q, EH, HU, U) with `S_k` replaced by its upper bound `Sbar x k`.
They imply the windows with the exact `S_k` (`SsD_le_Sbar`). -/
def WindowsBar (x : ℝ) (d : ℕ) (δ c0 : ℝ) : Prop :=
  etaD x d < δ ∧
  2 * (d.factorial : ℝ) ^ 2 * (Sbar x d / rhoD x d ^ 2) * CED x d ≤
    c0 * (δ - etaD x d) * kappaD x d * PD x d ∧
  2 * (d.factorial : ℝ) ^ 2 * (Sbar x d / rhoD x d ^ 2 + Sbar x (d - 1) / rhoD x (d - 1) ^ 2) * CHD x d ≤
    c0 * (δ - etaD x d) * kappaD x d * PD x d ∧
  CUD x d < PD x d

/-- The theorem's program: E if `ε² < h²`, H if `h² ≤ ε² < u²`, U otherwise. -/
noncomputable def gOfD (δ ε f0 : ℝ) (b : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (M : CoefIdxD n d → ℝ) : ℝ :=
  if ε ^ 2 < hSqD n d δ then EofD f0 b F M
  else if ε ^ 2 < uSqD n d δ then HofD f0 b F M else UofD f0 b F M

/-- Its cost in the paper model. -/
noncomputable def costOfD (n d : ℕ) (δ ε : ℝ) : ℝ :=
  if ε ^ 2 < hSqD n d δ then CED n d else if ε ^ 2 < uSqD n d δ then CHD n d else CUD n d

end BstLean.Part36
