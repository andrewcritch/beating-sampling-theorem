import BstLean.Part56Defs
import BstLean.Part59Defs

/-!
# Part 60, wave 0: frozen definitions — Theorem CD-J, the exact quadrature line program for
concentrated rank-one Bingham laws when `d_f > d_M`, under the charged baseline

Source: `delegations/answers/omCD-opus-prover.md` §1–§5 (Theorem CD-J, Prop X, Prop T2″ with Lemmas
U, L, E, H′, M), with the repairs of `chCD-opus.md` (D1: R2 band; D3: T1′ constant `5(k+1)²`; D4) and
`chCD-codex.md` (§1: Lemma H′ factor `A_{d,k}`, absorbed into the constant; §2: boundary bands; §5:
explicit unisolvence; §7: elementary Lemma M).
Specification: `delegations/answers/p60-spec-opus.md`.
This file holds definitions only. Provers must not edit it, and must not use `native_decide` or
`axiom` anywhere.

Conventions. Part 36, 41, 43, 53, 56 and 59 names are reused. `k = d_f`, `d = d_M`.
`f` is a coefficient vector `c : Mono n k → ℝ` (Part 59). Its tensor form is
`(c default, tensOf k c)`.

* **Weighted index set.** `LamIdx60 d k = {(α, l) ∈ {0..k}^d × {0..k} : |α| + 2l ≤ k}`. One element is
  both a node (the point `β = α`, `τ = l`, with `β₀ = 1`) and a monomial `β^α τ^l`.
  `JJ d k = Σ_{l ≤ ⌊k/2⌋} C(k − 2l + d, d)` (the source's `J`); `CardJ60` states `card = JJ`.
* **Vandermonde matrix and weights.** `Vmat60 d k λ p = p(λ)` (row: node, column: monomial).
  `momJ60 μ d v p = E_μ[β(x)^α τ(x)^l]` with Part 56's `β_j`, `τ`. `wJ60 k μ d v = (Vᵀ)⁻¹ μ⃗`.
* **Node values.** `yJ60 M v λ = u₀ + Σ_j α_j u_j` (anchors `u_j = ancRK M v j` of Part 56).
  `nodeA60 n d λ = l/𝒟` (`= σ² l`). `hev60 k c a y = Σ_α c_α Π_i q_{α_i}(y_i; a)` (Lemma Q of
  Part 59 at a general point and a general heat parameter).
* **The program value.** Coefficient form `gJQ60 w c M v = Σ_λ w_λ hev60 k c (l/𝒟) (yJ60 M v λ)`.
  Tensor form `gJH60 μ k f0 T v M = Σ_λ wJ60(μ)_λ (P_{l/𝒟} f)(yJ60 M v λ)`.
* **Programs.** The line program reads `In60 n d k = CoefIdxD n d ⊕ (Mono n k ⊕ (Fin n ⊕ LamIdx60 d k))`:
  `M`, `c`, `v`, the weights. The moment program reads Part 56's `InM56 n` (`t`, `v`) and returns one
  weight per node. `GSpec60`, `MomSpec60` are their specifications.
* **Costs.** `costLine60` (the line program's cost bound); `baselineF` (Part 59, reading R1),
  `baselineF2` (reading R2, one sample `= 2P + C_f`); `nuJ60`, `k0J60` (the amortization share and
  counter, R1), `nuJ60R2`, `k0J60R2` (R2).
* **Floor transfer objects.** `kap60 d x = κ_x = Σ_{j≤d} k_j(x,x)`; `NxA n d k A κ` is the seminorm
  `Σ_{c=1}^k ‖(P_{κ/𝒟}A)_c‖²/𝒟^c` (the source's `𝒩_x`, up to the factors `c!`); `NxF` is the same sum
  including `c = 0`; `FlA μ d k A = E_μ NxA(κ_x)`.
* **Statements.** The interfaces between the wave-1 files are `Prop`-valued definitions in §8. A
  wave-1 file proves one of them, and may take others as hypotheses; it does not import another
  wave-1 file.
-/

namespace BstLean.Part60

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono phiM frob IsSymmT Tens TSymm fval Pn NN varU)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part53 (TF fvA heatA sg)
open BstLean.Part56 (UnitV lawRK surrRK kJ betaJ tauR ancRK gLineH InM56 inRK Sfl)
open BstLean.Part59 (qH costF Pp baselineF binA radDef59 lam59)

variable {n d : ℕ}

/-! ## §1 The weighted index set -/

/-- `Λ = {(α, l) : α ∈ {0..k}^d, l ∈ {0..k}, |α| + 2l ≤ k}`: nodes and monomials of `Π_k^w`. -/
abbrev LamIdx60 (d k : ℕ) :=
  {p : (Fin d → Fin (k + 1)) × Fin (k + 1) // ∑ j, (p.1 j : ℕ) + 2 * (p.2 : ℕ) ≤ k}

/-- `J = Σ_{l=0}^{⌊k/2⌋} C(k − 2l + d, d)`. -/
def JJ (d k : ℕ) : ℕ := ∑ l ∈ Finset.range (k / 2 + 1), (k - 2 * l + d).choose d

/-- The monomial `β^α τ^l` of the index `p = (α, l)`. -/
noncomputable def monoW60 {k : ℕ} (p : LamIdx60 d k) (β : Fin d → ℝ) (τ : ℝ) : ℝ :=
  (∏ j, β j ^ (p.1.1 j : ℕ)) * τ ^ (p.1.2 : ℕ)

/-! ## §2 Vandermonde matrix, moments, weights -/

/-- `V_{λ, p} = p(λ)`: the monomial `p` at the integer node `λ` (`0^0 = 1`). -/
noncomputable def Vmat60 (d k : ℕ) : Matrix (LamIdx60 d k) (LamIdx60 d k) ℝ := fun q p =>
  monoW60 p (fun j => ((q.1.1 j : ℕ) : ℝ)) ((q.1.2 : ℕ) : ℝ)

/-- The moments `E_μ[β_1(x)^{α_1} ⋯ β_d(x)^{α_d} τ(x)^l]`. -/
noncomputable def momJ60 (k : ℕ) (μ : Measure (Fin n → ℝ)) (d : ℕ) (v : Fin n → ℝ) :
    LamIdx60 d k → ℝ := fun p =>
  ∫ x, monoW60 p (fun j => betaJ d (j.1 + 1) v x) (tauR d v x) ∂μ

/-- The weights `w = (Vᵀ)⁻¹ μ⃗`, so that `Σ_λ w_λ p(λ) = μ_p` when `V` is invertible. -/
noncomputable def wJ60 (k : ℕ) (μ : Measure (Fin n → ℝ)) (d : ℕ) (v : Fin n → ℝ) :
    LamIdx60 d k → ℝ :=
  Matrix.mulVec (Vmat60 d k).transpose⁻¹ (momJ60 k μ d v)

/-! ## §3 Node values -/

/-- The node point `y_λ = u₀ + Σ_{j=1}^d α_j u_j`. -/
noncomputable def yJ60 {k : ℕ} (M : CoefIdxD n d → ℝ) (v : Fin n → ℝ) (q : LamIdx60 d k) :
    Fin n → ℝ :=
  ancRK M v 0 + ∑ j : Fin d, (((q.1.1 j : ℕ) : ℝ)) • ancRK M v (j.1 + 1)

/-- The node heat parameter `l/𝒟 = σ² l`. -/
noncomputable def nodeA60 {k : ℕ} (n d : ℕ) (q : LamIdx60 d k) : ℝ := ((q.1.2 : ℕ) : ℝ) / DD n d

/-- `(P_a f)(y) = Σ_α c_α Π_i q_{α_i}(y_i; a)` (Lemma Q at a general point and parameter). -/
noncomputable def hev60 (k : ℕ) (c : Mono n k → ℝ) (a : ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ α : Mono n k, c α * ∏ i : Fin n, qH (α.2.1.count i) (y i) a

/-- **The program value, coefficient form**: `g_J = Σ_λ w_λ (P_{l/𝒟} f)(y_λ)` with weights `w`. -/
noncomputable def gJQ60 {k : ℕ} (w : LamIdx60 d k → ℝ) (c : Mono n k → ℝ) (M : CoefIdxD n d → ℝ)
    (v : Fin n → ℝ) : ℝ :=
  ∑ q : LamIdx60 d k, w q * hev60 k c (nodeA60 n d q) (yJ60 M v q)

/-- **The program value, tensor form**, with the weights of the law `μ`. -/
noncomputable def gJH60 (μ : Measure (Fin n → ℝ)) (k : ℕ) (f0 : ℝ) (T : Tens n) (v : Fin n → ℝ)
    (M : CoefIdxD n d → ℝ) : ℝ :=
  ∑ q : LamIdx60 d k, wJ60 k μ d v q *
    fvA k (heatA k (nodeA60 n d q) (TF k f0 T)) (yJ60 M v q)

/-! ## §4 Programs -/

/-- The line program's inputs: `M`, the coefficients `c` of `f`, `v`, the weights. -/
abbrev In60 (n d k : ℕ) := CoefIdxD n d ⊕ (Mono n k ⊕ (Fin n ⊕ LamIdx60 d k))

/-- The line program's input vector. -/
def inp60 {k : ℕ} (c : Mono n k → ℝ) (M : CoefIdxD n d → ℝ) (v : Fin n → ℝ)
    (w : LamIdx60 d k → ℝ) : In60 n d k → ℝ :=
  Sum.elim M (Sum.elim c (Sum.elim v w))

/-- The line program computes `g_J` from `M`, `c`, `v` and arbitrary weights `w`. -/
def GSpec60 {k : ℕ} (pg : Prog (In60 n d k) Unit) : Prop :=
  ∀ (c : Mono n k → ℝ) (M : CoefIdxD n d → ℝ) (v : Fin n → ℝ) (w : LamIdx60 d k → ℝ),
    pg.eval (inp60 c M v w) () = gJQ60 w c M v

/-- The moment program returns the quadrature weights of the surrogate at every `t ≥ 0`, unit `v`. -/
def MomSpec60 {k : ℕ} (pm : Prog (InM56 n) (LamIdx60 d k)) (K : ℕ) : Prop :=
  ∀ (t : ℝ) (v : Fin n → ℝ), 0 ≤ t → UnitV v → ∀ q : LamIdx60 d k,
    pm.eval (inRK t v) q = wJ60 k (surrRK n K t v) d v q

/-! ## §5 Costs and baselines -/

/-- The cost bound of the line program: `2P` (anchors), `(d+1)N` (`φ(v)`), per node one nested tree
`C_f` plus `4n(k+d+2)` (the node point, the table `q_e(y_i; l/𝒟)`, the weighted sum), and
`4⌊log₂ n⌋ + 16(k+d+2)²` for the constants. -/
noncomputable def costLine60 (n d k : ℕ) : ℝ :=
  2 * Pn n d + ((d : ℝ) + 1) * NN n d +
    (Fintype.card (LamIdx60 d k) : ℝ) * (costF n k + 4 * (n : ℝ) * ((k : ℝ) + d + 2)) +
    (4 * (Nat.log 2 n : ℝ) + 16 * ((k : ℝ) + d + 2) ^ 2)

/-- **The charged baseline, reading R2**: one sample costs `2P + C_f`;
`max(2P + C_f, 0.455 (2P + C_f)/ε²)`. -/
noncomputable def baselineF2 (n d k : ℕ) (ε : ℝ) : ℝ :=
  max (2 * Pn n d + costF n k) (455 / 1000 * (2 * Pn n d + costF n k) / ε ^ 2)

/-- The share `ν = (1 − J ε_hi²/0.91)/2` of the R1 baseline reserved for the moment program. -/
noncomputable def nuJ60 (J : ℕ) (εhi : ℝ) : ℝ := (1 - (J : ℝ) * εhi ^ 2 * 100 / 91) / 2

/-- The share `ν = (1 − J ε_hi²/0.455)/2` of the R2 baseline reserved for the moment program. -/
noncomputable def nuJ60R2 (J : ℕ) (εhi : ℝ) : ℝ := (1 - (J : ℝ) * εhi ^ 2 * 1000 / 455) / 2

/-- The R1 amortization threshold `k₀ = ⌈cost(pm)/(ν 𝔅₁(ε))⌉`. -/
noncomputable def k0J60 (n d k : ℕ) (cm : ℕ) (ε εhi : ℝ) : ℕ :=
  ⌈(cm : ℝ) / (nuJ60 (JJ d k) εhi * baselineF n d k ε)⌉₊

/-- The R2 amortization threshold `k₀ = ⌈cost(pm)/(ν 𝔅₂(ε))⌉`. -/
noncomputable def k0J60R2 (n d k : ℕ) (cm : ℕ) (ε εhi : ℝ) : ℕ :=
  ⌈(cm : ℝ) / (nuJ60R2 (JJ d k) εhi * baselineF2 n d k ε)⌉₊

/-! ## §6 Floor transfer objects -/

/-- `κ_x = ‖φ(x)‖² = Σ_{j=0}^d k_j(x, x)` (in `[1, d+1]` on the sphere). -/
noncomputable def kap60 (d : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (d + 1), kJ d j x x

/-- `𝒩(A; κ) = Σ_{c=1}^k ‖(P_{κ/𝒟} A)_c‖²/𝒟^c` (chaos `c ≥ 1` only). -/
noncomputable def NxA (n d k : ℕ) (A : Tens n) (κ : ℝ) : ℝ :=
  ∑ c ∈ Finset.Icc 1 k, frob (heatA k (κ / DD n d) A c) / DD n d ^ c

/-- The same sum including the chaos `c = 0`. -/
noncomputable def NxF (n d k : ℕ) (A : Tens n) (κ : ℝ) : ℝ :=
  ∑ c ∈ Finset.range (k + 1), frob (heatA k (κ / DD n d) A c) / DD n d ^ c

/-- `E_{x∼μ} 𝒩(A; κ_x)`. -/
noncomputable def FlA (μ : Measure (Fin n → ℝ)) (d k : ℕ) (A : Tens n) : ℝ :=
  ∫ x, NxA n d k A (kap60 d x) ∂μ

/-- `ρ_x² = 1 − (v·x)²`. -/
def rho2 (v x : Fin n → ℝ) : ℝ := 1 - (∑ i, v i * x i) ^ 2

/-! ## §7 Algebraic interfaces (the program side) -/

/-- **Count of nodes**: `|Λ| = J`. -/
def CardJ60 (d k : ℕ) : Prop := Fintype.card (LamIdx60 d k) = JJ d k

/-- **Unisolvence**: the integer nodes `Λ` are unisolvent for `Π_k^w` (`det V ≠ 0`). -/
def Unisolv60 (d k : ℕ) : Prop := (Vmat60 d k).det ≠ 0

/-- **Lemma Q, general point and parameter**: `hev60 k c a y = (P_a f)(y)` on the tensor form,
`a ≥ 0`, `n ≥ 1`. -/
def LemmaQ60 : Prop :=
  ∀ (n k : ℕ), 1 ≤ n → ∀ (c : Mono n k → ℝ) (a : ℝ), 0 ≤ a → ∀ y : Fin n → ℝ,
    hev60 k c a y = fvA k (heatA k a (TF k (c default) (BstLean.Part59.tensOf k c))) y

/-- **Prop X** (exact quadrature): for every law on the sphere, every unit `v`, every symmetric `f`
and every `M`, the quadrature value equals Part 56's heat form `E_μ (P_{σ²τ(x)} f)(μ_x)`. -/
def PropX60 (d k : ℕ) : Prop :=
  ∀ (n : ℕ) (μ : Measure (Fin n → ℝ)), SphLaw n μ → ∀ v : Fin n → ℝ, UnitV v →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T → ∀ M : CoefIdxD n d → ℝ,
      gJH60 μ k f0 T v M = gLineH μ k f0 T v M

/-! ## §8 Analytic interfaces (Prop T2″) -/

/-- **Lemma U** (upper bound, every law on the sphere):
`E_Z Var_μ h(σZφ(x)) ≤ (d+1)^k k! E_x 𝒩_full(h; κ_x)`. -/
def LemmaU60 (d k : ℕ) : Prop :=
  ∀ (n : ℕ) (μ : Measure (Fin n → ℝ)), SphLaw n μ → ∀ A : Tens n, (∀ j, IsSymmT (A j)) →
    Integrable (fun Z => varU μ (fun x => fvA k A (mapMD (sg n d • Z) x)))
        (stdGauss (CoefIdxD n d)) ∧
      ∫ Z, varU μ (fun x => fvA k A (mapMD (sg n d • Z) x)) ∂stdGauss (CoefIdxD n d) ≤
        ((d : ℝ) + 1) ^ k * (k.factorial : ℝ) * ∫ x, NxF n d k A (kap60 d x) ∂μ

/-- **Lemma H′** (with Lemma E: the chaos `0` of `h_r = binom(E, r) f` does not see the chaos `0` of
`f`): for `0 ≤ κ ≤ d+1`, `𝒩_full(h_r; κ) ≤ (8(d+1)(k+1)²)^{2r} n^r 𝒩(f; κ)`. -/
def LemmaH60 (d k : ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ A : Tens n, (∀ j, IsSymmT (A j)) → ∀ r : ℕ, 1 ≤ r → r ≤ k →
    ∀ κ : ℝ, 0 ≤ κ → κ ≤ (d : ℝ) + 1 →
      NxF n d k (binA r A) κ ≤
        (8 * ((d : ℝ) + 1) * ((k : ℝ) + 1) ^ 2) ^ (2 * r) * (n : ℝ) ^ r * NxA n d k A κ

/-- **Lemma L** (lower bound, Mehler): `E_x[ρ_x^{2k} 𝒩(f; κ_x)] ≤ E_Z S(σZ)` (`S` of Theorem RK-G). -/
def LemmaL60 (d k : ℕ) : Prop :=
  ∀ (n : ℕ) (μ : Measure (Fin n → ℝ)), SphLaw n μ → ∀ v : Fin n → ℝ, UnitV v →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T →
      ∫ x, rho2 v x ^ k * NxA n d k (TF k f0 T) (kap60 d x) ∂μ ≤
        ∫ Z, Sfl μ d k f0 T v (sg n d • Z) ∂stdGauss (CoefIdxD n d)

/-- **Lemma M** (no mass escapes to the poles), with the step `𝒩 ≤ θ^{−k} ρ^{2k} 𝒩` on the good set:
`E_x 𝒩(A; κ_x) ≤ C_M E_x[ρ_x^{2k} 𝒩(A; κ_x)]` under `D_{t,v}`, `t ∈ [0, C n]`, uniformly in `A`. -/
def LemmaM60 (d k : ℕ) (C CM : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ C * n → ∀ A : Tens n,
    ∫ x, NxA n d k A (kap60 d x) ∂lawRK n t v ≤
      CM * ∫ x, rho2 v x ^ k * NxA n d k A (kap60 d x) ∂lawRK n t v

/-- **Radial tail** (second event of Prop T2″), every law on the sphere:
`Pr_Z{√(s E_x 𝒩(f; κ_x)) ≤ radDef(Z/‖Z‖, λ)} ≤ C/(n s)`. -/
def RadialTail60 (d k : ℕ) (C : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ μ : Measure (Fin n → ℝ), SphLaw n μ →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) → ∀ s : ℝ, 0 < s →
      stdGauss (CoefIdxD n d) {Z | Real.sqrt (s * FlA μ d k (TF k f0 T)) ≤
        radDef59 μ k f0 T (unitOfD Z) (lam59 n d Z)} ≤ ENNReal.ofReal (C / (n * s))

end BstLean.Part60
