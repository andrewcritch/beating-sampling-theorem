import BstLean.Part53Defs

/-!
# Part 59, wave 0: frozen definitions — Theorem DL2-G, the constant-column program for every
output degree, under the charged baseline

Source: `delegations/answers/omDL2-opus-prover.md` lines 25–247 (Theorem DL2-G), with the repairs of
`chDL2-opus.md` (D1: `n₀ ≥ max(100, 2k)`) and `chDL2-codex.md` (§3: `𝒟 ≥ 1000` in Prop T2*).
Specification: `delegations/answers/p59-spec-opus.md`.
This file holds definitions only. Provers must not edit it, and must not use `native_decide` or
`axiom` anywhere.

Conventions. Part 36, 41, 43, 48 and 53 names are reused. `k = d_f`, `d = d_M`.

* **`f` as a coefficient vector.** The input `f` of the program and of the baseline is the vector of
  its monomial coefficients `c : Mono n k → ℝ` (`Mono n k = Σ i : Fin (k+1), Sym (Fin n) i`, the
  monomials `y^α`, `|α| ≤ k`, `C(n+k,k)` of them). `polyEval k c y = Σ_α c_α y^α`.
  `TopNZ k c`: some coefficient of degree exactly `k` is nonzero ("`f` of degree `k`").
* **The tensor form.** `tensOf k c` is the symmetric tensor family with `T_j[w] = c_{mset w}/orb(w)`,
  `orb(w)` the number of words with the multiset of `w`. Then `fval k (c default) (tensOf k c) =
  polyEval k c` (the interface `CoefTens59`). The analysis (Props E, F, T1*, T2*) runs on the tensor
  form, as in Part 53.
* **The charged baseline (Dev's A9).** `costF n k = 2·C(n+k,k) − 2` is the exact cost of the nested
  tree (multivariate Horner) evaluation of a degree-`k` polynomial (`HornerExact59`).
  `P′ = Pn n d + costF n k`, `baselineF n d k ε = max(2P′, 0.91 P′/ε²)` (reading R1 of the source).
* **The program `g₀`.** `qH e t a = E(t + √a g)^e` by the recursion `q₀ = 1`, `q₁ = t`,
  `q_{e+2} = t q_{e+1} + (e+1) a q_e` (Lemma Q). `g0Q n d k c M = Σ_α c_α Π_i qH (α_i) (y_i) a` with
  `y = M_{·,0} = colM M default` and `a = aH n d = (c₀ − 1)/𝒟`. `LemmaQ59`: `g0Q` equals Part 53's
  `g0` on the tensor form. `costG59` is the cost bound of the source's Prop C.
* **Laws with an upper density bound only.** `UpLaw n μ K`: `μ` is a probability law with a density
  `ρ ≤ K` relative to the uniform law on the sphere. No lower bound.
* **Statements.** The interfaces between the wave-1 files are `Prop`-valued definitions. A wave-1
  file proves one of them, and may take others as hypotheses; it does not import another wave-1 file.
-/

namespace BstLean.Part59

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM contr trL frob IsSymmT Tens TSymm fval Pn varU sdU mset)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part53 (sg c0 aH g0 heatA fvA Ncirc Reads53)

variable {n d : ℕ}

/-! ## §1 `f` as a coefficient vector -/

/-- `f(y) = Σ_{|α| ≤ k} c_α y^α`. -/
noncomputable def polyEval (k : ℕ) (c : Mono n k → ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ α : Mono n k, c α * phiM y α

/-- `f` has degree exactly `k`: some coefficient of degree `k` is nonzero. -/
def TopNZ (k : ℕ) (c : Mono n k → ℝ) : Prop :=
  ∃ α : Mono n k, α.1 = Fin.last k ∧ c α ≠ 0

/-- The number of words with the multiset of `w`: `j!/Π_i (count_i w)!`. -/
def orb {j : ℕ} (w : Fin j → Fin n) : ℕ :=
  Nat.multinomial Finset.univ (fun i => (mset w).count i)

/-- The multiset of a word of length `j ≤ k`, as a monomial of `Mono n k`. -/
def monoOf (k : ℕ) {j : ℕ} (hj : j ≤ k) (w : Fin j → Fin n) : Mono n k :=
  ⟨⟨j, by omega⟩, ⟨mset w, by simp [mset]⟩⟩

/-- The symmetric tensor family of the coefficient vector `c`: `T_j[w] = c_{mset w}/orb(w)`
(`j ≤ k`), `0` above `k`. -/
noncomputable def tensOf (k : ℕ) (c : Mono n k → ℝ) : Tens n := fun j w =>
  if h : j ≤ k then c (monoOf k h w) / (orb w : ℝ) else 0

/-- `B_μ(M) = E_μ f(M φ(x))` for `f = polyEval k c`. -/
noncomputable def BP (μ : Measure (Fin n → ℝ)) (k : ℕ) (c : Mono n k → ℝ) (M : CoefIdxD n d → ℝ) : ℝ :=
  ∫ x, polyEval k c (mapMD M x) ∂μ

/-- `Var_μ f(M φ(x))` for `f = polyEval k c`. -/
noncomputable def varP (μ : Measure (Fin n → ℝ)) (k : ℕ) (c : Mono n k → ℝ) (M : CoefIdxD n d → ℝ) : ℝ :=
  varU μ (fun x => polyEval k c (mapMD M x))

/-! ## §2 The charged baseline -/

/-- The exact cost of the nested-tree (multivariate Horner) evaluation of a degree-`k` polynomial
in `n` variables: one product and one sum per edge of the tree on the `C(n+k,k)` monomials. -/
noncomputable def costF (n k : ℕ) : ℝ := 2 * ((n + k).choose k : ℝ) - 2

/-- The cost of one charged sample, `P′ = P + C_f`. -/
noncomputable def Pp (n d k : ℕ) : ℝ := Pn n d + costF n k

/-- **The charged baseline** `max(2P′, 0.91 P′/ε²)` (Dev's A9; reading R1 of the source). -/
noncomputable def baselineF (n d k : ℕ) (ε : ℝ) : ℝ :=
  max (2 * Pp n d k) (91 / 100 * Pp n d k / ε ^ 2)

/-- The input type of the Horner program: the coefficients `c_α` and the point `y`. -/
abbrev InH (n k : ℕ) := Mono n k ⊕ Fin n

/-- **The baseline's `f`-program is honest**: a program from the constants `0` and `1` evaluates every
polynomial of degree `≤ k` at every point, with exactly `2·C(n+k,k) − 2` operations. -/
def HornerExact59 (n k : ℕ) : Prop :=
  ∃ pg : Prog (InH n k) Unit, BstLean.Part41.heavyCount pg = 0 ∧
    (∀ v : InH n k → ℝ, pg.eval v () = polyEval k (fun α => v (Sum.inl α)) (fun i => v (Sum.inr i))) ∧
    pg.cost = 2 * (n + k).choose k - 2

/-! ## §3 The program `g₀` -/

/-- `q_e(t; a) = E(t + √a g)^e`, by `q₀ = 1`, `q₁ = t`, `q_{e+2} = t q_{e+1} + (e+1) a q_e`. -/
noncomputable def qH : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 1
  | 1, t, _ => t
  | e + 2, t, a => t * qH (e + 1) t a + ((e : ℝ) + 1) * a * qH e t a

/-- **Program `g₀`** in the form of Lemma Q: `(P_a f)(y) = Σ_α c_α Π_i q_{α_i}(y_i; a)`,
`y = M_{·,0}`, `a = (c₀ − 1)/𝒟`. -/
noncomputable def g0Q (n d k : ℕ) (c : Mono n k → ℝ) (M : CoefIdxD n d → ℝ) : ℝ :=
  ∑ α : Mono n k, c α * ∏ i : Fin n, qH (α.2.1.count i) (colM M default i) (aH n d)

/-- The program's inputs: the entries of `M` and the coefficients of `f`. -/
abbrev In59 (n d k : ℕ) := CoefIdxD n d ⊕ Mono n k

def Mv59 {k : ℕ} (v : In59 n d k → ℝ) : CoefIdxD n d → ℝ := fun α => v (Sum.inl α)
def cv59 {k : ℕ} (v : In59 n d k → ℝ) : Mono n k → ℝ := fun α => v (Sum.inr α)

/-- The input vector for `f = c` and `M`. -/
def inp59 {k : ℕ} (c : Mono n k → ℝ) (M : CoefIdxD n d → ℝ) : In59 n d k → ℝ := Sum.elim M c

/-- `p` reads no entry `M_α` outside the constant column. It may read every coefficient of `f`. -/
def ConstColOnly59 {k : ℕ} (p : Prog (In59 n d k) Unit) : Prop :=
  ∀ α : CoefIdxD n d, Reads53 p (Sum.inl α) → α.1 = 0

/-- The cost bound of Prop C: the tree `2C(n+k,k) − 2`, the table `3n(k−1)`, and the constants
`Q_c ≤ 2⌊log₂ n⌋ + 6d + 3k + 10` (`n` by doubling, `N = Π (n+j)/j`, `c₀ − 1 = Σ 1/j!`, `a`, `e·a`). -/
noncomputable def costG59 (n d k : ℕ) : ℝ :=
  2 * ((n + k).choose k : ℝ) - 2 + 3 * (n : ℝ) * ((k - 1 : ℕ) : ℝ) +
    (2 * (Nat.log 2 n : ℝ) + 6 * d + 3 * k + 10)

/-! ## §4 Laws with an upper density bound -/

/-- `μ` is a probability law with density `ρ ≤ K` relative to the uniform law on the sphere. -/
def UpLaw (n : ℕ) (μ : Measure (Fin n → ℝ)) (K : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧
  ∃ ρ : (Fin n → ℝ) → ℝ, Measurable ρ ∧ (∀ x, 0 ≤ ρ x) ∧
    μ = (uniformSphere n).withDensity (fun x => ENNReal.ofReal (ρ x)) ∧
    ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → ρ x ≤ K

/-! ## §5 Seminorm `N°` of a family, the binomial Euler family, the radial defect -/

/-- `N°(A) = Σ_{c=1}^k σ^{2c} ‖(P_{σ²c₀} A)_c‖²`. `Ncirc n d k f0 T = NcA n d k (TF k f0 T)`. -/
noncomputable def NcA (n d k : ℕ) (A : Tens n) : ℝ :=
  ∑ c ∈ Finset.Icc 1 k, frob (heatA k (c0 d / DD n d) A c) / DD n d ^ c

/-- `binom(E, r)` on coefficient families: the degree-`j` part is multiplied by `C(j, r)`. -/
def binA (r : ℕ) (A : Tens n) : Tens n := fun j w => (j.choose r : ℝ) * A j w

/-- The radial defect `sd_μ[f(lWφ(x)) − f(Wφ(x))]`. -/
noncomputable def radDef59 (μ : Measure (Fin n → ℝ)) (k : ℕ) (f0 : ℝ) (T : Tens n)
    (W : CoefIdxD n d → ℝ) (l : ℝ) : ℝ :=
  sdU μ (fun x => fval k f0 T (mapMD (l • W) x) - fval k f0 T (mapMD W x))

/-- `λ = ‖Z‖/√𝒟` (Part 53's `T2Aux.radialScale`, restated so that this file needs no wave-1 import). -/
noncomputable def lam59 (n d : ℕ) (Z : CoefIdxD n d → ℝ) : ℝ :=
  Real.sqrt (∑ α, Z α ^ 2) / Real.sqrt (DD n d)

/-! ## §6 The interface statements -/

/-- **Coefficient form = tensor form.** `tensOf k c` is symmetric, gives the same polynomial, and has
`T_k ≠ 0` when `f` has degree `k`. -/
def CoefTens59 : Prop :=
  ∀ (n k : ℕ) (c : Mono n k → ℝ),
    TSymm k (tensOf k c) ∧
    (∀ y : Fin n → ℝ, fval k (c default) (tensOf k c) y = polyEval k c y) ∧
    (TopNZ k c → 0 < frob (tensOf k c k))

/-- **Lemma Q.** The nested-tree formula equals Part 53's `g₀ = (P_a f)(M_{·,0})` on the tensor form. -/
def LemmaQ59 : Prop :=
  ∀ (n d k : ℕ) (c : Mono n k → ℝ) (M : CoefIdxD n d → ℝ),
    g0Q n d k c M = g0 n d k (c default) (tensOf k c) M

/-- **Prop E** (proxy error), laws with `dD/dσ ≤ K`. -/
def PropE59 (d k : ℕ) (K C : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ μ : Measure (Fin n → ℝ), UpLaw n μ K →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
      Integrable (fun Z => (BofQ μ k f0 T (sg n d • Z) - g0 n d k f0 T (sg n d • Z)) ^ 2)
          (stdGauss (CoefIdxD n d)) ∧
      ∫ Z, (BofQ μ k f0 T (sg n d • Z) - g0 n d k f0 T (sg n d • Z)) ^ 2
          ∂stdGauss (CoefIdxD n d) ≤ C / n * Ncirc n d k f0 T

/-- **Prop F** (proxy floor), laws with `dD/dσ ≤ K`. -/
def PropF59 (d k : ℕ) (K : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ μ : Measure (Fin n → ℝ), UpLaw n μ K →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
      Ncirc n d k f0 T / 8 ≤ ∫ Z, varFQ μ k f0 T (sg n d • Z) ∂stdGauss (CoefIdxD n d)

/-- **Lemma R+**: for `𝒟 = |ι| ≥ 1000`, `λ = ‖Z‖/√𝒟` and every real polynomial `q ≥ 0` of degree
`≤ 2k`: `q(1) ≤ 2.5 (k+1)² E q(λ)`. -/
def LemmaRp59 (k : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι], 1000 ≤ Fintype.card ι → ∀ q : Polynomial ℝ, q.natDegree ≤ 2 * k →
    (∀ x : ℝ, 0 ≤ q.eval x) →
    q.eval 1 ≤ 5 / 2 * ((k : ℝ) + 1) ^ 2 *
      ∫ Z, q.eval (Real.sqrt (∑ i, Z i ^ 2) / Real.sqrt (Fintype.card ι)) ∂stdGauss ι

/-- **Lemma V** (proxy variance of any polynomial of degree `≤ k`), laws with `dD/dσ ≤ K`. -/
def LemmaV59 (d k : ℕ) (K C : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ μ : Measure (Fin n → ℝ), UpLaw n μ K →
    ∀ A : Tens n, (∀ j, IsSymmT (A j)) →
      Integrable (fun Z => varU μ (fun x => fvA k A (mapMD (sg n d • Z) x))) (stdGauss (CoefIdxD n d)) ∧
      ∫ Z, varU μ (fun x => fvA k A (mapMD (sg n d • Z) x)) ∂stdGauss (CoefIdxD n d) ≤ C * NcA n d k A

/-- **Lemma H** (size of `h_r = binom(E, r) f`): `N°(h_r) ≤ (5k²)^{2r} n^r N°(f)`. -/
def LemmaH59 (d k : ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ A : Tens n, (∀ j, IsSymmT (A j)) → ∀ r : ℕ, 1 ≤ r → r ≤ k →
    NcA n d k (binA r A) ≤ (5 * (k : ℝ) ^ 2) ^ (2 * r) * (n : ℝ) ^ r * NcA n d k A

/-- **Radial tail** (the second event of Prop T2*): `Pr_Z{√(sN°) ≤ radDef(Z/‖Z‖, λ)} ≤ C/(ns)`. -/
def RadialTail59 (d k : ℕ) (K C : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ μ : Measure (Fin n → ℝ), UpLaw n μ K →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) → ∀ s : ℝ, 0 < s →
      stdGauss (CoefIdxD n d) {Z | Real.sqrt (s * Ncirc n d k f0 T) ≤
        radDef59 μ k f0 T (unitOfD Z) (lam59 n d Z)} ≤ ENNReal.ofReal (C / (n * s))

/-- **Prop T1*** (error on the coefficient sphere, with Markov), laws with `dD/dσ ≤ K`. -/
def PropT1_59 (d k : ℕ) (K C : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ μ : Measure (Fin n → ℝ), UpLaw n μ K →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) → ∀ c : ℝ, 0 < c →
      stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
        c * Ncirc n d k f0 T ≤ (BofQ μ k f0 T (unitOfD Z) - g0 n d k f0 T (unitOfD Z)) ^ 2} ≤
        ENNReal.ofReal (C / (n * c))

/-- **Prop T2*** (floor on the coefficient sphere), laws with `dD/dσ ≤ K`. -/
def PropT2_59 (d k : ℕ) (K p s C : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ μ : Measure (Fin n → ℝ), UpLaw n μ K →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
      stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧ varFQ μ k f0 T (unitOfD Z) < s * Ncirc n d k f0 T} ≤
        ENNReal.ofReal (p + C / (n * s))

end BstLean.Part59
