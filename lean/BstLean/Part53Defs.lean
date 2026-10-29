import BstLean.Part51Defs

/-!
# Part 53, wave 0: frozen definitions — Theorem DL1, the constant-column program, every `d_f ≤ d_M + 1`

Source: `delegations/answers/omDL1-opus-prover.md` §1–§8, with the repairs of `chDL1-opus.md` and
`chDL1-codex.md` (the Stirling proof of Lemma R's endpoint density; the `L²` bound in Prop E).
Specification: `delegations/answers/p53-spec-opus.md`.
This file holds definitions only. Provers must not edit it, and must not use `native_decide` or
`axiom` anywhere.

Conventions. Part 36, 41, 43, 48 and 51 names are reused. `k = d_f`, `d = d_M`. `f = (f₀, T)` with
`f(y) = f₀ + Σ_{j=1}^k T_j[y, …, y]` (`fval`), `T_j` symmetric (`TSymm k T`). `φ(x)` is the vector of
raw monomials `x^β`, `|β| ≤ d` (`phiM`, index `Mono n d`); `default : Mono n d` is the constant
monomial `φ₀ = 1`. `M : CoefIdxD n d → ℝ`; `colM M p ∈ ℝⁿ` is the column of the monomial `p`, so
`m(0) = colM M default`. `𝒟 = DD n d = n·C(n+d,d) = Pn n d`, `σ = sg n d = 𝒟^{−1/2}`.

* **Full tensor family.** `TF k f0 T` has `TF 0 = f₀`, `TF j = T j` (`1 ≤ j ≤ k`), `TF j = 0` (`j > k`).
  `fvA k A y = Σ_{c ≤ k} A_c[y, …, y]`, so `fvA k (TF k f0 T) = fval k f0 T`.
* **Heat semigroup.** `heatA k v A` is the coefficient family of `P_v h = exp(vΔ/2) h` for
  `h = fvA k A` with symmetric `A`: `(P_v A)_c = Σ_{i} (v/2)^i/i! · (c+2i)!/c! · tr^i A_{c+2i}`
  (Lemma Tr). `v` may be negative.
* **The program.** `c₀ = c0 d = Σ_{j ≤ d} 1/j!`, `a = aH n d = (c₀ − 1)/𝒟`.
  `g0 n d k f0 T M = (P_a f)(M_{·,0})` (Program `g₀`). `gh` is its homogeneous extension
  `(P_{‖M‖² a} f)(M_{·,0})` (§7).
* **The norm `N°`.** `Tcirc = heatA k (c₀/𝒟) (TF k f0 T)` (the tensors `T°_c` of `f° = P_{σ² c₀} f`),
  `Ncirc = Σ_{c=1}^k σ^{2c} ‖T°_c‖²`.
* **Laws.** `DensLaw n μ Λ`: `μ` is a probability law with a density `ρ` with respect to the uniform law
  on the sphere, `e^{−Λ} ≤ ρ ≤ e^{Λ}` on the sphere.
* **Gaussian proxy.** `linZ Z ψ = Zψ ∈ ℝⁿ` for `ψ ∈ ℝ^N`. `wpair k s A A' ψ ψ'` is the right side of
  the chaos identity (Lemma W): `Σ_c c! s^{2c} ⟨(P_{s²‖ψ‖²}A)_c, (P_{s²‖ψ'‖²}A')_c⟩ ⟨ψ, ψ'⟩^c`.
* **Reading.** `Reads53 p i` (as Part 52's `Reads`): an instruction argument or an output of `p` is
  `inp i`. `ConstColOnly p`: `p` reads no entry `M_α` with `deg α ≥ 1`.
* **Statements.** The interfaces between the wave-1 files are `Prop`-valued definitions
  (`LemmaU53`, `LemmaS53`, `LemmaG53`, `LemmaTr53`, `LemmaW53`, `LemmaR53`, `GaussPolar53`, `PropE53`,
  `PropF53`, `PropH53`, `PropT1_53`, `PropT2_53`). A wave-1 file proves one of them, and may take
  others as hypotheses; it does not import another wave-1 file.
* **Cost.** `costG53 n d k` is the proved bound on the cost of the program (§2 of the source, with the
  weights and the constants built from `0` and `1`).
-/

namespace BstLean.Part53

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM phiSq colM contr trL frob IsSymmT Tens TSymm fval In41)

variable {n d : ℕ}

/-! ## §1 Tensor families, the heat semigroup -/

/-- The full tensor family of `f = (f₀, T)` at degree `k`. -/
def TF (k : ℕ) (f0 : ℝ) (T : Tens n) : Tens n := fun j w =>
  if j = 0 then f0 else if j ≤ k then T j w else 0

/-- `h(y) = Σ_{c ≤ k} A_c[y, …, y]`. -/
def fvA (k : ℕ) (A : Tens n) (y : Fin n → ℝ) : ℝ :=
  ∑ c ∈ Finset.range (k + 1), contr (A c) (fun _ => y)

/-- The heat semigroup on coefficient families: `(P_v A)_c = Σ_i (v/2)^i/i! (c+2i)!/c! tr^i A_{c+2i}`. -/
noncomputable def heatA (k : ℕ) (v : ℝ) (A : Tens n) : Tens n := fun c w =>
  ∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k),
    (v / 2) ^ i / (i.factorial : ℝ) * (((c + 2 * i).factorial : ℝ) / (c.factorial : ℝ)) *
      trL i (A (c + 2 * i)) (fun t => w ⟨t.1, by have := t.2; omega⟩)

/-! ## §2 The program `g₀` -/

/-- `σ = 𝒟^{−1/2}`. -/
noncomputable def sg (n d : ℕ) : ℝ := 1 / Real.sqrt (DD n d)

/-- `c₀ = Σ_{j=0}^d 1/j!`. -/
noncomputable def c0 (d : ℕ) : ℝ := ∑ j ∈ Finset.range (d + 1), 1 / (j.factorial : ℝ)

/-- `a = σ² (c₀ − 1)`. -/
noncomputable def aH (n d : ℕ) : ℝ := (c0 d - 1) / DD n d

/-- **Program `g₀`**: `g₀(M) = (P_a f)(M_{·,0})`. It reads only the constant column of `M` and `f`. -/
noncomputable def g0 (n d k : ℕ) (f0 : ℝ) (T : Tens n) (M : CoefIdxD n d → ℝ) : ℝ :=
  fvA k (heatA k (aH n d) (TF k f0 T)) (colM M default)

/-- The homogeneous extension `g^h(M) = (P_{‖M‖² a} f)(M_{·,0})` (§7); `g^h = g₀` on the sphere. -/
noncomputable def gh (n d k : ℕ) (f0 : ℝ) (T : Tens n) (M : CoefIdxD n d → ℝ) : ℝ :=
  fvA k (heatA k ((∑ α, M α ^ 2) * aH n d) (TF k f0 T)) (colM M default)

/-- The program's inputs for `f = (f₀, T)` and `M` (Part 41's input type `In41`). -/
def inp53 {k : ℕ} (f0 : ℝ) (T : Tens n) (M : CoefIdxD n d → ℝ) : In41 n d k → ℝ :=
  Sum.elim M (Sum.elim (fun _ => f0) (fun jw => T jw.1 jw.2))

/-- `p` reads the input `i`: some instruction has `inp i` as an argument, or some output is `inp i`. -/
def Reads53 {ι κ : Type} (p : Prog ι κ) (i : ι) : Prop :=
  (∃ I ∈ p.body, I.a = .inp i ∨ I.b = .inp i) ∨ ∃ o, p.out o = .inp i

/-- `p` reads no entry of `M` outside the constant column (the column of the constant monomial,
degree `0`). It may read every coefficient of `f`. -/
def ConstColOnly {k : ℕ} (p : Prog (In41 n d k) Unit) : Prop :=
  ∀ α : CoefIdxD n d, Reads53 p (Sum.inl α) → α.1 = 0

/-! ## §3 The norm `N°` -/

/-- `T°_c`, the coefficient tensors of `f° = P_{σ² c₀} f`. -/
noncomputable def Tcirc (n d k : ℕ) (f0 : ℝ) (T : Tens n) : Tens n :=
  heatA k (c0 d / DD n d) (TF k f0 T)

/-- `N°(f) = Σ_{c=1}^k σ^{2c} ‖T°_c‖²`. -/
noncomputable def Ncirc (n d k : ℕ) (f0 : ℝ) (T : Tens n) : ℝ :=
  ∑ c ∈ Finset.Icc 1 k, frob (Tcirc n d k f0 T c) / DD n d ^ c

/-! ## §4 Laws with a bounded density ratio -/

/-- `μ` is a probability law with density `ρ` relative to the uniform law on the sphere, and
`e^{−Λ} ≤ ρ ≤ e^{Λ}` on the sphere. -/
def DensLaw (n : ℕ) (μ : Measure (Fin n → ℝ)) (Λ : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧
  ∃ ρ : (Fin n → ℝ) → ℝ, Measurable ρ ∧ (∀ x, 0 ≤ ρ x) ∧
    μ = (uniformSphere n).withDensity (fun x => ENNReal.ofReal (ρ x)) ∧
    ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → Real.exp (-Λ) ≤ ρ x ∧ ρ x ≤ Real.exp Λ

/-! ## §5 The Gaussian proxy and Lemma W -/

/-- `Zψ ∈ ℝⁿ`: `(Zψ)_a = Σ_p Z_{p,a} ψ_p`. In particular `mapMD M x = linZ M (φ(x))`. -/
noncomputable def linZ (Z : CoefIdxD n d → ℝ) (ψ : Mono n d → ℝ) : Fin n → ℝ := fun a =>
  ∑ p : Mono n d, colM Z p a * ψ p

/-- `‖ψ‖²`. -/
noncomputable def nsq (ψ : Mono n d → ℝ) : ℝ := ∑ p, ψ p ^ 2

/-- `⟨A, A'⟩ = Σ_w A w · A' w` for order-`c` tensors. -/
def tinner {c : ℕ} (A A' : (Fin c → Fin n) → ℝ) : ℝ := ∑ w, A w * A' w

/-- The right side of Lemma W: `Σ_c c! s^{2c} ⟨(P_{s²‖ψ‖²}A)_c, (P_{s²‖ψ'‖²}A')_c⟩ ⟨ψ, ψ'⟩^c`. -/
noncomputable def wpair (k : ℕ) (s : ℝ) (A A' : Tens n) (ψ ψ' : Mono n d → ℝ) : ℝ :=
  ∑ c ∈ Finset.range (k + 1), (c.factorial : ℝ) * s ^ (2 * c) *
    tinner (heatA k (s ^ 2 * nsq ψ) A c) (heatA k (s ^ 2 * nsq ψ') A' c) *
    (∑ p, ψ p * ψ' p) ^ c

/-! ## §6 The interface statements -/

/-- `Σ_i x_i⁴`. -/
def p4 (x : Fin n → ℝ) : ℝ := ∑ i, x i ^ 4

/-- **Lemma U.** On the sphere, `0 ≤ u − c₀ ≤ d · p₄`, `u = ‖φ‖²`. -/
def LemmaU53 (d : ℕ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ), ∑ i, x i ^ 2 = 1 →
    0 ≤ phiSq d x - c0 d ∧ phiSq d x - c0 d ≤ d * p4 x

/-- **Lemma S.** `E_σ p₄^q ≤ (4q−1)!! n^{−q}`, `q ≥ 1`. -/
def LemmaS53 : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ q : ℕ, 1 ≤ q →
    ∫ x, p4 x ^ q ∂uniformSphere n ≤ ((4 * q - 1).doubleFactorial : ℝ) / (n : ℝ) ^ q

/-- `c_d = d (2d−1)!!`. -/
def cG (d : ℕ) : ℝ := d * ((2 * d - 1).doubleFactorial : ℝ)

/-- **Lemma G.** For `a ∈ ℝ^N` with `a₀ = 0`: `E_σ (a·φ)² ≤ (c_d/n) ‖a‖²`. -/
def LemmaG53 (d : ℕ) : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ a : Mono n d → ℝ, a default = 0 →
    ∫ x, (∑ p, a p * phiM x p) ^ 2 ∂uniformSphere n ≤ cG d / n * nsq a

/-- **Lemma Tr.** `‖tr^i A‖² ≤ nⁱ ‖A‖²` for every tensor `A` of order `j ≥ 2i` (no symmetry needed).
The order condition is needed: at `j < 2i`, `trL` counts unused contraction indices. -/
def LemmaTr53 : Prop :=
  ∀ (n j i : ℕ) (A : (Fin j → Fin n) → ℝ), 2 * i ≤ j → frob (trL i A) ≤ (n : ℝ) ^ i * frob A

/-- **Lemma W** (the chaos identity in the Gaussian proxy): for symmetric families `A, A'`, vectors
`ψ, ψ' ∈ ℝ^N` and a scale `s`, with `Z` standard Gaussian on `ℝ^{n×N}`,
`E_Z[h_A(s Zψ) h_{A'}(s Zψ')] = wpair k s A A' ψ ψ'`, and the product is integrable. -/
def LemmaW53 (k : ℕ) : Prop :=
  ∀ (n d : ℕ) (s : ℝ) (A A' : Tens n), (∀ j, IsSymmT (A j)) → (∀ j, IsSymmT (A' j)) →
    ∀ ψ ψ' : Mono n d → ℝ,
      Integrable (fun Z => fvA k A (s • linZ Z ψ) * fvA k A' (s • linZ Z ψ'))
        (stdGauss (CoefIdxD n d)) ∧
      ∫ Z, fvA k A (s • linZ Z ψ) * fvA k A' (s • linZ Z ψ') ∂stdGauss (CoefIdxD n d) =
        wpair k s A A' ψ ψ'

/-- **Lemma R** (the Remez step, with the Stirling repair): if `𝒟 = |ι| ≥ 1000` and `λ = ‖Z‖/√𝒟`,
then every real polynomial `p` of degree `≤ k` has `p(1)² ≤ 2.5 (k+1)² E p(λ)²`. -/
def LemmaR53 (k : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι], 1000 ≤ Fintype.card ι → ∀ p : Polynomial ℝ, p.natDegree ≤ k →
    p.eval 1 ^ 2 ≤ 5 / 2 * ((k : ℝ) + 1) ^ 2 *
      ∫ Z, (p.eval (Real.sqrt (∑ i, Z i ^ 2) / Real.sqrt (Fintype.card ι))) ^ 2 ∂stdGauss ι

/-- **Polar independence.** Under the standard Gaussian, the direction `Z/‖Z‖` and the radius `‖Z‖`
are independent. -/
def GaussPolar53 : Prop :=
  ∀ (n d : ℕ) (F : (CoefIdxD n d → ℝ) → ℝ → ℝ≥0∞), Measurable (Function.uncurry F) →
    ∫⁻ Z, F (unitOfD Z) (Real.sqrt (∑ α, Z α ^ 2)) ∂stdGauss (CoefIdxD n d) =
      ∫⁻ Z, ∫⁻ Z', F (unitOfD Z) (Real.sqrt (∑ α, Z' α ^ 2)) ∂stdGauss (CoefIdxD n d)
        ∂stdGauss (CoefIdxD n d)

/-- **Prop E** (the error in the Gaussian proxy): `E_Z (B − g₀)(σZ)² ≤ (C/n) N°` for `n ≥ n₀`, and the
integrand is integrable (so that the bound carries information). -/
def PropE53 (d k : ℕ) (Λ C : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ μ : Measure (Fin n → ℝ), DensLaw n μ Λ →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
      Integrable (fun Z => (BstLean.Part43.BofQ μ k f0 T (sg n d • Z) - g0 n d k f0 T (sg n d • Z)) ^ 2)
          (stdGauss (CoefIdxD n d)) ∧
      ∫ Z, (BstLean.Part43.BofQ μ k f0 T (sg n d • Z) - g0 n d k f0 T (sg n d • Z)) ^ 2
          ∂stdGauss (CoefIdxD n d) ≤ C / n * Ncirc n d k f0 T

/-- **Prop F** (the floor in the Gaussian proxy): `E_Z Var_μ f(σZφ(x)) ≥ N°/8` for `n ≥ n₀`. -/
def PropF53 (d k : ℕ) (Λ : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ μ : Measure (Fin n → ℝ), DensLaw n μ Λ →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
      Ncirc n d k f0 T / 8 ≤
        ∫ Z, BstLean.Part43.varFQ μ k f0 T (sg n d • Z) ∂stdGauss (CoefIdxD n d)

/-- **Prop H** (the radial part of the homogeneous extension, in the proof of Prop T1):
`E_Z (g^h − g₀)(σZ)² ≤ (C/n) N°` for `n ≥ n₀`, with the integrand integrable. -/
def PropH53 (d k : ℕ) (C : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
    Integrable (fun Z => (gh n d k f0 T (sg n d • Z) - g0 n d k f0 T (sg n d • Z)) ^ 2)
        (stdGauss (CoefIdxD n d)) ∧
    ∫ Z, (gh n d k f0 T (sg n d • Z) - g0 n d k f0 T (sg n d • Z)) ^ 2 ∂stdGauss (CoefIdxD n d) ≤
      C / n * Ncirc n d k f0 T

/-- **Prop T1** (the error on the coefficient sphere, with Markov): for every `c > 0`,
`Pr_M{(B − g₀)(M)² ≥ c N°} ≤ C/(n c)` for `n ≥ n₀`, `M = Z/‖Z‖`. -/
def PropT1_53 (d k : ℕ) (Λ C : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ μ : Measure (Fin n → ℝ), DensLaw n μ Λ →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) → ∀ c : ℝ, 0 < c →
      stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
        c * Ncirc n d k f0 T ≤
          (BstLean.Part43.BofQ μ k f0 T (unitOfD Z) - g0 n d k f0 T (unitOfD Z)) ^ 2} ≤
        ENNReal.ofReal (C / (n * c))

/-- **Prop T2** (the floor on the coefficient sphere): `Pr_M{Var_μ f(Mφ) < s N°} ≤ p + C/(n s)` for
`n ≥ n₀`, `M = Z/‖Z‖`. -/
def PropT2_53 (d k : ℕ) (Λ p s C : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ μ : Measure (Fin n → ℝ), DensLaw n μ Λ →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
      stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
        BstLean.Part43.varFQ μ k f0 T (unitOfD Z) < s * Ncirc n d k f0 T} ≤
        ENNReal.ofReal (p + C / (n * s))

/-! ## §7 Cost -/

/-- The proved bound on the cost of the program `g₀`: `3·C(n+k,k)` for the evaluation at `m(0)`
(one product for the monomial, one for its coefficient, one addition), `(k+1)²(n+2)·C(n+k−1,k−2)` for
the traces `tr^i T_{c+2i}` and their weighted sums (`c ≤ k − 2`), and the constants built from `0` and
`1` (`𝒟` by doubling, `c₀`, the weights `(a/2)^i (c+2i)!/(i! c!)`, the orbit sizes per partition type). -/
noncomputable def costG53 (n d k : ℕ) : ℝ :=
  3 * ((n + k).choose k : ℝ) + ((k : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) * ((n + k - 1).choose (k - 2) : ℝ) +
    64 * ((k : ℝ) + d + 2) ^ 3 * 2 ^ (k + 1) + 8 * ((Nat.log 2 (Fintype.card (CoefIdxD n d)) : ℝ) + 2)

end BstLean.Part53
