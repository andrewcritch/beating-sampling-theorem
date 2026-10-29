import BstLean.Part37Defs

/-!
# Part 40, wave 0: frozen definitions for the explicit `(2,2)` theorem at every diagonal Bingham law

Paper: `proofs/option-m/40-explicit-22-every-diagonal-bingham.tex` (Theorem `route (b)`, reading S).
Specification: `delegations/answers/p40-spec-opus.md`. This file holds definitions only. Provers must
not edit it, and must not use `native_decide` anywhere.

Conventions.
* The coefficient space `CoefIdx n`, the readers `cOf`, `LOf`, `aOf`, `Bof`, `varOf`, `unitOf`,
  `qformC`, `stdGauss` are Part 29's; `Dc n = |CoefIdx n| = nN` and `r2 Z = ‖Z‖²` are Part 33's;
  `bingham n θ` and `P37` are Part 37's. `θ : Fin n → ℝ` is arbitrary.
* `Mono n` indexes the raw monomials of degree `≤ 2`: the constant, `xᵢ`, and `xᵢxⱼ` (`i ≤ j`).
  `phi p x` is the monomial. `idx k p` is the coefficient of monomial `p` in output `k`, so
  `colOf M p = M_p` is the paper's column of `p`. `monIdx`, `outIdx` invert `idx`.
* `momE μ p = E_μ φ_p`, `momG μ p q = E_μ φ_pφ_q` (the matrix `G`).
* A kept set `K` is a finset of ordered pairs of monomials. `Rmat μ K` is `G` with the constant row
  and column and the entries of `K` set to `0` (the paper's `R`). `KeepOK μ k' K`: `K` is symmetric,
  has at most `k' + 1` ordered pairs (units), and `‖R‖_F² ≤ (25/16)/k'` (Lemma D1′, item 2).
  `keepSet μ k'` is a set with `KeepOK` (chosen by `Classical.epsilon`; `kept_exists` shows that one
  exists for a sign-symmetric law). The paper's top-`U` set is one such set.
* The program `gOf40L μ K` is `g_k` of Lemma D1′, written with the moment constants of `μ`
  (reading S: the moments of `D(θ)` enter as constants). `gOf40 n θ ε` uses `μ = bingham n θ`,
  `k' = kOf40 n ε` and `K = keepSet μ k'`.
* `Akron R F` is `A = R ⊗ F` on `CoefIdx n`.
* `ymap Z x = Zφ(x)`; `linZ g Z = ℓ_Z`, `quadZ F Z = q_Z`; `varL μ h = Var_μ h`;
  `Pof = Var(√D_c ℓ_Z + q_Z)` (the paper's `𝒫`), `Cof = Var q_Z` (the paper's `C`),
  `Qa = Var_μ(cᵀ F Z' φ')` (so `‖𝒜c‖² = 4 Qa`), `trSig μ = tr Σ_μ`.
* `SphLaw n μ`: a probability law carried by the unit sphere. `SignSym n μ`: a `SphLaw` invariant
  under every sign flip `flipAt i`.
* Constants of the proof: `σ = sig40 = 0.0085`, `s = s40 = 39.13`, `K = 80`, `x = 7`,
  `η_n = eta40 n`, `γ'_n = gam40 n`, `ρ* = rho40 = 3/8`, the floor failure
  `etaG40 = 2e^{−7} + ρ* + 1/80`, `L'(n) = Lp40 n`.
* The cost model stays outside Lean, as in Parts 29 and 35–39: `costOf40 n ε` is the paper's bound
  `(n² + 3n + 1)(k′ + 1) + 7n²` (Lemma `cost`), taken as a definition.
-/

namespace BstLean.Part40

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss qformι funF frobSq CoefIdx cOf LOf aOf Bof varOf unitOf qformC
  symOfRaw mapM)
open BstLean.Part33 (Dc r2)
open BstLean.Part37 (bingham P37)

variable {n : ℕ}

/-! ## §1 Monomials, columns and the matrix `G` -/

/-- Raw monomials of degree `≤ 2`: constant, `xᵢ`, `xᵢxⱼ` with `i ≤ j`. -/
abbrev Mono (n : ℕ) := Unit ⊕ Fin n ⊕ {p : Fin n × Fin n // p.1 ≤ p.2}

/-- The constant monomial. -/
def constM : Mono n := Sum.inl ()

/-- The monomial `φ_p(x)`. -/
def phi : Mono n → (Fin n → ℝ) → ℝ
  | Sum.inl _, _ => 1
  | Sum.inr (Sum.inl i), x => x i
  | Sum.inr (Sum.inr p), x => x p.1.1 * x p.1.2

/-- The coefficient index of monomial `p` in output `k`. -/
def idx (k : Fin n) : Mono n → CoefIdx n
  | Sum.inl _ => Sum.inl k
  | Sum.inr (Sum.inl i) => Sum.inr (Sum.inl (k, i))
  | Sum.inr (Sum.inr p) => Sum.inr (Sum.inr ⟨(p.1.1, p.1.2, k), p.2⟩)

/-- The monomial of a coefficient index. -/
def monIdx : CoefIdx n → Mono n
  | Sum.inl _ => Sum.inl ()
  | Sum.inr (Sum.inl ki) => Sum.inr (Sum.inl ki.2)
  | Sum.inr (Sum.inr q) => Sum.inr (Sum.inr ⟨(q.1.1, q.1.2.1), q.2⟩)

/-- The output of a coefficient index. -/
def outIdx : CoefIdx n → Fin n
  | Sum.inl k => k
  | Sum.inr (Sum.inl ki) => ki.1
  | Sum.inr (Sum.inr q) => q.1.2.2

/-- The column `M_p ∈ ℝⁿ` of monomial `p`. -/
def colOf (M : CoefIdx n → ℝ) (p : Mono n) : Fin n → ℝ := fun k => M (idx k p)

/-- `E_μ φ_p`. -/
noncomputable def momE (μ : Measure (Fin n → ℝ)) (p : Mono n) : ℝ := ∫ x, phi p x ∂μ

/-- `G_pq = E_μ φ_p φ_q`. -/
noncomputable def momG (μ : Measure (Fin n → ℝ)) (p q : Mono n) : ℝ := ∫ x, phi p x * phi q x ∂μ

/-! ## §2 The laws -/

/-- The sign flip of coordinate `i`. -/
def flipAt (i : Fin n) (x : Fin n → ℝ) : Fin n → ℝ := fun j => if j = i then -x j else x j

/-- A probability law carried by the unit sphere. -/
structure SphLaw (n : ℕ) (μ : Measure (Fin n → ℝ)) : Prop where
  prob : IsProbabilityMeasure μ
  sphere : ∀ᵐ x ∂μ, ∑ i, x i ^ 2 = 1

/-- A sign-symmetric law on the sphere. -/
structure SignSym (n : ℕ) (μ : Measure (Fin n → ℝ)) : Prop where
  sph : SphLaw n μ
  flip : ∀ i : Fin n, μ.map (flipAt i) = μ

/-! ## §3 The branch `g_k` (Lemma D1′) -/

/-- The residual `R`: `G` with the constant row and column and the kept entries set to `0`. -/
noncomputable def Rmat (μ : Measure (Fin n → ℝ)) (K : Finset (Mono n × Mono n)) (p q : Mono n) : ℝ := by
  classical
  exact if p ≠ constM ∧ q ≠ constM ∧ (p, q) ∉ K then momG μ p q else 0

/-- `K` is an admissible kept set for `k'`: symmetric, at most `k' + 1` units, `‖R‖_F² ≤ (25/16)/k'`. -/
def KeepOK (μ : Measure (Fin n → ℝ)) (k' : ℕ) (K : Finset (Mono n × Mono n)) : Prop :=
  (∀ p q, (p, q) ∈ K → (q, p) ∈ K) ∧ K.card ≤ k' + 1 ∧
    ∑ p, ∑ q, Rmat μ K p q ^ 2 ≤ 25 / 16 / (k' : ℝ)

/-- The kept set of the program: an admissible set (see `kept_exists`). -/
noncomputable def keepSet (μ : Measure (Fin n → ℝ)) (k' : ℕ) : Finset (Mono n × Mono n) :=
  Classical.epsilon (KeepOK μ k')

/-- The program `g_k` with kept set `K` and the moment constants of `μ`:
  `f₀ + bᵀ M E φ + Σ_{p,q} (G − R)_{pq} M_pᵀ F M_q + tr F · tr R / D_c`. -/
noncomputable def gOf40L (μ : Measure (Fin n → ℝ)) (K : Finset (Mono n × Mono n)) (f0 : ℝ)
    (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (M : CoefIdx n → ℝ) : ℝ :=
  f0 + ∑ k, g k * ∑ p, colOf M p k * momE μ p +
    ∑ p, ∑ q, (momG μ p q - Rmat μ K p q) * ∑ k, ∑ l, F k l * colOf M p k * colOf M q l +
    (∑ k, F k k) * (∑ p, Rmat μ K p p) / Dc n

/-- `A = R ⊗ F` on the coefficient space. -/
def Akron (R : Mono n → Mono n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (CoefIdx n) (CoefIdx n) ℝ :=
  fun α β => R (monIdx α) (monIdx β) * F (outIdx α) (outIdx β)

/-! ## §4 The spread and the floor quantities -/

/-- `Zφ(x)`: the map `m_Z` at `x`. -/
noncomputable def ymap (Z : CoefIdx n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  mapM (cOf Z) (LOf Z) (fun k => symOfRaw (aOf Z k)) x

/-- `ℓ_Z(x) = bᵀ Z φ(x)`. -/
noncomputable def linZ (g : Fin n → ℝ) (Z : CoefIdx n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ k, g k * ymap Z x k

/-- `q_Z(x) = φ(x)ᵀ Zᵀ F Z φ(x)`. -/
noncomputable def quadZ (F : Matrix (Fin n) (Fin n) ℝ) (Z : CoefIdx n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ k, ∑ l, F k l * ymap Z x k * ymap Z x l

/-- `Var_μ h`. -/
noncomputable def varL (μ : Measure (Fin n → ℝ)) (h : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ x, (h x - ∫ y, h y ∂μ) ^ 2 ∂μ

/-- `𝒫(Z) = Var_μ(√D_c ℓ_Z + q_Z)`. -/
noncomputable def Pof (μ : Measure (Fin n → ℝ)) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (Z : CoefIdx n → ℝ) : ℝ :=
  varL μ (fun x => Real.sqrt (Dc n) * linZ g Z x + quadZ F Z x)

/-- `C(Z) = Var_μ q_Z`. -/
noncomputable def Cof (μ : Measure (Fin n → ℝ)) (F : Matrix (Fin n) (Fin n) ℝ) (Z : CoefIdx n → ℝ) : ℝ :=
  varL μ (quadZ F Z)

/-- `Qa(Z) = Var_μ(cᵀ F Z' φ'(x))`, `c = cOf Z`, `Z'φ' = Zφ − c`; so `‖𝒜c‖² = 4 Qa`. -/
noncomputable def Qa (μ : Measure (Fin n → ℝ)) (F : Matrix (Fin n) (Fin n) ℝ) (Z : CoefIdx n → ℝ) : ℝ :=
  varL μ (fun x => ∑ k, ∑ l, cOf Z k * F k l * (ymap Z x l - cOf Z l))

/-- `tr Σ_μ = Σ_{p ≠ const} Var_μ φ_p`. -/
noncomputable def trSig (μ : Measure (Fin n → ℝ)) : ℝ := by
  classical
  exact ∑ p : Mono n, if p = constM then 0 else varL μ (phi p)

/-! ## §5 Constants of the proof -/

/-- `σ = 0.0085`. -/
noncomputable def sig40 : ℝ := 85 / 10000

/-- `s = 39.13`, the Chernoff parameter of Lemma SB. -/
noncomputable def s40 : ℝ := 3913 / 100

/-- `ρ* = 3/8`, the certified bound on `e^{sσ} E_h (1 + 2 s h²)^{−1/2}` (true value `0.369864`). -/
noncomputable def rho40 : ℝ := 3 / 8

/-- `E_h (1 + 2 s h²)^{−1/2}`, `h ∼ N(0, 1)`. -/
noncomputable def sbInt (s : ℝ) : ℝ := ∫ h, 1 / Real.sqrt (1 + 2 * s * h ^ 2) ∂gaussianReal 0 1

/-- `η_n = (2√(7 D_c) + 14)/D_c` (Lemma `norm` at `x = 7`). -/
noncomputable def eta40 (n : ℕ) : ℝ := (2 * Real.sqrt (7 * Dc n) + 14) / Dc n

/-- `γ'_n = (2√σ − η_n √(80(18 + n/16)))/(1 + η_n)`. -/
noncomputable def gam40 (n : ℕ) : ℝ :=
  (2 * Real.sqrt sig40 - eta40 n * Real.sqrt (80 * (18 + (n : ℝ) / 16))) / (1 + eta40 n)

/-- The floor failure `2e^{−7} + ρ* + 1/80`. -/
noncomputable def etaG40 : ℝ := 2 * Real.exp (-7) + rho40 + 1 / 80

/-- `L'(n) = n − 18 + (41n + 12)/(n² + 3n + 1)`. -/
noncomputable def Lp40 (n : ℕ) : ℝ :=
  (n : ℝ) - 18 + (41 * (n : ℝ) + 12) / ((n : ℝ) ^ 2 + 3 * n + 1)

/-! ## §6 The precision, the program and its cost -/

/-- The budget `𝔅(ε) = P · max(1, 2/ε²)`. -/
noncomputable def Bud40 (n : ℕ) (ε : ℝ) : ℝ := P37 (n : ℝ) * max 1 (2 / ε ^ 2)

/-- `k' = ⌊(𝔅 − 7n² − 1)/(n² + 3n + 1)⌋ − 1`. -/
noncomputable def kOf40 (n : ℕ) (ε : ℝ) : ℕ :=
  ⌊(Bud40 n ε - 7 * (n : ℝ) ^ 2 - 1) / ((n : ℝ) ^ 2 + 3 * n + 1)⌋₊ - 1

/-- The program of Theorem `route (b)`: `g_k` at `D = bingham n θ`, `k' = kOf40 n ε`. -/
noncomputable def gOf40 (θ : Fin n → ℝ) (ε : ℝ) (f0 : ℝ) (g : Fin n → ℝ)
    (F : Matrix (Fin n) (Fin n) ℝ) (M : CoefIdx n → ℝ) : ℝ :=
  gOf40L (bingham n θ) (keepSet (bingham n θ) (kOf40 n ε)) f0 g F M

/-- The paper's cost bound under reading S, moment charges included (Lemma `cost`). -/
noncomputable def costOf40 (n : ℕ) (ε : ℝ) : ℝ :=
  ((n : ℝ) ^ 2 + 3 * n + 1) * ((kOf40 n ε : ℝ) + 1) + 7 * (n : ℝ) ^ 2

end BstLean.Part40
