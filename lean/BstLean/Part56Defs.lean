import BstLean.Part53Defs

/-!
# Part 56, wave 0: frozen definitions — Theorem RK, the line program for dense rank-one Bingham laws

Source: `delegations/answers/omRK-opus-prover.md` lines 19–181 (Theorem RK, Theorem RK-G, Lemma MC,
Key Lemma, Prop D, §5 moments, §6 transfer), with the repairs of `chRK-codex.md` and `chRK-opus.md`
(the Key Lemma is used at rank `r = 1` only; `t ∈ [0, C n]`).
Specification: `delegations/answers/p56-spec-opus.md`.
This file holds definitions only. Provers must not edit it, and must not use `native_decide` or
`axiom` anywhere.

Conventions. Part 41, 43, 50 and 53 names are reused. `k = d_f`, `d = d_M`, `f = (f₀, T)`,
`TF k f0 T` is the full tensor family (`TF 0 = f₀`), `σ = sg n d = 𝒟^{−1/2}`, `𝒟 = DD n d = Pn n d`.

* **Law.** `rk1 t v = t·vvᵀ`; `lawRK n t v = binghamA n (rk1 t v) ∝ exp(t (v·x)²) σ` (Part 50).
  `surrRK n K t v = binghamKA n K (rk1 t v) ∝ p_K(t (v·x)²) σ` (the surrogate `Q̃`).
  `KRK C n e = Kof43 (C n) e` (the truncation order, uniform over `t ∈ [0, C n]`; accuracy `etaQ e`).
* **Blocks and kernels.** `phiB d j x` is the degree-`j` block `φ_j(x)` (zero off degree `j`).
  `kJ d j x y = ⟨φ_j(x), φ_j(y)⟩`, `betaJ d j v x = k_j(x,v)/k_j(v,v)`,
  `KR d v x y = Σ_{j=1}^d (k_j(x,y) − k_j(x,v)k_j(y,v)/k_j(v,v))` (residual kernel `K_R`),
  `tauR d v x = K_R(x,x)`, `rhoR d v x y = K_R(x,y)/√(τ(x)τ(y))` (`0` if a factor is `0`, by Lean's
  `x/0 = 0`), `deltaSq μ d v = E_{x,y∼μ⊗μ} ρ_R(x,y)²` (`δ²`).
* **Anchors.** `ancRK M v j = M φ_j(v) = M_j φ_j(v) ∈ ℝⁿ` (`u_j`). `mux M v x = Σ_j β_j(x) u_j`
  (the conditional mean of `m(x)` given the anchors, in the Gaussian proxy).
* **Program value, heat form.** `gLineH μ k f0 T v M = E_{x∼μ} (P_{σ² τ(x)} f)(μ_x)`, with Part 53's
  heat semigroup `heatA`. In the proxy `M = σZ` this is `E[B_μ | u_0, …, u_d]`.
* **Program value, weight form.** Keys `KeyRK k d = {(i, l, j⃗) : i, l ≤ k, j⃗ ∈ {0..d}^{i−2l}}`.
  `wickC i l = i!/(2^l l! (i−2l)!)`. The weight of a key under `μ` is
  `wRK μ d v (i,l,j⃗) = wickC i l · σ^{2l} · E_μ[τ^l Π_r β_{j_r}]`. `gW k A c u` is the weighted sum
  `Σ_{2l ≤ i} c(i,l,j⃗) · (tr^l A_i)[u_{j_1}, …, u_{j_{i−2l}}]`. `gLineW μ … = gW k (TF k f0 T) (wRK μ d v) u`.
* **Conditional variance.** `cvarG k f0 T a y = Var_{g∼N(0,I)} f(y + a g)`.
  `Sfl μ d k f0 T v M = E_{x∼μ} cvarG(σ√τ(x), μ_x)` (the quantity `S` of Theorem RK-G at `M = σZ`).
* **Proxy normalizer.** `EV56 d μ k f0 T = E_Z Var_μ f(σ Z φ(x))`.
* **Programs.** The line program reads `In56 n d k = In41 n d k ⊕ (Fin n ⊕ KeyRK k d)`: the entries of
  `M`, `f₀`, `T`, then `v`, then the weights. The moment program reads `InM56 n = Unit ⊕ Fin n`
  (`t`, then `v`) and returns one weight per key. `GSpec56`, `MomSpec56` are their specifications.
* **Cost.** `costLine56` (the proved-cost bound of the line program), `onceCost56` (of the moment
  program), `nuRK εhi` (the share of the baseline reserved for the amortized moment program),
  `k0RK` (the amortization counter threshold), `etaRK` (the surrogate accuracy of the main proof).
* **Gaussian split.** `projA v Z = Π Z`, `Π` the orthogonal projection onto `span{φ_j(v)}` in the
  monomial index; `PropSplit56` states the independent split `Z = Π Z + (Z − Π Z)`.
* **Statements.** The interfaces between the wave-1 files are `Prop`-valued definitions in §9.
  A wave-1 file proves one of them, and may take others as hypotheses; it does not import another
  wave-1 file.
-/

namespace BstLean.Part56

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono phiM contr trL frob Tens TSymm fval In41 Pn NN baseline varU)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part50 (binghamA binghamKA)
open BstLean.Part53 (TF fvA heatA sg linZ inp53)

variable {n d : ℕ}

/-! ## §1 The law and the surrogate -/

/-- `v` is a unit vector. -/
def UnitV (v : Fin n → ℝ) : Prop := ∑ i, v i ^ 2 = 1

/-- `t · v vᵀ`. -/
def rk1 (t : ℝ) (v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i j => t * v i * v j

/-- The rank-one Bingham law `D_{t,v} ∝ exp(t (v·x)²) σ`. -/
noncomputable def lawRK (n : ℕ) (t : ℝ) (v : Fin n → ℝ) : Measure (Fin n → ℝ) := binghamA n (rk1 t v)

/-- The truncation order `K = Kof43 (C n) e` (Part 43's order at the range bound `C n`); the surrogate
then has accuracy `etaQ e` uniformly in `t ∈ [0, C n]` (Part 50's `surrA_bias`). -/
noncomputable def KRK (C : ℝ) (n : ℕ) (e : ℝ) : ℕ := BstLean.Part43.Kof43 (C * n) e

/-- The surrogate `Q̃ ∝ p_K(t (v·x)²) σ`. -/
noncomputable def surrRK (n K : ℕ) (t : ℝ) (v : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  binghamKA n K (rk1 t v)

/-! ## §2 Blocks, kernels, correlations -/

/-- The degree-`j` block `φ_j(x)` of the monomial vector. -/
noncomputable def phiB (d j : ℕ) (x : Fin n → ℝ) : Mono n d → ℝ := fun p =>
  if (p.1 : ℕ) = j then phiM x p else 0

/-- `k_j(x, y) = ⟨φ_j(x), φ_j(y)⟩`. -/
noncomputable def kJ (d j : ℕ) (x y : Fin n → ℝ) : ℝ := ∑ p : Mono n d, phiB d j x p * phiB d j y p

/-- `β_j(x) = k_j(x, v)/k_j(v, v)`. -/
noncomputable def betaJ (d j : ℕ) (v x : Fin n → ℝ) : ℝ := kJ d j x v / kJ d j v v

/-- The residual kernel `K_R(x, y) = Σ_{j=1}^d (k_j(x,y) − k_j(x,v) k_j(y,v)/k_j(v,v))`. -/
noncomputable def KR (d : ℕ) (v x y : Fin n → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 d, (kJ d j x y - kJ d j x v * kJ d j y v / kJ d j v v)

/-- `τ(x) = K_R(x, x)`. -/
noncomputable def tauR (d : ℕ) (v x : Fin n → ℝ) : ℝ := KR d v x x

/-- `ρ_R(x, y) = K_R(x,y)/√(τ(x) τ(y))` (`0` when a factor vanishes). -/
noncomputable def rhoR (d : ℕ) (v x y : Fin n → ℝ) : ℝ :=
  KR d v x y / Real.sqrt (tauR d v x * tauR d v y)

/-- `δ² = E_{x,y ∼ μ⊗μ} ρ_R(x, y)²`. -/
noncomputable def deltaSq (μ : Measure (Fin n → ℝ)) (d : ℕ) (v : Fin n → ℝ) : ℝ :=
  ∫ x, ∫ y, rhoR d v x y ^ 2 ∂μ ∂μ

/-! ## §3 Anchors and the conditional mean -/

/-- The anchor `u_j = M φ_j(v) ∈ ℝⁿ`. -/
noncomputable def ancRK (M : CoefIdxD n d → ℝ) (v : Fin n → ℝ) (j : ℕ) : Fin n → ℝ :=
  linZ M (phiB d j v)

/-- The conditional mean `μ_x = Σ_{j ≤ d} β_j(x) u_j`. -/
noncomputable def mux (M : CoefIdxD n d → ℝ) (v x : Fin n → ℝ) : Fin n → ℝ :=
  ∑ j ∈ Finset.range (d + 1), betaJ d j v x • ancRK M v j

/-! ## §4 The program value -/

/-- Heat form: `g_μ(M) = E_{x∼μ} (P_{σ² τ(x)} f)(μ_x)`. -/
noncomputable def gLineH (μ : Measure (Fin n → ℝ)) (k : ℕ) (f0 : ℝ) (T : Tens n) (v : Fin n → ℝ)
    (M : CoefIdxD n d → ℝ) : ℝ :=
  ∫ x, fvA k (heatA k (sg n d ^ 2 * tauR d v x) (TF k f0 T)) (mux M v x) ∂μ

/-- The keys `(i, l, j⃗)`, `i, l ≤ k`, `j⃗ ∈ {0..d}^{i−2l}`. -/
abbrev KeyRK (k d : ℕ) := Σ il : Fin (k + 1) × Fin (k + 1), Fin ((il.1 : ℕ) - 2 * (il.2 : ℕ)) → Fin (d + 1)

/-- `i!/(2^l l! (i−2l)!) = C(i, 2l)(2l−1)!!`. -/
noncomputable def wickC (i l : ℕ) : ℝ :=
  (i.factorial : ℝ) / (2 ^ l * (l.factorial : ℝ) * ((i - 2 * l).factorial : ℝ))

/-- The weight of a key under `μ`: `wickC i l · σ^{2l} · E_μ[τ^l Π_r β_{j_r}]`. -/
noncomputable def wRK (μ : Measure (Fin n → ℝ)) (d : ℕ) (v : Fin n → ℝ) {k : ℕ} (κ : KeyRK k d) : ℝ :=
  wickC κ.1.1 κ.1.2 * (sg n d ^ 2) ^ (κ.1.2 : ℕ) *
    ∫ x, tauR d v x ^ (κ.1.2 : ℕ) * ∏ r, betaJ d (κ.2 r) v x ∂μ

/-- The weighted sum `Σ_{2l ≤ i} c(i,l,j⃗) (tr^l A_i)[u_{j_1}, …, u_{j_{i−2l}}]`. -/
noncomputable def gW (k : ℕ) (A : Tens n) (c : KeyRK k d → ℝ) (u : ℕ → Fin n → ℝ) : ℝ :=
  ∑ κ : KeyRK k d, if 2 * (κ.1.2 : ℕ) ≤ (κ.1.1 : ℕ) then
    c κ * contr (trL (κ.1.2 : ℕ) (A κ.1.1)) (fun r => u (κ.2 r)) else 0

/-- Weight form: `g_μ(M) = gW k (TF k f0 T) (wRK μ d v) (u_0, …, u_d)`. -/
noncomputable def gLineW (μ : Measure (Fin n → ℝ)) (k : ℕ) (f0 : ℝ) (T : Tens n) (v : Fin n → ℝ)
    (M : CoefIdxD n d → ℝ) : ℝ :=
  gW k (TF k f0 T) (wRK μ d v) (fun j => ancRK M v j)

/-! ## §5 Conditional variance, the quantity `S`, the proxy normalizer -/

/-- `Var_{g ∼ N(0, I)} f(y + a g)`. -/
noncomputable def cvarG (k : ℕ) (f0 : ℝ) (T : Tens n) (a : ℝ) (y : Fin n → ℝ) : ℝ :=
  ∫ g, fval k f0 T (y + a • g) ^ 2 ∂stdGauss (Fin n) -
    (∫ g, fval k f0 T (y + a • g) ∂stdGauss (Fin n)) ^ 2

/-- `S_μ(M) = E_{x∼μ} Var(f(m(x)) | anchors)`, evaluated at `M` with residual scale `σ√τ(x)`. -/
noncomputable def Sfl (μ : Measure (Fin n → ℝ)) (d k : ℕ) (f0 : ℝ) (T : Tens n) (v : Fin n → ℝ)
    (M : CoefIdxD n d → ℝ) : ℝ :=
  ∫ x, cvarG k f0 T (sg n d * Real.sqrt (tauR d v x)) (mux M v x) ∂μ

/-- `E_Z Var_μ f(σ Z φ(x))`. -/
noncomputable def EV56 (d : ℕ) (μ : Measure (Fin n → ℝ)) (k : ℕ) (f0 : ℝ) (T : Tens n) : ℝ :=
  ∫ Z, varFQ μ k f0 T (sg n d • Z) ∂stdGauss (CoefIdxD n d)

/-! ## §6 Key Lemma objects -/

/-- The unit vector `w = P g/‖P g‖`, `P = I − v vᵀ` (uniform on the sphere of `v^⊥` for `g` Gaussian). -/
noncomputable def perpDir (v g : Fin n → ℝ) : Fin n → ℝ :=
  (1 / Real.sqrt (∑ i, (g i - (∑ l, v l * g l) * v i) ^ 2)) • fun i => g i - (∑ l, v l * g l) * v i

/-- `Φ_{j,i}(a, w)`: the part of `φ_j(a + w)` homogeneous of degree `i` in `w`. -/
noncomputable def PhiJI (d j i : ℕ) (a w : Fin n → ℝ) : Mono n d → ℝ := fun p =>
  if (p.1 : ℕ) = j then
    (((p.2 : Multiset (Fin n)).map fun l => Polynomial.C (a l) + Polynomial.X * Polynomial.C (w l)).prod).coeff i
  else 0

/-! ## §7 Programs -/

/-- The line program's inputs: `M`, `f₀`, `T`, then `v`, then the weights. -/
abbrev In56 (n d k : ℕ) := In41 n d k ⊕ (Fin n ⊕ KeyRK k d)

/-- The line program's input vector. -/
def inp56 {k : ℕ} (f0 : ℝ) (T : Tens n) (M : CoefIdxD n d → ℝ) (v : Fin n → ℝ) (c : KeyRK k d → ℝ) :
    In56 n d k → ℝ :=
  Sum.elim (inp53 (k := k) f0 T M) (Sum.elim v c)

/-- The moment program's inputs: `t`, then `v`. -/
abbrev InM56 (n : ℕ) := Unit ⊕ Fin n

/-- The moment program's input vector. -/
def inRK (t : ℝ) (v : Fin n → ℝ) : InM56 n → ℝ := Sum.elim (fun _ => t) v

/-- The line program computes the weighted sum from `M`, `f`, `v` and arbitrary weights `c`. -/
def GSpec56 {k : ℕ} (pg : Prog (In56 n d k) Unit) : Prop :=
  ∀ (f0 : ℝ) (T : Tens n) (M : CoefIdxD n d → ℝ) (v : Fin n → ℝ) (c : KeyRK k d → ℝ), TSymm k T →
    pg.eval (inp56 f0 T M v c) () = gW k (TF k f0 T) c (fun j => ancRK M v j)

/-- The moment program returns the surrogate weights at every `t ≥ 0` and every unit `v`. -/
def MomSpec56 {k : ℕ} (pm : Prog (InM56 n) (KeyRK k d)) (K : ℕ) : Prop :=
  ∀ (t : ℝ) (v : Fin n → ℝ), 0 ≤ t → UnitV v → ∀ κ : KeyRK k d,
    pm.eval (inRK t v) κ = wRK (surrRK n K t v) d v κ

/-! ## §8 Cost and parameters -/

/-- The proved-cost bound of the line program: `(d+1)N` for `φ(v)` (at most `d` products per monomial),
`2P` for the anchors, and
`4(k+2)³(d+1)^k(n+1)^k` for the traces, the multilinear values and the weighted sum. -/
noncomputable def costLine56 (n d k : ℕ) : ℝ :=
  2 * Pn n d + ((d : ℝ) + 1) * NN n d + 4 * ((k : ℝ) + 2) ^ 3 * ((d : ℝ) + 1) ^ k * ((n : ℝ) + 1) ^ k

/-- The proved-cost bound of the moment program (polynomial in `n`, linear-squared in `K`). -/
noncomputable def onceCost56 (n d k K : ℕ) : ℝ :=
  ((K : ℝ) + 2) ^ 2 * ((n : ℝ) + 2) ^ (8 * d * k + 8) * ((8 * d * k + 8).factorial : ℝ)

/-- The share `ν = (1 − 200 ε_hi²/91)/2` of the baseline reserved for the moment program. -/
noncomputable def nuRK (εhi : ℝ) : ℝ := (1 - 200 * εhi ^ 2 / 91) / 2

/-- The amortization threshold `k₀ = ⌈cost(pm) / (ν 𝔅(ε))⌉`. -/
noncomputable def k0RK (n d : ℕ) (c : ℕ) (ε εhi : ℝ) : ℕ :=
  ⌈(c : ℝ) / (nuRK εhi * baseline n d ε)⌉₊

/-- The surrogate accuracy `η = ε_lo √s / (100 (k+1))`, so that `5(k+1)² η²/(ε² s) ≤ 1/2000`. -/
noncomputable def etaRK (k : ℕ) (s εlo : ℝ) : ℝ := εlo * Real.sqrt s / (100 * ((k : ℝ) + 1))

/-- The Part 43 accuracy parameter `e = etaRK/ξ`, so that `etaQ e ≤ etaRK k s ε_lo`. -/
noncomputable def eRK (k : ℕ) (s εlo : ℝ) : ℝ := etaRK k s εlo / BstLean.Part43.xi43

/-! ## §9 The interface statements -/

/-- **Lemma MC** (maximal correlation of Gaussian pairs, Gebelein–Witsenhausen): for `|ρ| ≤ 1`,
`X = g`, `Y = ρ g + √(1−ρ²) h` with `g, h` independent standard Gaussian in `ℝⁿ`, and square-integrable
`Φ, Ψ`: `|Cov(Φ(X), Ψ(Y))| ≤ |ρ| sd Φ sd Ψ`. -/
def LemmaMC56 : Prop :=
  ∀ (n : ℕ) (ρ : ℝ), |ρ| ≤ 1 → ∀ Φ Ψ : (Fin n → ℝ) → ℝ,
    MemLp Φ 2 (stdGauss (Fin n)) → MemLp Ψ 2 (stdGauss (Fin n)) →
    |(∫ g, ∫ h, Φ g * Ψ (ρ • g + Real.sqrt (1 - ρ ^ 2) • h) ∂stdGauss (Fin n) ∂stdGauss (Fin n)) -
        (∫ g, Φ g ∂stdGauss (Fin n)) * (∫ g, Ψ g ∂stdGauss (Fin n))| ≤
      |ρ| * Real.sqrt (varU (stdGauss (Fin n)) Φ) * Real.sqrt (varU (stdGauss (Fin n)) Ψ)

/-- **Weights** (Wick expansion, algebra): the weight form equals the heat form. -/
def PropWeights56 (d k : ℕ) : Prop :=
  ∀ (n : ℕ) (μ : Measure (Fin n → ℝ)), SphLaw n μ → ∀ v : Fin n → ℝ, UnitV v →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T → ∀ M : CoefIdxD n d → ℝ,
      gLineW μ k f0 T v M = gLineH μ k f0 T v M

/-- The projection `Π = Σ_j φ_j(v) φ_j(v)ᵀ / k_j(v,v)` on the monomial index, applied to each output
column of `Z`: `(Π Z)_{q,a} = Σ_p Π_{q,p} Z_{p,a}`. The anchors of `Z` are those of `Π Z`. -/
noncomputable def projA (v : Fin n → ℝ) (Z : CoefIdxD n d → ℝ) : CoefIdxD n d → ℝ := fun α =>
  ∑ j ∈ Finset.range (d + 1), phiB d j v ⟨α.1, α.2.1⟩ / kJ d j v v *
    ∑ p : Mono n d, phiB d j v p * Z ⟨p.1, (p.2, α.2.2)⟩

/-- **Gaussian split**: for unit `v`, `Z ↦ Π Z` and `Z ↦ Z − Π Z` are independent under the standard
Gaussian, and `Π Z + (Z' − Π Z')` (with `Z'` an independent copy) has the law of `Z`. -/
def PropSplit56 (d : ℕ) : Prop :=
  ∀ (n : ℕ) (v : Fin n → ℝ), UnitV v → ∀ F : (CoefIdxD n d → ℝ) → ℝ≥0∞, Measurable F →
    ∫⁻ Z, F Z ∂stdGauss (CoefIdxD n d) =
      ∫⁻ Z, ∫⁻ Z', F (projA v Z + (Z' - projA v Z')) ∂stdGauss (CoefIdxD n d)
        ∂stdGauss (CoefIdxD n d)

/-- **Orthogonality** (the heat form is `E[B | anchors]` in the proxy `M = σZ`): `B` and `g` are
square-integrable, `Var_μ` is integrable, and `B − g` is orthogonal to every measurable function of the
anchors that is square-integrable. -/
def PropOrth56 (d k : ℕ) : Prop :=
  ∀ (n : ℕ) (μ : Measure (Fin n → ℝ)), SphLaw n μ → ∀ v : Fin n → ℝ, UnitV v →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T →
      MemLp (fun Z : CoefIdxD n d → ℝ => BofQ μ k f0 T (sg n d • Z)) 2 (stdGauss (CoefIdxD n d)) ∧
      MemLp (fun Z : CoefIdxD n d → ℝ => gLineH μ k f0 T v (sg n d • Z)) 2 (stdGauss (CoefIdxD n d)) ∧
      Integrable (fun Z : CoefIdxD n d → ℝ => varFQ μ k f0 T (sg n d • Z)) (stdGauss (CoefIdxD n d)) ∧
      ∀ h : (Fin (d + 1) → Fin n → ℝ) → ℝ, Measurable h →
        MemLp (fun Z : CoefIdxD n d → ℝ => h (fun j => ancRK (sg n d • Z) v j)) 2
          (stdGauss (CoefIdxD n d)) →
        ∫ Z, (BofQ μ k f0 T (sg n d • Z) - gLineH μ k f0 T v (sg n d • Z)) *
          h (fun j => ancRK (sg n d • Z) v j) ∂stdGauss (CoefIdxD n d) = 0

/-- **Theorem RK-G, error part**: `E_Z (B − g)(σZ)² ≤ δ · E_Z S(σZ)`, with the integrand integrable. -/
def PropRKGErr56 (d k : ℕ) : Prop :=
  ∀ (n : ℕ) (μ : Measure (Fin n → ℝ)), SphLaw n μ → ∀ v : Fin n → ℝ, UnitV v →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T →
      Integrable (fun Z : CoefIdxD n d → ℝ =>
          (BofQ μ k f0 T (sg n d • Z) - gLineH μ k f0 T v (sg n d • Z)) ^ 2) (stdGauss (CoefIdxD n d)) ∧
      ∫ Z, (BofQ μ k f0 T (sg n d • Z) - gLineH μ k f0 T v (sg n d • Z)) ^ 2 ∂stdGauss (CoefIdxD n d) ≤
        Real.sqrt (deltaSq μ d v) * ∫ Z, Sfl μ d k f0 T v (sg n d • Z) ∂stdGauss (CoefIdxD n d)

/-- **Theorem RK-G, floor part**: `(1 − δ) E_Z S(σZ) ≤ E_Z Var_μ f(σZφ)`. -/
def PropRKGFloor56 (d k : ℕ) : Prop :=
  ∀ (n : ℕ) (μ : Measure (Fin n → ℝ)), SphLaw n μ → ∀ v : Fin n → ℝ, UnitV v →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T →
      (1 - Real.sqrt (deltaSq μ d v)) * ∫ Z, Sfl μ d k f0 T v (sg n d • Z) ∂stdGauss (CoefIdxD n d) ≤
        EV56 d μ k f0 T

/-- **Key Lemma** at rank one: for `|s|, |s'| ≤ 1`, `w, w'` independent uniform on the sphere of `v^⊥`,
and `1 ≤ i, i' ≤ j ≤ d`: `E ⟨Φ_{j,i}(s v, w), Φ_{j,i'}(s' v, w')⟩² ≤ C_K/(n − 1)`. -/
def KeyLemma56 (d : ℕ) (CK : ℝ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ v : Fin n → ℝ, UnitV v → ∀ s s' : ℝ, |s| ≤ 1 → |s'| ≤ 1 →
    ∀ j i i' : ℕ, j ≤ d → 1 ≤ i → i ≤ j → 1 ≤ i' → i' ≤ j →
      ∫ g, ∫ g', (∑ p : Mono n d, PhiJI d j i (s • v) (perpDir v g) p *
          PhiJI d j i' (s' • v) (perpDir v g') p) ^ 2 ∂stdGauss (Fin n) ∂stdGauss (Fin n) ≤
        CK / ((n : ℝ) - 1)

/-- **Prop D**: `δ² ≤ C_D/(n − 1)` for every rank-one Bingham law, every unit `v`, every real `t`. -/
def PropD56 (d : ℕ) (CD : ℝ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, deltaSq (lawRK n t v) d v ≤ CD / ((n : ℝ) - 1)

/-- **Surrogate**: for `t ∈ [0, C n]`, `E_Z (g_{Q̃} − g_D)(σZ)² ≤ etaQ(e)² E_Z Var_D f(σZφ)`,
`Q̃ = surrRK n (KRK C n e) t v`. -/
def PropSurr56 (d k : ℕ) (C η : ℝ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ C * n →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T →
      Integrable (fun Z : CoefIdxD n d → ℝ =>
          (gLineH (surrRK n (KRK C n η) t v) k f0 T v (sg n d • Z) -
            gLineH (lawRK n t v) k f0 T v (sg n d • Z)) ^ 2) (stdGauss (CoefIdxD n d)) ∧
      ∫ Z, (gLineH (surrRK n (KRK C n η) t v) k f0 T v (sg n d • Z) -
          gLineH (lawRK n t v) k f0 T v (sg n d • Z)) ^ 2 ∂stdGauss (CoefIdxD n d) ≤
        BstLean.Part43.etaQ η ^ 2 * EV56 d (lawRK n t v) k f0 T

/-- **Prop T1′** (error on the coefficient sphere, with Markov), for the weight form of the surrogate
program: `Pr_M{c · EV < (B_D − g_{Q̃})(M)²} ≤ (C_err/√n + 5(k+1)² etaQ(e)²)/c`, `Q̃` at `K = KRK C n e`. -/
def PropT1_56 (d k : ℕ) (C η Cerr : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ C * n →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) → ∀ c : ℝ, 0 < c →
      stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
        c * EV56 d (lawRK n t v) k f0 T <
          (BofQ (lawRK n t v) k f0 T (unitOfD Z) -
            gLineW (surrRK n (KRK C n η) t v) k f0 T v (unitOfD Z)) ^ 2} ≤
        ENNReal.ofReal ((Cerr / Real.sqrt n + 5 * ((k : ℝ) + 1) ^ 2 * BstLean.Part43.etaQ η ^ 2) / c)

/-- **Lower bound on `S`** (the Hermite identity, the inverse heat operator and Lemma Tr, plus the
lower tail `E_D (1 − (v·x)²)^k ≥ θ^k/2` for `t ≤ C n`):
`E_Z S(σZ) ≥ c_L n^{−⌊(k−1)/2⌋} Σ_{j=1}^k ‖T_j‖²/𝒟^j`. -/
def PropLow56 (d k : ℕ) (C cL : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ C * n →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T →
      cL * (∑ j ∈ Finset.Icc 1 k, frob (T j) / DD n d ^ j) / (n : ℝ) ^ ((k - 1) / 2) ≤
        ∫ Z, Sfl (lawRK n t v) d k f0 T v (sg n d • Z) ∂stdGauss (CoefIdxD n d)

/-- **Prop T2′** (floor on the coefficient sphere): `Pr_M{Var_D f(Mφ) < s · EV} ≤ p + C₂/n`. -/
def PropT2_56 (d k : ℕ) (C p s C2 : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ C * n →
    ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
      stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
        varFQ (lawRK n t v) k f0 T (unitOfD Z) < s * EV56 d (lawRK n t v) k f0 T} ≤
        ENNReal.ofReal (p + C2 / n)

end BstLean.Part56
