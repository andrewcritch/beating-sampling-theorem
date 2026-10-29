import BstLean.Part60Defs

/-!
# Part 61, wave 0: frozen definitions — Theorem JW, the two-point integrated-variance rule
(`J′ = 2`) for concentrated rank-one Bingham laws when `d_f > d_M`, under the charged baseline

Source: `delegations/answers/omJW-opus-prover.md` §2, §4, §5 (Lemma QT, the rule `g_K`, Lemmas A, C,
W, S, Prop K, Cor W, Lemma Sur, Theorem JW), with the repair of `chJW-opus.md` §4: the node `ŝ′` is
any real number (here a Newton iterate of the surrogate moment `E_Q̃ s²`), used consistently in the
node points, in `K̂` and in the heat moments `m_l`. No square root occurs in a program.
Specification: `delegations/answers/p61-spec-opus.md`.
This file holds definitions only. Provers must not edit it, and must not use `native_decide` or
`axiom` anywhere.

Conventions. Part 36, 41, 43, 53, 56, 59 and 60 names are reused. `k = d_f`, `d = d_M`,
`L = ⌊k/2⌋`. `f` is a coefficient vector `c : Mono n k → ℝ` (Part 59); its tensor form is
`(c default, tensOf k c)`.

* **Heat polynomial in `τ`.** `qHP e y s2 ∈ ℝ[τ]` is Part 59's `qH e y a` at the symbolic variance
  `a = s2·τ`. `hpol61 k c s2 y = Σ_α c_α Π_i qHP(α_i, y_i, s2)`; its value at `τ` is
  `hev60 k c (s2 τ) y = (P_{s2 τ} f)(y)` and its degree is `≤ L` (`LemmaQT61`).
* **The rule.** `yK61 M v z = Σ_{j≤d} z^j u_j = m(z v)`; `Khat61 d v r = Σ_j r^{2j} k_j(v,v)`;
  `momK61 μ d v r l = E_μ (κ_x − K̂)^l`. Coefficient form
  `gKQ61 m r c M v = ½ Σ_{z = ±r} Σ_{l ≤ L} m_l [τ^l] hpol61 k c σ² (yK61 M v z)`.
  Tensor form `gKH61 μ k f0 T v r M = ½ Σ_{z=±r} E_{x∼μ} (P_{σ²(κ_x − K̂)} f)(yK61 M v z)`.
  Cluster form `gKC61` (each `x` uses the node of its own sign `q(x)`).
* **Displacement.** `omega61 μ d v r = E_μ Σ_{j≤d} (β_j(x) − (q(x) r)^j)² k_j(v,v)` (`= E|a_x − ā_{q(x)}|²`).
* **Node.** `newt61 N a` is `N` Newton steps `z ↦ (z + a/z)/2` from `z = 1`; the node is
  `rK61 N μ v = newt61 N (E_μ s²)`, `s = v·x`, with `N = newtN61 n = ⌊log₂ n⌋ + 1`.
* **Programs.** The moment program reads `(t, v)` (Part 56's `InM56`) and returns `OutK61 k`:
  the node `r` and the heat moments `m_l`, `l ≤ L`, under the surrogate. The line program reads
  `InK61 n d k = M ⊕ (c ⊕ (v ⊕ OutK61 k))`.
* **Costs.** `costLine61` (the line program's cost bound), Part 59's `baselineF` (R1), Part 60's
  `baselineF2` (R2), the amortization shares `nuK61`, `nuK61R2` and the counters `k0K61`, `k0K61R2`.
* **Statements.** §8–§9 hold the interfaces between the wave-1 files as `Prop`-valued definitions.
-/

namespace BstLean.Part61

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono phiM frob IsSymmT Tens TSymm fval Pn NN varU)
open BstLean.Part43 (BofQ varFQ etaQ)
open BstLean.Part53 (TF fvA heatA sg)
open BstLean.Part56 (UnitV lawRK surrRK kJ betaJ tauR ancRK gLineH InM56 inRK KRK EV56)
open BstLean.Part59 (qH costF Pp baselineF)
open BstLean.Part60 (hev60 kap60 FlA baselineF2)

variable {n d : ℕ}

/-! ## §1 The heat polynomial in the variable `τ` (Lemma QT) -/

/-- `q_e(y; s2·τ) ∈ ℝ[τ]`: Part 59's `qH e y a` at the symbolic variance `a = s2·τ`. -/
noncomputable def qHP : ℕ → ℝ → ℝ → Polynomial ℝ
  | 0, _, _ => 1
  | 1, y, _ => Polynomial.C y
  | e + 2, y, s2 => Polynomial.C y * qHP (e + 1) y s2 +
      Polynomial.C (((e : ℝ) + 1) * s2) * Polynomial.X * qHP e y s2

/-- `T(τ) = (P_{s2 τ} f)(y) = Σ_α c_α Π_i q_{α_i}(y_i; s2 τ)` as an element of `ℝ[τ]`. -/
noncomputable def hpol61 (k : ℕ) (c : Mono n k → ℝ) (s2 : ℝ) (y : Fin n → ℝ) : Polynomial ℝ :=
  ∑ α : Mono n k, Polynomial.C (c α) * ∏ i : Fin n, qHP (α.2.1.count i) (y i) s2

/-! ## §2 The two-point rule -/

/-- `s = v·x`. -/
def sx61 (v x : Fin n → ℝ) : ℝ := ∑ i, v i * x i

/-- The node point `m(z v) = Σ_{j ≤ d} z^j u_j` (anchors `u_j = ancRK M v j`). -/
noncomputable def yK61 (M : CoefIdxD n d → ℝ) (v : Fin n → ℝ) (z : ℝ) : Fin n → ℝ :=
  ∑ j ∈ Finset.range (d + 1), z ^ j • ancRK M v j

/-- `K̂ = K(r v, r v) = Σ_{j ≤ d} r^{2j} k_j(v, v)`. -/
noncomputable def Khat61 (d : ℕ) (v : Fin n → ℝ) (r : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (d + 1), r ^ (2 * j) * kJ d j v v

/-- The heat moments `m_l = E_μ (κ_x − K̂)^l`. -/
noncomputable def momK61 (μ : Measure (Fin n → ℝ)) (d : ℕ) (v : Fin n → ℝ) (r : ℝ) (l : ℕ) : ℝ :=
  ∫ x, (kap60 d x - Khat61 d v r) ^ l ∂μ

/-- **The program value, coefficient form**:
`g_K = ½ Σ_{z = ±r} Σ_{l ≤ ⌊k/2⌋} m_l [τ^l] (P_{σ²τ} f)(m(z v))`, `σ² = 1/𝒟`. -/
noncomputable def gKQ61 {k : ℕ} (m : Fin (k / 2 + 1) → ℝ) (r : ℝ) (c : Mono n k → ℝ)
    (M : CoefIdxD n d → ℝ) (v : Fin n → ℝ) : ℝ :=
  (1 / 2) * (∑ l : Fin (k / 2 + 1), m l * (hpol61 k c (1 / DD n d) (yK61 M v r)).coeff l +
    ∑ l : Fin (k / 2 + 1), m l * (hpol61 k c (1 / DD n d) (yK61 M v (-r))).coeff l)

/-- **The program value, tensor form**: `½ Σ_{z=±r} E_{x∼μ} (P_{σ²(κ_x − K̂)} f)(m(z v))`. -/
noncomputable def gKH61 (μ : Measure (Fin n → ℝ)) (k : ℕ) (f0 : ℝ) (T : Tens n) (v : Fin n → ℝ)
    (r : ℝ) (M : CoefIdxD n d → ℝ) : ℝ :=
  (1 / 2) * ((∫ x, fvA k (heatA k (sg n d ^ 2 * (kap60 d x - Khat61 d v r)) (TF k f0 T))
      (yK61 M v r) ∂μ) +
    ∫ x, fvA k (heatA k (sg n d ^ 2 * (kap60 d x - Khat61 d v r)) (TF k f0 T)) (yK61 M v (-r)) ∂μ)

/-- The cluster sign `q(x) = +1` if `v·x ≥ 0`, else `−1`. -/
noncomputable def sgn61 (v x : Fin n → ℝ) : ℝ := if 0 ≤ sx61 v x then 1 else -1

/-- **Cluster form** (Lemma A): `E_{x∼μ} (P_{σ²(κ_x − K̂)} f)(m(q(x) r v))`. -/
noncomputable def gKC61 (μ : Measure (Fin n → ℝ)) (k : ℕ) (f0 : ℝ) (T : Tens n) (v : Fin n → ℝ)
    (r : ℝ) (M : CoefIdxD n d → ℝ) : ℝ :=
  ∫ x, fvA k (heatA k (sg n d ^ 2 * (kap60 d x - Khat61 d v r)) (TF k f0 T))
    (yK61 M v (sgn61 v x * r)) ∂μ

/-- **The displacement** `ω² = E_μ |a_x − ā_{q(x)}|² = E_μ Σ_{j≤d} (β_j(x) − (q(x) r)^j)² k_j(v,v)`. -/
noncomputable def omega61 (μ : Measure (Fin n → ℝ)) (d : ℕ) (v : Fin n → ℝ) (r : ℝ) : ℝ :=
  ∫ x, ∑ j ∈ Finset.range (d + 1), (betaJ d j v x - (sgn61 v x * r) ^ j) ^ 2 * kJ d j v v ∂μ

/-! ## §3 The node -/

/-- `N` Newton steps for `√a` from `z₀ = 1`: `z ↦ (z + a/z)/2`. -/
noncomputable def newt61 : ℕ → ℝ → ℝ
  | 0, _ => 1
  | N + 1, a => (newt61 N a + a / newt61 N a) / 2

/-- `E_μ s²`, `s = v·x`. -/
noncomputable def s2mom61 (μ : Measure (Fin n → ℝ)) (v : Fin n → ℝ) : ℝ := ∫ x, sx61 v x ^ 2 ∂μ

/-- The number of Newton steps, `⌊log₂ n⌋ + 1` (so `2^{−N} ≤ 1/n`). -/
def newtN61 (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- The node `ŝ′ = newt61 N (E_μ s²)`. -/
noncomputable def rK61 (N : ℕ) (μ : Measure (Fin n → ℝ)) (v : Fin n → ℝ) : ℝ :=
  newt61 N (s2mom61 μ v)

/-! ## §4 Programs -/

/-- The moment program's outputs: the node `r` (left) and the heat moments `m_l`, `l ≤ ⌊k/2⌋`. -/
abbrev OutK61 (k : ℕ) := Unit ⊕ Fin (k / 2 + 1)

/-- The line program's inputs: `M`, the coefficients `c` of `f`, `v`, the moment program's outputs. -/
abbrev InK61 (n d k : ℕ) := CoefIdxD n d ⊕ (Mono n k ⊕ (Fin n ⊕ OutK61 k))

/-- The line program's input vector. -/
def inpK61 {k : ℕ} (c : Mono n k → ℝ) (M : CoefIdxD n d → ℝ) (v : Fin n → ℝ)
    (o : OutK61 k → ℝ) : InK61 n d k → ℝ :=
  Sum.elim M (Sum.elim c (Sum.elim v o))

/-- The program value read from the moment program's output vector `o`. -/
noncomputable def gKQo61 {k : ℕ} (o : OutK61 k → ℝ) (c : Mono n k → ℝ) (M : CoefIdxD n d → ℝ)
    (v : Fin n → ℝ) : ℝ :=
  gKQ61 (fun l => o (Sum.inr l)) (o (Sum.inl ())) c M v

/-- The line program computes `g_K` from `M`, `c`, `v` and an arbitrary output vector `o`. -/
def GSpec61 {k : ℕ} (pg : Prog (InK61 n d k) Unit) : Prop :=
  ∀ (c : Mono n k → ℝ) (M : CoefIdxD n d → ℝ) (v : Fin n → ℝ) (o : OutK61 k → ℝ),
    pg.eval (inpK61 c M v o) () = gKQo61 o c M v

/-- The moment program returns, under the surrogate `Q̃ = surrRK n K t v`, the node
`r = rK61 (newtN61 n) Q̃ v` and the heat moments `m_l = momK61 Q̃ d v r l`, at every `t ≥ 0`, unit `v`. -/
def MomSpec61 {k : ℕ} (pm : Prog (InM56 n) (OutK61 k)) (d K : ℕ) : Prop :=
  ∀ (t : ℝ) (v : Fin n → ℝ), 0 ≤ t → UnitV v →
    pm.eval (inRK t v) (Sum.inl ()) = rK61 (newtN61 n) (surrRK n K t v) v ∧
    ∀ l : Fin (k / 2 + 1), pm.eval (inRK t v) (Sum.inr l) =
      momK61 (surrRK n K t v) d v (rK61 (newtN61 n) (surrRK n K t v) v) (l : ℕ)

/-! ## §5 Costs and amortization -/

/-- The cost bound of the line program: `2P` (anchors), `(d+1)N` (`φ(v)`), two runs of Lemma QT's
tree over `ℝ[τ]/(τ^{L+1})`, each `C_f + 16(k+1)² C(n+k−2, k−1) + 4n(k+d+2)(k+1)` (the plain Horner
edges, the expensive edges, the table, the node point and the final sum), and
`4⌊log₂ n⌋ + 32(k+d+2)²` for the constants. -/
noncomputable def costLine61 (n d k : ℕ) : ℝ :=
  2 * Pn n d + ((d : ℝ) + 1) * NN n d +
    2 * (costF n k + 16 * ((k : ℝ) + 1) ^ 2 * ((n + k - 2).choose (k - 1) : ℝ) +
      4 * (n : ℝ) * ((k : ℝ) + d + 2) * ((k : ℝ) + 1)) +
    (4 * (Nat.log 2 n : ℝ) + 32 * ((k : ℝ) + d + 2) ^ 2)

/-- `a₁ = ε_hi²/0.455` (R1): the line program costs about `2P′ ≤ a₁ 𝔅₁(ε)`. -/
noncomputable def aK61 (εhi : ℝ) : ℝ := εhi ^ 2 * 200 / 91

/-- `a₂ = ε_hi²/0.2275` (R2): the line program costs about `2P + 2C_f ≤ a₂ 𝔅₂(ε)`. -/
noncomputable def aK61R2 (εhi : ℝ) : ℝ := εhi ^ 2 * 400 / 91

/-- The share `ν = (1 − a)/4` of the baseline reserved for the moment program (R1). -/
noncomputable def nuK61 (εhi : ℝ) : ℝ := (1 - aK61 εhi) / 4

/-- The share `ν = (1 − a)/4` of the baseline reserved for the moment program (R2). -/
noncomputable def nuK61R2 (εhi : ℝ) : ℝ := (1 - aK61R2 εhi) / 4

/-- The R1 amortization threshold `k₀ = ⌈cost(pm)/(ν 𝔅₁(ε))⌉`. -/
noncomputable def k0K61 (n d k : ℕ) (cm : ℕ) (ε εhi : ℝ) : ℕ :=
  ⌈(cm : ℝ) / (nuK61 εhi * baselineF n d k ε)⌉₊

/-- The R2 amortization threshold `k₀ = ⌈cost(pm)/(ν 𝔅₂(ε))⌉`. -/
noncomputable def k0K61R2 (n d k : ℕ) (cm : ℕ) (ε εhi : ℝ) : ℕ :=
  ⌈(cm : ℝ) / (nuK61R2 εhi * baselineF2 n d k ε)⌉₊

/-! ## §8 Algebraic and program interfaces -/

/-- **Lemma QT, value and degree**: `hpol61 k c s2 y` evaluated at `τ` is `hev60 k c (s2 τ) y`, and
its degree is `≤ ⌊k/2⌋`. Every real `s2`, `τ`. -/
def LemmaQT61 : Prop :=
  ∀ (n k : ℕ) (c : Mono n k → ℝ) (s2 : ℝ) (y : Fin n → ℝ),
    (∀ τ : ℝ, (hpol61 k c s2 y).eval τ = hev60 k c (s2 * τ) y) ∧
    (hpol61 k c s2 y).natDegree ≤ k / 2

/-- **Lemma Q at every real heat parameter** (also `a < 0`): `hev60 k c a y = (P_a f)(y)`, `n ≥ 1`. -/
def LemmaQneg61 : Prop :=
  ∀ (n k : ℕ), 1 ≤ n → ∀ (c : Mono n k → ℝ) (a : ℝ) (y : Fin n → ℝ),
    hev60 k c a y = fvA k (heatA k a (TF k (c default) (BstLean.Part59.tensOf k c))) y

/-- **Evaluation**: with the exact heat moments of a law `μ` on the sphere, the coefficient form
equals the tensor form (Lemma QT integrated against `μ`), for every real node `r`. -/
def EvalK61 (k : ℕ) : Prop :=
  ∀ (n d : ℕ), 1 ≤ n → ∀ (μ : Measure (Fin n → ℝ)), SphLaw n μ → ∀ (v : Fin n → ℝ) (r : ℝ)
    (c : Mono n k → ℝ) (M : CoefIdxD n d → ℝ),
    gKQ61 (fun l : Fin (k / 2 + 1) => momK61 μ d v r l) r c M v =
      gKH61 μ k (c default) (BstLean.Part59.tensOf k c) v r M

/-- **Newton** (`0 ≤ a ≤ 1`): `√a ≤ z_N ≤ 1` and `z_N − √a ≤ 2^{−N}`. -/
def Newton61 : Prop :=
  ∀ (N : ℕ) (a : ℝ), 0 ≤ a → a ≤ 1 →
    Real.sqrt a ≤ newt61 N a ∧ newt61 N a ≤ 1 ∧ newt61 N a - Real.sqrt a ≤ 1 / 2 ^ N

/-- **Line program** (`k ≤ n`, `d ≥ 1`, `k ≥ 2`): computes `g_K` within `costLine61`. -/
def LineProg61 (n d k : ℕ) : Prop :=
  ∃ pg : Prog (InK61 n d k) Unit, BstLean.Part41.heavyCount pg = 0 ∧ GSpec61 pg ∧
    (pg.cost : ℝ) ≤ costLine61 n d k

/-! ## §9 Analytic interfaces -/

/-- **Lemma A** (cluster form): under `D_{t,v}` (even in `x`), `g_K = E_x Φ(ā_{q(x)}, κ_x − K̂)`. -/
def LemmaA61 (d k : ℕ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ (t : ℝ) (v : Fin n → ℝ), UnitV v → ∀ (r f0 : ℝ) (T : Tens n)
    (M : CoefIdxD n d → ℝ),
    gKH61 (lawRK n t v) k f0 T v r M = gKC61 (lawRK n t v) k f0 T v r M

/-- **Prop K** (chaos error of the cluster form; Lemma C, chaos orthogonality, Cauchy–Schwarz), every
law on the sphere, every node `|r| ≤ 1`:
`E_Z (gLineH_μ − gKC_μ)(σZ)² ≤ C_K ω²(μ, r) E_x 𝒩(f; κ_x)`. -/
def PropK61 (d k : ℕ) (CK : ℝ) : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (μ : Measure (Fin n → ℝ)), SphLaw n μ → ∀ v : Fin n → ℝ, UnitV v →
    ∀ r : ℝ, |r| ≤ 1 → ∀ (f0 : ℝ) (T : Tens n), TSymm k T →
      Integrable (fun Z : CoefIdxD n d → ℝ =>
          (gLineH μ k f0 T v (sg n d • Z) - gKC61 μ k f0 T v r (sg n d • Z)) ^ 2)
        (stdGauss (CoefIdxD n d)) ∧
      ∫ Z, (gLineH μ k f0 T v (sg n d • Z) - gKC61 μ k f0 T v r (sg n d • Z)) ^ 2
          ∂stdGauss (CoefIdxD n d) ≤ CK * omega61 μ d v r * FlA μ d k (TF k f0 T)

/-- **Lemma Sur** (surrogate step, same node on both sides), `t ∈ [0, C n]`, `|r| ≤ 1`:
`E_Z (gKH_{Q̃} − gKH_D)(σZ)² ≤ C_H etaQ(e)² (E_Z Var_D f(σZφ) + E_x 𝒩(f; κ_x))`. -/
def LemmaSur61 (d k : ℕ) (C e CH : ℝ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ C * n →
    ∀ r : ℝ, |r| ≤ 1 → ∀ (f0 : ℝ) (T : Tens n), TSymm k T →
      Integrable (fun Z : CoefIdxD n d → ℝ =>
          (gKH61 (surrRK n (KRK C n e) t v) k f0 T v r (sg n d • Z) -
            gKH61 (lawRK n t v) k f0 T v r (sg n d • Z)) ^ 2) (stdGauss (CoefIdxD n d)) ∧
      ∫ Z, (gKH61 (surrRK n (KRK C n e) t v) k f0 T v r (sg n d • Z) -
          gKH61 (lawRK n t v) k f0 T v r (sg n d • Z)) ^ 2 ∂stdGauss (CoefIdxD n d) ≤
        CH * etaQ e ^ 2 * (EV56 d (lawRK n t v) k f0 T + FlA (lawRK n t v) d k (TF k f0 T))

/-- **Lemma W** (every unit `v`, every real `t`):
`E_D Σ_{j≤d} (β_j(x) − s^j)² k_j(v,v) ≤ C_W/(n − 1)`. -/
def LemmaW61 (d : ℕ) (CW : ℝ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ,
    ∫ x, ∑ j ∈ Finset.range (d + 1), (betaJ d j v x - sx61 v x ^ j) ^ 2 * kJ d j v v
        ∂lawRK n t v ≤ CW / ((n : ℝ) - 1)

/-- **Lemma S** (concentration of `u = s²`), `t ∈ [0, C n]`: `E_D (s² − E_D s²)² ≤ C_S/√n`. -/
def LemmaS61 (C CS : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ C * n →
    ∫ x, (sx61 v x ^ 2 - s2mom61 (lawRK n t v) v) ^ 2 ∂lawRK n t v ≤ CS / Real.sqrt n

/-- **Cor W** (the displacement is small), `t ∈ [0, C n]`, `0 ≤ r ≤ 1`:
`ω²(D, r) ≤ C_ω (n^{−1/4} + |E_D s² − r²|)`. -/
def CorW61 (d : ℕ) (C Cω : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n → ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ C * n →
    ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      omega61 (lawRK n t v) d v r ≤
        Cω * (1 / Real.sqrt (Real.sqrt n) + |s2mom61 (lawRK n t v) v - r ^ 2|)

/-- **Surrogate moment**: `0 ≤ E_{Q̃} s² ≤ 1` and `|E_{Q̃} s² − E_D s²| ≤ etaQ(e)` for `t ∈ [0, C n]`, `e > 0`. -/
def MomSur61 (C e : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ C * n →
    0 ≤ s2mom61 (surrRK n (KRK C n e) t v) v ∧ s2mom61 (surrRK n (KRK C n e) t v) v ≤ 1 ∧
    |s2mom61 (surrRK n (KRK C n e) t v) v - s2mom61 (lawRK n t v) v| ≤ etaQ e

/-- **Prop T1 for `g_K`** (Lemma R along rays and Markov; `g_K(λW)` is a polynomial of degree `≤ k`
in `λ`): a proxy bound `E_Z (B_μ − gKH_ν)(σZ)² ≤ X·E` (as a lower integral, so that no
integrability is assumed) with `E ≥ 0` gives
`Pr_M{c E < (B_μ − gKH_ν)(M)²} ≤ 5(k+1)² X / c` on the coefficient sphere. -/
def PropT1K61 (d k : ℕ) : Prop :=
  ∀ n : ℕ, 1000 ≤ n → ∀ (μ ν : Measure (Fin n → ℝ)), SphLaw n μ → SphLaw n ν →
    ∀ (v : Fin n → ℝ) (r f0 : ℝ) (T : Tens n), TSymm k T → ∀ X E c : ℝ, 0 ≤ E → 0 < c →
      ∫⁻ Z, ENNReal.ofReal ((BofQ μ k f0 T (sg n d • Z) - gKH61 ν k f0 T v r (sg n d • Z)) ^ 2)
          ∂stdGauss (CoefIdxD n d) ≤ ENNReal.ofReal (X * E) →
      stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
        c * E < (BofQ μ k f0 T (unitOfD Z) - gKH61 ν k f0 T v r (unitOfD Z)) ^ 2} ≤
        ENNReal.ofReal (5 * ((k : ℝ) + 1) ^ 2 * X / c)

end BstLean.Part61
