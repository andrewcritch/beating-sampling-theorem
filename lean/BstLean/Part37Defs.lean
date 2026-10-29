import BstLean.Part33Defs

/-!
# Part 37, wave 0: frozen definitions for the explicit `(2,2)` theorem over the Bingham ball

Paper: `proofs/option-m/37-explicit-22-bingham-ball.tex`. Specification:
`delegations/answers/p37-spec-opus.md`. This file holds definitions only. Provers must not edit it, and must
not use `native_decide` anywhere.

Conventions.
* The coefficient space, the readers `cOf`, `LOf`, `aOf`, the quantity `Bof μ f0 g F M = E_μ f(m_M(x))`,
  `varOf`, `unitOf`, `qformC` and `stdGauss` are Part 29's. `f` is Part 29's `funF` (quadratic `f`).
* `θ : Fin n → ℝ` with `‖θ‖_∞ ≤ 1/4` (`InBall θ`). The paper's `θ ∈ ℝᵗ`, `t ≤ n`, is the case `θ i = 0` for
  `i ≥ t`. The costs below use the worst case `t = n` (`T = n + 1`).
* `bingham n θ` is the law `D(θ)`: density `e^{q_θ}/Z_θ` with respect to `uniformSphere n`.
* `binghamK n K θ` is the law `D_K(θ)`: density `T_K(q_θ)/Z_K`, with `T_K` the degree-`K` Taylor polynomial
  of `exp`. The moments that the program computes by the truncated series (`momK`) are exactly the moments
  of `D_K` (file `Part37Series`, `numK_eq`). The proof compares `D_K` with `D` through the density ratio
  (`Part37Close`), so it needs no norm event, no `χ²` event and no `b`-floor.
* `phiTab`/`phi0` is the program's power-sum recurrence for the coefficients of `∏ᵢ (1 − 2θᵢ s)^{−1/2}`;
  `mulGeom c` multiplies a series by `(1 − c s)^{−1}`; `phiW θ w` does this once for each entry of the list
  `w`; `dfC w = ∏ᵢ (2 αᵢ − 1)!!` with `αᵢ = w.count i`. The monomial of `w` is `∏_{i ∈ w} x_i²` (`wmono`).
* Branches E, H (the corrected branch, `cᵀF(c + 2τ)`), U take the moment vector `mu`, `W` (or its diagonal
  `m4`) as arguments; the program `gOf37` passes the computed moments `muK`, `WK`.
* `K` is `Kof ε`: the least `K ≥ 3` with `η_K ≤ λ ε`, `λ = 1/50` (`etaK`). This is a rational test.
* `D_c` is Part 33's `Dc n = |CoefIdx n|`.
* The costs `P37`, `CE`, `CH`, `CU` are the paper's charges (paper cost model), taken as definitions.
-/

namespace BstLean.Part37

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss qformι funF frobSq CoefIdx cOf LOf aOf Bof varOf unitOf qformC
  uniformSphere kappa eta)
open BstLean.Part33 (SphereProd floorY4 rawQ Dc)

variable {n : ℕ}

/-! ## §1 The laws -/

/-- `q_θ(x) = Σ θᵢ xᵢ²`. -/
def qth (θ : Fin n → ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, θ i * x i ^ 2

/-- The Bingham ball `‖θ‖_∞ ≤ 1/4`. -/
def InBall (θ : Fin n → ℝ) : Prop := ∀ i, |θ i| ≤ 1 / 4

/-- `Z_θ = E_U e^{q_θ}`. -/
noncomputable def Zth (n : ℕ) (θ : Fin n → ℝ) : ℝ := ∫ x, Real.exp (qth θ x) ∂uniformSphere n

/-- The law `D(θ)`. -/
noncomputable def bingham (n : ℕ) (θ : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  (uniformSphere n).withDensity (fun x => ENNReal.ofReal (Real.exp (qth θ x) / Zth n θ))

/-- The degree-`K` Taylor polynomial of `exp`. -/
noncomputable def taylorExp (K : ℕ) (s : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (K + 1), s ^ k / (k.factorial : ℝ)

/-- `Z_K = E_U T_K(q_θ)`. -/
noncomputable def ZK (n K : ℕ) (θ : Fin n → ℝ) : ℝ := ∫ x, taylorExp K (qth θ x) ∂uniformSphere n

/-- The law `D_K(θ)`, whose moments the program computes. -/
noncomputable def binghamK (n K : ℕ) (θ : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  (uniformSphere n).withDensity (fun x => ENNReal.ofReal (taylorExp K (qth θ x) / ZK n K θ))

/-! ## §2 The program's moment computation -/

/-- Power sums `p_j = Σ θᵢ^j`. -/
def psum (θ : Fin n → ℝ) (j : ℕ) : ℝ := ∑ i, θ i ^ j

/-- `phiTab θ K` holds the coefficients `a_0, …, a_K` of `∏ᵢ (1 − 2θᵢ s)^{−1/2} = exp(Σ ψ_j s^j)`, from
the recurrence `k a_k = Σ_{j=1}^k 2^{j−1} p_j a_{k−j}`. Entries past `K` are not used. -/
noncomputable def phiTab (θ : Fin n → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun k => if k = 0 then 1 else 0
  | K + 1 => fun k => if k ≤ K then phiTab θ K k else
      (∑ j ∈ Finset.range (K + 1), 2 ^ j * psum θ (j + 1) * phiTab θ K (K - j)) / ((K : ℝ) + 1)

/-- `a_k = [s^k] ∏ᵢ (1 − 2θᵢ s)^{−1/2}`, as the program computes it. -/
noncomputable def phi0 (θ : Fin n → ℝ) (k : ℕ) : ℝ := phiTab θ k k

/-- Multiplication of a series by `(1 − c s)^{−1}` (the program runs the equivalent recurrence
`b_k = a_k + c b_{k−1}`). -/
noncomputable def mulGeom (c : ℝ) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (k + 1), c ^ r * a (k - r)

/-- `[s^k] ∏ᵢ (1 − 2θᵢ s)^{−1/2} ∏_{i ∈ w} (1 − 2θᵢ s)^{−1}`. -/
noncomputable def phiW (θ : Fin n → ℝ) (w : List (Fin n)) : ℕ → ℝ :=
  w.foldr (fun i a => mulGeom (2 * θ i) a) (phi0 θ)

/-- `∏ᵢ (2αᵢ − 1)!!`, `αᵢ = w.count i` (natural subtraction: `(2·0 − 1)!! = 0!! = 1`). -/
noncomputable def dfC (w : List (Fin n)) : ℝ := ∏ i, ((2 * w.count i - 1).doubleFactorial : ℝ)

/-- `ρ_m = ∏_{r<m} (n + 2r)`. -/
noncomputable def rhoP (n m : ℕ) : ℝ := ∏ r ∈ Finset.range m, ((n : ℝ) + 2 * r)

/-- The truncated numerator `N̂_K(w) = Σ_{k ≤ K} dfC w · phiW θ w k / ρ_{|w|+k}`. -/
noncomputable def numK (n K : ℕ) (θ : Fin n → ℝ) (w : List (Fin n)) : ℝ :=
  dfC w * ∑ k ∈ Finset.range (K + 1), phiW θ w k / rhoP n (w.length + k)

/-- The computed moment `N̂_K(w)/N̂_K([])`. -/
noncomputable def momK (n K : ℕ) (θ : Fin n → ℝ) (w : List (Fin n)) : ℝ :=
  numK n K θ w / numK n K θ []

/-- `μ̂ᵢ`. -/
noncomputable def muK (n K : ℕ) (θ : Fin n → ℝ) (i : Fin n) : ℝ := momK n K θ [i]

/-- `Ŵᵢⱼ` (`Ŵᵢᵢ = m̂ᵢ₄`, `Ŵᵢⱼ = m̂ᵢⱼ`). -/
noncomputable def WK (n K : ℕ) (θ : Fin n → ℝ) (i j : Fin n) : ℝ := momK n K θ [i, j]

/-- The closed (multinomial) form of the series coefficient:
`Σ_{|κ| = k} ∏ᵢ θᵢ^{κᵢ} (2(αᵢ + κᵢ) − 1)!! / κᵢ!`. -/
noncomputable def phiCoef (θ : Fin n → ℝ) (w : List (Fin n)) (k : ℕ) : ℝ :=
  ∑ κ ∈ Finset.Nat.antidiagonalTuple n k,
    ∏ i, θ i ^ κ i * ((2 * (w.count i + κ i) - 1).doubleFactorial : ℝ) / ((κ i).factorial : ℝ)

/-- The monomial `∏_{i ∈ w} xᵢ²`. -/
def wmono (w : List (Fin n)) (x : Fin n → ℝ) : ℝ := (w.map (fun i => x i ^ 2)).prod

/-! ## §3 Laws with sign symmetry -/

/-- A law whose moments up to degree four are those of a sign-symmetric law with second moments `mu` and
fourth moments `W` (`W i i = E xᵢ⁴`, `W i j = E xᵢ² xⱼ²`). -/
structure SymMoments (n : ℕ) (μ : Measure (Fin n → ℝ)) (mu : Fin n → ℝ) (W : Fin n → Fin n → ℝ) :
    Prop where
  int1 : ∀ i, Integrable (fun x : Fin n → ℝ => x i) μ
  int2 : ∀ i j, Integrable (fun x : Fin n → ℝ => x i * x j) μ
  int3 : ∀ i j k, Integrable (fun x : Fin n → ℝ => x i * x j * x k) μ
  int4 : ∀ i j k l, Integrable (fun x : Fin n → ℝ => x i * x j * x k * x l) μ
  m1 : ∀ i, ∫ x, x i ∂μ = 0
  m2 : ∀ i j, ∫ x, x i * x j ∂μ = if i = j then mu i else 0
  m3 : ∀ i j k, ∫ x, x i * x j * x k ∂μ = 0
  m4 : ∀ i j k l, ∫ x, x i * x j * x k * x l ∂μ =
    if i = j ∧ j = k ∧ k = l then W i i else
      (if i = j ∧ k = l then W i k else 0) + (if i = k ∧ j = l then W i j else 0) +
        (if i = l ∧ j = k then W i j else 0)

/-! ## §4 The branches -/

/-- `ω = 9/(8n(n+2))`. -/
noncomputable def omega37 (n : ℕ) : ℝ := 9 / (8 * (n : ℝ) * (n + 2))

/-- `τ_k = Σᵢ Q_{k,ii} μᵢ`. -/
noncomputable def tauB (M : CoefIdx n → ℝ) (mu : Fin n → ℝ) (k : Fin n) : ℝ := ∑ i, aOf M k i i * mu i

/-- `t_k = Σᵢ Q_{k,ii}`. -/
noncomputable def trB (M : CoefIdx n → ℝ) (k : Fin n) : ℝ := ∑ i, aOf M k i i

/-- `E[m_k m_l]` for a sign-symmetric law with moments `mu`, `W`. -/
noncomputable def secB (M : CoefIdx n → ℝ) (mu : Fin n → ℝ) (W : Fin n → Fin n → ℝ) (k l : Fin n) : ℝ :=
  cOf M k * cOf M l + cOf M k * tauB M mu l + cOf M l * tauB M mu k
    + ∑ i, LOf M k i * mu i * LOf M l i
    + ∑ i, ∑ j, aOf M k i i * W i j * aOf M l j j
    + ∑ i, ∑ j, (if i < j then W i j * aOf M k i j * aOf M l i j else 0)

/-- Branch E (the exact formula). -/
noncomputable def EofB (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (M : CoefIdx n → ℝ)
    (mu : Fin n → ℝ) (W : Fin n → Fin n → ℝ) : ℝ :=
  f0 + ∑ k, g k * (cOf M k + tauB M mu k) + ∑ k, ∑ l, F k l * secB M mu W k l

/-- Branch H (heat, as fixed by the cost challenge). -/
noncomputable def HofB (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (M : CoefIdx n → ℝ)
    (mu m4 : Fin n → ℝ) : ℝ :=
  f0 + ∑ k, g k * (cOf M k + tauB M mu k)
    + ∑ k, ∑ l, F k l * cOf M k * (cOf M l + 2 * tauB M mu l)
    + ∑ k, ∑ l, F k l * ∑ i, LOf M k i * mu i * LOf M l i
    + omega37 n * ∑ k, ∑ l, F k l * trB M k * trB M l
    + (∑ k, F k k) * ((1 + ∑ i, m4 i) / 2 - n * omega37 n) / Dc n

/-- Branch U. -/
noncomputable def UofB (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (M : CoefIdx n → ℝ)
    (mu m4 : Fin n → ℝ) : ℝ :=
  f0 + ∑ k, g k * (cOf M k + tauB M mu k)
    + ∑ k, ∑ l, F k l * (cOf M k + tauB M mu k) * (cOf M l + tauB M mu l)
    + (∑ k, F k k) * (1 + (1 + ∑ i, m4 i) / 2 - ∑ i, mu i ^ 2) / Dc n

/-- `A_H = F ⊗ G'`, `G' = (W − ωJ) ⊕ diag(m_ij)` on the quadratic block. -/
noncomputable def AHB (F : Matrix (Fin n) (Fin n) ℝ) (W : Fin n → Fin n → ℝ) :
    Matrix (CoefIdx n) (CoefIdx n) ℝ := fun α β =>
  match α, β with
  | Sum.inr (Sum.inr p), Sum.inr (Sum.inr q) =>
      F p.1.2.2 q.1.2.2 *
        (if p.1.1 = p.1.2.1 ∧ q.1.1 = q.1.2.1 then W p.1.1 q.1.1 - omega37 n
        else if p.1.1 < p.1.2.1 ∧ p.1.1 = q.1.1 ∧ p.1.2.1 = q.1.2.1 then W p.1.1 p.1.2.1 else 0)
  | _, _ => 0

/-- `A_U = F ⊗ Σ_D`, `Σ_D = diag(μ) ⊕ (W − μμᵀ) ⊕ diag(m_ij)`. -/
noncomputable def AUB (F : Matrix (Fin n) (Fin n) ℝ) (mu : Fin n → ℝ) (W : Fin n → Fin n → ℝ) :
    Matrix (CoefIdx n) (CoefIdx n) ℝ := fun α β =>
  match α, β with
  | Sum.inr (Sum.inl (k, i)), Sum.inr (Sum.inl (l, i')) => if i = i' then F k l * mu i else 0
  | Sum.inr (Sum.inr p), Sum.inr (Sum.inr q) =>
      F p.1.2.2 q.1.2.2 *
        (if p.1.1 = p.1.2.1 ∧ q.1.1 = q.1.2.1 then W p.1.1 q.1.1 - mu p.1.1 * mu q.1.1
        else if p.1.1 < p.1.2.1 ∧ p.1.1 = q.1.1 ∧ p.1.2.1 = q.1.2.1 then W p.1.1 p.1.2.1 else 0)
  | _, _ => 0

/-- `‖G'‖_F²`. -/
noncomputable def gpSq (W : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, (W i j - omega37 n) ^ 2 + ∑ i, ∑ j, (if i < j then W i j ^ 2 else 0)

/-- `‖Σ_D‖_F²`. -/
noncomputable def sdSq (mu : Fin n → ℝ) (W : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, mu i ^ 2 + ∑ i, ∑ j, (W i j - mu i * mu j) ^ 2 + ∑ i, ∑ j, (if i < j then W i j ^ 2 else 0)

/-! ## §5 Constants, thresholds, the moment precision -/

/-- `g_H` (Lemma `frob`), with `ρ' = 33/20`, `σ = 21/40`, `3ρ' − 9/8 = 153/40`. -/
noncomputable def gH (n : ℝ) : ℝ :=
  (n * (n - 1) * (21 / 40) ^ 2 + n * (153 / 40) ^ 2) / (n ^ 2 * (n + 2) ^ 2) + (33 / 20) / (2 * n * (n + 2))

/-- `s_D` (Lemma `frob`). -/
noncomputable def sD (n : ℝ) : ℝ :=
  (33 / 20) / n + (33 / 20) / (2 * n * (n + 2)) + 9 * (33 / 20) ^ 2 / (n + 2) ^ 2

/-- `h_D² = 8ρ' g_H / ((1 − λ)² q κₙ)`, `q = δ − η'ₙ`, `λ = 1/50`. -/
noncomputable def hSq (n δ : ℝ) : ℝ := 8 * (33 / 20) * gH n / ((49 / 50) ^ 2 * (δ - eta n) * kappa n)

/-- `u_D² = 8ρ' s_D / ((1 − λ)² q κₙ)`. -/
noncomputable def uSq (n δ : ℝ) : ℝ := 8 * (33 / 20) * sD n / ((49 / 50) ^ 2 * (δ - eta n) * kappa n)

/-- `τ_K = (1/4)^{K+1} ρ' / (K+1)!` bounds `|T_K(q)/e^q − 1|` on the ball (`ρ' ≥ e^{1/2}`). -/
noncomputable def tauK (K : ℕ) : ℝ := (1 / 4) ^ (K + 1) * (33 / 20) / ((K + 1).factorial : ℝ)

/-- `η_K = 2τ_K/(1 − τ_K)` bounds `|dD_K/dD − 1|`. -/
noncomputable def etaK (K : ℕ) : ℝ := 2 * tauK K / (1 - tauK K)

/-- The program's `K`: the least `K ≥ 3` with `η_K ≤ ε/50` (`3` if there is none, which happens only for
`ε ≤ 0`). -/
noncomputable def Kof (ε : ℝ) : ℕ := by
  classical
  exact if h : ∃ K : ℕ, 3 ≤ K ∧ etaK K ≤ ε / 50 then Nat.find h else 3

/-- The paper's `τ_K = a^{K+1}/((K+1)!(1 − a/(K+2)))`, `a = 1/4` (Lemma `M2`; file `Part37Paper` only). -/
noncomputable def tauP (K : ℕ) : ℝ :=
  (1 / 4) ^ (K + 1) / (((K + 1).factorial : ℝ) * (1 - (1 / 4) / ((K : ℝ) + 2)))

/-- The paper's `η_K = 2τ_K ē/(1 − τ_K ē)`, `ē = 1.285` (Lemma `M2`; file `Part37Paper` only). -/
noncomputable def etaP (K : ℕ) : ℝ := 2 * tauP K * (257 / 200) / (1 - tauP K * (257 / 200))

/-! ## §6 The paper's cost model (definitions) -/

/-- `P = n(N − 1) = n²(n+3)/2`. -/
noncomputable def P37 (n : ℝ) : ℝ := n ^ 2 * (n + 3) / 2

/-- The prover's charge for `μ̂, m̂₄, Ẑ` at `t = n`. -/
noncomputable def momC (n K : ℝ) : ℝ :=
  2 * n * K + K ^ 2 + 15 * K + 12 * K * (n + 1) + 10 * (n + 1) + 100

/-- The same with the pairs `m̂ᵢⱼ` (branch E). -/
noncomputable def momCE (n K : ℝ) : ℝ := momC n K + 3 * K * (n + 1) * (n + 2) + 2 * (n + 1) * (n + 2)

/-- Cost of branch E, moments included. -/
noncomputable def CE (n K : ℝ) : ℝ :=
  n ^ 2 * (n + 1) ^ 2 / 2 + n ^ 2 * (n - 1) / 2 + 6 * n ^ 3 + 25 * n ^ 2 + 20 * n + 100 + momCE n K

/-- Cost of branch H (fixed), moments included. -/
noncomputable def CH (n K : ℝ) : ℝ := n ^ 3 + 15 * n ^ 2 + 30 * n + 200 + momC n K

/-- Cost of branch U, moments included. -/
noncomputable def CU (n K : ℝ) : ℝ := 4 * n ^ 2 + 30 * n + 200 + momC n K

/-! ## §7 The program -/

/-- The program `g_{θ,f,ε}`: E if `ε² < h_D²`, H if `h_D² ≤ ε² < u_D²`, U otherwise, at the computed moments
with `K = Kof ε`. -/
noncomputable def gOf37 (θ : Fin n → ℝ) (δ ε : ℝ) (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (M : CoefIdx n → ℝ) : ℝ :=
  if ε ^ 2 < hSq n δ then EofB f0 g F M (muK n (Kof ε) θ) (WK n (Kof ε) θ)
  else if ε ^ 2 < uSq n δ then HofB f0 g F M (muK n (Kof ε) θ) (fun i => WK n (Kof ε) θ i i)
  else UofB f0 g F M (muK n (Kof ε) θ) (fun i => WK n (Kof ε) θ i i)

/-- The cost of the branch the program takes. -/
noncomputable def costOf37 (n : ℕ) (δ ε : ℝ) : ℝ :=
  if ε ^ 2 < hSq n δ then CE n (Kof ε)
  else if ε ^ 2 < uSq n δ then CH n (Kof ε)
  else CU n (Kof ε)

end BstLean.Part37
