import BstLean.Part40Defs
import BstLean.CostModel

/-!
# Part 42, wave 0: frozen definitions — every diagonal Bingham law, computed moments, counter `k`

Paper: `proofs/option-m/42-every-diagonal-bingham-computed-moments.tex` (Theorem K, algorithm MOM,
Lemmas MC, T, E, D1″, O, the budget `Φ₆`, `k₀`, Corollary `k₀ = 1`).
Specification: `delegations/answers/p42-spec-opus.md`. This file holds definitions only. Provers must
not edit it, and must not use `native_decide` or `axiom` anywhere.

Conventions.
* Part 40's names are reused: `Mono n`, `constM`, `phi`, `idx`, `colOf`, `momE`, `momG`, `KeepOK`,
  `keepSet`, `SphLaw`, `SignSym`, `Akron`, `ymap`, `linZ`, `quadZ`, `varL`, `eta40` (`x = 7`),
  `gam40` (`K_C = 80`), `rho40 = 3/8`. `bingham n θ`, `P37` are Part 37's; `Dc`, `r2` Part 33's.
* **MOM's targets.** `bsh θ i0 = θ − θ_{i0}` (the shift; `i0` is a build-time index). `omg n m = ω_m`,
  `pw b j = P_j = 2^{j−1} Σ bᵢʲ`, and the recursions `phiC` (`φ_k`), `phiI` (`φ^{(i)}_k`), `phiII`
  (`φ^{(ii)}_k`), `phiIJ` (`[t^k] Φ/((1−2tbᵢ)(1−2tbⱼ))`). `Zr`, `muR`, `WR` are MOM's
  `Z̃`, `μ̃ᵢ`, `W̃ᵢⱼ`. `momR b K e` is MOM's value of the monomial with exponent vector `e`
  (zero if some exponent is odd); `ER b K p = momR (ex p)` and `GR b K p q = momR (ex p + ex q)`.
  `tauR = 3/2 + S̃₄/2 − Σ_{kept diagonal} G̃_pp`. MOM's program outputs `ER`, `GR` on the kept set,
  and `tauR / D_c`.
* **The truncated sphere sums.** `NT b K h = Σ_{k ≤ K} E_σ[h (b·u)^k]/k!`, `momET`, `momGT` (the
  paper's `N^{(K)}_α / N^{(K)}_0`). `deltaK A K = Σ_{k > K} A^k/k!`, `Kof A η` is Lemma `choice of K`.
* **The programs.** `MomOut n` indexes MOM's outputs; `In42 n` is the branch program's input
  (`M`, `f₀`, `b`, `F`, MOM's outputs). `heavy42` counts constants other than `0` and `1`; both
  programs must have `heavy42 = 0`, so every rational constant (`ω_m`, `1/k`, `2^{j−1}`, `3/2`,
  `1/D_c`) is built from `1` and charged. `momCost`, `gCost` are the proved cost bounds.
* **The branch with computed constants.** `GtOf Et Gk K` is `G̃` (constant row and column `Et`,
  kept entries `Gk`, zero elsewhere); `gOf42L Et Gk K τd` is the paper's `g` with `τd = τ̃/D_c`;
  `Rp μ Et Gk K = G − G̃` (the paper's `R′`).
* **The floor quantities of Lemma O.** `linPart Z x = Lx`, `hvec μ Z = Z E_μφ` (the paper's `h`),
  `w0`, `v0`, `Yw = ‖w₀ᵀLx‖²_{L²(μ)}`, `Yb = ‖bᵀLx‖²_{L²(μ)}`, `linErr Δ b Z = bᵀ Z Δ`, `vnorm`.
* **Constants.** `B6 n ε = P max(2, 0.91/ε²)` (rule A6), `gfix n = 6n² + 10n + 20`,
  `kOf42 n ε = ⌊(0.95 B6 − gfix − 1)/(n+1)²⌋ − 1`, `L6 n`, `eta42 n ε = min(ε/10⁶, ε/(600√n), 1/100)`,
  `kap42 = 1 + 2√10 + 20` (`x_l = 10`), `sigO = 10⁻⁵`, `Phi42 n` (the failure budget),
  `spread θ = max θ − min θ`, `k0 n θ ε` (the amortization threshold).
-/

namespace BstLean.Part42

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss frobSq CoefIdx Bof varOf unitOf qformC uniformSphere)
open BstLean.Part33 (Dc r2)
open BstLean.Part37 (bingham P37)
open BstLean.Part40 (Mono constM phi idx colOf momE momG KeepOK keepSet SphLaw SignSym Akron ymap
  linZ quadZ varL eta40 gam40)

variable {n : ℕ}

/-! ## §1 Monomials -/

/-- The linear monomial `xᵢ`. -/
def linM (i : Fin n) : Mono n := Sum.inr (Sum.inl i)

/-- The square monomial `xᵢ²`. -/
def sqM (i : Fin n) : Mono n := Sum.inr (Sum.inr ⟨(i, i), le_refl i⟩)

/-- The exponent vector of a monomial. -/
def ex : Mono n → Fin n → ℕ
  | Sum.inl _ => fun _ => 0
  | Sum.inr (Sum.inl i) => fun k => if k = i then 1 else 0
  | Sum.inr (Sum.inr p) => fun k => (if k = p.1.1 then 1 else 0) + (if k = p.1.2 then 1 else 0)

/-! ## §2 MOM's recursions and values -/

/-- The shift `bᵢ = θᵢ − θ_{i0}`. -/
def bsh (θ : Fin n → ℝ) (i0 : Fin n) : Fin n → ℝ := fun i => θ i - θ i0

/-- `ω_m = 1/∏_{l<m}(n + 2l)`. -/
noncomputable def omg (n m : ℕ) : ℝ := 1 / ∏ l ∈ Finset.range m, ((n : ℝ) + 2 * l)

/-- `P_j = 2^{j−1} Σᵢ bᵢʲ`. -/
noncomputable def pw (b : Fin n → ℝ) (j : ℕ) : ℝ := 2 ^ (j - 1) * ∑ i, b i ^ j

/-- `φ_0 = 1`, `k φ_k = Σ_{j=1}^k P_j φ_{k−j}`. -/
noncomputable def phiC (b : Fin n → ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => (∑ j : Fin (k + 1), pw b (j + 1) * phiC b (k - j)) / (k + 1)
decreasing_by omega

/-- `φ^{(i)}_k = φ_k + 2bᵢ φ^{(i)}_{k−1}`. -/
noncomputable def phiI (b : Fin n → ℝ) (i : Fin n) : ℕ → ℝ
  | 0 => 1
  | k + 1 => phiC b (k + 1) + 2 * b i * phiI b i k

/-- `φ^{(ii)}_k = φ^{(i)}_k + 2bᵢ φ^{(ii)}_{k−1}`. -/
noncomputable def phiII (b : Fin n → ℝ) (i : Fin n) : ℕ → ℝ
  | 0 => 1
  | k + 1 => phiI b i (k + 1) + 2 * b i * phiII b i k

/-- `[t^k] Φ/((1−2tbᵢ)(1−2tbⱼ))`, by `φ^{(ij)}_k = φ^{(i)}_k + 2bⱼ φ^{(ij)}_{k−1}`. -/
noncomputable def phiIJ (b : Fin n → ℝ) (i j : Fin n) : ℕ → ℝ
  | 0 => 1
  | k + 1 => phiI b i (k + 1) + 2 * b j * phiIJ b i j k

/-- MOM's `Z̃ = Σ_{k ≤ K} ω_k φ_k`. -/
noncomputable def Zr (b : Fin n → ℝ) (K : ℕ) : ℝ := ∑ k ∈ Finset.range (K + 1), omg n k * phiC b k

/-- MOM's `μ̃ᵢ = S¹ᵢ/Z̃`. -/
noncomputable def muR (b : Fin n → ℝ) (K : ℕ) (i : Fin n) : ℝ :=
  (∑ k ∈ Finset.range (K + 1), omg n (k + 1) * phiI b i k) / Zr b K

/-- MOM's `W̃ᵢᵢ = 3S³ᵢ/Z̃` and, for `i ≠ j`, `W̃ᵢⱼ`. -/
noncomputable def WR (b : Fin n → ℝ) (K : ℕ) (i j : Fin n) : ℝ := by
  classical
  exact (if i = j then 3 * ∑ k ∈ Finset.range (K + 1), omg n (k + 2) * phiII b i k
    else ∑ k ∈ Finset.range (K + 1), omg n (k + 2) * phiIJ b i j k) / Zr b K

/-- MOM's value of the monomial with exponent vector `e` (degree `≤ 4`). -/
noncomputable def momR (b : Fin n → ℝ) (K : ℕ) (e : Fin n → ℕ) : ℝ := by
  classical
  exact if ∃ i, Odd (e i) then 0
    else if ∑ i, e i = 0 then 1
    else if ∑ i, e i = 2 then ∑ i, (if e i = 2 then muR b K i else 0)
    else ∑ i, ∑ j, (if i < j ∧ e i = 2 ∧ e j = 2 then WR b K i j else 0) +
      ∑ i, (if e i = 4 then WR b K i i else 0)

/-- MOM's `E φ_p`. -/
noncomputable def ER (b : Fin n → ℝ) (K : ℕ) (p : Mono n) : ℝ := momR b K (ex p)

/-- MOM's `G_pq`. -/
noncomputable def GR (b : Fin n → ℝ) (K : ℕ) (p q : Mono n) : ℝ := momR b K (ex p + ex q)

/-- MOM's `τ̃ = 3/2 + S̃₄/2 − Σ_{(p,p) kept, p ≠ const} G̃_pp`. -/
noncomputable def tauR (b : Fin n → ℝ) (K : ℕ) (Kset : Finset (Mono n × Mono n)) : ℝ := by
  classical
  exact 3 / 2 + (∑ i, WR b K i i) / 2 - ∑ p, (if p ≠ constM ∧ (p, p) ∈ Kset then GR b K p p else 0)

/-! ## §3 The truncated sphere sums and the choice of `K` -/

/-- `N^{(K)}_h = Σ_{k ≤ K} E_σ[h (b·u)^k]/k!`, `u = x²`. -/
noncomputable def NT (b : Fin n → ℝ) (K : ℕ) (h : (Fin n → ℝ) → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (K + 1),
    ∫ x, h x * (∑ i, b i * x i ^ 2) ^ k / (k.factorial : ℝ) ∂uniformSphere n

/-- `N^{(K)}_{φ_p} / N^{(K)}_0`. -/
noncomputable def momET (b : Fin n → ℝ) (K : ℕ) (p : Mono n) : ℝ := NT b K (phi p) / NT b K (fun _ => 1)

/-- `N^{(K)}_{φ_pφ_q} / N^{(K)}_0`. -/
noncomputable def momGT (b : Fin n → ℝ) (K : ℕ) (p q : Mono n) : ℝ :=
  NT b K (fun x => phi p x * phi q x) / NT b K (fun _ => 1)

/-- `δ_K = Σ_{k > K} A^k/k!`. -/
noncomputable def deltaK (A : ℝ) (K : ℕ) : ℝ :=
  Real.exp A - ∑ k ∈ Finset.range (K + 1), A ^ k / (k.factorial : ℝ)

/-- `K(A, η) = ⌈max(e²A, ln(4/η))⌉ − 1` (Lemma `choice of K`). -/
noncomputable def Kof (A η : ℝ) : ℕ := ⌈max (Real.exp 2 * A) (Real.log (4 / η))⌉₊ - 1

/-- The spread `A = max θ − min θ`. -/
noncomputable def spread (θ : Fin n → ℝ) : ℝ := (⨆ i, θ i) - ⨅ i, θ i

/-- The tie pattern of `θ`. -/
noncomputable def tieSet (θ : Fin n → ℝ) : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter fun ij => θ ij.1 = θ ij.2

/-- `θ'` has the tie pattern `ties`. -/
def TieOK (ties : Finset (Fin n × Fin n)) (θ' : Fin n → ℝ) : Prop :=
  ∀ i j, (i, j) ∈ ties ↔ θ' i = θ' j

/-! ## §4 The programs -/

/-- MOM's outputs: `E φ_p` for every `p`, `G_pq` (read on the kept set), and `τ̃/D_c`. -/
abbrev MomOut (n : ℕ) := Mono n ⊕ (Mono n × Mono n) ⊕ Unit

/-- The branch program's inputs: `M`, `f₀`, `b`, `F`, and MOM's outputs. -/
abbrev In42 (n : ℕ) := CoefIdx n ⊕ Unit ⊕ Fin n ⊕ (Fin n × Fin n) ⊕ MomOut n

def Mv (v : In42 n → ℝ) : CoefIdx n → ℝ := fun a => v (Sum.inl a)
def f0v (v : In42 n → ℝ) : ℝ := v (Sum.inr (Sum.inl ()))
def gv (v : In42 n → ℝ) : Fin n → ℝ := fun i => v (Sum.inr (Sum.inr (Sum.inl i)))
def Fv (v : In42 n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => v (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, j)))))
def cv (v : In42 n → ℝ) : MomOut n → ℝ := fun o => v (Sum.inr (Sum.inr (Sum.inr (Sum.inr o))))

/-- The input vector for `M`, `f = (f₀, b, F)` and constants `c`. -/
def inp42 (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (M : CoefIdx n → ℝ)
    (c : MomOut n → ℝ) : In42 n → ℝ :=
  Sum.elim M (Sum.elim (fun _ => f0) (Sum.elim g (Sum.elim (fun ij => F ij.1 ij.2) c)))

/-- `1` for a constant other than `0` and `1`. -/
def argHeavy42 {ι : Type} : Arg ι → ℕ
  | .cst q => if q = 0 ∨ q = 1 then 0 else 1
  | _ => 0

/-- The number of constant arguments other than `0` and `1`. -/
def heavy42 {ι κ : Type} [Fintype κ] (p : Prog ι κ) : ℕ :=
  (p.body.map fun I => argHeavy42 I.a + argHeavy42 I.b).sum + ∑ o, argHeavy42 (p.out o)

/-- The proved bound on MOM's cost (Lemma MC plus the cost of building every constant from `1`). -/
noncomputable def momCost (n K c : ℕ) : ℝ :=
  (K : ℝ) ^ 2 + (12 * (n : ℝ) + 8) * K + 8 * n + 5 * c + 4 * (Nat.log 2 n : ℝ) + 120

/-- The fixed part of the branch program's cost. -/
noncomputable def gfix (n : ℕ) : ℝ := 6 * (n : ℝ) ^ 2 + 10 * n + 20

/-- The proved bound on the branch program's cost: `(n+1)²` per kept ordered pair. -/
noncomputable def gCost (n c : ℕ) : ℝ := ((n : ℝ) + 1) ^ 2 * c + gfix n

/-- MOM's specification at `θ'`: build-time choices `i0`, `K`, `Kset`. -/
def MomSpec (pm : Prog (Fin n) (MomOut n)) (i0 : Fin n) (K : ℕ) (Kset : Finset (Mono n × Mono n))
    (θ' : Fin n → ℝ) : Prop :=
  (∀ q, pm.eval θ' (Sum.inl q) = ER (bsh θ' i0) K q) ∧
  (∀ pq ∈ Kset, pm.eval θ' (Sum.inr (Sum.inl pq)) = GR (bsh θ' i0) K pq.1 pq.2) ∧
  pm.eval θ' (Sum.inr (Sum.inr ())) = tauR (bsh θ' i0) K Kset / Dc n

/-! ## §5 The branch with computed constants -/

/-- `G̃`: constant row and column `Et`, kept entries `Gk`, zero elsewhere. -/
noncomputable def GtOf (Et : Mono n → ℝ) (Gk : Mono n → Mono n → ℝ) (Kset : Finset (Mono n × Mono n))
    (p q : Mono n) : ℝ := by
  classical
  exact if p = constM then Et q else if q = constM then Et p else if (p, q) ∈ Kset then Gk p q else 0

/-- The paper's `g` with computed constants:
  `f₀ + bᵀ M Ẽφ + Σ_{p,q} G̃_pq M_pᵀ F M_q + tr F · τd` (`τd = τ̃/D_c`). -/
noncomputable def gOf42L (Et : Mono n → ℝ) (Gk : Mono n → Mono n → ℝ)
    (Kset : Finset (Mono n × Mono n)) (τd : ℝ) (f0 : ℝ) (g : Fin n → ℝ)
    (F : Matrix (Fin n) (Fin n) ℝ) (M : CoefIdx n → ℝ) : ℝ :=
  f0 + ∑ k, g k * ∑ p, colOf M p k * Et p +
    ∑ p, ∑ q, GtOf Et Gk Kset p q * ∑ k, ∑ l, F k l * colOf M p k * colOf M q l +
    (∑ k, F k k) * τd

/-- `R′ = G − G̃`. -/
noncomputable def Rp (μ : Measure (Fin n → ℝ)) (Et : Mono n → ℝ) (Gk : Mono n → Mono n → ℝ)
    (Kset : Finset (Mono n × Mono n)) (p q : Mono n) : ℝ :=
  momG μ p q - GtOf Et Gk Kset p q

/-- The branch program's specification for the kept set `Kset`: on every input with `F` symmetric,
`Gk` symmetric on `Kset`, and MOM's output shape (`Ẽφ` is `1` at the constant, `0` at linear and cross
monomials), the program returns `gOf42L`. -/
def GSpec (pg : Prog (In42 n) Unit) (Kset : Finset (Mono n × Mono n)) : Prop :=
  ∀ v : In42 n → ℝ, (Fv v).IsSymm →
    (∀ pq ∈ Kset, cv v (Sum.inr (Sum.inl pq)) = cv v (Sum.inr (Sum.inl pq.swap))) →
    (∀ p, ex p ≠ (fun _ => 0) → (∀ i, ex p ≠ (fun k => if k = i then 2 else 0)) →
      cv v (Sum.inl p) = 0) →
    cv v (Sum.inl constM) = 1 →
    pg.eval v () = gOf42L (fun q => cv v (Sum.inl q)) (fun p q => cv v (Sum.inr (Sum.inl (p, q))))
      Kset (cv v (Sum.inr (Sum.inr ()))) (f0v v) (gv v) (Fv v) (Mv v)

/-! ## §6 The floor quantities of Lemma O -/

/-- `L x`: the linear block of `Z` applied to `x`. -/
noncomputable def linPart (Z : CoefIdx n → ℝ) (x : Fin n → ℝ) (k : Fin n) : ℝ :=
  ∑ i, Z (idx k (linM i)) * x i

/-- `h = Z E_μ φ`. -/
noncomputable def hvec (μ : Measure (Fin n → ℝ)) (Z : CoefIdx n → ℝ) (k : Fin n) : ℝ :=
  ∑ p, Z (idx k p) * momE μ p

/-- `w₀(x) = √D_c b + 2F(c + Qφ₂(x))`. -/
noncomputable def w0 (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (Z : CoefIdx n → ℝ)
    (x : Fin n → ℝ) (k : Fin n) : ℝ :=
  Real.sqrt (Dc n) * g k + 2 * ∑ l, F k l * (ymap Z x l - linPart Z x l)

/-- `v₀ = √D_c b + 2F h`. -/
noncomputable def v0 (μ : Measure (Fin n → ℝ)) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (Z : CoefIdx n → ℝ) (k : Fin n) : ℝ :=
  Real.sqrt (Dc n) * g k + 2 * ∑ l, F k l * hvec μ Z l

/-- `Y_w = ‖w₀ᵀ L x‖²_{L²(μ)}`. -/
noncomputable def Yw (μ : Measure (Fin n → ℝ)) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (Z : CoefIdx n → ℝ) : ℝ :=
  ∫ x, (∑ k, w0 g F Z x k * linPart Z x k) ^ 2 ∂μ

/-- `Y_b = ‖bᵀ L x‖²_{L²(μ)}`. -/
noncomputable def Yb (μ : Measure (Fin n → ℝ)) (g : Fin n → ℝ) (Z : CoefIdx n → ℝ) : ℝ :=
  ∫ x, (∑ k, g k * linPart Z x k) ^ 2 ∂μ

/-- `bᵀ Z Δ` (unnormalised linear error). -/
noncomputable def linErr (Δ : Mono n → ℝ) (g : Fin n → ℝ) (Z : CoefIdx n → ℝ) : ℝ :=
  ∑ k, g k * ∑ p, Z (idx k p) * Δ p

/-- The Euclidean norm. -/
noncomputable def vnorm {ι : Type} [Fintype ι] (v : ι → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

/-! ## §7 Constants, the budget and the counter -/

/-- The realistic baseline `𝔅₆(ε) = P max(2, 0.91/ε²)` (rule A6). -/
noncomputable def B6 (n : ℕ) (ε : ℝ) : ℝ := P37 (n : ℝ) * max 2 (91 / 100 / ε ^ 2)

/-- `k′ = ⌊(0.95 𝔅₆ − gfix − 1)/(n+1)²⌋ − 1`. -/
noncomputable def kOf42 (n : ℕ) (ε : ℝ) : ℕ :=
  ⌊(95 / 100 * B6 n ε - gfix n - 1) / ((n : ℝ) + 1) ^ 2⌋₊ - 1

/-- `L₆(n) = 0.455 (0.95 n²(n+3) − gfix − 1 − 2(n+1)²)/(n+1)²`, a lower bound on `k′ε²`. -/
noncomputable def L6 (n : ℕ) : ℝ :=
  455 / 1000 * (95 / 100 * (n : ℝ) ^ 2 * (n + 3) - gfix n - 1 - 2 * ((n : ℝ) + 1) ^ 2) /
    ((n : ℝ) + 1) ^ 2

/-- The precision `η(n, ε) = min(ε/10⁶, ε/(600√n), 1/100)`. -/
noncomputable def eta42 (n : ℕ) (ε : ℝ) : ℝ :=
  min (ε / 10 ^ 6) (min (ε / (600 * Real.sqrt n)) (1 / 100))

/-- `κ = 1 + 2√x_l + 2x_l` at `x_l = 10`. -/
noncomputable def kap42 : ℝ := 1 + 2 * Real.sqrt 10 + 20

/-- `σ_o = 10⁻⁵`. -/
noncomputable def sigO : ℝ := 1 / 10 ^ 5

/-- The failure budget: `2e^{−7} + ρ* + 1/80` (part 40's events), `√(eσ_o)` (Lemma O(b)),
`2e^{−10}` (Lemma O(c) and the event `|Fh|² ≤ 2κv`), `2e^{−25/2}` (the `b`-error at `z = 5`),
`10⁻⁶` (the `η²` part of Chebyshev) and the Chebyshev term. -/
noncomputable def Phi42 (n : ℕ) : ℝ :=
  2 * Real.exp (-7) + 3 / 8 + 1 / 80 + Real.sqrt (Real.exp 1 * sigO) + 2 * Real.exp (-10) +
    2 * Real.exp (-(25 / 2)) + 1 / 10 ^ 6 + 25 / 8 / ((99 / 100) ^ 2 * L6 n * gam40 n ^ 2)

/-- The amortization threshold `k₀ = ⌈C_mom/(0.05 𝔅₆)⌉`, with MOM's proved cost bound at
`K = Kof (spread θ) η` and the kept set of the theorem. -/
noncomputable def k0 (n : ℕ) (θ : Fin n → ℝ) (ε : ℝ) : ℕ :=
  ⌈momCost n (Kof (spread θ) (eta42 n ε)) (keepSet (bingham n θ) (kOf42 n ε)).card /
    (5 / 100 * B6 n ε)⌉₊

end BstLean.Part42
