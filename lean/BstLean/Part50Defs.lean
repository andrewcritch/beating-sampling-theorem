import BstLean.Part48Defs

/-!
# Part 50, wave 0: frozen definitions — Theorem GA′ (every symmetric Bingham law of bounded spread)

Source: `delegations/answers/omGA-opus-prover.md` (Lemma M′, Theorem GA′, the moment program) and
`omGA-codex-disprover.md` (why `mass43` fails for dense `A`). Specification:
`delegations/answers/p50-spec-opus.md`. This file holds definitions only. Provers must not edit it,
and must not use `native_decide` or `axiom` anywhere.

Conventions. Part 41, 43 and 48 names are reused. `k = d_f`, `d = d_M`. A matrix is
`Matrix (Fin n) (Fin n) ℝ`.

* **Quadratic form and spread.** `qA A x = Σ_{i,j} A_ij x_i x_j`. `SpreadLE A Λ`: for all unit `x, y`,
  `qA A x − qA A y ≤ Λ` (this is `λ_max − λ_min ≤ Λ` for symmetric `A`). `PSDq B`: `qA B x ≥ 0` for all `x`.
* **The shift (computed by the program, no build-time real data).** `shiftA A i0 N = A − (A_{i0 i0} − N)·I`.
  For `SpreadLE A Λ` and `N ≥ Λ`, on the sphere `0 ≤ qA (shiftA A i0 N) x ≤ Λ + N ≤ 2N`, because
  `A_{i0 i0} = qA A e_{i0}`. `NofL Λ = ⌈Λ⌉₊`, `aA Λ = 2 NofL Λ` (range bound and entry bound),
  `KqA Λ ε = Kof43 (aA Λ) ε` (truncation order).
* **The laws.** `binghamA n A ∝ exp(qA A x)·σ` (the target `D(A)`). `binghamKA n K B ∝ p_K(qA B x)·σ`
  (Taylor law). `surrA n A i0 Λ ε = binghamKA n (KqA Λ ε) (shiftA A i0 (NofL Λ))` (the surrogate `Q̃(A)`).
  `Antipodal n μ`: `SphLaw n μ` and `μ.map Neg.neg = μ` (replaces `SignSym`).
* **Mass (Lemma M′).** `MA j d a K = Σ_{t ≤ K} (2a)^t/t! · U″_{j+t}(d)`.
* **Allocation.** `AUA`, `tauA`, `OcntA`, `KeepOKA`, `keepSetA` are Part 43's `AU`, `tau43`, `Ocnt43`,
  `KeepOK43`, `keepSet43` with `MA j d a K` in place of `Upp j d`. `keepSet50`, `gOf50` instantiate them
  at the surrogate.
* **Moment program.** Input type `Fin n × Fin n` (the matrix entries, `matIn A`). `MomSpecA`: on every
  used key the program returns the weight of `binghamKA n Kq (shiftA A' i0 N)`. `onceCostA` is the
  proved-cost bound; it only enters `k0A`. The heights `bA` (moment constants `E_σ x^s / t!`) and `bKA`
  (key constants) are defined as `log₂` of the sum of `|num| + den` over the constants themselves.
* **Budget.** `Phi50`, `BudgetOK50` are Part 48's `Phi48`, `BudgetOK48` with `tauA` in place of
  `tau43` and `2 ≤ d` in place of `1 ≤ d`. `k0A` is the amortization counter.
-/

namespace BstLean.Part50

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono frob levels cS Bfix Pn epsS baseline thetaT Kc etaR Lk bQ)
open BstLean.Part43 (Params43 RR Upp Kof43 nu43 xi43 keys43 wKeyR gTCR)
open BstLean.Part48 (gam48)

variable {n d : ℕ}

/-! ## §1 Quadratic forms, spread, shift -/

/-- `qA A x = xᵀ A x = Σ_{i,j} A_ij x_i x_j`. -/
def qA (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, ∑ j, A i j * x i * x j

/-- `λ_max(A) − λ_min(A) ≤ Λ`, stated through the quadratic form on the unit sphere. -/
def SpreadLE (A : Matrix (Fin n) (Fin n) ℝ) (Λ : ℝ) : Prop :=
  ∀ x y : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → ∑ i, y i ^ 2 = 1 → qA A x - qA A y ≤ Λ

/-- `B ⪰ 0` through its quadratic form. -/
def PSDq (B : Matrix (Fin n) (Fin n) ℝ) : Prop := ∀ x : Fin n → ℝ, 0 ≤ qA B x

/-- The shift `Ā = A − (A_{i0 i0} − N) I`, computed by the moment program from the entries of `A`. -/
def shiftA (A : Matrix (Fin n) (Fin n) ℝ) (i0 : Fin n) (N : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => A i j - if i = j then A i0 i0 - N else 0

/-- `N = ⌈Λ⌉₊`. -/
noncomputable def NofL (Λ : ℝ) : ℕ := ⌈Λ⌉₊

/-- `a = 2N`: the bound on the shifted range and on the shifted entries. -/
noncomputable def aA (Λ : ℝ) : ℝ := 2 * (NofL Λ : ℝ)

/-- The truncation order `K = Kof43 (2N) ε`. -/
noncomputable def KqA (Λ ε : ℝ) : ℕ := Kof43 (aA Λ) ε

/-- The program's input vector: the entries of `A`. -/
def matIn (A : Matrix (Fin n) (Fin n) ℝ) : Fin n × Fin n → ℝ := fun ij => A ij.1 ij.2

/-! ## §2 The laws -/

/-- `Z_A = E_σ exp(xᵀAx)`. -/
noncomputable def ZA (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∫ x, Real.exp (qA A x) ∂uniformSphere n

/-- The Bingham law `D(A) ∝ exp(xᵀAx) σ`. -/
noncomputable def binghamA (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : Measure (Fin n → ℝ) :=
  (uniformSphere n).withDensity (fun x => ENNReal.ofReal (Real.exp (qA A x) / ZA n A))

/-- `Z_K = E_σ p_K(xᵀBx)`. -/
noncomputable def ZKA (n K : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∫ x, BstLean.Part37.taylorExp K (qA B x) ∂uniformSphere n

/-- The Taylor law `∝ p_K(xᵀBx) σ`. -/
noncomputable def binghamKA (n K : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) : Measure (Fin n → ℝ) :=
  (uniformSphere n).withDensity (fun x => ENNReal.ofReal (BstLean.Part37.taylorExp K (qA B x) / ZKA n K B))

/-- The surrogate `Q̃(A) = binghamKA n K (shiftA A i0 N)`, `N = ⌈Λ⌉₊`, `K = Kof43 (2N) ε`. -/
noncomputable def surrA (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (i0 : Fin n) (Λ ε : ℝ) :
    Measure (Fin n → ℝ) :=
  binghamKA n (KqA Λ ε) (shiftA A i0 (NofL Λ))

/-- An antipodal law on the sphere (replaces `SignSym`). -/
structure Antipodal (n : ℕ) (μ : Measure (Fin n → ℝ)) : Prop where
  sph : SphLaw n μ
  neg : μ.map (fun x => -x) = μ

/-! ## §3 The mass bound (Lemma M′) -/

/-- `M_j(a, K) = Σ_{t ≤ K} (2a)^t/t! · U″_{j+t}(d)`. -/
noncomputable def MA (j d : ℕ) (a : ℝ) (K : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (K + 1), (2 * a) ^ t / (t.factorial : ℝ) * Upp (j + t) d

/-! ## §4 Allocation and kept sets -/

/-- `A′_U = Σ_{(j,l)} c_s M_j² n^{k−s} / (4 s 4^l)`. -/
noncomputable def AUA (n d k : ℕ) (a : ℝ) (K : ℕ) : ℝ :=
  ∑ jl ∈ levels k, cS n (jl.1 - 2 * jl.2) * MA jl.1 d a K ^ 2 * (n : ℝ) ^ (k - (jl.1 - 2 * jl.2)) /
    (4 * (jl.1 - 2 * jl.2 : ℕ) * 4 ^ jl.2)

/-- `τ′ = A′_U / ((1 − ν) 0.91 P − 0.455 B_fix)`. -/
noncomputable def tauA (n d k : ℕ) (a : ℝ) (K : ℕ) : ℝ :=
  AUA n d k a K / ((1 - nu43) * (91 / 100) * Pn n d - 455 / 1000 * Bfix n k)

/-- `O′_{j,l} = min(#orbits, ⌈M_j² n^{k−s} / (4 s 4^l τ′ ε*)⌉)`. -/
noncomputable def OcntA (n d k : ℕ) (a : ℝ) (K : ℕ) (ε : ℝ) (j l : ℕ) : ℕ :=
  min (Fintype.card (Sym (Mono n d) (j - 2 * l)))
    ⌈MA j d a K ^ 2 * (n : ℝ) ^ (k - (j - 2 * l)) /
      (4 * (j - 2 * l : ℕ) * 4 ^ l * tauA n d k a K * epsS ε)⌉₊

/-- An admissible kept set for level `(j, l)` under `μ`, with the quota `O′` and threshold `τ′`. -/
def KeepOKA (n d k : ℕ) (μ : Measure (Fin n → ℝ)) (ε a : ℝ) (K : ℕ) (j l : ℕ)
    (S : Finset (Multiset (Mono n d))) : Prop :=
  S.card ≤ OcntA n d k a K ε j l ∧ (∀ o ∈ S, Multiset.card o = j - 2 * l) ∧
    (frob (fun w : Fin (j - 2 * l) → Mono n d => RR μ S l w) ≤
      tauA n d k a K * epsS ε * (j - 2 * l : ℕ) * 4 ^ l / (n : ℝ) ^ (k - (j - 2 * l)))

/-- The kept sets under `μ` (build-time control, chosen by `Classical.epsilon`). -/
noncomputable def keepSetA (n d k : ℕ) (μ : Measure (Fin n → ℝ)) (ε a : ℝ) (K : ℕ) (j l : ℕ) :
    Finset (Multiset (Mono n d)) :=
  Classical.epsilon (KeepOKA n d k μ ε a K j l)

/-- The kept sets of the surrogate `Q̃(A)`. -/
noncomputable def keepSet50 (n d k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (i0 : Fin n) (Λ ε : ℝ) :
    ℕ → ℕ → Finset (Multiset (Mono n d)) :=
  keepSetA n d k (surrA n A i0 Λ ε) ε (aA Λ) (KqA Λ ε)

/-- The theorem's branch: `g^{Q̃}_TC` with the kept sets of `Q̃(A)`. -/
noncomputable def gOf50 (k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (i0 : Fin n) (Λ ε f0 : ℝ)
    (T : BstLean.Part41.Tens n) (M : CoefIdxD n d → ℝ) : ℝ :=
  gTCR (surrA n A i0 Λ ε) k (keepSet50 n d k A i0 Λ ε) f0 T M

/-! ## §5 The moment program -/

/-- The moment program's specification at `A'`, for build-time data `i0`, `N`, `Kq` and the kept
sets: on every used key it returns the weight of `binghamKA n Kq (shiftA A' i0 N)`. -/
def MomSpecA {k : ℕ} (pm : Prog (Fin n × Fin n) (BstLean.Part43.KeyF n d k))
    (K : ℕ → ℕ → Finset (Multiset (Mono n d))) (i0 : Fin n) (N Kq : ℕ)
    (A' : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ κ ∈ keys43 k K, pm.eval (matIn A') κ = wKeyR (binghamKA n Kq (shiftA A' i0 N)) K κ

/-- `E_σ x^s = Π_i (s_i − 1)!! / Π_{r < |s|/2} (n + 2r)` (`0` if some exponent is odd), as a rational. -/
noncomputable def sphereMonoA (n : ℕ) (s : Multiset (Fin n)) : ℚ :=
  (∏ i, if Even (s.count i) then ((s.count i - 1).doubleFactorial : ℚ) else 0) /
    ∏ r ∈ Finset.range (Multiset.card s / 2), ((n : ℚ) + 2 * r)

/-- The rational constant of one term of a surrogate moment: `E_σ x^s / t!`. -/
noncomputable def qMomA (n t : ℕ) (s : Multiset (Fin n)) : ℚ := sphereMonoA n s / (t.factorial : ℚ)

/-- A height bound for the moment constants `qMomA n t s` (`t ≤ K`, `|s| ≤ kd + 2K`): the sum of
`|num| + den` over all of them. -/
noncomputable def HA (n d k Kq : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (Kq + 1), ∑ m ∈ Finset.range (k * d + 2 * Kq + 1), ∑ s : Sym (Fin n) m,
    ((qMomA n t (s : Multiset (Fin n))).num.natAbs + (qMomA n t (s : Multiset (Fin n))).den)

/-- `b_M = ⌊log₂ H_A⌋ + 1`, so that every moment constant has `|num|, den < 2^{b_M}`. -/
noncomputable def bA (n d k Kq : ℕ) : ℕ := Nat.log 2 (HA n d k Kq) + 1

/-- The constant of a key: `κ_{j,j/2}` for a scalar key, `κ_{j,l} μ_{s,i} |orbit q|` otherwise. -/
noncomputable def cKeyA {k : ℕ} (κ : BstLean.Part43.KeyF n d k) : ℚ :=
  if 2 * κ.2.1.1 = κ.1.1 then BstLean.Part41.kapQ n d κ.1.1 κ.2.1.1
  else BstLean.Part41.kapQ n d κ.1.1 κ.2.1.1 * BstLean.Part41.muQ n d (κ.1.1 - 2 * κ.2.1.1) κ.2.2.1.1 *
    (BstLean.Part41.orbSize κ.2.2.2.2.1 : ℚ)

/-- `b_K = ⌊log₂ Σ_κ (|num c_κ| + den c_κ)⌋ + 1`, so that every key constant has `|num|, den < 2^{b_K}`. -/
noncomputable def bKA (n d k : ℕ) : ℕ :=
  Nat.log 2 (∑ κ : BstLean.Part43.KeyF n d k, ((cKeyA κ).num.natAbs + (cKeyA κ).den)) + 1

/-- The cost of one surrogate moment `E_{Q̃} x^s` by direct expansion: numerator and denominator,
each a sum over `t ≤ K` and `c ∈ ([n] × [n])^t` of `qMomA · Π_r Ā_{c_r}` (one constant of height
`< 2^{b_M}` and at most `K + 2` operations per term), then one division. -/
noncomputable def termA (n d k Kq : ℕ) : ℕ :=
  2 * (Kq + 1) * (n + 1) ^ (2 * Kq) * (4 * bA n d k Kq + Kq + 2) + 1

/-- The proved bound on the moment program's cost: the shift (`N` from `1`, then `n` diagonal
updates), then per used key at most `#Mono^k` moments (`termA` each), their two levels of sums
(at most `2 #Mono^k` additions), and one key constant with one product. -/
noncomputable def onceCostA (n d k Kq N : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d))) : ℝ :=
  (N : ℝ) + 2 * n +
    ((keys43 (n := n) (d := d) k K).card : ℝ) *
      ((Fintype.card (Mono n d) : ℝ) ^ k * (termA n d k Kq + 2) + 4 * bKA n d k + 1)

/-! ## §6 Budget and the counter -/

/-- `Φ′(n) = p_sb + 2e^{−x} + β + L τ′ / ((1 − ξ)² γ²)`. -/
noncomputable def Phi50 (n d k : ℕ) (q : Params43) (t a : ℝ) (K : ℕ) : ℝ :=
  q.psb + 2 * Real.exp (-q.x) + q.beta + Lk k * tauA n d k a K / ((1 - xi43) ^ 2 * gam48 n d k q t ^ 2)

/-- The conditions of the proof of Theorem GA′ at `n`, failure budget `δ`, small-ball level `t`,
mass parameters `a`, `K`. None depends on `A`, `f`. -/
def BudgetOK50 (n d k : ℕ) (q : Params43) (δ t a : ℝ) (K : ℕ) : Prop :=
  2 ≤ n ∧ 2 ≤ d ∧ 0 < tauA n d k a K ∧
  0 < q.psb ∧ 0 < q.x ∧ 0 < q.beta ∧ 0 < q.eta ∧
  (1 + 1 / q.eta) * thetaT n d k < 1 ∧ etaR n d q.x < 1 ∧ 0 < Kc n d k q.eta ∧
  0 < gam48 n d k q t ∧ 455 / 1000 * Bfix n k < (1 - nu43) * (91 / 100) * Pn n d ∧
  Phi50 n d k q t a K ≤ δ

/-- The amortization threshold `k₀′ = ⌈C′_once / (ν 𝔅(ε))⌉`. -/
noncomputable def k0A (n d k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (i0 : Fin n) (Λ ε : ℝ) : ℕ :=
  ⌈onceCostA n d k (KqA Λ ε) (NofL Λ) (keepSet50 n d k A i0 Λ ε) / (nu43 * baseline n d ε)⌉₊

end BstLean.Part50
