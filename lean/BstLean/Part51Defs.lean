import BstLean.Part50Defs

/-!
# Part 51, wave 0: frozen definitions — Theorem G for general exponential families (Claim EF)

Source: `delegations/answers/omEF-opus-prover.md` and `omEF-codex-disprover.md`. Specification:
`delegations/answers/p51-spec-opus.md`. This file holds definitions only. Provers must not edit it,
and must not use `native_decide` or `axiom` anywhere.

Conventions. Part 41, 43, 48 and 50 names are reused. `k = d_f`, `d = d_M`, `r` is the degree bound
of the exponent.

* **Exponents.** A *linear letter* is `o : Option (Fin n)`: `none` is the constant `1`, `some i` is
  `x_i` (`xl`). A word is `w : Fin r → Option (Fin n)`. The exponent with coefficient vector
  `b : WordR n r → ℝ` is `polR b x = Σ_w b_w Π_k xl x (w k)`. Every real polynomial of degree `≤ r` on
  `ℝ^n` is `polR b` for some `b` (expand each monomial and pad it with `none`). The program reads `b`.
* **Oscillation.** `OscLE U Λ`: for all unit `x, y`, `U x − U y ≤ Λ`. `CoefLE b B`: `|b_w| ≤ B` for all `w`.
  `NonnegS V`: `V ≥ 0` on the sphere.
* **The shift (computed by the program).** `evalE b i0 = polR b (e_{i0})` written as a sum of input
  coefficients (`inE i0 w`: every letter of `w` is `none` or `some i0`). `shiftR b i0 N` subtracts
  `evalE b i0 − N` from the coefficient of the constant word `w0 = (none, …, none)`. On the sphere,
  `OscLE (polR b) Λ` and `Λ ≤ N` give `0 ≤ polR (shiftR b i0 N) ≤ 2N`.
* **The laws.** `lawE n U ∝ exp(U x)·σ` (the target `D_u`), `lawKE n K V ∝ p_K(V x)·σ` (Taylor law).
  For a matrix `A`, `lawE n (qA A)` is `binghamA n A` by definition.
  `surrE n b i0 Λ ε = lawKE n (KqA Λ ε) (polR (shiftR b i0 (NofL Λ)))` is the surrogate `Q̃_u`.
* **Mass (Lemma M‴, linear letters).** `ME j d r a K = Σ_{t ≤ K} a^t/t! · U″_{j+rt}(d)`.
  The mass of the surrogate is `≤ ME j d r a K` for every representation `β` of the shifted exponent
  on the sphere with `|β_w| ≤ a`. EF-B uses `β = shiftR b`, `a = aB r B Λ`. The full claim uses the
  representation of Lemma R, `a = aR r Λ = (r^r + 2)·N`.
* **Allocation, budget.** `AUE`, `tauE`, `OcntE`, `KeepOKE`, `keepSetE`, `PhiE`, `BudgetOKE` are
  Part 50's `AUA`, `tauA`, `OcntA`, `KeepOKA`, `keepSetA`, `Phi50`, `BudgetOK50` with `ME j d r a K` in
  place of `MA j d a K`.
* **Moment program.** Input type `WordR n r`. `MomSpecE`, `onceCostE`, `k0E` are Part 50's
  `MomSpecA`, `onceCostA`, `k0A` for word inputs (moment constants up to length `kd + rK`).
-/

namespace BstLean.Part51

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono frob levels cS Bfix Pn epsS baseline thetaT Kc etaR Lk bQ)
open BstLean.Part43 (Params43 RR Upp Kof43 nu43 xi43 keys43 wKeyR gTCR)
open BstLean.Part48 (gam48)
open BstLean.Part50 (NofL KqA sphereMonoA cKeyA bKA)

variable {n d : ℕ}

/-! ## §1 Exponents, oscillation, shift -/

/-- Linear letters: `none` is `1`, `some i` is `x_i`. -/
abbrev Lin (n : ℕ) := Option (Fin n)

/-- Words of `r` linear letters. -/
abbrev WordR (n r : ℕ) := Fin r → Lin n

/-- The value of a linear letter. -/
def xl (x : Fin n → ℝ) : Lin n → ℝ
  | none => 1
  | some i => x i

/-- The exponent `u_b(x) = Σ_w b_w Π_k xl x (w k)` (degree `≤ r`). -/
noncomputable def polR {r : ℕ} (b : WordR n r → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ w, b w * ∏ k, xl x (w k)

/-- `sup_S U − inf_S U ≤ Λ`. -/
def OscLE (U : (Fin n → ℝ) → ℝ) (Λ : ℝ) : Prop :=
  ∀ x y : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → ∑ i, y i ^ 2 = 1 → U x - U y ≤ Λ

/-- A coefficient bound. -/
def CoefLE {r : ℕ} (b : WordR n r → ℝ) (B : ℝ) : Prop := ∀ w, |b w| ≤ B

/-- `V ≥ 0` on the sphere. -/
def NonnegS (V : (Fin n → ℝ) → ℝ) : Prop := ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → 0 ≤ V x

/-- Every letter of `w` is `none` or `some i0` (so `Π_k xl e_{i0} (w k) = 1`; otherwise it is `0`). -/
def inE {r : ℕ} (i0 : Fin n) (w : WordR n r) : Prop := ∀ k, w k = none ∨ w k = some i0

instance {r : ℕ} (i0 : Fin n) (w : WordR n r) : Decidable (inE i0 w) := by
  unfold inE; infer_instance

/-- `u_b(e_{i0})` as a sum of input coefficients. -/
noncomputable def evalE {r : ℕ} (b : WordR n r → ℝ) (i0 : Fin n) : ℝ :=
  ∑ w, if inE i0 w then b w else 0

/-- The constant word. -/
def w0 {r : ℕ} : WordR n r := fun _ => none

/-- The shifted coefficients: `v = u_b − (u_b(e_{i0}) − N)`. -/
noncomputable def shiftR {r : ℕ} (b : WordR n r → ℝ) (i0 : Fin n) (N : ℕ) : WordR n r → ℝ :=
  fun w => b w - if w = w0 then evalE b i0 - N else 0

/-- The EF-B coefficient bound of the shifted exponent: `(2^r + 1) B + N`. -/
noncomputable def aB (r : ℕ) (B Λ : ℝ) : ℝ := (2 ^ r + 1) * B + NofL Λ

/-- The coefficient bound of Lemma R: `(r^r + 2) N`. -/
noncomputable def aR (r : ℕ) (Λ : ℝ) : ℝ := ((r : ℝ) ^ r + 2) * NofL Λ

/-! ## §2 The laws -/

/-- `Z_U = E_σ exp(U)`. -/
noncomputable def ZE (n : ℕ) (U : (Fin n → ℝ) → ℝ) : ℝ := ∫ x, Real.exp (U x) ∂uniformSphere n

/-- The exponential-family law `D_U ∝ exp(U) σ`. -/
noncomputable def lawE (n : ℕ) (U : (Fin n → ℝ) → ℝ) : Measure (Fin n → ℝ) :=
  (uniformSphere n).withDensity (fun x => ENNReal.ofReal (Real.exp (U x) / ZE n U))

/-- `Z_K = E_σ p_K(V)`. -/
noncomputable def ZKE (n K : ℕ) (V : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ x, BstLean.Part37.taylorExp K (V x) ∂uniformSphere n

/-- The Taylor law `∝ p_K(V) σ`. -/
noncomputable def lawKE (n K : ℕ) (V : (Fin n → ℝ) → ℝ) : Measure (Fin n → ℝ) :=
  (uniformSphere n).withDensity (fun x => ENNReal.ofReal (BstLean.Part37.taylorExp K (V x) / ZKE n K V))

/-- The surrogate `Q̃_u = lawKE n K (polR (shiftR b i0 N))`, `N = ⌈Λ⌉₊`, `K = Kof43 (2N) ε`. -/
noncomputable def surrE (n : ℕ) {r : ℕ} (b : WordR n r → ℝ) (i0 : Fin n) (Λ ε : ℝ) :
    Measure (Fin n → ℝ) :=
  lawKE n (KqA Λ ε) (polR (shiftR b i0 (NofL Λ)))

/-! ## §3 The mass bound (Lemma M‴) -/

/-- `M_j = Σ_{t ≤ K} a^t/t! · U″_{j+rt}(d)`. -/
noncomputable def ME (j d r : ℕ) (a : ℝ) (K : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (K + 1), a ^ t / (t.factorial : ℝ) * Upp (j + t * r) d

/-! ## §4 Allocation and kept sets -/

noncomputable def AUE (n d k r : ℕ) (a : ℝ) (K : ℕ) : ℝ :=
  ∑ jl ∈ levels k, cS n (jl.1 - 2 * jl.2) * ME jl.1 d r a K ^ 2 * (n : ℝ) ^ (k - (jl.1 - 2 * jl.2)) /
    (4 * (jl.1 - 2 * jl.2 : ℕ) * 4 ^ jl.2)

noncomputable def tauE (n d k r : ℕ) (a : ℝ) (K : ℕ) : ℝ :=
  AUE n d k r a K / ((1 - nu43) * (91 / 100) * Pn n d - 455 / 1000 * Bfix n k)

noncomputable def OcntE (n d k r : ℕ) (a : ℝ) (K : ℕ) (ε : ℝ) (j l : ℕ) : ℕ :=
  min (Fintype.card (Sym (Mono n d) (j - 2 * l)))
    ⌈ME j d r a K ^ 2 * (n : ℝ) ^ (k - (j - 2 * l)) /
      (4 * (j - 2 * l : ℕ) * 4 ^ l * tauE n d k r a K * epsS ε)⌉₊

def KeepOKE (n d k r : ℕ) (μ : Measure (Fin n → ℝ)) (ε a : ℝ) (K : ℕ) (j l : ℕ)
    (S : Finset (Multiset (Mono n d))) : Prop :=
  S.card ≤ OcntE n d k r a K ε j l ∧ (∀ o ∈ S, Multiset.card o = j - 2 * l) ∧
    (frob (fun w : Fin (j - 2 * l) → Mono n d => RR μ S l w) ≤
      tauE n d k r a K * epsS ε * (j - 2 * l : ℕ) * 4 ^ l / (n : ℝ) ^ (k - (j - 2 * l)))

noncomputable def keepSetE (n d k r : ℕ) (μ : Measure (Fin n → ℝ)) (ε a : ℝ) (K : ℕ) (j l : ℕ) :
    Finset (Multiset (Mono n d)) :=
  Classical.epsilon (KeepOKE n d k r μ ε a K j l)

/-- The kept sets of the surrogate `Q̃_u`, at the mass parameter `a`. -/
noncomputable def keepSet51 (n d k : ℕ) {r : ℕ} (b : WordR n r → ℝ) (i0 : Fin n) (Λ ε a : ℝ) :
    ℕ → ℕ → Finset (Multiset (Mono n d)) :=
  keepSetE n d k r (surrE n b i0 Λ ε) ε a (KqA Λ ε)

/-- The theorem's branch. -/
noncomputable def gOf51 (k : ℕ) {r : ℕ} (b : WordR n r → ℝ) (i0 : Fin n) (Λ ε a f0 : ℝ)
    (T : BstLean.Part41.Tens n) (M : CoefIdxD n d → ℝ) : ℝ :=
  gTCR (surrE n b i0 Λ ε) k (keepSet51 n d k b i0 Λ ε a) f0 T M

/-! ## §5 The moment program -/

/-- The moment program's specification at `b'`: on every used key it returns the weight of
`lawKE n Kq (polR (shiftR b' i0 N))`. -/
def MomSpecE {k r : ℕ} (pm : Prog (WordR n r) (BstLean.Part43.KeyF n d k))
    (K : ℕ → ℕ → Finset (Multiset (Mono n d))) (i0 : Fin n) (N Kq : ℕ) (b' : WordR n r → ℝ) : Prop :=
  ∀ κ ∈ keys43 k K, pm.eval b' κ = wKeyR (lawKE n Kq (polR (shiftR b' i0 N))) K κ

/-- The moment constants `E_σ x^s / t!` (`t ≤ K`, `|s| ≤ kd + rK`): the sum of `|num| + den`. -/
noncomputable def HE (n d k r Kq : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (Kq + 1), ∑ m ∈ Finset.range (k * d + r * Kq + 1), ∑ s : Sym (Fin n) m,
    ((BstLean.Part50.qMomA n t (s : Multiset (Fin n))).num.natAbs +
      (BstLean.Part50.qMomA n t (s : Multiset (Fin n))).den)

noncomputable def bE (n d k r Kq : ℕ) : ℕ := Nat.log 2 (HE n d k r Kq) + 1

/-- The cost of one surrogate moment by direct expansion over `t ≤ K` and `c ∈ (WordR n r)^t`. -/
noncomputable def termE (n d k r Kq : ℕ) : ℕ :=
  2 * (Kq + 1) * (n + 1) ^ (r * Kq) * (4 * bE n d k r Kq + Kq + 2) + 1

/-- The proved bound on the moment program's cost: the shift (`N` from `1`, the sum `evalE`, two
subtractions), then per used key at most `#Mono^k` moments. -/
noncomputable def onceCostE (n d k r Kq N : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d))) : ℝ :=
  (N : ℝ) + (n + 1 : ℝ) ^ r + 2 +
    ((keys43 (n := n) (d := d) k K).card : ℝ) *
      ((Fintype.card (Mono n d) : ℝ) ^ k * (termE n d k r Kq + 2) + 4 * bKA n d k + 1)

/-! ## §6 Budget and the counter -/

noncomputable def PhiE (n d k : ℕ) (q : Params43) (t : ℝ) (r : ℕ) (a : ℝ) (K : ℕ) : ℝ :=
  q.psb + 2 * Real.exp (-q.x) + q.beta + Lk k * tauE n d k r a K / ((1 - xi43) ^ 2 * gam48 n d k q t ^ 2)

/-- The conditions of the proof at `n` (none depends on the exponent or on `f`). The level `t` is the
small-ball level times `e^{−Λ}` (Lemma F_u). -/
def BudgetOKE (n d k : ℕ) (q : Params43) (δ t : ℝ) (r : ℕ) (a : ℝ) (K : ℕ) : Prop :=
  2 ≤ n ∧ 2 ≤ d ∧ 0 < tauE n d k r a K ∧
  0 < q.psb ∧ 0 < q.x ∧ 0 < q.beta ∧ 0 < q.eta ∧
  (1 + 1 / q.eta) * thetaT n d k < 1 ∧ etaR n d q.x < 1 ∧ 0 < Kc n d k q.eta ∧
  0 < gam48 n d k q t ∧ 455 / 1000 * Bfix n k < (1 - nu43) * (91 / 100) * Pn n d ∧
  PhiE n d k q t r a K ≤ δ

/-- The amortization threshold `k₀ = ⌈C_once / (ν 𝔅(ε))⌉`. -/
noncomputable def k0E (n d k : ℕ) {r : ℕ} (b : WordR n r → ℝ) (i0 : Fin n) (Λ ε a : ℝ) : ℕ :=
  ⌈onceCostE n d k r (KqA Λ ε) (NofL Λ) (keepSet51 n d k b i0 Λ ε a) / (nu43 * baseline n d ε)⌉₊

end BstLean.Part51
