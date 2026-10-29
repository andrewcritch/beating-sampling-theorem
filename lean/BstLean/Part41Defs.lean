import BstLean.Part36Defs
import BstLean.CostModel

/-!
# Part 41, wave 0: frozen definitions for Theorem TC-LF (every `d_M ≥ d_f ≥ 2`, every `f`, `θ = 0`)

Paper: `proofs/option-m/41-arbitrary-degree.tex`. Specification: `delegations/answers/p41-spec-opus.md`.
This file holds definitions only. Provers must not edit it, and must not use `native_decide` anywhere.

Conventions.
* `k = d_f`, `d = d_M`. The law of `x` is Part 29's `uniformSphere n` (`θ = 0`).
* `Mono n d = Σ i : Fin (d+1), Sym (Fin n) i` indexes the `N = C(n+d, d)` raw monomials, the constant
  included. `m(x) = M φ(x)` is Part 36's `mapMD`, with `M : CoefIdxD n d → ℝ`; `colM M p` is the column
  `M_p ∈ ℝⁿ`. `D = DD n d = nN` (Part 36), and `P = D` is the per-sample cost.
* A tensor of order `j` on `ι` is a function `(Fin j → ι) → R`. `contr A v = Σ_w A w ∏_t v t (w t)` is
  `A[v₁, …, v_j]`. `trL l A` contracts the slot pairs `(0,1), …, (2l−2, 2l−1)`; its free slots are the
  slots `2l, …, j−1`, in order. `frob A = Σ_w (A w)²`.
* `f = f₀ + Σ_{j=1}^k T_j[y^{⊗j}]`, `T : (j : ℕ) → (Fin j → Fin n) → ℝ`. Only `T j` for `1 ≤ j ≤ k`
  enter. The headline asks each `T j` to be symmetric (`TSymm`) and `T k ≠ 0`.
* The moment constants are exact rationals: `sphMomQ e = E x^e = ∏ (e_a − 1)!!/ρ_{|e|/2}(n)` and
  `HQ l w = H_{j,l}[w] = E[‖φ‖^{2l} φ_{w₁} ⋯ φ_{w_s}]` (`s = j − 2l`). A kept set is a finset of
  multisets (orbits). `HKQ K l w` keeps the entries whose orbit `mset w` is in `K`; `RQ = HQ − HKQ`.
* The kept set of level `(j, l)` is chosen by the predicate `KeepOK` (card `≤ O_{j,l}`, orbits of size
  `s`, `‖R_{j,l}‖² ≤ τ ε*² n^{−(k−s)} s 4^l`), by `Classical.epsilon`. `kept_exists` (wave 1) proves that
  such a set exists; the paper's top-`O` set is one.
* `gTC` is the paper's formula for the branch (the display after Definition `branch`), with ordered
  sums. `gProg` is the branch as a straight-line program in `BstLean.Cost`; its rational constants
  (the weights `κ μ |orbit| (tr^i H^K)[q]`) are "heavy" constants, each charged `n` operations in
  `chargedCost`. `inline_consts` and `gProg_heights` (wave 1) replace each heavy constant by a
  subprogram from the constants `0` and `1` alone, so the headline program uses no other constant.
  This replaces Lemma MC (see the specification, flag 2).
* The budget, floor and failure constants are the paper's (Lemmas C, LF, LF-ball, upper tails, the
  proof of Theorem TC-LF), with two changes listed in the specification: the trace cost
  `Σ n^{j−2m}(n^m − 1)` in `Bfix` and the crude contamination constant `PsiB` in `XiC`.
-/

namespace BstLean.Part41

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD monoVal rhoD)

variable {n d : ℕ}

/-! ## §1 Monomials and columns -/

/-- The raw monomials of degree `≤ d`: a degree `i ≤ d` and a multiset `β` of size `i`. -/
abbrev Mono (n d : ℕ) := Σ i : Fin (d + 1), Sym (Fin n) i

instance : Inhabited (Mono n d) := ⟨⟨0, Sym.nil⟩⟩

/-- `φ_p(x) = x^β`. -/
noncomputable def phiM (x : Fin n → ℝ) (p : Mono n d) : ℝ := monoVal x p.2.1

/-- `‖φ(x)‖² = Σ_p φ_p(x)²`. -/
noncomputable def phiSq (d : ℕ) (x : Fin n → ℝ) : ℝ := ∑ p : Mono n d, phiM x p ^ 2

/-- The exponent of monomial `p` at coordinate `a`. -/
def expo (p : Mono n d) (a : Fin n) : ℕ := p.2.1.count a

/-- The column `M_p ∈ ℝⁿ` of monomial `p`. -/
def colM (M : CoefIdxD n d → ℝ) (p : Mono n d) : Fin n → ℝ := fun a => M ⟨p.1, (p.2, a)⟩

/-- `N = |Mono n d| = C(n+d, d)` as a real number. -/
noncomputable def NN (n d : ℕ) : ℝ := (Fintype.card (Mono n d) : ℝ)

/-! ## §2 Tensors -/

section tensors
variable {ι R : Type*}

/-- `A[v₁, …, v_j] = Σ_w A w ∏_t v_t(w_t)`. -/
def contr [Fintype ι] [CommSemiring R] {j : ℕ} (A : (Fin j → ι) → R) (v : Fin j → ι → R) : R :=
  ∑ w : Fin j → ι, A w * ∏ t, v t (w t)

/-- The word of order `j` whose slots `2t, 2t+1` (`t < l`) hold `c t` and whose slots `≥ 2l` hold `w`. -/
def glue (j l : ℕ) (c : Fin l → ι) (w : Fin (j - 2 * l) → ι) : Fin j → ι := fun t =>
  if h : t.1 < 2 * l then c ⟨t.1 / 2, by omega⟩ else w ⟨t.1 - 2 * l, by have := t.2; omega⟩

/-- `tr^l A`: contract the slot pairs `(2t, 2t+1)`, `t < l`. -/
def trL [Fintype ι] [AddCommMonoid R] {j : ℕ} (l : ℕ) (A : (Fin j → ι) → R) :
    (Fin (j - 2 * l) → ι) → R := fun w => ∑ c : Fin l → ι, A (glue j l c w)

/-- `‖A‖² = Σ_w (A w)²`. -/
def frob [Fintype ι] [CommSemiring R] {j : ℕ} (A : (Fin j → ι) → R) : R := ∑ w, A w ^ 2

/-- `A` is a symmetric tensor. -/
def IsSymmT {j : ℕ} (A : (Fin j → ι) → R) : Prop := ∀ (σ : Equiv.Perm (Fin j)) (w : Fin j → ι), A (w ∘ σ) = A w

/-- The orbit (multiset of entries) of a word. -/
def mset {j : ℕ} (w : Fin j → ι) : Multiset ι := (Finset.univ : Finset (Fin j)).val.map w

/-- A word of length `a` that lists the multiset `q` (when `card q = a`). -/
noncomputable def wordOf [Inhabited ι] (a : ℕ) (q : Multiset ι) : Fin a → ι := fun t => q.toList.getD t.1 default

end tensors

/-! ## §3 The function `f`, `B`, the spread -/

/-- The tensors of `f`: `T j` is the degree-`j` part. -/
abbrev Tens (n : ℕ) := (j : ℕ) → (Fin j → Fin n) → ℝ

/-- Every `T j`, `1 ≤ j ≤ k`, is symmetric. -/
def TSymm (k : ℕ) (T : Tens n) : Prop := ∀ j, 1 ≤ j → j ≤ k → IsSymmT (T j)

/-- `f(y) = f₀ + Σ_{j=1}^k T_j[y, …, y]`. -/
def fval (k : ℕ) (f0 : ℝ) (T : Tens n) (y : Fin n → ℝ) : ℝ :=
  f0 + ∑ j ∈ Finset.Icc 1 k, contr (T j) (fun _ => y)

/-- `B(M) = E_x f(M φ(x))`, `x` uniform on the sphere. -/
noncomputable def Bof (k : ℕ) (f0 : ℝ) (T : Tens n) (M : CoefIdxD n d → ℝ) : ℝ :=
  ∫ x, fval k f0 T (mapMD M x) ∂uniformSphere n

/-- `Var_μ h`. -/
noncomputable def varU (μ : Measure (Fin n → ℝ)) (h : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ x, (h x - ∫ y, h y ∂μ) ^ 2 ∂μ

/-- `sd_μ h = √Var_μ h`. -/
noncomputable def sdU (μ : Measure (Fin n → ℝ)) (h : (Fin n → ℝ) → ℝ) : ℝ := Real.sqrt (varU μ h)

/-- `Var_x f(M φ(x))`. -/
noncomputable def varF (k : ℕ) (f0 : ℝ) (T : Tens n) (M : CoefIdxD n d → ℝ) : ℝ :=
  varU (uniformSphere n) (fun x => fval k f0 T (mapMD M x))

/-! ## §4 Exact rational constants -/

/-- `ρ_m(n) = n(n+2)⋯(n+2m−2)` in `ℚ`. -/
def rhoQ (n m : ℕ) : ℚ := ∏ t ∈ Finset.range m, ((n : ℚ) + 2 * t)

/-- `E x^e` on the unit sphere: `∏_a (e_a − 1)!! / ρ_{|e|/2}(n)` if every `e_a` is even, else `0`. -/
noncomputable def sphMomQ (e : Fin n → ℕ) : ℚ := by
  classical
  exact if ∀ a, Even (e a) then
    (∏ a, ((e a - 1).doubleFactorial : ℚ)) / rhoQ n ((∑ a, e a) / 2) else 0

/-- `H_{j,l}[w] = E[‖φ‖^{2l} φ_{w₁} ⋯ φ_{w_s}]`, `w : Fin s → Mono n d`. -/
noncomputable def HQ {s : ℕ} (l : ℕ) (w : Fin s → Mono n d) : ℚ :=
  ∑ c : Fin l → Mono n d, sphMomQ (fun a => ∑ t, 2 * expo (c t) a + ∑ t, expo (w t) a)

/-- The kept part `H^K`. -/
noncomputable def HKQ {s : ℕ} (K : Finset (Multiset (Mono n d))) (l : ℕ) (w : Fin s → Mono n d) : ℚ := by
  classical
  exact if mset w ∈ K then HQ l w else 0

/-- The residual `R = H − H^K ≥ 0`. -/
noncomputable def RQ {s : ℕ} (K : Finset (Multiset (Mono n d))) (l : ℕ) (w : Fin s → Mono n d) : ℚ :=
  HQ l w - HKQ K l w

/-- `c_{j,l} = j! / (l! 2^l (j−2l)!)`. -/
def cQ (j l : ℕ) : ℚ := (j.factorial : ℚ) / ((l.factorial : ℚ) * 2 ^ l * ((j - 2 * l).factorial : ℚ))

/-- `D = |CoefIdxD n d| = nN` in `ℚ`. -/
def DQ (n d : ℕ) : ℚ := (Fintype.card (CoefIdxD n d) : ℚ)

/-- `κ_{j,l} = c_{j,l} / ∏_{i<l} (D + 2s + 2i)`, `s = j − 2l`. -/
def kapQ (n d j l : ℕ) : ℚ :=
  cQ j l / ∏ i ∈ Finset.range l, (DQ n d + 2 * ((j - 2 * l : ℕ) : ℚ) + 2 * i)

/-- `μ_{s,i} = (−1)^i c_{s,i} / ∏_{m=1}^{i} (D + 2s − 2 − 2m)`. -/
def muQ (n d s i : ℕ) : ℚ :=
  (-1) ^ i * cQ s i / ∏ m ∈ Finset.Icc 1 i, (DQ n d + 2 * (s : ℚ) - 2 - 2 * m)

/-! ## §5 The branch `g_TC` (Definition `branch`, the display after it) -/

/-- The levels `(j, l)` with `1 ≤ j ≤ k` and `s = j − 2l ≥ 1`. -/
def levels (k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 k ×ˢ Finset.range (k + 1)).filter fun jl => 2 * jl.2 < jl.1

/-- `g_TC(M)`, for kept sets `K j l`:
`f₀ + Σ_{j even} κ_{j,j/2} tr^{j/2}T_j H_{j,j/2}
  + Σ_{(j,l)} κ_{j,l} Σ_{i ≤ s/2} μ_{s,i} Σ_{w} (tr^i H^K_{j,l})[w] · (tr^{l+i} T_j)[M_{w₁}, …]`
(at `‖M‖ = 1`, `⟨π₀ C, M^{⊗s}⟩ = Σ_i μ_{s,i} ⟨tr^i C, M^{⊗(s−2i)}⟩`). -/
noncomputable def gTC (k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d))) (f0 : ℝ) (T : Tens n)
    (M : CoefIdxD n d → ℝ) : ℝ :=
  f0 + ∑ j ∈ (Finset.Icc 1 k).filter (fun j => Even j),
      (kapQ n d j (j / 2) : ℝ) * (HQ (n := n) (d := d) (s := j - 2 * (j / 2)) (j / 2) (fun _ => default) : ℝ) *
        contr (trL (j / 2) (T j)) (fun _ _ => 0)
    + ∑ jl ∈ levels k, (kapQ n d jl.1 jl.2 : ℝ) *
      ∑ i ∈ Finset.range ((jl.1 - 2 * jl.2) / 2 + 1), (muQ n d (jl.1 - 2 * jl.2) i : ℝ) *
        ∑ w : Fin (jl.1 - 2 * jl.2 - 2 * i) → Mono n d,
          ((trL i (HKQ (s := jl.1 - 2 * jl.2) (K jl.1 jl.2) jl.2) w : ℚ) : ℝ) *
            contr (trL (jl.2 + i) (T jl.1)) (fun t => colM M (w ⟨t.1, by have := t.2; omega⟩))

/-! ## §6 The error tensors (Lemma E) -/

/-- `‖W_s‖²`, `W_s = Σ_{l : s+2l ≤ k} κ_{s+2l,l} tr^l T_{s+2l} ⊗ R_{s+2l,l}` on the combined index. -/
noncomputable def WfrobSq (k s : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d))) (T : Tens n) : ℝ :=
  ∑ a : Fin s → Fin n, ∑ p : Fin s → Mono n d,
    (∑ l ∈ (Finset.range (k + 1)).filter (fun l => s + 2 * l ≤ k),
      (kapQ n d (s + 2 * l) l : ℝ) * trL l (T (s + 2 * l)) (fun t => a ⟨t.1, by have := t.2; omega⟩) *
        (RQ (K (s + 2 * l) l) l (fun t : Fin (s + 2 * l - 2 * l) => p ⟨t.1, by have := t.2; omega⟩) : ℝ)) ^ 2

/-! ## §7 Weighted norms of `f` -/

/-- `‖a_{j,l}‖² = c_{j,l}² D^{−j} ‖tr^l T_j‖²`. -/
noncomputable def aSq (n d : ℕ) (T : Tens n) (j l : ℕ) : ℝ :=
  (cQ j l : ℝ) ^ 2 / DD n d ^ j * frob (trL l (T j))

/-- `𝒩(f) = Σ_{(j,l), s ≥ 1} n^{−(k−s)} s! s 4^l ‖a_{j,l}‖²`. -/
noncomputable def Nn (n d k : ℕ) (T : Tens n) : ℝ :=
  ∑ jl ∈ levels k, ((jl.1 - 2 * jl.2).factorial : ℝ) * (jl.1 - 2 * jl.2 : ℕ) * 4 ^ jl.2 *
    aSq n d T jl.1 jl.2 / (n : ℝ) ^ (k - (jl.1 - 2 * jl.2))

/-- `t_j = n^{−(k−j)} j! j ‖a_{j,0}‖²`. -/
noncomputable def tj (n d k : ℕ) (T : Tens n) (j : ℕ) : ℝ :=
  (j.factorial : ℝ) * j * aSq n d T j 0 / (n : ℝ) ^ (k - j)

/-! ## §8 The mass bound `Ŝ_j` (Lemma `mass`) -/

/-- `G̃(t) = Σ_{a ∈ {0..d}^j, a ≠ 0, |a| even} (|a| − 1)!! t^a`. -/
noncomputable def Gt (j d : ℕ) : MvPolynomial (Fin j) ℚ := by
  classical
  exact ∑ a : Fin j → Fin (d + 1),
    if (∑ i, (a i : ℕ)) ≠ 0 ∧ Even (∑ i, (a i : ℕ)) then
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (a i : ℕ))
        (((∑ i, (a i : ℕ)) - 1).doubleFactorial : ℚ)
    else 0

/-- `g[s, m]`: the sum of the coefficients of `G̃^s` of total degree `2m` with every exponent `≤ d`. -/
noncomputable def gsm (j d s m : ℕ) : ℚ := by
  classical
  exact ∑ e ∈ (Gt j d ^ s).support,
    if (∀ i, e i ≤ d) ∧ e.sum (fun _ b => b) = 2 * m then (Gt j d ^ s).coeff e else 0

/-- `Ŝ_j(x) = 1 + Σ_{s ≥ 1, m} g[s,m] x^{s−m}/s!`. -/
noncomputable def Shat (j d : ℕ) (x : ℝ) : ℝ :=
  1 + ∑ s ∈ Finset.Icc 1 (j * d), ∑ m ∈ Finset.range (j * d + 1),
    (gsm j d s m : ℝ) * x ^ s / (x ^ m * (s.factorial : ℝ))

/-- `S_{j,l} = Σ_w |H_{j,l}[w]|`, the `ℓ¹` mass of `H_{j,l}` (`s = j − 2l`). -/
noncomputable def massH (n d j l : ℕ) : ℝ :=
  ∑ w : Fin (j - 2 * l) → Mono n d, |(HQ (n := n) (d := d) l w : ℝ)|

/-! ## §9 Cost, allocation, precision (Lemma C) -/

/-- `C_orb(a) = (2n−1)(n^a − 1)/(n − 1)` (`a ≥ 1`), `C_orb(0) = 0`. -/
noncomputable def Corb (n a : ℕ) : ℝ :=
  if a = 0 then 0 else (2 * (n : ℝ) - 1) * ((n : ℝ) ^ a - 1) / ((n : ℝ) - 1)

/-- `c_s = n + Σ_{i ≤ s/2} C(s, 2i) (C_orb(s − 2i) + 2n + 8)`, the cost of one kept orbit. -/
noncomputable def cS (n s : ℕ) : ℝ :=
  n + ∑ i ∈ Finset.range (s / 2 + 1), ((s.choose (2 * i) : ℕ) : ℝ) * (Corb n (s - 2 * i) + 2 * n + 8)

/-- `A(n) = Σ_{(j,l)} c_s Ŝ_j² n^{k−s} / (4 s 4^l)`. -/
noncomputable def Afun (n d k : ℕ) : ℝ :=
  ∑ jl ∈ levels k, cS n (jl.1 - 2 * jl.2) * Shat jl.1 d n ^ 2 * (n : ℝ) ^ (k - (jl.1 - 2 * jl.2)) /
    (4 * (jl.1 - 2 * jl.2 : ℕ) * 4 ^ jl.2)

/-- `B_fix = 1 + Σ c_s + Σ_j Σ_{m=1}^{j/2} n^{j−2m}(n^m − 1) + k³(n+5) + k(n+3)`. -/
noncomputable def Bfix (n k : ℕ) : ℝ :=
  1 + ∑ jl ∈ levels k, cS n (jl.1 - 2 * jl.2) +
    ∑ j ∈ Finset.Icc 1 k, ∑ m ∈ Finset.Icc 1 (j / 2), (n : ℝ) ^ (j - 2 * m) * ((n : ℝ) ^ m - 1) +
    (k : ℝ) ^ 3 * (n + 5) + k * (n + 3)

/-- `P = nN`. -/
noncomputable def Pn (n d : ℕ) : ℝ := DD n d

/-- `τ(n) = A / (0.91 P − 0.455 B_fix)`. -/
noncomputable def tauF (n d k : ℕ) : ℝ := Afun n d k / (91 / 100 * Pn n d - 455 / 1000 * Bfix n k)

/-- `ε*² = min(ε², 0.455)`. -/
noncomputable def epsS (ε : ℝ) : ℝ := min (ε ^ 2) (455 / 1000)

/-- The baseline `max(2P, 0.91 P / ε²)`. -/
noncomputable def baseline (n d : ℕ) (ε : ℝ) : ℝ := max (2 * Pn n d) (91 / 100 * Pn n d / ε ^ 2)

/-- `O_{j,l} = min(#orbits, ⌈Ŝ_j² n^{k−s} / (4 s 4^l τ ε*²)⌉)`. -/
noncomputable def Ocnt (n d k : ℕ) (ε : ℝ) (j l : ℕ) : ℕ :=
  min (Fintype.card (Sym (Mono n d) (j - 2 * l)))
    ⌈Shat j d n ^ 2 * (n : ℝ) ^ (k - (j - 2 * l)) /
      (4 * (j - 2 * l : ℕ) * 4 ^ l * tauF n d k * epsS ε)⌉₊

/-- An admissible kept set for level `(j, l)`. -/
def KeepOK (n d k : ℕ) (ε : ℝ) (j l : ℕ) (K : Finset (Multiset (Mono n d))) : Prop :=
  K.card ≤ Ocnt n d k ε j l ∧ (∀ o ∈ K, Multiset.card o = j - 2 * l) ∧
    (frob (fun w : Fin (j - 2 * l) → Mono n d => (RQ K l w : ℝ)) ≤
      tauF n d k * epsS ε * (j - 2 * l : ℕ) * 4 ^ l / (n : ℝ) ^ (k - (j - 2 * l)))

/-- The kept sets of the program (see `kept_exists`). -/
noncomputable def keepSet (n d k : ℕ) (ε : ℝ) (j l : ℕ) : Finset (Multiset (Mono n d)) :=
  Classical.epsilon (KeepOK n d k ε j l)

/-- The theorem's branch. -/
noncomputable def gOf41 (k : ℕ) (ε f0 : ℝ) (T : Tens n) (M : CoefIdxD n d → ℝ) : ℝ :=
  gTC k (keepSet n d k ε) f0 T M

/-! ## §10 The program in the cost model -/

open BstLean.Cost

/-- Inputs: `M`, `f₀`, and the entries of `T j`, `j ≤ k`. -/
abbrev In41 (n d k : ℕ) := CoefIdxD n d ⊕ Unit ⊕ (Σ j : Fin (k + 1), Fin j → Fin n)

def Mv {k : ℕ} (v : In41 n d k → ℝ) : CoefIdxD n d → ℝ := fun α => v (Sum.inl α)
def f0v {k : ℕ} (v : In41 n d k → ℝ) : ℝ := v (Sum.inr (Sum.inl ()))
def Tv {k : ℕ} (v : In41 n d k → ℝ) : Tens n := fun j w =>
  if h : j < k + 1 then v (Sum.inr (Sum.inr ⟨⟨j, h⟩, w⟩)) else 0

/-- The input index of `T_j[w]` (`j ≤ k`; otherwise the `f₀` slot, never used). -/
def Tidx (k : ℕ) (j : ℕ) (w : Fin j → Fin n) : In41 n d k :=
  if h : j < k + 1 then Sum.inr (Sum.inr ⟨⟨j, h⟩, w⟩) else Sum.inr (Sum.inl ())

/-- The trace slots `(j, m, w)`, `w` a word of order `j − 2m`. -/
abbrev TrTag (n : ℕ) := Σ jm : ℕ × ℕ, Fin (jm.1 - 2 * jm.2) → Fin n

/-- The trace slots that the program computes: `1 ≤ j ≤ k`, `1 ≤ m ≤ j/2`. -/
noncomputable def trSlots (n k : ℕ) : List (TrTag n) :=
  ((Finset.Icc 1 k ×ˢ Finset.Icc 1 k).filter fun jm => 2 * jm.2 ≤ jm.1).toList.flatMap fun jm =>
    (Finset.univ : Finset (Fin (jm.1 - 2 * jm.2) → Fin n)).toList.map fun w => ⟨jm, w⟩

/-- One trace slot, directly from the inputs: `tr^m T_j[w] = Σ_c T_j[glue c w]` (`n^m − 1` additions). -/
noncomputable def trSlotProg {k : ℕ} (x : TrTag n) : Prog (In41 n d k) Unit :=
  Prog.sumArgs ((Finset.univ : Finset (Fin x.1.2 → Fin n)).toList.map fun c =>
    Arg.inp (Tidx k x.1.1 (glue x.1.1 x.1.2 c x.2)))

/-- Stage 1: every partial trace `tr^m T_j`, `m ≥ 1`. -/
noncomputable def trProg (n d k : ℕ) : Prog (In41 n d k) (TrTag n) :=
  Prog.par (trSlotProg (d := d)) (trSlots n k)

/-- The argument that reads `tr^m T_j[w]` in stage 2. -/
def trArg {k : ℕ} (j m : ℕ) (w : Fin (j - 2 * m) → Fin n) : Arg (In41 n d k ⊕ TrTag n) :=
  if h : m = 0 then Arg.inp (Sum.inl (Tidx k j (fun t => w ⟨t.1, by subst h; have := t.2; omega⟩)))
  else Arg.inp (Sum.inr ⟨(j, m), w⟩)

/-- Contraction of an order-`a` tensor with `a` vectors, one slot at a time (last slot first):
`(2n − 1)(n^{a−1} + ⋯ + 1) = C_orb(a)` operations. -/
noncomputable def contractProg {ι : Type} : (a : ℕ) → ((Fin a → Fin n) → Arg ι) → (Fin a → Fin n → Arg ι) →
    Prog ι Unit
  | 0, A, _ => Prog.ofArgs fun _ => A finZeroElim
  | a + 1, A, v =>
      (Prog.par (fun w : Fin a → Fin n => Prog.sumProd ((List.finRange n).map fun c =>
          (A (Fin.snoc (α := fun _ => Fin n) w c), v (Fin.last a) c)))
        (Finset.univ : Finset (Fin a → Fin n)).toList).bind
      (contractProg a (fun w => Arg.inp (Sum.inr w)) (fun t c => (v (Fin.castSucc t) c).rename Sum.inl))

/-- A term key `(j, l, i, q)`: level `(j, l)`, trace depth `i`, orbit `q` of `tr^i H^K_{j,l}`.
The `s = 0` scalar of an even `j` is the key `(j, j/2, 0, 0)`. -/
abbrev Key (n d : ℕ) := ℕ × ℕ × ℕ × Multiset (Mono n d)

/-- The number of distinct words that list `q`. -/
noncomputable def orbSize {α : Type*} [DecidableEq α] (q : Multiset α) : ℕ :=
  (Multiset.card q).factorial / ∏ x ∈ q.toFinset, (q.count x).factorial

/-- The rational weight of a key: `κ_{j,j/2} H_{j,j/2}` for the scalars, and
`κ_{j,l} μ_{s,i} |orbit q| (tr^i H^K_{j,l})[q]` otherwise. -/
noncomputable def wKey (K : ℕ → ℕ → Finset (Multiset (Mono n d))) (key : Key n d) : ℚ :=
  if 2 * key.2.1 = key.1 then
    kapQ n d key.1 key.2.1 * HQ (n := n) (d := d) (s := key.1 - 2 * key.2.1) key.2.1 (fun _ => default)
  else kapQ n d key.1 key.2.1 * muQ n d (key.1 - 2 * key.2.1) key.2.2.1 * (orbSize key.2.2.2 : ℚ) *
    trL key.2.2.1 (HKQ (s := key.1 - 2 * key.2.1) (K key.1 key.2.1) key.2.1) (wordOf _ key.2.2.2)

/-- The keys of the program: the scalars, then every `(j, l, i)` and every orbit `q` of size `s − 2i`
with `(tr^i H^K)[q] ≠ 0`. -/
noncomputable def keys (k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d))) : List (Key n d) := by
  classical
  exact (((Finset.Icc 1 k).filter fun j => Even j).toList.map fun j => (j, j / 2, 0, (0 : Multiset (Mono n d)))) ++
    (levels k).toList.flatMap fun jl =>
      (List.range ((jl.1 - 2 * jl.2) / 2 + 1)).flatMap fun i =>
        (((Finset.univ : Finset (Sym (Mono n d) (jl.1 - 2 * jl.2 - 2 * i))).filter fun q =>
            trL i (HKQ (s := jl.1 - 2 * jl.2) (K jl.1 jl.2) jl.2) (wordOf _ q.1) ≠ 0).toList.map fun q => (jl.1, jl.2, i, q.1))

/-- The program for one key: contract `tr^{l+i} T_j` with the columns of `q`, times the weight. -/
noncomputable def keyProg (k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d))) (key : Key n d) :
    Prog (In41 n d k ⊕ TrTag n) Unit :=
  (contractProg (key.1 - 2 * (key.2.1 + key.2.2.1))
      (fun w => trArg key.1 (key.2.1 + key.2.2.1) w)
      (fun t c => Arg.inp (Sum.inl (Sum.inl ⟨(wordOf _ key.2.2.2 t).1, ((wordOf _ key.2.2.2 t).2, c)⟩)))).bind
    (Prog.op1 .mul (Arg.inp (Sum.inr ())) (Arg.cst (wKey K key)))

/-- The branch `g_TC` as a straight-line program: the traces, every key, then one sum. -/
noncomputable def gProgL (n d k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d))) : Prog (In41 n d k) Unit := by
  classical
  exact (trProg n d k).bind
    ((Prog.par (keyProg k K) (keys k K)).bind
      (Prog.sumArgs (Arg.inp (Sum.inl (Sum.inl (Sum.inr (Sum.inl ()))) ) ::
        (keys k K).map fun key => Arg.inp (Sum.inr key))))

/-- The theorem's program. -/
noncomputable def gProg (n d k : ℕ) (ε : ℝ) : Prog (In41 n d k) Unit := gProgL n d k (keepSet n d k ε)

/-- `1` if an argument is a constant other than `0` and `1` (a "heavy" constant), else `0`. -/
def argHeavy {ι : Type} : Arg ι → ℕ
  | .cst q => if q = 0 ∨ q = 1 then 0 else 1
  | _ => 0

/-- The number of heavy constant arguments of a program. -/
def heavyCount {ι κ : Type} [Fintype κ] (p : Prog ι κ) : ℕ :=
  (p.body.map fun I => argHeavy I.a + argHeavy I.b).sum + ∑ o, argHeavy (p.out o)

/-- The heavy constants of a program, as a list. -/
noncomputable def heavyConsts {ι κ : Type} [Fintype κ] (p : Prog ι κ) : List ℚ :=
  ((p.body.flatMap fun I => [I.a, I.b]) ++ (Finset.univ : Finset κ).toList.map p.out).filterMap fun
    | .cst q => if q = 0 ∨ q = 1 then none else some q
    | _ => none

/-- The cost with a charge of `n` for each heavy constant (Definition `cost`). -/
def chargedCost {ι κ : Type} [Fintype κ] (n : ℕ) (p : Prog ι κ) : ℕ := p.cost + n * heavyCount p

/-- The height bound of the moment constants: `ρ_{kd}(n) (D + 2k)^{2k} (k!)³ N^k (d+1)^k`. -/
def Hgt (n d k : ℕ) : ℕ :=
  (∏ t ∈ Finset.range (k * d), (n + 2 * t)) * (Fintype.card (CoefIdxD n d) + 2 * k) ^ (2 * k) *
    k.factorial ^ 3 * Fintype.card (Mono n d) ^ k * (d + 1) ^ k

/-- `b_Q = ⌊log₂ Hgt⌋ + 1`: every heavy constant has `|num|, den < 2^{b_Q}`. -/
def bQ (n d k : ℕ) : ℕ := Nat.log 2 (Hgt n d k) + 1

/-! ## §11 The Gaussian side: `𝒫`, the floor, the upper tails -/

/-- `u_j(Z)(x) = T_j[(Zφ(x))^{⊗j}]`. -/
noncomputable def uJ (T : Tens n) (j : ℕ) (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) : ℝ :=
  contr (T j) (fun _ => mapMD Z x)

/-- `𝒫(Z)(x) = Σ_{j=1}^k D^{−j/2} u_j(Z)(x)`. -/
noncomputable def Pcal (k : ℕ) (T : Tens n) (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 k, uJ T j Z x / Real.sqrt (DD n d) ^ j

/-- `r² = ‖Z‖²`. -/
noncomputable def r2 (Z : CoefIdxD n d → ℝ) : ℝ := ∑ α, Z α ^ 2

/-- `ρ = √D / r`. -/
noncomputable def rhoZ (Z : CoefIdxD n d → ℝ) : ℝ := Real.sqrt (DD n d) / Real.sqrt (r2 Z)

/-- The upper-tail sum `Σ_j D^{−j/2} sd_x u_j`. -/
noncomputable def upperSum (k : ℕ) (T : Tens n) (Z : CoefIdxD n d → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 k, sdU (uniformSphere n) (uJ T j Z) / Real.sqrt (DD n d) ^ j

/-- The column of the pure monomial `x^β`, `β` a `d`-subset (`0` if `|β| ≠ d`). -/
noncomputable def colP (Z : CoefIdxD n d → ℝ) (β : Finset (Fin n)) : Fin n → ℝ :=
  if h : β.card = d then fun a => Z ⟨Fin.last d, (⟨β.val, h⟩, a)⟩ else 0

/-- The ordered partitions of `S` into `s` blocks of size `d`. -/
noncomputable def parts (d s : ℕ) (S : Finset (Fin n)) : Finset (Fin s → Finset (Fin n)) := by
  classical
  exact Finset.univ.filter fun π => (∀ t, (π t).card = d) ∧
    (∀ t t', t ≠ t' → Disjoint (π t) (π t')) ∧ Finset.univ.biUnion π = S

/-- `q_S[b] = √m_S s! X_S[b] = ρ_{sd}(n)^{−1/2} Σ_{ordered partitions} b[Z_{β₁}, …, Z_{β_s}]`. -/
noncomputable def qS {s : ℕ} (b : (Fin s → Fin n) → ℝ) (S : Finset (Fin n)) (Z : CoefIdxD n d → ℝ) : ℝ :=
  (Real.sqrt (rhoD n (s * d)))⁻¹ * ∑ π ∈ parts d s S, contr b (fun t => colP Z (π t))

/-- `w_S = ⟨𝒫, x^S⟩ / √m_S`. -/
noncomputable def wS (k : ℕ) (T : Tens n) (S : Finset (Fin n)) (Z : CoefIdxD n d → ℝ) : ℝ :=
  (∫ x, Pcal k T Z x * ∏ a ∈ S, x a ∂uniformSphere n) * Real.sqrt (rhoD n (S.card))

/-- `ν_{s,l} = E[‖φ‖^{2l} x^{2S}] / m_S`, `S = {0, …, sd − 1}` (it depends only on `|S| = sd`). -/
noncomputable def nuC (n d s l : ℕ) : ℝ :=
  (∫ x, phiSq d x ^ l * ∏ a : Fin n, (if a.1 < s * d then x a ^ 2 else 1) ∂uniformSphere n) * rhoD n (s * d)

/-- `a_{j,l} = c_{j,l} D^{−j/2} tr^l T_j`. -/
noncomputable def aT (n d : ℕ) (T : Tens n) (j l : ℕ) : (Fin (j - 2 * l) → Fin n) → ℝ := fun w =>
  (cQ j l : ℝ) / Real.sqrt (DD n d) ^ j * trL l (T j) w

/-- The effective tensor `b_s = Σ_{l ≥ 0, s+2l ≤ k} ν_{s,l} a_{s+2l,l}` (Lemma LC). -/
noncomputable def bEff (n d k : ℕ) (T : Tens n) (s : ℕ) : (Fin s → Fin n) → ℝ := fun w =>
  ∑ l ∈ (Finset.range (k + 1)).filter (fun l => s + 2 * l ≤ k),
    nuC n d s l * aT n d T (s + 2 * l) l (fun t => w ⟨t.1, by have := t.2; omega⟩)

/-- The pure part `P_α = Σ_s n^{−(k−s)} Σ_{|S| = sd} q_S[b_s]²`. -/
noncomputable def Palpha (k : ℕ) (T : Tens n) (Z : CoefIdxD n d → ℝ) : ℝ :=
  ∑ s ∈ Finset.Icc 1 k, (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (s * d),
    qS (bEff n d k T s) S Z ^ 2) / (n : ℝ) ^ (k - s)

/-- The contamination `H_α = Σ_s n^{−(k−s)} Σ_{|S| = sd} (w_S − q_S)²`. -/
noncomputable def Halpha (k : ℕ) (T : Tens n) (Z : CoefIdxD n d → ℝ) : ℝ :=
  ∑ s ∈ Finset.Icc 1 k, (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (s * d),
    (wS k T S Z - qS (bEff n d k T s) S Z) ^ 2) / (n : ℝ) ^ (k - s)

/-! ## §12 Floor and failure constants -/

/-- The largest of `g 1, …, g k` (and `0`). -/
noncomputable def maxJ (k : ℕ) (g : ℕ → ℝ) : ℝ := ((List.range' 1 k).map g).foldr max 0

/-- `λ_{n,s} = ∏_{i < sd} (n − i)/(n + 2i)`. -/
noncomputable def lamS (n d s : ℕ) : ℝ := ∏ i ∈ Finset.range (s * d), ((n : ℝ) - i) / ((n : ℝ) + 2 * i)

/-- `μ_n = λ_{n,k} / (k (d!)^k)`. -/
noncomputable def muN (n d k : ℕ) : ℝ := lamS n d k / (k * (d.factorial : ℝ) ^ k)

/-- `L_s = #{l ≥ 1 : s + 2l ≤ k}`. -/
def Ls (k s : ℕ) : ℕ := (k - s) / 2

/-- `θ̃ = max_j Σ_{l ≥ 1, s ≥ 1} L_s ω̃_{s,l} n^{−l}`. -/
noncomputable def thetaT (n d k : ℕ) : ℝ :=
  maxJ k fun j => ∑ l ∈ (Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j),
    (Ls k (j - 2 * l) : ℝ) * (((j - 2 * l).factorial : ℝ) * (j - 2 * l : ℕ) * ((d : ℝ) + 1) ^ (2 * l) *
      (cQ j l : ℝ) ^ 2 / ((j.factorial : ℝ) * j)) / (n : ℝ) ^ l

/-- `ρ̄ = max_j (1 + Σ_{l ≥ 1, s ≥ 1} s! s 4^l c_{j,l}² n^{−l} / (j! j))`. -/
noncomputable def rhoBar (n k : ℕ) : ℝ :=
  maxJ k fun j => 1 + ∑ l ∈ (Finset.Icc 1 (j / 2)).filter (fun l => 2 * l < j),
    ((j - 2 * l).factorial : ℝ) * (j - 2 * l : ℕ) * 4 ^ l * (cQ j l : ℝ) ^ 2 /
      ((j.factorial : ℝ) * j * (n : ℝ) ^ l)

/-- The crude contamination constant `Ψ̄_m = (d+1)^m Σ_{s=1}^{m−1} n^{−(m−1−s)}` (from `Ψ_m(s) ≤ (d+1)^m`). -/
noncomputable def PsiB (n d m : ℕ) : ℝ := ((d : ℝ) + 1) ^ m * ∑ s ∈ Finset.Ico 1 m, 1 / (n : ℝ) ^ (m - 1 - s)

/-- `Ξ = max_j Σ_{l, m = j−2l ≥ 2} (L_m + 1) m! c_{j,l}² (d+1)^{2l} Ψ̄_m n^{−l} / (j! j)`. -/
noncomputable def XiC (n d k : ℕ) : ℝ :=
  maxJ k fun j => ∑ l ∈ (Finset.range (j / 2 + 1)).filter (fun l => 2 * l + 2 ≤ j),
    ((Ls k (j - 2 * l) : ℝ) + 1) * ((j - 2 * l).factorial : ℝ) * (cQ j l : ℝ) ^ 2 * ((d : ℝ) + 1) ^ (2 * l) *
      PsiB n d (j - 2 * l) / ((n : ℝ) ^ l * (j.factorial : ℝ) * j)

/-- `K_c = ρ̄ (1 + η) / (1 − (1 + 1/η) θ̃)`. -/
noncomputable def Kc (n d k : ℕ) (η : ℝ) : ℝ := rhoBar n k * (1 + η) / (1 - (1 + 1 / η) * thetaT n d k)

/-- `h_n = Ξ (1 + η) / (n μ_n (1 − (1 + 1/η) θ̃))`. -/
noncomputable def hN (n d k : ℕ) (η : ℝ) : ℝ :=
  XiC n d k * (1 + η) / ((n : ℝ) * muN n d k * (1 - (1 + 1 / η) * thetaT n d k))

/-- `q_n = Σ_{i=d}^{kd} C(kd, i) C(n − kd, kd − i) / C(n, kd)`. -/
noncomputable def qN (n d k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc d (k * d), ((k * d).choose i : ℝ) * ((n - k * d).choose (k * d - i) : ℝ) /
    (n.choose (k * d) : ℝ)

/-- `π_n(ϑ) = σ² / (σ² + (1 − ϑ)²)`, `σ² = (9^k − 1) q_n`. -/
noncomputable def piN (n d k : ℕ) (th : ℝ) : ℝ :=
  (9 ^ k - 1) * qN n d k / ((9 ^ k - 1) * qN n d k + (1 - th) ^ 2)

/-- `G'_j` of Lemma `upper`. -/
noncomputable def Gpj (n d k j : ℕ) : ℝ :=
  (n : ℝ) ^ (k - j) / ((j.factorial : ℝ) * j) *
    (((d : ℝ) + 1) ^ j * ∑ l ∈ (Finset.range (j / 2 + 1)).filter (fun l => 2 * l < j),
        ((j - 2 * l).factorial : ℝ) * (cQ j l : ℝ) ^ 2 * (n : ℝ) ^ l +
      (if Even j then (cQ j (j / 2) : ℝ) ^ 2 * (n : ℝ) ^ (j / 2) *
        (Real.sqrt (((d : ℝ) + 1) ^ j) - Real.sqrt (2 ^ j)) ^ 2 / 4 else 0))

/-- `Γ' = k max_j G'_j`. -/
noncomputable def GamP (n d k : ℕ) : ℝ := k * maxJ k (Gpj n d k)

/-- `η_r = (2√(Dx) + 2x)/D`. -/
noncomputable def etaR (n d : ℕ) (x : ℝ) : ℝ := (2 * Real.sqrt (DD n d * x) + 2 * x) / DD n d

/-- `η_k = (1 − η_r)^{−k/2} − 1`. -/
noncomputable def etaK (n d k : ℕ) (x : ℝ) : ℝ := 1 / Real.sqrt ((1 - etaR n d x) ^ k) - 1

/-- `L = ⌊(k − 1)/2⌋ + 1`. -/
def Lk (k : ℕ) : ℕ := (k - 1) / 2 + 1

/-- The parameters `(x, β, β_H, ϑ, η)` of the proof. -/
structure Params where
  x : ℝ
  beta : ℝ
  betaH : ℝ
  th : ℝ
  eta : ℝ

/-- `γ = √(μ_n/K_c) (√ϑ − √(h_n/β_H)) − η_k √(Γ'/β)`. -/
noncomputable def gam41 (n d k : ℕ) (q : Params) : ℝ :=
  Real.sqrt (muN n d k / Kc n d k q.eta) * (Real.sqrt q.th - Real.sqrt (hN n d k q.eta / q.betaH)) -
    etaK n d k q.x * Real.sqrt (GamP n d k / q.beta)

/-- `Φ_LF(n) = 2e^{−x} + π_n(ϑ) + β + β_H + L τ / γ²`. -/
noncomputable def PhiLF (n d k : ℕ) (q : Params) : ℝ :=
  2 * Real.exp (-q.x) + piN n d k q.th + q.beta + q.betaH + Lk k * tauF n d k / gam41 n d k q ^ 2

/-- The conditions of the proof of Theorem TC-LF at `n` (none depends on `f` or `ε`). -/
def BudgetOK (n d k : ℕ) (q : Params) : Prop :=
  2 ≤ n ∧ 1 ≤ d ∧ k * d ≤ n ∧ 0 < tauF n d k ∧
  0 < q.x ∧ 0 < q.beta ∧ 0 < q.betaH ∧ 0 < q.th ∧ q.th < 1 ∧ 0 < q.eta ∧
  (1 + 1 / q.eta) * thetaT n d k < 1 ∧ etaR n d q.x < 1 ∧
  0 < muN n d k ∧ 0 < Kc n d k q.eta ∧ 0 < hN n d k q.eta ∧
  Real.sqrt (hN n d k q.eta / q.betaH) < Real.sqrt q.th ∧
  0 < gam41 n d k q ∧ 455 / 1000 * Bfix n k < 91 / 100 * Pn n d ∧ 4 * bQ n d k ≤ n ∧
  PhiLF n d k q ≤ 1 / 2

/-- The parameters of the `(3,3)` certificate (`n₀ = 35 800 000`; `Φ_LF(n₀) ≈ 0.49955`). -/
noncomputable def prm33 : Params := ⟨10, 1 / 1000, 5 / 100, 999 / 1000, 3 / 10000⟩

/-- The parameters of the `(3,4)` certificate (`n₀ = 7 420 000`; `Φ_LF(n₀) ≈ 0.48964`). -/
noncomputable def prm34 : Params := ⟨12, 1 / 1000, 25 / 100, 999 / 1000, 1 / 1000⟩

end BstLean.Part41
