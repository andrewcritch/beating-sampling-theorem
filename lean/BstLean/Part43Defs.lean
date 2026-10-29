import BstLean.Part41Defs
import BstLean.Part42Defs

/-!
# Part 43, wave 0: frozen definitions — arbitrary degree under every diagonal Bingham law

Paper: `proofs/option-m/43-arbitrary-degree-every-diagonal-bingham.tex` (Theorem G, Lemmas K, B, M,
tail, F, F′, SB, cost, one-time cost). Specification: `delegations/answers/p43-spec-opus.md`.
This file holds definitions only. Provers must not edit it, and must not use `native_decide` or
`axiom` anywhere.

Conventions.
* Part 41's names are reused: `Mono n d`, `phiM`, `phiSq`, `colM`, `contr`, `trL`, `frob`, `IsSymmT`,
  `mset`, `wordOf`, `Tens`, `TSymm`, `fval`, `varU`, `sdU`, `levels`, `cQ`, `kapQ`, `muQ`, `aT`, `Nn`,
  `uJ`, `Pcal`, `r2`, `rhoZ`, `cS`, `Bfix`, `Pn`, `epsS`, `baseline`, `thetaT`, `rhoBar`, `Kc`,
  `GamP`, `etaR`, `etaK`, `Lk`, `orbSize`, `heavyCount`, `Hgt`, `bQ`, `In41` (with `Mv`, `f0v`, `Tv`).
  `k = d_f`, `d = d_M`. The coefficient space is Part 36's `CoefIdxD n d`, `M = Z/‖Z‖`.
* **Law-general quantities.** For a law `μ` on `ℝⁿ`: `BofQ μ` is `B_μ(M) = E_μ f(Mφ(x))`, `varFQ μ`
  is `Var_μ f(Mφ(x))`, `HR μ l w = E_μ[‖φ‖^{2l} φ_{w₁}⋯φ_{w_s}]` (a real number), `HKR`, `RR` its kept
  part and residual, `gTCR μ` Part 41's branch formula `gTC` with `HR μ` in place of `HQ`,
  `WfrobSqR μ` Part 41's `‖W_s‖²` with `RR μ`, `upperSumQ μ` Part 41's `upperSum` under `μ`.
* **The laws.** `D(θ) = bingham n θ` (Part 37). `bmin θ = θ − min θ` (so `bmin θ ≥ 0`). The surrogate
  is `surrT θ ε = binghamK n (Kof43 (spread θ) ε) (bmin θ)` (Part 37's Taylor law; density
  `p_K(b·u)/Z_K` with respect to the uniform law). `etaQ ε = min(ξε, 1/2)`, `ξ = xi43 = 1/20`;
  `Kof43 A ε = ⌈A + u*⌉` (Definition `surrogate law`).
* **Mass.** `Nj j d β` counts the ordered `j`-tuples of exponent vectors on `Fin m` with degree `≤ d`
  and sum `2β`; `Upp j d = U″_j = Σ_{m ≤ jd/2} max_{β : Fin m → ℕ, |β| = m} N_j(2β) β!/m!`.
  `massR μ j l = Σ_w |H_{j,l}[w]|`.
* **Allocation (Lemma `cost`).** `AU`, `tau43` (with the share `ν = nu43 = 1/20` reserved), `Ocnt43`,
  `KeepOK43 μ`, `keepSet43 μ` (chosen by `Classical.epsilon`; build-time control, not charged).
  `gOf43 θ ε` is the theorem's branch: `gTCR` for the surrogate with its kept sets.
* **Programs.** `KeyF n d k` is a finite type that holds every key `(j, l, i, q)`; `keys43 k K` is the
  set of keys used (the scalars, and every orbit `q` of size `s − 2i` below a kept orbit). `wKeyR μ K`
  is the weight of a key (`κ μ |orbit| (tr^i H^K)[q]`, or `κ H` for a scalar). `gTCW` is the branch
  written through the weights. The moment program `pm : Prog (Fin n) (KeyF n d k)` maps `θ` to the
  weights (`MomSpec43`); the branch program `pg : Prog (In43 n d k) Unit` maps `M`, `f` and the
  weights to `g` (`GSpec43`). Both must have `heavyCount = 0` (constants `0` and `1` only).
  `onceCost` is the proved bound on the cost of `pm`; `gCost43` the bound on the cost of `pg`.
* **Small ball.** `FradeliziGauss` is Fradelizi's Corollary 4 (`s = 0`) for the standard Gaussian on
  `ℝ^ι`, any finite `ι`. `chebP h = T_h(2X − 1)`, `Ch h = 1 + ∫₁^∞ e^{−λ} dT_h(2λ−1)` in the closed form
  `1 + e^{−1} Σ_{m=1}^h p^{(m)}(1)`, `tsb k p = 1/(C_{2k} T_{2k}(2λ−1))`, `λ = −1/ln(1−p)`.
* **The floor.** `bq n d k T s q = b_s(q) = Σ_l q^l a_{s+2l,l}` (Lemma F).
* **Budget.** `Params43 = (p_sb, x, β, η_c)`, `gam43`, `Phi43`, `BudgetOK43`, `k0_43`.
-/

namespace BstLean.Part43

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD rhoD)
open BstLean.Part41 (Mono phiM phiSq colM contr trL frob IsSymmT mset wordOf Tens TSymm fval varU sdU
  levels cQ kapQ muQ aT Nn uJ Pcal cS Bfix Pn epsS baseline thetaT rhoBar Kc GamP etaR etaK Lk
  orbSize heavyCount bQ In41)

variable {n d : ℕ}

/-! ## §1 Law-general quantities -/

/-- `B_μ(M) = E_μ f(M φ(x))`. -/
noncomputable def BofQ (μ : Measure (Fin n → ℝ)) (k : ℕ) (f0 : ℝ) (T : Tens n) (M : CoefIdxD n d → ℝ) : ℝ :=
  ∫ x, fval k f0 T (mapMD M x) ∂μ

/-- `Var_μ f(M φ(x))`. -/
noncomputable def varFQ (μ : Measure (Fin n → ℝ)) (k : ℕ) (f0 : ℝ) (T : Tens n) (M : CoefIdxD n d → ℝ) : ℝ :=
  varU μ (fun x => fval k f0 T (mapMD M x))

/-- `H^μ_{j,l}[w] = E_μ[‖φ‖^{2l} φ_{w₁} ⋯ φ_{w_s}]`, `w : Fin s → Mono n d`. -/
noncomputable def HR (μ : Measure (Fin n → ℝ)) {s : ℕ} (l : ℕ) (w : Fin s → Mono n d) : ℝ :=
  ∫ x, phiSq d x ^ l * ∏ t, phiM x (w t) ∂μ

/-- The kept part of `H^μ`. -/
noncomputable def HKR (μ : Measure (Fin n → ℝ)) {s : ℕ} (K : Finset (Multiset (Mono n d))) (l : ℕ)
    (w : Fin s → Mono n d) : ℝ := by
  classical
  exact if mset w ∈ K then HR μ l w else 0

/-- The residual `R^μ = H^μ − H^{μ,K}`. -/
noncomputable def RR (μ : Measure (Fin n → ℝ)) {s : ℕ} (K : Finset (Multiset (Mono n d))) (l : ℕ)
    (w : Fin s → Mono n d) : ℝ :=
  HR μ l w - HKR μ K l w

/-- Part 41's branch formula `gTC` with the moments of `μ`. -/
noncomputable def gTCR (μ : Measure (Fin n → ℝ)) (k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (f0 : ℝ) (T : Tens n) (M : CoefIdxD n d → ℝ) : ℝ :=
  f0 + ∑ j ∈ (Finset.Icc 1 k).filter (fun j => Even j),
      (kapQ n d j (j / 2) : ℝ) * HR (n := n) (d := d) μ (s := j - 2 * (j / 2)) (j / 2) (fun _ => default) *
        contr (trL (j / 2) (T j)) (fun _ _ => 0)
    + ∑ jl ∈ levels k, (kapQ n d jl.1 jl.2 : ℝ) *
      ∑ i ∈ Finset.range ((jl.1 - 2 * jl.2) / 2 + 1), (muQ n d (jl.1 - 2 * jl.2) i : ℝ) *
        ∑ w : Fin (jl.1 - 2 * jl.2 - 2 * i) → Mono n d,
          trL i (HKR μ (s := jl.1 - 2 * jl.2) (K jl.1 jl.2) jl.2) w *
            contr (trL (jl.2 + i) (T jl.1)) (fun t => colM M (w ⟨t.1, by have := t.2; omega⟩))

/-- Part 41's `‖W_s‖²` (Lemma E) with the residuals of `μ`. -/
noncomputable def WfrobSqR (μ : Measure (Fin n → ℝ)) (k s : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (T : Tens n) : ℝ :=
  ∑ a : Fin s → Fin n, ∑ p : Fin s → Mono n d,
    (∑ l ∈ (Finset.range (k + 1)).filter (fun l => s + 2 * l ≤ k),
      (kapQ n d (s + 2 * l) l : ℝ) * trL l (T (s + 2 * l)) (fun t => a ⟨t.1, by have := t.2; omega⟩) *
        RR μ (K (s + 2 * l) l) l (fun t : Fin (s + 2 * l - 2 * l) => p ⟨t.1, by have := t.2; omega⟩)) ^ 2

/-- The upper-tail sum `Σ_j D^{−j/2} sd_μ u_j`. -/
noncomputable def upperSumQ (μ : Measure (Fin n → ℝ)) (k : ℕ) (T : Tens n) (Z : CoefIdxD n d → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 k, sdU μ (uJ T j Z) / Real.sqrt (DD n d) ^ j

/-- The `ℓ¹` mass `S_{j,l}(μ) = Σ_w |H^μ_{j,l}[w]|` (`s = j − 2l`). -/
noncomputable def massR (μ : Measure (Fin n → ℝ)) (d j l : ℕ) : ℝ :=
  ∑ w : Fin (j - 2 * l) → Mono n d, |HR μ l w|

/-! ## §2 The surrogate law (Definition `surrogate law`, Lemma K) -/

/-- `ξ = 1/20`. -/
noncomputable def xi43 : ℝ := 1 / 20

/-- `ν = 1/20`, the share of the baseline reserved for the one-time cost. -/
noncomputable def nu43 : ℝ := 1 / 20

/-- `η_Q = min(ξε, 1/2)`. -/
noncomputable def etaQ (ε : ℝ) : ℝ := min (xi43 * ε) (1 / 2)

/-- `L_η = ln((1 + η_Q)/η_Q)`. -/
noncomputable def Leta (ε : ℝ) : ℝ := Real.log ((1 + etaQ ε) / etaQ ε)

/-- `u* = L_η/3 + √(L_η²/9 + 2 A L_η)`. -/
noncomputable def ustar (A ε : ℝ) : ℝ := Leta ε / 3 + Real.sqrt (Leta ε ^ 2 / 9 + 2 * A * Leta ε)

/-- `K = ⌈A + u*⌉`. -/
noncomputable def Kof43 (A ε : ℝ) : ℕ := ⌈A + ustar A ε⌉₊

/-- `b = θ − min θ ≥ 0`. -/
noncomputable def bmin (θ : Fin n → ℝ) : Fin n → ℝ := fun i => θ i - ⨅ j, θ j

/-- The surrogate law `Q̃_K ∝ p_K(b·u) σ`, `K = Kof43 (spread θ) ε`. -/
noncomputable def surrT (n : ℕ) (θ : Fin n → ℝ) (ε : ℝ) : Measure (Fin n → ℝ) :=
  BstLean.Part37.binghamK n (Kof43 (BstLean.Part42.spread θ) ε) (bmin θ)

/-! ## §3 The mass bound `U″_j` (Lemma M) -/

/-- `N_j(2β)`: ordered `j`-tuples of exponent vectors on `Fin m`, each of degree `≤ d`, summing to `2β`. -/
noncomputable def Nj (j d m : ℕ) (β : Fin m → ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin j → Fin m → Fin (d + 1))).filter fun e =>
    (∀ t, ∑ a, (e t a : ℕ) ≤ d) ∧ (∀ a, ∑ t, (e t a : ℕ) = 2 * β a)).card

/-- `max_{β : Fin m → ℕ, |β| = m} N_j(2β) β!/m!` (`0` if there is no such `β`). -/
noncomputable def UppTerm (j d m : ℕ) : ℝ := by
  classical
  exact (((Finset.univ : Finset (Fin m → Fin (m + 1))).filter fun β => ∑ a, (β a : ℕ) = m).toList.map
    fun β => (Nj j d m (fun a => (β a : ℕ)) : ℝ) * (∏ a, ((β a : ℕ).factorial : ℝ)) / (m.factorial : ℝ)).foldr
      max 0

/-- `U″_j = Σ_{m=0}^{⌊jd/2⌋} max_{|β| = m} N_j(2β) β!/m!`. -/
noncomputable def Upp (j d : ℕ) : ℝ := ∑ m ∈ Finset.range (j * d / 2 + 1), UppTerm j d m

/-! ## §4 Allocation and kept sets (Lemma `cost`, Lemma `tail for Q̃`) -/

/-- `A_U = Σ_{(j,l)} c_s U″_j² n^{k−s} / (4 s 4^l)`. -/
noncomputable def AU (n d k : ℕ) : ℝ :=
  ∑ jl ∈ levels k, cS n (jl.1 - 2 * jl.2) * Upp jl.1 d ^ 2 * (n : ℝ) ^ (k - (jl.1 - 2 * jl.2)) /
    (4 * (jl.1 - 2 * jl.2 : ℕ) * 4 ^ jl.2)

/-- `τ = A_U / ((1 − ν) 0.91 P − 0.455 B_fix)`. -/
noncomputable def tau43 (n d k : ℕ) : ℝ :=
  AU n d k / ((1 - nu43) * (91 / 100) * Pn n d - 455 / 1000 * Bfix n k)

/-- `O_{j,l} = min(#orbits, ⌈U″_j² n^{k−s} / (4 s 4^l τ ε*²)⌉)`. -/
noncomputable def Ocnt43 (n d k : ℕ) (ε : ℝ) (j l : ℕ) : ℕ :=
  min (Fintype.card (Sym (Mono n d) (j - 2 * l)))
    ⌈Upp j d ^ 2 * (n : ℝ) ^ (k - (j - 2 * l)) /
      (4 * (j - 2 * l : ℕ) * 4 ^ l * tau43 n d k * epsS ε)⌉₊

/-- An admissible kept set for level `(j, l)` under the law `μ`. -/
def KeepOK43 (n d k : ℕ) (μ : Measure (Fin n → ℝ)) (ε : ℝ) (j l : ℕ) (K : Finset (Multiset (Mono n d))) :
    Prop :=
  K.card ≤ Ocnt43 n d k ε j l ∧ (∀ o ∈ K, Multiset.card o = j - 2 * l) ∧
    (frob (fun w : Fin (j - 2 * l) → Mono n d => RR μ K l w) ≤
      tau43 n d k * epsS ε * (j - 2 * l : ℕ) * 4 ^ l / (n : ℝ) ^ (k - (j - 2 * l)))

/-- The kept sets under `μ` (build-time control, chosen by `Classical.epsilon`). -/
noncomputable def keepSet43 (n d k : ℕ) (μ : Measure (Fin n → ℝ)) (ε : ℝ) (j l : ℕ) :
    Finset (Multiset (Mono n d)) :=
  Classical.epsilon (KeepOK43 n d k μ ε j l)

/-- The theorem's branch: `g^{Q̃}_TC` with the kept sets of `Q̃`. -/
noncomputable def gOf43 (k : ℕ) (θ : Fin n → ℝ) (ε f0 : ℝ) (T : Tens n) (M : CoefIdxD n d → ℝ) : ℝ :=
  gTCR (surrT n θ ε) k (keepSet43 n d k (surrT n θ ε) ε) f0 T M

/-! ## §5 Keys, weights and the programs -/

/-- A finite type holding every key `(j, l, i, q)`, `q` an orbit of size `a ≤ k`. -/
abbrev KeyF (n d k : ℕ) := Fin (k + 1) × Fin (k + 1) × Fin (k + 1) × (Σ a : Fin (k + 1), Sym (Mono n d) a)

/-- The keys used: the scalars `(j, j/2, 0, ∅)` (`j` even), and `(j, l, i, q)` for a level `(j, l)`,
`2i ≤ s`, `|q| = s − 2i` and `q ≤ o` for some kept orbit `o`. -/
def IsKey (k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d))) (κ : KeyF n d k) : Prop :=
  (Even κ.1.1 ∧ 1 ≤ κ.1.1 ∧ κ.2.1.1 = κ.1.1 / 2 ∧ κ.2.2.1.1 = 0 ∧ κ.2.2.2.1.1 = 0) ∨
  ((κ.1.1, κ.2.1.1) ∈ levels k ∧ 2 * κ.2.2.1.1 ≤ κ.1.1 - 2 * κ.2.1.1 ∧
    κ.2.2.2.1.1 = κ.1.1 - 2 * κ.2.1.1 - 2 * κ.2.2.1.1 ∧
    ∃ o ∈ K κ.1.1 κ.2.1.1, κ.2.2.2.2.1 ≤ o)

/-- The set of keys used. -/
noncomputable def keys43 (k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d))) : Finset (KeyF n d k) := by
  classical
  exact Finset.univ.filter (IsKey k K)

/-- The weight of a key under `μ`: `κ_{j,j/2} H^μ_{j,j/2}` for a scalar (`2l = j`), and
`κ_{j,l} μ_{s,i} |orbit q| (tr^i H^{μ,K}_{j,l})[q]` otherwise. -/
noncomputable def wKeyR (μ : Measure (Fin n → ℝ)) {k : ℕ} (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (κ : KeyF n d k) : ℝ :=
  if 2 * κ.2.1.1 = κ.1.1 then
    (kapQ n d κ.1.1 κ.2.1.1 : ℝ) * HR (n := n) (d := d) μ (s := κ.1.1 - 2 * κ.2.1.1) κ.2.1.1 (fun _ => default)
  else (kapQ n d κ.1.1 κ.2.1.1 : ℝ) * (muQ n d (κ.1.1 - 2 * κ.2.1.1) κ.2.2.1.1 : ℝ) *
    (orbSize κ.2.2.2.2.1 : ℝ) *
    trL κ.2.2.1.1 (HKR μ (s := κ.1.1 - 2 * κ.2.1.1) (K κ.1.1 κ.2.1.1) κ.2.1.1)
      (wordOf _ κ.2.2.2.2.1)

/-- The term of a key: `(tr^{l+i} T_j)[M_{q₁}, …]`. -/
noncomputable def termK {k : ℕ} (T : Tens n) (M : CoefIdxD n d → ℝ) (κ : KeyF n d k) : ℝ :=
  contr (trL (κ.2.1.1 + κ.2.2.1.1) (T κ.1.1))
    (fun t => colM M (wordOf (κ.1.1 - 2 * (κ.2.1.1 + κ.2.2.1.1)) κ.2.2.2.2.1 t))

/-- The branch written through key weights `w`: `f₀ + Σ_{keys} w(key) · term(key)`. -/
noncomputable def gTCW (k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d))) (f0 : ℝ) (T : Tens n)
    (M : CoefIdxD n d → ℝ) (w : KeyF n d k → ℝ) : ℝ :=
  f0 + ∑ κ ∈ keys43 k K, w κ * termK T M κ

/-- The branch program's inputs: `M`, `f₀`, the entries of `T_j` (`j ≤ k`), and the key weights. -/
abbrev In43 (n d k : ℕ) := In41 n d k ⊕ KeyF n d k

/-- The input vector for `f = (f₀, T)`, `M` and weights `c`. -/
def inp43 {k : ℕ} (f0 : ℝ) (T : Tens n) (M : CoefIdxD n d → ℝ) (c : KeyF n d k → ℝ) : In43 n d k → ℝ :=
  Sum.elim (Sum.elim M (Sum.elim (fun _ => f0) (fun jw => T jw.1 jw.2))) c

/-- The moment program's specification at `θ'`, for build-time data `i0` (an argmin), the truncation
order `Kq` and the kept sets `K`: on every used key it returns the weight of the surrogate
`binghamK n Kq (θ' − θ'_{i0})`. -/
def MomSpec43 {k : ℕ} (pm : Prog (Fin n) (KeyF n d k)) (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (i0 : Fin n) (Kq : ℕ) (θ' : Fin n → ℝ) : Prop :=
  ∀ κ ∈ keys43 k K, pm.eval θ' κ =
    wKeyR (BstLean.Part37.binghamK n Kq (BstLean.Part42.bsh θ' i0)) K κ

/-- The branch program's specification: on every input it returns `gTCW` of its weights. -/
def GSpec43 {k : ℕ} (pg : Prog (In43 n d k) Unit) (K : ℕ → ℕ → Finset (Multiset (Mono n d))) : Prop :=
  ∀ v : In43 n d k → ℝ, pg.eval v () =
    gTCW k K (BstLean.Part41.f0v (v ∘ Sum.inl)) (BstLean.Part41.Tv (v ∘ Sum.inl))
      (BstLean.Part41.Mv (v ∘ Sum.inl)) (fun κ => v (Sum.inr κ))

/-- The proved bound on the branch program's cost (Part 41's `gProgL` count without constant charges). -/
noncomputable def gCost43 (n k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d))) : ℝ :=
  ∑ jl ∈ levels k, cS n (jl.1 - 2 * jl.2) * ((K jl.1 jl.2).card : ℝ) +
    ∑ j ∈ Finset.Icc 1 k, ∑ m ∈ Finset.Icc 1 (j / 2), (n : ℝ) ^ (j - 2 * m) * ((n : ℝ) ^ m - 1) +
    k * (n + 3)

/-- `δ_R = (K+1)(d+1)^{⌊k/2⌋}`, the dimension of the truncated ring of Lemma `ring`. -/
def deltaR (d k Kq : ℕ) : ℕ := (Kq + 1) * (d + 1) ^ (k / 2)

/-- `V_once = Σ_{l ≤ k/2} C(n + ⌊(k−2l)d/2⌋, ⌊(k−2l)d/2⌋)`, the number of values (Lemma `one-time cost`). -/
def Vonce (n d k : ℕ) : ℕ :=
  ∑ l ∈ Finset.range (k / 2 + 1), (n + (k - 2 * l) * d / 2).choose ((k - 2 * l) * d / 2)

/-- A bit bound for the constants of the ring algorithm (`ω_m`, double factorials, `1/t!`,
`m ≤ kd + K`). -/
def bR (n d k Kq : ℕ) : ℕ := (k * d + Kq + 2) ^ 2 * (Nat.log 2 (n + 2 * (k * d + Kq)) + 2)

/-- The proved bound on the moment program's cost: the values (Lemma `ring`, with slack, and the
constants built from `1`), then the key weights (one constant and one product per key and per
contributing kept orbit, constants of height `< 2^{bQ}`). -/
noncomputable def onceCost (n d k Kq : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d))) : ℝ :=
  16 * ((n : ℝ) + Vonce n d k) * (k * d + 2) *
      ((deltaR d k Kq : ℝ) ^ 2 + deltaR d k Kq * (4 * bR n d k Kq + 4)) +
    16 * (Kq : ℝ) ^ 2 + 64 +
    (2 * ∑ jl ∈ levels k, (2 : ℝ) ^ (jl.1 - 2 * jl.2) * ((K jl.1 jl.2).card : ℝ) + k + 1) *
      (4 * bQ n d k + 2)

/-! ## §6 Small ball (Lemma SB, Fradelizi's Corollary 4) -/

/-- **Fradelizi's Corollary 4** (`s = 0`) for the standard Gaussian on `ℝ^ι`: for a real polynomial
`P` of degree `≤ h`, `t > 1`, `c > 0`: `γ{|P| ≥ c T_h(t)} ≤ γ{|P| ≥ c}^{(t+1)/2}`. -/
def FradeliziGauss : Prop :=
  ∀ (ι : Type) [Fintype ι] (P : MvPolynomial ι ℝ) (h : ℕ), P.totalDegree ≤ h →
    ∀ t c : ℝ, 1 < t → 0 < c →
      (stdGauss ι {z | c * (Polynomial.Chebyshev.T ℝ (h : ℤ)).eval t ≤ |MvPolynomial.eval z P|}).toReal ≤
        ((stdGauss ι {z | c ≤ |MvPolynomial.eval z P|}).toReal) ^ ((t + 1) / 2)

/-- `T_h(2X − 1)`. -/
noncomputable def chebP (h : ℕ) : Polynomial ℝ :=
  (Polynomial.Chebyshev.T ℝ (h : ℤ)).comp (2 * Polynomial.X - 1)

/-- `C_h = 1 + ∫₁^∞ e^{−λ} (d/dλ) T_h(2λ − 1) dλ = 1 + e^{−1} Σ_{m=1}^h p^{(m)}(1)`, `p = chebP h`. -/
noncomputable def Ch (h : ℕ) : ℝ :=
  1 + Real.exp (-1) * ∑ m ∈ Finset.Icc 1 h, (Polynomial.derivative^[m] (chebP h)).eval 1

/-- `λ = −1/ln(1 − p_sb)`. -/
noncomputable def lamP (p : ℝ) : ℝ := -1 / Real.log (1 - p)

/-- `t_sb = 1/(C_{2k} T_{2k}(2λ − 1))`. -/
noncomputable def tsb (k : ℕ) (p : ℝ) : ℝ := 1 / (Ch (2 * k) * (chebP (2 * k)).eval (lamP p))

/-! ## §7 The floor (Lemmas F, F′) -/

/-- `b_s(q) = Σ_{l : s+2l ≤ k} q^l a_{s+2l,l}`. -/
noncomputable def bq (n d k : ℕ) (T : Tens n) (s : ℕ) (q : ℝ) : (Fin s → Fin n) → ℝ := fun w =>
  ∑ l ∈ (Finset.range (k + 1)).filter (fun l => s + 2 * l ≤ k),
    q ^ l * aT n d T (s + 2 * l) l (fun t => w ⟨t.1, by have := t.2; omega⟩)

/-! ## §8 Budget and the counter -/

/-- The parameters `(p_sb, x, β, η_c)`. -/
structure Params43 where
  psb : ℝ
  x : ℝ
  beta : ℝ
  eta : ℝ

/-- `γ = √(t_sb/K_c) − η_k √(Γ'/β)`. -/
noncomputable def gam43 (n d k : ℕ) (q : Params43) : ℝ :=
  Real.sqrt (tsb k q.psb / Kc n d k q.eta) - etaK n d k q.x * Real.sqrt (GamP n d k / q.beta)

/-- `Φ(n) = p_sb + 2e^{−x} + β + L τ / ((1 − ξ)² γ²)`. -/
noncomputable def Phi43 (n d k : ℕ) (q : Params43) : ℝ :=
  q.psb + 2 * Real.exp (-q.x) + q.beta + Lk k * tau43 n d k / ((1 - xi43) ^ 2 * gam43 n d k q ^ 2)

/-- The conditions of the proof of Theorem G at `n` (none depends on `θ`, `f` or `ε`). -/
def BudgetOK43 (n d k : ℕ) (q : Params43) : Prop :=
  2 ≤ n ∧ 1 ≤ d ∧ 0 < tau43 n d k ∧
  0 < q.psb ∧ q.psb < 1 - Real.exp (-1) ∧ 0 < q.x ∧ 0 < q.beta ∧ 0 < q.eta ∧
  (1 + 1 / q.eta) * thetaT n d k < 1 ∧ etaR n d q.x < 1 ∧ 0 < Kc n d k q.eta ∧
  0 < gam43 n d k q ∧ 455 / 1000 * Bfix n k < (1 - nu43) * (91 / 100) * Pn n d ∧
  Phi43 n d k q ≤ 1 / 2

/-- The amortization threshold `k₀ = ⌈C_once / (ν 𝔅(ε))⌉`. -/
noncomputable def k0_43 (n d k : ℕ) (θ : Fin n → ℝ) (ε : ℝ) : ℕ :=
  ⌈onceCost n d k (Kof43 (BstLean.Part42.spread θ) ε) (keepSet43 n d k (surrT n θ ε) ε) /
    (nu43 * baseline n d ε)⌉₊

/-- The parameters of the certificates: `p_sb = 0.46`, `x = 12`, `β = 3·10⁻⁴`, `η_c = 0.01`. -/
noncomputable def prm43 : Params43 := ⟨46 / 100, 12, 3 / 10000, 1 / 100⟩

end BstLean.Part43
