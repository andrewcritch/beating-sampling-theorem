import BstLean.Part43Defs

/-!
# Part 45, wave 0: frozen definitions — the sharper small-ball step (Theorem INT) at `δ = 1/100`

Sources: `delegations/answers/omSHARP-opus-prover.md` §1–§3 (Lemma R, Lemma H, Theorem CC) and
`delegations/answers/omSHARP2-codex-prover.md` §2–§4 (Theorem INT). Specification:
`delegations/answers/p45-spec-opus.md`. This file holds definitions only. Provers must not edit it,
and must not use `native_decide` or `axiom` anywhere.

Conventions. Part 41 and Part 43 names are reused (`Pcal`, `varU`, `bq`, `Nn`, `Kc`, `frob`, `mapMD`,
`CoefIdxD`, `DD`, `stdGauss`, `FradeliziGauss`, `Params43`, `tau43`, `xi43`, `nu43`). `k = d_f`, `d = d_M`.
`V(Z) = Var_μ 𝒫(Z)`, `𝒫(Z)(x) = Σ_j D^{−j/2} T_j[(Zφ(x))^{⊗j}]`, so `F_j = D^{−j/2} T_j`.

* **Constants of Theorem INT.** `Bh h = 1 + 2^{2h−1} h!` (scalar bound (1)); `mr r = 2^{−r} Γ(1/2 − r)/√π`
  (`= E|g|^{−2r}`, negative moment (2)); `aK k p = p^{2k−2}/(B_{2k−2} m_r^{2k−2})`, `r = 1/(2k−2)`;
  `bK k p n = n p^{2k}/((k−1) B_{2k})`; `tK k p n = aK bK/(aK + bK)` (Case B with `n₁ = n`).
* **The constant-column split.** `joinZ c Z` replaces the constant column of `Z` (the coefficients of
  the degree-`0` monomial, indices `⟨0, (∅, a)⟩`) by `c ∈ ℝⁿ`.
* **Lemma H.** `wbar μ Z x = Zφ(x) − E_μ Zφ` (the constant column cancels); `consW a w` is the word
  `(a, w₁, …, w_{k−1})`; `Qk μ k T Z = k!·k·D^{−k}·E_μ Σ_w (Σ_a T_k[a, w] w̄_a(x))²`
  `= k!·k·E_μ ‖F_k[w̄(x), ·^{k−1}]‖²`; `betaK = β_k = k!·k·‖F_k‖² = k!·k·‖T_k‖²/D^k`.
* **Lemma R.** `Sbar μ k T = E_μ Σ_{s=1}^k n^{−(k−s)} s!·s·‖b_s(‖φ(x)‖²)‖²` (the paper's `S̄`).
* **Budget.** `gam45`, `Phi45`, `BudgetOK45` are Part 44's `gam43`, `Phi43`, `BudgetOK44` with the
  small-ball level `tsb k p_sb` replaced by `tK k p_sb n`, and the side condition `p_sb < 1 − e^{−1}`
  replaced by `p_sb ≤ 1`. `prm45 = (0.008, 16, 10⁻⁶, 0.01)`.
-/

namespace BstLean.Part45

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD DD mapMD)
open BstLean.Part41 (Mono phiSq frob Tens varU Pcal Nn Kc thetaT etaR etaK GamP Lk Bfix Pn)
open BstLean.Part43 (Params43 bq tau43 xi43 nu43)

variable {n d : ℕ}

/-! ## §1 Constants of Theorem INT -/

/-- `B_h = 1 + 2^{2h−1} h!`: `Pr{W < u E W} ≤ (B_h u)^{1/h}` for a nonnegative Gaussian polynomial `W`
of degree `≤ h`. -/
noncomputable def Bh (h : ℕ) : ℝ := 1 + 2 ^ (2 * h - 1) * (h.factorial : ℝ)

/-- `m_r = E|g|^{−2r} = 2^{−r} Γ(1/2 − r)/√π` (`0 < r < 1/2`). -/
noncomputable def mr (r : ℝ) : ℝ := (2 : ℝ) ^ (-r) * Real.Gamma (1 / 2 - r) / Real.sqrt Real.pi

/-- The exponent `r = 1/(2k − 2)` of the integrated step. -/
noncomputable def rK (k : ℕ) : ℝ := 1 / ((2 * k - 2 : ℕ) : ℝ)

/-- `a_k(p) = p^{2k−2} / (B_{2k−2} m_r^{2k−2})`, `r = 1/(2k−2)` (Case A level). -/
noncomputable def aK (k : ℕ) (p : ℝ) : ℝ :=
  p ^ (2 * k - 2) / (Bh (2 * k - 2) * mr (rK k) ^ (2 * k - 2))

/-- `b_k(p, n) = n p^{2k} / ((k − 1) B_{2k})` (Case B level, `n₁ = n`). -/
noncomputable def bK (k : ℕ) (p : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * p ^ (2 * k) / (((k - 1 : ℕ) : ℝ) * Bh (2 * k))

/-- `t_k(p, n) = a_k b_k / (a_k + b_k)`: Theorem INT's uniform level. -/
noncomputable def tK (k : ℕ) (p : ℝ) (n : ℕ) : ℝ := aK k p * bK k p n / (aK k p + bK k p n)

/-! ## §2 The constant-column split -/

/-- `joinZ c Z`: `Z` with its constant column (indices of degree `0`) replaced by `c`. -/
def joinZ (c : Fin n → ℝ) (Z : CoefIdxD n d → ℝ) : CoefIdxD n d → ℝ := fun ι =>
  if ι.1 = 0 then c ι.2.2 else Z ι

/-! ## §3 Lemma H: the conditional floor `Q` and `β_k` -/

/-- `w̄(x) = Zφ(x) − E_μ Zφ` (the constant column cancels). -/
noncomputable def wbar (μ : Measure (Fin n → ℝ)) (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) (a : Fin n) : ℝ :=
  mapMD Z x a - ∫ y, mapMD Z y a ∂μ

/-- The word `(a, w₁, …, w_{k−1})` of length `k`. -/
def consW {k : ℕ} (a : Fin n) (w : Fin (k - 1) → Fin n) : Fin k → Fin n := fun t =>
  if h : t.1 = 0 then a else w ⟨t.1 - 1, by have := t.2; omega⟩

/-- `Q(Z) = k!·k·D^{−k}·E_μ Σ_{w ∈ [n]^{k−1}} (Σ_a T_k[a, w] w̄_a(x))² = k!·k·E_μ‖F_k[w̄(x), ·]‖²`. -/
noncomputable def Qk (μ : Measure (Fin n → ℝ)) (k : ℕ) (T : Tens n) (Z : CoefIdxD n d → ℝ) : ℝ :=
  ((k.factorial : ℝ) * k / DD n d ^ k) *
    ∫ x, ∑ w : Fin (k - 1) → Fin n, (∑ a : Fin n, T k (consW a w) * wbar μ Z x a) ^ 2 ∂μ

/-- `β_k = k!·k·‖F_k‖² = k!·k·‖T_k‖²/D^k`. -/
noncomputable def betaK (n d k : ℕ) (T : Tens n) : ℝ :=
  (k.factorial : ℝ) * k * frob (T k) / DD n d ^ k

/-! ## §4 Lemma R: the weighted floor `S̄` -/

/-- `S̄ = E_μ Σ_{s=1}^k n^{−(k−s)} s!·s·‖b_s(‖φ(x)‖²)‖²`. -/
noncomputable def Sbar (μ : Measure (Fin n → ℝ)) (k : ℕ) (T : Tens n) : ℝ :=
  ∫ x, ∑ s ∈ Finset.Icc 1 k,
    (s.factorial : ℝ) * s * frob (bq n d k T s (phiSq d x)) / (n : ℝ) ^ (k - s) ∂μ

/-! ## §5 Budget -/

/-- `γ = √(t_k(p_sb, n)/K_c) − η_k √(Γ'/β)`. -/
noncomputable def gam45 (n d k : ℕ) (q : Params43) : ℝ :=
  Real.sqrt (tK k q.psb n / Kc n d k q.eta) - etaK n d k q.x * Real.sqrt (GamP n d k / q.beta)

/-- `Φ(n) = p_sb + 2e^{−x} + β + L τ / ((1 − ξ)² γ²)`. -/
noncomputable def Phi45 (n d k : ℕ) (q : Params43) : ℝ :=
  q.psb + 2 * Real.exp (-q.x) + q.beta + Lk k * tau43 n d k / ((1 - xi43) ^ 2 * gam45 n d k q ^ 2)

/-- The conditions of the proof of Theorem G at `n`, small-ball level `t_k(p_sb, n)`, failure budget `δ`. -/
def BudgetOK45 (n d k : ℕ) (q : Params43) (δ : ℝ) : Prop :=
  2 ≤ n ∧ 1 ≤ d ∧ 0 < tau43 n d k ∧
  0 < q.psb ∧ q.psb ≤ 1 ∧ 0 < q.x ∧ 0 < q.beta ∧ 0 < q.eta ∧
  (1 + 1 / q.eta) * thetaT n d k < 1 ∧ etaR n d q.x < 1 ∧ 0 < Kc n d k q.eta ∧
  0 < gam45 n d k q ∧ 455 / 1000 * Bfix n k < (1 - nu43) * (91 / 100) * Pn n d ∧
  Phi45 n d k q ≤ δ

/-- The parameters of the certificates: `p_sb = 0.008`, `x = 16`, `β = 10⁻⁶`, `η_c = 0.01`. -/
noncomputable def prm45 : Params43 := ⟨8 / 1000, 16, 1 / 1000000, 1 / 100⟩

end BstLean.Part45
