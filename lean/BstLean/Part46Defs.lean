import BstLean.Part45Defs

/-!
# Part 46, wave 0: frozen definitions — Theorem INT with the sharp Case A constant (Corollary VQ-top)

Sources: `delegations/answers/omSHARP3-opus-prover.md` §1–§3 and §5 (Lemma 1, Lemma 2, Theorem VC,
Lemma N, Corollary VQ-top). Specification: `delegations/answers/p46-spec-opus.md`. This file holds
definitions only. Provers must not edit it, and must not use `native_decide` or `axiom` anywhere.

Conventions. Part 41, 43 and 45 names are reused. `k = d_f = 3` throughout the new small-ball step.

* **Degree-2 maps `ℝⁿ → ℝᴺ`.** One coordinate is `quadQ A b v c = Σ_{ij} A_{ij} c_i c_j + Σ_i b_i c_i + v`.
  `A` need not be symmetric. `symFrob A = ‖(A + Aᵀ)/2‖_F²`. `varQ A b = 2·symFrob A + ‖b‖²` is the
  variance of `quadQ A b v` under `N(0, I_n)`. For `A : Fin N → Matrix`, `normSqP A b v c = ‖P(c)‖²`,
  `sigA2 A = σ_A² = 2 Σ_k symFrob (A k)` (the energy of the Hermite level-2 part), and `covM A b` is the
  covariance matrix of `P`: `covM_{kl} = Cov(P_k, P_l) = 2⟨sym A_k, sym A_l⟩_F + ⟨b_k, b_l⟩`.
  Its trace is `W = E‖P − EP‖²`.
* **Constants of Theorem VC.** `Jint = J = ∫₀^∞ |sin y| y^{−3/2} dy`; `LamInd = (2/π) J` (Lemma 2(a));
  `LamG = 2^{1/4} Γ(1/4)/√(2π)` (Lemma 2(b)); `c1 = 2^{−1/4} LamInd`; `c2 = Γ(1/4)/√π`;
  `FN μ* = (2μ*)^{−1/4} Γ(1/(2μ*) − 1/4)/Γ(1/(2μ*))` (Lemma N). The Lean proof uses `μ* = 2/5`, where
  `c2·FN(2/5) = 4 (5/4)^{1/4}/√π = 2.38623` (no `Γ(1/4)` remains), and `CT = 2.39`.
* **Case A level.** `a46 p = p⁴/(CT⁴ m_{1/4}⁴)` replaces Part 45's `aK 3 p = p⁴/(B₄ m_{1/4}⁴)`
  (`B₄ = 3073`). `t46 p n = a46·bK/(a46 + bK)` with Part 45's Case B level `bK 3 p n`.
* **Budget.** `gam46`, `Phi46`, `BudgetOK46` are Part 45's `gam45`, `Phi45`, `BudgetOK45` at `k = 3`,
  with `tK 3 p_sb n` replaced by `t46 p_sb n`. The certificates use Part 45's `prm45`.
-/

namespace BstLean.Part46

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss qformι)
open BstLean.Part36 (CoefIdxD DD mapMD)
open BstLean.Part41 (Mono phiSq frob Tens varU Pcal Nn Kc thetaT etaR etaK GamP Lk Bfix Pn)
open BstLean.Part43 (Params43 bq tau43 xi43 nu43)
open BstLean.Part45 (Bh mr bK)

variable {n d : ℕ}

/-! ## §1 Degree-2 maps `ℝⁿ → ℝᴺ` -/

/-- One coordinate: `q(c) = Σ_{ij} A_{ij} c_i c_j + Σ_i b_i c_i + v`. -/
def quadQ (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (v : ℝ) (c : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * c i * c j + ∑ i, b i * c i + v

/-- `‖(A + Aᵀ)/2‖_F²`. -/
noncomputable def symFrob (A : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, ((A i j + A j i) / 2) ^ 2

/-- `Var_{c∼N(0,I)} quadQ A b v c = 2‖(A + Aᵀ)/2‖_F² + ‖b‖²`. -/
noncomputable def varQ (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) : ℝ := 2 * symFrob A + ∑ i, b i ^ 2

/-- `‖P(c)‖² = Σ_k quadQ (A k) (b k) (v k) c ²`. -/
def normSqP {N : ℕ} (A : Fin N → Matrix (Fin n) (Fin n) ℝ) (b : Fin N → Fin n → ℝ) (v : Fin N → ℝ)
    (c : Fin n → ℝ) : ℝ :=
  ∑ k, quadQ (A k) (b k) (v k) c ^ 2

/-- `σ_A² = 2 Σ_k ‖(A_k + A_kᵀ)/2‖_F²`, the energy of the Hermite level-2 part of `P`. -/
noncomputable def sigA2 {N : ℕ} (A : Fin N → Matrix (Fin n) (Fin n) ℝ) : ℝ := 2 * ∑ k, symFrob (A k)

/-- The covariance matrix of `P`: `Cov(P_k, P_l) = 2⟨sym A_k, sym A_l⟩_F + ⟨b_k, b_l⟩`. -/
noncomputable def covM {N : ℕ} (A : Fin N → Matrix (Fin n) (Fin n) ℝ) (b : Fin N → Fin n → ℝ) :
    Matrix (Fin N) (Fin N) ℝ := fun k l =>
  2 * ∑ i, ∑ j, ((A k i j + A k j i) / 2) * ((A l i j + A l j i) / 2) + ∑ i, b k i * b l i

/-! ## §2 Constants of Lemma 2, Theorem VC and Lemma N -/

/-- `J = ∫₀^∞ |sin y| y^{−3/2} dy` (`= 3.35671…`). -/
noncomputable def Jint : ℝ := ∫ y in Set.Ioi (0 : ℝ), |Real.sin y| * y ^ (-(3 / 2 : ℝ))

/-- `Λ_ind = (2/π) J` (Lemma 2(a), the indicator through trapezoids). -/
noncomputable def LamInd : ℝ := 2 / Real.pi * Jint

/-- `Λ_G = 2^{1/4} Γ(1/4)/√(2π)` (Lemma 2(b), the Gaussian test function). -/
noncomputable def LamG : ℝ :=
  (2 : ℝ) ^ (1 / 4 : ℝ) * Real.Gamma (1 / 4) / Real.sqrt (2 * Real.pi)

/-- `c₁ = 2^{−1/4} Λ_ind` (Strategy 1). -/
noncomputable def c1 : ℝ := (2 : ℝ) ^ (-(1 / 4 : ℝ)) * LamInd

/-- `c₂ = Γ(1/4)/√π` (Strategy 2). -/
noncomputable def c2 : ℝ := Real.Gamma (1 / 4) / Real.sqrt Real.pi

/-- `F(μ*) = (2μ*)^{−1/4} Γ(1/(2μ*) − 1/4)/Γ(1/(2μ*))` (Lemma N). -/
noncomputable def FN (ms : ℝ) : ℝ :=
  (2 * ms) ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / (2 * ms) - 1 / 4) / Real.Gamma (1 / (2 * ms))

/-- The Lean constant of Corollary VQ-top: `C_T = 2.39` (paper: `2.34`). -/
noncomputable def CT : ℝ := 239 / 100

/-! ## §3 The Case A level and the budget at `k = 3` -/

/-- `a₃(p) = p⁴/(C_T⁴ m_{1/4}⁴)` (Case A level from Corollary VQ-top). -/
noncomputable def a46 (p : ℝ) : ℝ := p ^ 4 / (CT ^ 4 * mr (1 / 4) ^ 4)

/-- `t₃(p, n) = a₃ b₃/(a₃ + b₃)`, `b₃ = bK 3 p n` (Case B with `n₁ = n`, unchanged). -/
noncomputable def t46 (p : ℝ) (n : ℕ) : ℝ := a46 p * bK 3 p n / (a46 p + bK 3 p n)

/-- `γ = √(t₃(p_sb, n)/K_c) − η_3 √(Γ'/β)`. -/
noncomputable def gam46 (n d : ℕ) (q : Params43) : ℝ :=
  Real.sqrt (t46 q.psb n / Kc n d 3 q.eta) - etaK n d 3 q.x * Real.sqrt (GamP n d 3 / q.beta)

/-- `Φ(n) = p_sb + 2e^{−x} + β + L τ / ((1 − ξ)² γ²)` at `k = 3`. -/
noncomputable def Phi46 (n d : ℕ) (q : Params43) : ℝ :=
  q.psb + 2 * Real.exp (-q.x) + q.beta + Lk 3 * tau43 n d 3 / ((1 - xi43) ^ 2 * gam46 n d q ^ 2)

/-- The conditions of the proof of Theorem G at `n`, `k = 3`, small-ball level `t₃(p_sb, n)`. -/
def BudgetOK46 (n d : ℕ) (q : Params43) (δ : ℝ) : Prop :=
  2 ≤ n ∧ 1 ≤ d ∧ 0 < tau43 n d 3 ∧
  0 < q.psb ∧ q.psb ≤ 1 ∧ 0 < q.x ∧ 0 < q.beta ∧ 0 < q.eta ∧
  (1 + 1 / q.eta) * thetaT n d 3 < 1 ∧ etaR n d q.x < 1 ∧ 0 < Kc n d 3 q.eta ∧
  0 < gam46 n d q ∧ 455 / 1000 * Bfix n 3 < (1 - nu43) * (91 / 100) * Pn n d ∧
  Phi46 n d q ≤ δ

end BstLean.Part46
