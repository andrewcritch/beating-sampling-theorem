import BstLean.Part38Defs

/-!
# Part 39, wave 0: frozen definitions for the `(2,2)` theorem at a single Bingham spike

Paper: `proofs/option-m/39-explicit-22-bingham-spike.tex` (Theorem A). Specification:
`delegations/answers/p39-spec-opus.md`. This file holds definitions only. Provers must not edit it,
and must not use `native_decide` anywhere.

Conventions.
* `θ = lam · e₁` is `spikeθ lam : Fin n → ℝ`; the spike coordinate is the index with value `0`.
  Definitions test `i.val = 0`, so that they need no `NeZero n` instance. Only the 3-set floor
  (`coef3`, `Y3`, `SpikeParityGe`) uses `(0 : Fin n)` and takes `[NeZero n]`.
* `D = bingham n (spikeθ lam)` and `D_K = binghamK n K (spikeθ lam)` are Part 37's laws. The density
  of `D_K` is `T_K(lam x₁²)`, the paper's `D_K` (Lemma `series`).
* `tperp x = Σ_{i ≠ 0} xᵢ²` is the paper's `t = 1 − s²` on the sphere. `tauD n lam k = E_D t^k`.
* The program computes `τ₁, τ₂` of `D_K` by the one-dimensional series (`Sser`, `tau1K`, `tau2K`)
  and builds the moment arrays `muS`, `WS` from them (paper Lemma `structure`).
* Branches E (Part 37's `EofB`), `H_S` (`HofS`) and `U_S` (`UofS`); residual matrices `AHS`, `AUS`.
* The precision is `Kof39 lam ε`: the least `K ≥ Kmin lam = max(⌈7.39 lam⌉, 9)` with
  `η_K = r_K/(1 − r_K) ≤ ε/50`, `r_K = lam^{K+1}/(K+1)!` (a rational test, as in part 38).
* Costs (definitions, paper cost model): `CE39`, `CH39`, `CU39` and `Cmom39 K = 13(K+3) + 20`.
-/

namespace BstLean.Part39

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss qformι funF frobSq CoefIdx cOf LOf aOf Bof varOf unitOf qformC
  uniformSphere kappa eta)
open BstLean.Part33 (floorW4 rawQ Dc)
open BstLean.Part29 (coefX)
open BstLean.Part37 (qth bingham Zth taylorExp ZK binghamK tauB EofB P37)

variable {n : ℕ}

/-! ## §1 The spike, the law, `t` -/

/-- `θ = lam · e₁` (the spike coordinate is the index `0`). -/
def spikeθ (lam : ℝ) : Fin n → ℝ := fun i => if i.val = 0 then lam else 0

/-- `t = Σ_{i ≠ 0} xᵢ²` (`= 1 − x₁²` on the sphere). -/
def tperp (x : Fin n → ℝ) : ℝ := ∑ i, if i.val = 0 then 0 else x i ^ 2

/-- `τ_k(D) = E_{D(lam e₁)} t^k`. -/
noncomputable def tauD (n : ℕ) (lam : ℝ) (k : ℕ) : ℝ := ∫ x, tperp x ^ k ∂bingham n (spikeθ lam)

/-! ## §2 The program's moment computation (paper Lemma `series`) -/

/-- `b_m = ∏_{r<m} (1/2 + r)/(n/2 + r) = E_U x₁^{2m}`. -/
noncomputable def bU (n m : ℕ) : ℝ := ∏ r ∈ Finset.range m, ((1 / 2 + r) / ((n : ℝ) / 2 + r))

/-- `S_k = Σ_{j ≤ K} lam^j/j! · b_{j+k}`. -/
noncomputable def Sser (n K : ℕ) (lam : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (K + 1), lam ^ j / (j.factorial : ℝ) * bU n (j + k)

/-- `τ₁(D_K) = 1 − S₁/S₀`, as the program computes it. -/
noncomputable def tau1K (n K : ℕ) (lam : ℝ) : ℝ := 1 - Sser n K lam 1 / Sser n K lam 0

/-- `τ₂(D_K) = 1 − 2S₁/S₀ + S₂/S₀`, as the program computes it. -/
noncomputable def tau2K (n K : ℕ) (lam : ℝ) : ℝ :=
  1 - 2 * (Sser n K lam 1 / Sser n K lam 0) + Sser n K lam 2 / Sser n K lam 0

/-- `w = τ₂/((n−1)(n+1))`. -/
noncomputable def wS (n : ℕ) (t2 : ℝ) : ℝ := t2 / (((n : ℝ) - 1) * ((n : ℝ) + 1))

/-- `a = (τ₁ − τ₂)/(n−1)`. -/
noncomputable def aS (n : ℕ) (t1 t2 : ℝ) : ℝ := (t1 - t2) / ((n : ℝ) - 1)

/-- The second moments: `μ₁ = 1 − τ₁`, `μ_⊥ = τ₁/(n−1)`. -/
noncomputable def muS (n : ℕ) (t1 _t2 : ℝ) : Fin n → ℝ := fun i =>
  if i.val = 0 then 1 - t1 else t1 / ((n : ℝ) - 1)

/-- The fourth moments `W i j = E xᵢ² xⱼ²` (`W i i = E xᵢ⁴`): `ν = 1 − 2τ₁ + τ₂` at `(1,1)`, `a` on
  `(1,j)`, `3w` on `(j,j)`, `w` on `(j,k)`, `j ≠ k` in `⊥`. -/
noncomputable def WS (n : ℕ) (t1 t2 : ℝ) : Fin n → Fin n → ℝ := fun i j =>
  if i.val = 0 ∧ j.val = 0 then 1 - 2 * t1 + t2
  else if i.val = 0 ∨ j.val = 0 then aS n t1 t2
  else if i = j then 3 * wS n t2 else wS n t2

/-! ## §3 The branches `H_S`, `U_S` and their residual matrices (paper Lemma `branches`) -/

/-- `tr R_H = w (n−1)(2 + (n−2)/2)`. -/
noncomputable def trRH (n : ℕ) (t2 : ℝ) : ℝ :=
  wS n t2 * ((n : ℝ) - 1) * (2 + ((n : ℝ) - 2) / 2)

/-- `tr R_U = (n−1) μ_⊥ + 2w(n−1) + (n−1) a + w (n−1)(n−2)/2`. -/
noncomputable def trRU (n : ℕ) (t1 t2 : ℝ) : ℝ :=
  ((n : ℝ) - 1) * (t1 / ((n : ℝ) - 1)) + 2 * wS n t2 * ((n : ℝ) - 1) + ((n : ℝ) - 1) * aS n t1 t2
    + wS n t2 * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 2

/-- Branch `H_S`: all of `MGMᵀ` except `M R_H Mᵀ`, which is replaced by its mean. The kept squares
  block is `W − 2w I_⊥`; the kept cross block is the row of the spike index (weight `a`). -/
noncomputable def HofS (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (M : CoefIdx n → ℝ)
    (t1 t2 : ℝ) : ℝ :=
  f0 + ∑ k, g k * (cOf M k + tauB M (muS n t1 t2) k)
    + ∑ k, ∑ l, F k l * cOf M k * (cOf M l + 2 * tauB M (muS n t1 t2) l)
    + ∑ k, ∑ l, F k l * ∑ i, LOf M k i * muS n t1 t2 i * LOf M l i
    + ∑ k, ∑ l, F k l * ∑ i, ∑ j, aOf M k i i *
        (WS n t1 t2 i j - (if i = j ∧ i.val ≠ 0 then 2 * wS n t2 else 0)) * aOf M l j j
    + ∑ k, ∑ l, F k l * ∑ i, ∑ j,
        (if i.val = 0 ∧ i < j then WS n t1 t2 i j * aOf M k i j * aOf M l i j else 0)
    + (∑ k, F k k) * trRH n t2 / Dc n

/-- Branch `U_S`: `f₀ + bᵀm̄ + m̄ᵀFm̄ + μ₁ L₁ᵀFL₁ + ⟨F, D_g K' D_gᵀ⟩ + tr F tr R_U / D_c`, with
  `K' = Cov(xᵢ², xⱼ²) − 2w I_⊥`. -/
noncomputable def UofS (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (M : CoefIdx n → ℝ)
    (t1 t2 : ℝ) : ℝ :=
  f0 + ∑ k, g k * (cOf M k + tauB M (muS n t1 t2) k)
    + ∑ k, ∑ l, F k l * (cOf M k + tauB M (muS n t1 t2) k) * (cOf M l + tauB M (muS n t1 t2) l)
    + ∑ k, ∑ l, F k l * ∑ i, (if i.val = 0 then LOf M k i * muS n t1 t2 i * LOf M l i else 0)
    + ∑ k, ∑ l, F k l * ∑ i, ∑ j, aOf M k i i *
        (WS n t1 t2 i j - muS n t1 t2 i * muS n t1 t2 j
          - (if i = j ∧ i.val ≠ 0 then 2 * wS n t2 else 0)) * aOf M l j j
    + (∑ k, F k k) * trRU n t1 t2 / Dc n

/-- `A_H = F ⊗ R_H`: `2w` on the squares of `⊥`, `w` on the cross pairs inside `⊥`. -/
noncomputable def AHS (F : Matrix (Fin n) (Fin n) ℝ) (t2 : ℝ) :
    Matrix (CoefIdx n) (CoefIdx n) ℝ := fun α β =>
  match α, β with
  | Sum.inr (Sum.inr p), Sum.inr (Sum.inr q) =>
      F p.1.2.2 q.1.2.2 *
        (if p.1.1 = p.1.2.1 ∧ q.1.1 = q.1.2.1 ∧ p.1.1 = q.1.1 ∧ p.1.1.val ≠ 0 then 2 * wS n t2
        else if p.1.1 < p.1.2.1 ∧ p.1.1 = q.1.1 ∧ p.1.2.1 = q.1.2.1 ∧ p.1.1.val ≠ 0 then wS n t2
        else 0)
  | _, _ => 0

/-- `A_U = F ⊗ R_U`: `μ_⊥` on the linear columns of `⊥`, `2w` on the squares of `⊥`, `a` on the
  cross pairs `(1, j)`, `w` on the cross pairs inside `⊥`. -/
noncomputable def AUS (F : Matrix (Fin n) (Fin n) ℝ) (t1 t2 : ℝ) :
    Matrix (CoefIdx n) (CoefIdx n) ℝ := fun α β =>
  match α, β with
  | Sum.inr (Sum.inl (k, i)), Sum.inr (Sum.inl (l, i')) =>
      if i = i' ∧ i.val ≠ 0 then F k l * (t1 / ((n : ℝ) - 1)) else 0
  | Sum.inr (Sum.inr p), Sum.inr (Sum.inr q) =>
      F p.1.2.2 q.1.2.2 *
        (if p.1.1 = p.1.2.1 ∧ q.1.1 = q.1.2.1 ∧ p.1.1 = q.1.1 ∧ p.1.1.val ≠ 0 then 2 * wS n t2
        else if p.1.1 < p.1.2.1 ∧ p.1.1 = q.1.1 ∧ p.1.2.1 = q.1.2.1 then
          (if p.1.1.val = 0 then aS n t1 t2 else wS n t2)
        else 0)
  | _, _ => 0

/-! ## §4 The floors (paper Lemmas `floor4`, `floor3`, `floor`) -/

/-- `Σ_{S ⊂ ⊥, |S| = 4} C_S²` (raw coefficients `G = rawQ Z`; no weight). -/
noncomputable def Y4perp (F : Matrix (Fin n) (Fin n) ℝ) (G : Fin n × Fin n × Fin n → ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ.filter (fun i : Fin n => i.val ≠ 0)).powersetCard 4, coefX F S G

/-- `C'_{jk}`, the coefficient of `x₁ xⱼ x_k` in `f(Z φ(x))` (`F` symmetric):
  `2(L₁ᵀ F Z_{(jk)} + Lⱼᵀ F Z_{(1k)} + L_kᵀ F Z_{(1j)})`. -/
noncomputable def coef3 [NeZero n] (F : Matrix (Fin n) (Fin n) ℝ) (Z : CoefIdx n → ℝ) (j k : Fin n) :
    ℝ :=
  2 * ∑ a, ∑ b, F a b *
    (LOf Z a 0 * aOf Z b j k + LOf Z a j * aOf Z b 0 k + LOf Z a k * aOf Z b 0 j)

/-- `Y₃ = Σ_{0 < j < k} C'_{jk}²`. -/
noncomputable def Y3 [NeZero n] (F : Matrix (Fin n) (Fin n) ℝ) (Z : CoefIdx n → ℝ) : ℝ :=
  ∑ j, ∑ k, if j.val ≠ 0 ∧ j < k then coef3 F Z j k ^ 2 else 0

/-- `η₃ = 4(2n−1)/C(n−1,2) = 8(2n−1)/((n−1)(n−2))`. -/
noncomputable def eta3 (n : ℝ) : ℝ := 8 * (2 * n - 1) / ((n - 1) * (n - 2))

/-- `β₃ = 2(n−2)/(n+1)`. -/
noncomputable def beta3 (n : ℝ) : ℝ := 2 * (n - 2) / (n + 1)

/-- A sign-symmetric law with lower bounds on the two families of parity weights the floor uses:
  `E x_S² ≥ w4` for four distinct indices in `⊥`, and `E x₁² xⱼ² x_k² ≥ w3` for `j ≠ k` in `⊥`. -/
structure SpikeParityGe (n : ℕ) [NeZero n] (μ : Measure (Fin n → ℝ)) (w4 w3 : ℝ) : Prop where
  integ : ∀ (r : ℕ), r ≤ 8 → ∀ τ : Fin r → Fin n,
    Integrable (fun x : Fin n → ℝ => ∏ s, x (τ s)) μ
  parity : ∀ (r : ℕ), r ≤ 8 → ∀ τ : Fin r → Fin n,
    (∃ i, Odd (Finset.univ.filter (fun s => τ s = i)).card) → ∫ x, ∏ s, x (τ s) ∂μ = 0
  sq4 : ∀ σ : Fin 4 → Fin n, Function.Injective σ → (∀ s, (σ s).val ≠ 0) →
    w4 ≤ ∫ x, ∏ s, x (σ s) ^ 2 ∂μ
  sq3 : ∀ j k : Fin n, j ≠ k → j.val ≠ 0 → k.val ≠ 0 →
    w3 ≤ ∫ x, x 0 ^ 2 * x j ^ 2 * x k ^ 2 ∂μ

/-! ## §5 Thresholds (`λ`-free; paper Theorem A) -/

/-- `g_H = (n+6)/(2(n−1)(n+1)²)`: `‖R_H‖_F² = g_H τ₂²`. -/
noncomputable def gH39 (n : ℝ) : ℝ := (n + 6) / (2 * (n - 1) * (n + 1) ^ 2)

/-- `g_U = 2/(n−1) + g_H`. -/
noncomputable def gU39 (n : ℝ) : ℝ := 2 / (n - 1) + gH39 n

/-- `ρ_K = 1004/1000`. -/
noncomputable def rhoK : ℝ := 1004 / 1000

/-- `q = δ − η'_{n−1} − η₃`. -/
noncomputable def q39 (n δ : ℝ) : ℝ := δ - eta (n - 1) - eta3 n

/-- `h² = 8 ρ_K g_H/(κ_{n−1} q (49/50)²)`. -/
noncomputable def hSq39 (n δ : ℝ) : ℝ :=
  8 * rhoK * gH39 n / (kappa (n - 1) * q39 n δ * (49 / 50) ^ 2)

/-- `u² = 8 ρ_K g_U/(κ_{n−1} q (49/50)²)`. -/
noncomputable def uSq39 (n δ : ℝ) : ℝ :=
  8 * rhoK * gU39 n / (kappa (n - 1) * q39 n δ * (49 / 50) ^ 2)

/-! ## §6 The precision -/

/-- `r_K = lam^{K+1}/(K+1)!`: `1 − r_K ≤ T_K(s)/e^s ≤ 1` on `0 ≤ s ≤ lam`. -/
noncomputable def rS (lam : ℝ) (K : ℕ) : ℝ := lam ^ (K + 1) / ((K + 1).factorial : ℝ)

/-- `η_K = r_K/(1 − r_K)` bounds `|dD_K/dD − 1|`. -/
noncomputable def etaS (lam : ℝ) (K : ℕ) : ℝ := rS lam K / (1 - rS lam K)

/-- `K_min = max(⌈7.39 lam⌉, 9)`. Past it, `r_K ≤ e^{−10}` and `η_{K+1} ≤ η_K/7`. -/
noncomputable def Kmin (lam : ℝ) : ℕ := max ⌈(739 / 100 : ℝ) * lam⌉₊ 9

/-- The program's `K`: the least `K ≥ Kmin lam` with `η_K ≤ ε/50` (`Kmin lam` if there is none). -/
noncomputable def Kof39 (lam ε : ℝ) : ℕ := by
  classical
  exact if h : ∃ K : ℕ, Kmin lam ≤ K ∧ etaS lam K ≤ ε / 50 then Nat.find h else Kmin lam

/-- A natural-number bound for `K_min` over `0 ≤ lam ≤ n^{3/2}`:
  `7.39 n^{3/2} ≤ 7.39 n(n+121)/22` (AM–GM at `√n = 11`). -/
def Kbar (n : ℕ) : ℕ := 739 * n * (n + 121) / 2200 + 1

/-- The real-valued form of `Kbar` used by the certificates. -/
noncomputable def KbarR (n : ℝ) : ℝ := 739 * n * (n + 121) / 2200 + 1

/-! ## §7 Costs (paper cost model; definitions) -/

/-- The counted cost of the moment series at precision `K`. -/
noncomputable def Cmom39 (K : ℝ) : ℝ := 13 * (K + 3) + 20

/-- Branch E (part 37's charge, without its moment part). -/
noncomputable def CE39 (n : ℝ) : ℝ :=
  n ^ 2 * (n + 1) ^ 2 / 2 + n ^ 2 * (n - 1) / 2 + 6 * n ^ 3 + 25 * n ^ 2 + 20 * n + 100

/-- Branch `H_S` (counted). -/
noncomputable def CH39 (n : ℝ) : ℝ := 2 * n ^ 3 + 12 * n ^ 2 + 12 * n + 19

/-- Branch `U_S` (counted). -/
noncomputable def CU39 (n : ℝ) : ℝ := 9 * n ^ 2 + 11 * n + 28

/-! ## §8 The program and its cost -/

/-- The program `g_{lam,f,ε}`: E if `ε² < h²`, `H_S` if `h² ≤ ε² < u²`, `U_S` otherwise, at the
  moments `τ₁, τ₂` of `D_K` computed by the series with `K = Kof39 lam ε`. -/
noncomputable def gOf39 (lam δ ε : ℝ) (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (M : CoefIdx n → ℝ) : ℝ :=
  if ε ^ 2 < hSq39 n δ then
    EofB f0 g F M (muS n (tau1K n (Kof39 lam ε) lam) (tau2K n (Kof39 lam ε) lam))
      (WS n (tau1K n (Kof39 lam ε) lam) (tau2K n (Kof39 lam ε) lam))
  else if ε ^ 2 < uSq39 n δ then
    HofS f0 g F M (tau1K n (Kof39 lam ε) lam) (tau2K n (Kof39 lam ε) lam)
  else UofS f0 g F M (tau1K n (Kof39 lam ε) lam) (tau2K n (Kof39 lam ε) lam)

/-- The cost of the branch the program takes, moment series included. -/
noncomputable def costOf39 (n : ℕ) (lam δ ε : ℝ) : ℝ :=
  if ε ^ 2 < hSq39 n δ then CE39 n + Cmom39 (Kof39 lam ε)
  else if ε ^ 2 < uSq39 n δ then CH39 n + Cmom39 (Kof39 lam ε)
  else CU39 n + Cmom39 (Kof39 lam ε)

end BstLean.Part39
