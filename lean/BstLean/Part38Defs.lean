import BstLean.Part37Defs

/-!
# Part 38, wave 0: frozen definitions for the `(2,2)` theorem over the ball `‖θ‖_∞ ≤ n/16`

Paper: `proofs/option-m/38-explicit-22-bingham-linear-ball.tex`. Specification:
`delegations/answers/p38-spec-opus.md`. This file holds definitions only. Provers must not edit it,
and must not use `native_decide` anywhere.

Conventions.
* Every radius-free definition is Part 37's and is reused: `qth`, `bingham`, `Zth`, `taylorExp`,
  `ZK`, `binghamK`, the series (`phiTab`, `phi0`, `mulGeom`, `phiW`, `dfC`, `rhoP`, `numK`, `momK`,
  `muK`, `WK`, `phiCoef`, `wmono`), `SymMoments`, `tauB`, `trB`, `secB`, `EofB`, `UofB`, `AUB`,
  `sdSq` and the costs `P37`, `momC`, `momCE`, `CE`, `CH`, `CU`.
* `θ : Fin n → ℝ` with `‖θ‖_∞ ≤ n/16` (`InBall38 θ`). The paper's `θ ∈ ℝᵗ`, `t ≤ n`, is the case `θ
  i = 0` for `i ≥ t`. The costs use the worst case `t = n`.
* Route (specification §1): the moment error goes through the law `D_K` (Part 37's route). The
  moment bounds under `D(θ)` come from a dimension-raising identity (`Part38Raise`) and a
  two-coordinate extension bound (`Part38Split`); they replace the paper's Gaussian conditioning, so
  the proof uses no unimodality and no Yamazato theorem.
* Branch H takes its constant `ω` as an argument (`HofBW`, `AHBW`, `gpSqW`); the program passes
  `omega38 n`.
* The program's precision is `Kof38 n ε`: the least `K ≥ K12 n = ⌊3n/4⌋ + 1` with `η_K ≤ ε/50`.
-/

namespace BstLean.Part38

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss qformι funF frobSq CoefIdx cOf LOf aOf Bof varOf unitOf qformC
  uniformSphere kappa eta)
open BstLean.Part33 (SphereProd floorY4 floorW4 rawQ Dc)
open BstLean.Part37 (qth bingham Zth taylorExp ZK binghamK dfC rhoP momK muK WK wmono tauB trB
  EofB UofB AUB sdSq P37 momC momCE CE CH CU)

variable {n : ℕ}

/-! ## §1 The ball and the dimension-raising maps -/

/-- The Bingham ball `‖θ‖_∞ ≤ n/16`. -/
def InBall38 (θ : Fin n → ℝ) : Prop := ∀ i, |θ i| ≤ (n : ℝ) / 16

/-- `θ⁺ = (θ, θᵢ, θᵢ) ∈ ℝ^{n+2}`: the parameter of the raised problem (`Part38Raise`). -/
def raiseθ (θ : Fin n → ℝ) (i : Fin n) : Fin (n + 2) → ℝ := Fin.append θ (fun _ : Fin 2 => θ i)

/-- The first `N` coordinates of `ϑ ∈ ℝ^{N+2}`. -/
def restrict2 {N : ℕ} (ϑ : Fin (N + 2) → ℝ) : Fin N → ℝ := fun i => ϑ (Fin.castAdd 2 i)

/-! ## §2 Sign-symmetric laws with a lower bound on the squares (the floor) -/

/-- Part 29's `SphereParity` with `E x_S² ≥ w` in place of `E x_S² = w`. -/
structure SphereParityGe (n : ℕ) (μ : Measure (Fin n → ℝ)) (w : ℝ) : Prop where
  integ : ∀ (r : ℕ), r ≤ 8 → ∀ τ : Fin r → Fin n,
    Integrable (fun x : Fin n → ℝ => ∏ s, x (τ s)) μ
  parity : ∀ (r : ℕ), r ≤ 8 → ∀ τ : Fin r → Fin n,
    (∃ i, Odd (Finset.univ.filter (fun s => τ s = i)).card) → ∫ x, ∏ s, x (τ s) ∂μ = 0
  square : ∀ σ : Fin 4 → Fin n, Function.Injective σ → w ≤ ∫ x, ∏ s, x (σ s) ^ 2 ∂μ

/-! ## §3 Branch H with a free constant `ω` -/

/-- Branch H with constant `ω` (Part 37's `HofB` with `omega37 n` replaced by `ω`). -/
noncomputable def HofBW (ω : ℝ) (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (M : CoefIdx n → ℝ) (mu m4 : Fin n → ℝ) : ℝ :=
  f0 + ∑ k, g k * (cOf M k + tauB M mu k)
    + ∑ k, ∑ l, F k l * cOf M k * (cOf M l + 2 * tauB M mu l)
    + ∑ k, ∑ l, F k l * ∑ i, LOf M k i * mu i * LOf M l i
    + ω * ∑ k, ∑ l, F k l * trB M k * trB M l
    + (∑ k, F k k) * ((1 + ∑ i, m4 i) / 2 - n * ω) / Dc n

/-- `A_H = F ⊗ G'`, `G' = (W − ωJ) ⊕ diag(m_ij)`, with constant `ω`. -/
noncomputable def AHBW (ω : ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (W : Fin n → Fin n → ℝ) :
    Matrix (CoefIdx n) (CoefIdx n) ℝ := fun α β =>
  match α, β with
  | Sum.inr (Sum.inr p), Sum.inr (Sum.inr q) =>
      F p.1.2.2 q.1.2.2 *
        (if p.1.1 = p.1.2.1 ∧ q.1.1 = q.1.2.1 then W p.1.1 q.1.1 - ω
        else if p.1.1 < p.1.2.1 ∧ p.1.1 = q.1.1 ∧ p.1.2.1 = q.1.2.1 then W p.1.1 p.1.2.1 else 0)
  | _, _ => 0

/-- `‖G'‖_F²` with constant `ω`. -/
noncomputable def gpSqW (ω : ℝ) (W : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, (W i j - ω) ^ 2 + ∑ i, ∑ j, (if i < j then W i j ^ 2 else 0)

/-! ## §4 Moment constants (absolute, not divided by the uniform moments) -/

/-- `η̄ = 1/1000` bounds `|dD_K/dD − 1|` for every `K ≥ K12 n` (`Part38Kof`). -/
noncomputable def etaBar : ℝ := 1 / 1000

/-- `ℓ = 778/1000 ≤ e^{−1/4}`. -/
noncomputable def lc : ℝ := 778 / 1000

/-- The floor constant `L₄ = ℓ⁴ ≤ e^{−1}`. -/
noncomputable def L4c : ℝ := lc ^ 4

/-- Upper bound for `E_{D_K} xᵢ²`: `(1 + η̄)/(n − 2 − n/4)`. -/
noncomputable def up1 (n : ℝ) : ℝ := (1 + etaBar) / (n - 2 - n / 4)

/-- Upper bound for `E_{D_K} xᵢ² xⱼ²`, `i ≠ j` (three times it bounds `E_{D_K} xᵢ⁴`): `(1 + η̄)/((n
  − 2 − n/4)(n − n/4))`. -/
noncomputable def up2 (n : ℝ) : ℝ := (1 + etaBar) / ((n - 2 - n / 4) * (n - n / 4))

/-- Lower bound for `E_{D_K} xᵢ² xⱼ²`, `i ≠ j` (three times it bounds `E_{D_K} xᵢ⁴` below): `(1 −
  η̄) ℓ²/(n(n+2))`. -/
noncomputable def lo2 (n : ℝ) : ℝ := (1 - etaBar) * lc ^ 2 / (n * (n + 2))

/-- Branch H's constant `ω = (up₂ + lo₂)/2` (the paper's `ω'/(n(n+2))`). -/
noncomputable def omega38 (n : ℝ) : ℝ := (up2 n + lo2 n) / 2

/-- The generic Frobenius bound for `G'` at `ω = (up + lo)/2`. -/
noncomputable def gHgen (n lo up : ℝ) : ℝ :=
  n * (n - 1) * ((up - lo) / 2) ^ 2 + n * (3 * up - (up + lo) / 2) ^ 2 + up / 2

/-- The generic Frobenius bound for `Σ_D`. -/
noncomputable def sDgen (n u1 up : ℝ) : ℝ := u1 + up / 2 + (3 * n * up) ^ 2

/-- `g_H` over the ball. -/
noncomputable def gH38 (n : ℝ) : ℝ := gHgen n (lo2 n) (up2 n)

/-- `s_D` over the ball. -/
noncomputable def sD38 (n : ℝ) : ℝ := sDgen n (up1 n) (up2 n)

/-- `h_D² = 8 g_H / ((1 − λ)² q κₙ L₄)`, `q = δ − η'ₙ`, `λ = 1/50`. -/
noncomputable def hSq38 (n δ : ℝ) : ℝ := 8 * gH38 n / ((49 / 50) ^ 2 * (δ - eta n) * kappa n * L4c)

/-- `u_D² = 8 s_D / ((1 − λ)² q κₙ L₄)`. -/
noncomputable def uSq38 (n δ : ℝ) : ℝ := 8 * sD38 n / ((49 / 50) ^ 2 * (δ - eta n) * kappa n * L4c)

/-! ## §5 The Taylor precision -/

/-- `ē = 2.719^{⌈n/16⌉} ≥ e^{n/16}`. -/
noncomputable def ebar (n : ℕ) : ℝ := (2719 / 1000 : ℝ) ^ ((n + 15) / 16)

/-- `τ_K = a^{K+1}/((K+1)!) · (K+2)/(K+2−a)`, `a = n/16`: the tail of `e^s` past degree `K`, `|s| ≤
  a`. -/
noncomputable def tau38 (n K : ℕ) : ℝ :=
  ((n : ℝ) / 16) ^ (K + 1) / ((K + 1).factorial : ℝ) *
    (((K : ℝ) + 2) / ((K : ℝ) + 2 - (n : ℝ) / 16))

/-- `r_K = τ_K ē` bounds `|T_K(q)/e^q − 1|` on the ball. -/
noncomputable def r38 (n K : ℕ) : ℝ := tau38 n K * ebar n

/-- `η_K = 2 r_K/(1 − r_K)` bounds `|dD_K/dD − 1|`. -/
noncomputable def eta38 (n K : ℕ) : ℝ := 2 * r38 n K / (1 - r38 n K)

/-- The least precision the program uses: `K12 n = ⌊3n/4⌋ + 1`. Past it, `η_{K+1} ≤ η_K/12`. -/
def K12 (n : ℕ) : ℕ := 3 * n / 4 + 1

/-- The program's `K`: the least `K ≥ K12 n` with `η_K ≤ ε/50` (`K12 n` if there is none). -/
noncomputable def Kof38 (n : ℕ) (ε : ℝ) : ℕ := by
  classical
  exact if h : ∃ K : ℕ, K12 n ≤ K ∧ eta38 n K ≤ ε / 50 then Nat.find h else K12 n

/-! ## §6 The program and its cost -/

/-- The program `g_{θ,f,ε}`: E if `ε² < h_D²`, H (constant `omega38 n`) if `h_D² ≤ ε² < u_D²`, U
  otherwise, at the computed moments with `K = Kof38 n ε`. -/
noncomputable def gOf38 (θ : Fin n → ℝ) (δ ε : ℝ) (f0 : ℝ) (g : Fin n → ℝ)
    (F : Matrix (Fin n) (Fin n) ℝ)
    (M : CoefIdx n → ℝ) : ℝ :=
  if ε ^ 2 < hSq38 n δ then EofB f0 g F M (muK n (Kof38 n ε) θ) (WK n (Kof38 n ε) θ)
  else if ε ^ 2 < uSq38 n δ then
    HofBW (omega38 n) f0 g F M (muK n (Kof38 n ε) θ) (fun i => WK n (Kof38 n ε) θ i i)
  else UofB f0 g F M (muK n (Kof38 n ε) θ) (fun i => WK n (Kof38 n ε) θ i i)

/-- The cost of the branch the program takes (Part 37's charges at `t = n`). -/
noncomputable def costOf38 (n : ℕ) (δ ε : ℝ) : ℝ :=
  if ε ^ 2 < hSq38 n δ then CE n (Kof38 n ε)
  else if ε ^ 2 < uSq38 n δ then CH n (Kof38 n ε)
  else CU n (Kof38 n ε)

end BstLean.Part38
