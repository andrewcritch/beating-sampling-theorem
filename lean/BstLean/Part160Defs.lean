import BstLean.Part154All
import BstLean.Part158All

/-!
# Part 160 (file `Defs`): the three scalar hypotheses for the Agent frame bound

Role: `delegations/statements/p160-spec.md`. Do not use `sorry`, `native_decide` or `axiom`.

Paper: `proofs/option-n/theorem7-04-frame-numerator.tex`, Lemma `t7:p04:split`.

Notation: `t_A = 2/m_A`, `γ_A = 2/n`, `h(ξ) = hStand D c ξ` (the last hidden vector of `A` at the
stand-in input `sphPt (ĉ + τ₀ ξ)`), `b = D.bA c.1 c.2.1.1` (the Agent centre of the design),
`r = res b h`, `μ = E_ξ h`.

* `muStand D c`: the mean `μ` of the hidden vector under the stand-in input distribution.
* `COV_at D c N`: `t_A·Var_ξ⟨h, w⟩ ≤ N·(γ_A/n)·|w|²` for every `w` (`n‖t_A Cov(h)‖_op/γ_A ≤ N`).
* `CENTRE_at D c ξ`: `t_A·|μ − b|² ≤ ξ·γ_A/n`.
* `MASS_at D c d β`: `n·Pr_ξ(t_A|r|² < γ_A d) ≤ β`.
* `COV_hyp`, `CENTRE_hyp`, `MASS_hyp`: the same for every retained value in a set `E`.
* `AgentCentre154 D`: the Agent centre of the design is `bT n n A₁ A₂ ĉ τ₀ / ρ` (the centre of
  Part 154; it is the centre `bAp` of `paperDesign`).
* `WINDOW_hyp D E`: on `E`: `τ₀ > 0` and `0.46 ≤ θ_in ≤ 0.55` (a World hypothesis).
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157
open BstLean.Part150 (rhoC thetaC bT)

variable {n : ℕ}

/-- The mean of the last hidden vector of `A` under the stand-in input distribution. -/
noncomputable def muStand (D : Design n) (c : Ret n) : Fin (mA n) → ℝ :=
  fun j => ∫ ξ, hStand D c ξ j ∂stdGauss (Fin n)

/-- **The covariance bound at one retained value**: `t_A·Var_ξ⟨h, w⟩ ≤ N·(γ_A/n)·|w|²`. -/
def COV_at (D : Design n) (c : Ret n) (N : ℝ) : Prop :=
  ∀ w : Fin (mA n) → ℝ,
    2 / (mA n : ℝ) * ∫ ξ, (∑ j, (hStand D c ξ j - muStand D c j) * w j) ^ 2 ∂stdGauss (Fin n) ≤
      N * (2 / (n : ℝ)) / n * ∑ j, w j ^ 2

/-- **The centre charge at one retained value**: `t_A·|μ − b|² ≤ ξ·γ_A/n`. -/
def CENTRE_at (D : Design n) (c : Ret n) (xi : ℝ) : Prop :=
  2 / (mA n : ℝ) * normSq (muStand D c - D.bA c.1 c.2.1.1) ≤ xi * (2 / (n : ℝ)) / n

/-- **The mass of the inputs with a small residual energy at one retained value**:
`n·Pr_ξ(t_A·|r(ξ)|² < γ_A·d) ≤ β`. -/
def MASS_at (D : Design n) (c : Ret n) (d β : ℝ) : Prop :=
  (n : ℝ) * (stdGauss (Fin n)).real
    {ξ | 2 / (mA n : ℝ) * normSq (res (D.bA c.1 c.2.1.1) (hStand D c ξ)) < 2 / (n : ℝ) * d} ≤ β

/-- (COV): the covariance bound on a set of retained values. Paper: `N_cov`,
`theorem7-04-frame-numerator.tex`, Proposition `t7:p04:certificate`. -/
def COV_hyp (D : Design n) (N : ℝ) (E : Set (Ret n)) : Prop := ∀ c ∈ E, COV_at D c N

/-- (CENTRE): the centre charge on a set of retained values. Paper: `ξ′`,
`theorem7-05-centre.tex`, Proposition `t7:p05:certificate`. -/
def CENTRE_hyp (D : Design n) (xi : ℝ) (E : Set (Ret n)) : Prop := ∀ c ∈ E, CENTRE_at D c xi

/-- (MASS): the mass bound on a set of retained values. Paper: `n·β_d`,
`theorem7-06-cutoff.tex`, Proposition `t7:p06:cutoffs`. -/
def MASS_hyp (D : Design n) (d β : ℝ) (E : Set (Ret n)) : Prop := ∀ c ∈ E, MASS_at D c d β

/-- The Agent centre of the design is the binomial centre of Parts 150 and 154:
`b = bT n n A₁ A₂ ĉ τ₀ / ρ`, `ρ = √(|ĉ|² + n τ₀²)`. -/
def AgentCentre154 (D : Design n) : Prop :=
  ∀ c : Ret n, D.bA c.1 c.2.1.1 =
    (1 / rhoC c.1.2 (D.tau0 c)) • bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)

/-- `τ₀` of the design is a measurable function of the retained World data only. -/
def TauWorld (D : Design n) : Prop :=
  ∃ τW : WRet n → ℝ, Measurable τW ∧ ∀ c : Ret n, D.tau0 c = τW c.1

/-- (WINDOW), a World hypothesis: on `E`, `τ₀ > 0` and `0.46 ≤ θ_in ≤ 0.55`,
`θ_in = n τ₀²/(|ĉ|² + n τ₀²)`. -/
def WINDOW_hyp (D : Design n) (E : Set (Ret n)) : Prop :=
  ∀ c ∈ E, 0 < D.tau0 c ∧ 46 / 100 ≤ thetaC c.1.2 (D.tau0 c) ∧ thetaC c.1.2 (D.tau0 c) ≤ 55 / 100

lemma hStand_eq (D : Design n) (c : Ret n) (ξ : Fin n → ℝ) :
    hStand D c ξ = hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ)) := rfl

lemma muStand_eq (D : Design n) (c : Ret n) :
    muStand D c = BstLean.Part153.hid2Mean_cr c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) := rfl

end BstLean.Part160
