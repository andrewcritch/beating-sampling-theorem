import BstLean.Part145K5

/-!
# Part 145 (K7): the kernel bound with three orthogonal blocks and a general World term

`kernB` of `Part145K5` uses the chord `chord_pW` (`pW = σ₄·τ`). Here the bound `pW` of
`‖κ^{∘4}(t) − κ^{∘6}(0)‖₂` is a hypothesis.

* `eDBp bK τ pW n`: the kernel constant `√(E1² + E2² + (B2 + E4 + √(E3x² + pW²))²)`.
* **`kernBp`**: `‖kD − S(1 − Q)‖₂ ≤ S·eDBp bK τ pW n` (from `kernDistB_of`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Cost
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142 BstLean.Part143

/-- The kernel constant with three orthogonal blocks, at a general `τ`, bias constant `bK` and
bound `pW` of the World term. -/
noncomputable def eDBp (bK τ pW : ℝ) (n : ℕ) : ℝ :=
  √(asmE1 (mF n) (dA0 n (mA n)) (dA1 n (mA n)) (dA2 n (mA n)) τ ^ 2 +
    asmE2 n (mA n) (mF n) (dA0 n (mA n)) (dA1 n (mA n)) (dA2 n (mA n)) (cAdlt n (mA n)) τ ^ 2 +
    (bK * ((1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ))) +
      asmE4 (rR0 n (mA n)) (rR1 n) (rR1' n) (rR2 n (mA n)) τ +
      √(asmE3x (cC0x n (mA n)) (cC1 n) (cC1x' n) (cC2x n (mA n)) τ ^ 2 + pW ^ 2)) ^ 2)

lemma eDBp_nonneg (bK τ pW : ℝ) (n : ℕ) : 0 ≤ eDBp bK τ pW n := Real.sqrt_nonneg _

/-- `eDB` is `eDBp` at `pW = σ₄·τ`. -/
lemma eDB_eq_eDBp (bK τ : ℝ) (n : ℕ) : eDB bK τ n = eDBp bK τ (sig4 * τ) n := rfl

/-- **The kernel bound with three orthogonal blocks and a general World term**, `n ≥ 4096`. -/
theorem kernBp {n : ℕ} (hn : 4096 ≤ n) {bK : ℝ} (hbK : 0 ≤ bK)
    (hB : ∀ y y' : Fin n → ℝ,
      Integrable (fun F₁ : Matrix (Fin (mF n)) (Fin n) ℝ => rF0 F₁ y y')
        (gaussMat (mF n) n (2 / (n : ℝ))) ∧
      |∫ F₁, rF0 F₁ y y' ∂gaussMat (mF n) n (2 / (n : ℝ))| ≤
        2 / (n : ℝ) * (bK * ((normSq y + normSq y') / 2)))
    {τ pW : ℝ} (hτ : 0 ≤ τ)
    (hT : L2le ((lawU2 (2 * n)).prod (mlpGauss (2 * n) (mW n) n))
      (fun z : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × MlpParam (2 * n) (mW n) n =>
        tX z - kappa (kappa 0)) τ)
    (hW5 : L2le ((lawU2 (2 * n)).prod (mlpGauss (2 * n) (mW n) n))
      (fun z : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × MlpParam (2 * n) (mW n) n =>
        kappa^[4] (tX z) - kappa^[6] 0) pW) :
    L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0))
      (4 / (n : ℝ) * eDBp bK τ pW n) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  unfold eDBp
  exact kernDistB_of (cA := cAg) hn1 hN hmA hmF measurable_cAg
    (cC1_nonneg n) (cC1x'_nonneg n) (cC2x_nonneg n (mA n)) (rR1_nonneg n) (rR1'_nonneg n)
    (rR2_nonneg n (mA n)) hτ hbK (cC_ref_nonneg n (mA n)) (rR_ref_nonneg n (mA n))
    (fun x x' hx hx' => cAg_integral hn1 hmA hx hx')
    (fun x x' hx hx' => cAg_L2x hn1 hmA hx hx')
    (fun x x' hx hx' => agent_rem_L2 hn1 hmA hx hx')
    (dA0_nonneg n (mA n)) (dA1_nonneg n (mA n)) (dA2_nonneg n (mA n)) (cAdlt_nonneg n (mA n))
    (fun x x' hx hx' => agent_diff_L2_of reluEDStmt reluPhiStmt hn1 hmA hx hx')
    (fun x x' hx hx' => agent_dlt_L2_of reluSqStmt reluDltStmt linDltStmt hn1 hmA hx hx')
    hB hT hW5

end BstLean.Part145

open BstLean.Part145 in
#print axioms kernBp
