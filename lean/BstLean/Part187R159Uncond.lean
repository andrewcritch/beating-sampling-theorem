import BstLean.Part159Uncond
import BstLean.Part187R143HidC
import BstLean.Part187R143HidC2
import BstLean.Part187R159Hat
import BstLean.Part187R159Win
import BstLean.Part187R159Frame
import BstLean.Part187R159Paper
import BstLean.Part187R159PaperF
import BstLean.Part187R159PaperW

/-! Part 187 (file `Part187R159Uncond`): copy of `Part159Uncond` re-proved at the floor `16250 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part159.R

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part156 BstLean.Part157 BstLean.Part158

variable {n : ℕ}

/-- **The World package for the centre and the scalar of the paper's program**
(every `n ≥ 16 384`), for every design with `b_W = bWp`, `τ₀ = tau0p`: `EVENTS_hyp` with the
hidden charge `0.00163204` and the Hellinger moment `7.37·10⁻⁹` (the charge of the other events is
a hypothesis), and `FRAME_W_hyp` with `1.377/n`. -/
theorem paper_world (hn : 16250 ≤ n) (D : Design n) (hD : D.bW = bWp)
    (hτ : ∀ c : Ret n, D.tau0 c = tau0p c.1.1) :
    (∀ {E₁ : Set (Ret n)}, MeasurableSet E₁ → ∀ {δextra : ℝ},
      (retDist D.toCentres).real (HP n ∩ E₁ᶜ) ≤ δextra →
        EVENTS_hyp D.toCentres (HP n) E₁ (HbarW D) δPap vPap δextra) ∧
    (∀ {E : Set (Ret n)}, E ⊆ HP n → FRAME_W_hyp D.toCentres (cWL / n) E) :=
  ⟨fun hE₁ _ h3 => events_paper hn (constC (by omega)) (constK (by omega)) D hD hτ hE₁ h3,
    fun hE => frame_w_paper hn (constC (by omega)) D.toCentres hD hE⟩

/-- **The retained World window for the design of the paper's program** (every `n ≥ 16 384`),
with no hypothesis on the constants (Lemma `t7:p02:window`). -/
theorem theta_window_paper' (hn : 16250 ≤ n) (D : Design n)
    (hD : D.bW = bWp) (hτ : ∀ c : Ret n, D.tau0 c = tau0p c.1.1) {c : Ret n} (hc : c ∈ HP n) :
    0 < D.tau0 c ∧
      D.tau0 c ^ 2 = 2 / (mW n : ℝ) * normSq (D.bW c.1.1) *
        (2 / (mW n : ℝ) * normSq (D.bW c.1.1) * ccP n c.1.1 - 1) ∧
      994 / 1000 ≤ 2 / (mW n : ℝ) * normSq (D.bW c.1.1) * ccP n c.1.1 - 1 ∧
      2 / (mW n : ℝ) * normSq (D.bW c.1.1) * ccP n c.1.1 - 1 ≤ 1057 / 1000 ∧
      (c ∈ Ethm D.toCentres → 465 / 1000 ≤ thetaIn D c) ∧
      (c ∈ Ethp D.toCentres → thetaIn D c ≤ 528 / 1000) :=
  theta_window_paper hn (constC (by omega)) (constK (by omega)) D hD hτ hc

end BstLean.Part159.R

