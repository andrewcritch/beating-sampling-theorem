import BstLean.Part235Wide
import BstLean.Part235Core
import BstLean.Part235Junction

/-! Part 235: concrete geometry and conditional covariance charges from 11883.
The theta window and the paper-sharp TI inputs remain explicit. -/
namespace BstLean.Part235
open MeasureTheory Real Matrix
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part160 BstLean.Part182
open BstLean.Part199

/-- Actual wide pairs enter one of the twelve closed overlap cells. -/
theorem wide_pair_cells {n : ℕ} (hn : 11883 ≤ n) {c : Fin n → ℝ} {τ : ℝ}
    (hτ : 0 < τ) (hθ : thetaC c τ ∈ Set.Icc (46 / 100) (528 / 1000))
    {p : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ GammaS c exampleWide.t exampleWide.z exampleWide.pair) :
    ∃ j < 12,
      overlapLo (34 / 100) (73 / 100) j ≤ sphPt (c + τ • p.1) ⬝ᵥ sphPt (c + τ • p.2) ∧
      sphPt (c + τ • p.1) ⬝ᵥ sphPt (c + τ • p.2) ≤ overlapHi (34 / 100) (73 / 100) j :=
  pair_cell_contains (by omega) hτ exampleWide (by norm_num)
    (wide_overlap_guard hn hθ.1 hθ.2) hp

/-- Actual core pairs enter one of the twelve closed overlap cells. -/
theorem core_pair_cells {n : ℕ} (hn : 11883 ≤ n) {c : Fin n → ℝ} {τ : ℝ}
    (hτ : 0 < τ) (hθ : thetaC c τ ∈ Set.Icc (46 / 100) (528 / 1000))
    {p : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ GammaS c exampleCore.t exampleCore.z exampleCore.pair) :
    ∃ j < 12,
      overlapLo (40 / 100) (63 / 100) j ≤ sphPt (c + τ • p.1) ⬝ᵥ sphPt (c + τ • p.2) ∧
      sphPt (c + τ • p.1) ⬝ᵥ sphPt (c + τ • p.2) ≤ overlapHi (40 / 100) (63 / 100) j :=
  pair_cell_contains (by omega) hτ exampleCore (by norm_num)
    (core_overlap_guard hn hθ.1 hθ.2) hp

/-- The inherited geometry has no dimension cap and includes the complete M1/M2
dimension ranges. The local TI inputs are hypotheses, rather than checked paper data. -/
theorem routes_joint_charge {n : ℕ} (hn : 11883 ≤ n) (D : Design n) (hτ : TauWorld D)
    {lam₀ lam₁ δ ε : ℝ} (hlam : lam₁ ≤ lam₀) (hδ : 0 ≤ δ) (hε : 0 < ε)
    (hwide : ∀ j < 12, TI_hyp n (overlapLo (34 / 100) (73 / 100) j)
      (overlapHi (34 / 100) (73 / 100) j) lam₀ δ)
    (hcore : ∀ j < 12, TI_hyp n (overlapLo (40 / 100) (63 / 100) j)
      (overlapHi (40 / 100) (63 / 100) j) lam₁ δ) :
    (retDist D.toCentres).real
      (agentEv D (JointCovEvent n exampleWide exampleCore
        (46 / 100) (528 / 1000) lam₀ lam₁ (δ / ε)))ᶜ ≤ ε := by
  exact JointCovEvent_ret_charge (by omega) D hτ exampleWide exampleCore example_nested
    hlam hδ hε (fun _ h => wide_overlap_guard hn h.1 h.2)
    (fun _ h => core_overlap_guard hn h.1 h.2)
    (TI_of_twelve_cells (by norm_num) hwide) (TI_of_twelve_cells (by norm_num) hcore)

/-- The paper tail value yields payment 1/4000 only under the stated sharp TI inputs. -/
theorem paper_charge_conditional {n : ℕ} (hn : 11883 ≤ n) (D : Design n)
    (hτ : TauWorld D) {lam₀ lam₁ : ℝ} (hlam : lam₁ ≤ lam₀)
    (hwide : ∀ j < 12, TI_hyp n (overlapLo (34 / 100) (73 / 100) j)
      (overlapHi (34 / 100) (73 / 100) j) lam₀ (50 * exp (-46)))
    (hcore : ∀ j < 12, TI_hyp n (overlapLo (40 / 100) (63 / 100) j)
      (overlapHi (40 / 100) (63 / 100) j) lam₁ (50 * exp (-46))) :
    (retDist D.toCentres).real
      (agentEv D (JointCovEvent n exampleWide exampleCore
        (46 / 100) (528 / 1000) lam₀ lam₁
        ((50 * exp (-46)) / (1 / 4000))))ᶜ ≤ 1 / 4000 :=
  routes_joint_charge hn D hτ hlam (by positivity) (by norm_num) hwide hcore

end BstLean.Part235
