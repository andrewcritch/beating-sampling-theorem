import BstLean.Part182Ev
import BstLean.Part150P45b

/-!
# Part 182 (file `EvW`): the covariance event of the frame window, and its charge

No proof is left open; no `native_decide` or `axiom` is used.

* `winT c τ`: `0.46 ≤ θ ≤ 0.528` (the World window of Part 159, as used by the frame pieces).
* `SCovT n`: the event "outside the window, or `badMass ≤ 10⁻¹⁴`" for the wide input sets
  `(t₀, z₀, t₁) = (5, 14, 8)` and the pair constant `λ = 0.582` (measurable).
* **`SCovT_charge`**: GIVEN the two-input hypothesis `TI_hyp n 0.386 0.638 0.582 10⁻¹⁸` and the
  geometry `0.386 ≤ x·x' ≤ 0.638` on `Γ` in the window, `Pr_{A₁,A₂}(not SCovT) ≤ 10⁻⁴` at every
  `(c, τ)` with `τ > 0`; `SCovT_ret_charge`: the same charge for the retained data.
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part160
open BstLean.Part153 (nuA)

variable {n : ℕ}

/-- The frame window `0.46 ≤ θ ≤ 0.528`. -/
def winT (c : Fin n → ℝ) (τ : ℝ) : Prop := 46 / 100 ≤ thetaC c τ ∧ thetaC c τ ≤ 528 / 1000

/-- **The covariance event of the window**: outside the window, or the pair mass of the bad pairs
(wide sets `(5, 14, 8)`, `λ = 0.582`) is at most `10⁻¹⁴`. -/
def SCovT (n : ℕ) : Set (AgFam n) :=
  {k | ¬ winT k.1.1 k.1.2} ∪ SCov n 5 14 8 (582 / 1000) (1 / 10 ^ 14)

lemma measurable_thetaC_key' : Measurable (fun k : AgFam n => thetaC k.1.1 k.1.2) := by
  unfold thetaC rhoC normSq
  fun_prop

theorem measurableSet_SCovT (n : ℕ) : MeasurableSet (SCovT n) := by
  have hw : MeasurableSet {k : AgFam n | winT k.1.1 k.1.2} :=
    (measurableSet_le measurable_const measurable_thetaC_key').inter
      (measurableSet_le measurable_thetaC_key' measurable_const)
  exact hw.compl.union (measurableSet_SCov _ _ _ _ _)

/-- The geometry hypothesis of the window: every pair of `Γ(5, 14, 8)` has `0.386 ≤ x·x' ≤ 0.638`. -/
def GeoT (n : ℕ) : Prop :=
  ∀ (c : Fin n → ℝ) (τ : ℝ), 0 < τ → winT c τ → ∀ p ∈ GammaS c 5 14 8,
    386 / 1000 ≤ sphPt (c + τ • p.1) ⬝ᵥ sphPt (c + τ • p.2) ∧
      sphPt (c + τ • p.1) ⬝ᵥ sphPt (c + τ • p.2) ≤ 638 / 1000

/-- **The charge of `SCovT` at one `(c, τ)`**, given the two-input hypothesis. -/
theorem SCovT_charge (hn : 1 ≤ n) (hgeo : GeoT n)
    (hTI : TI_hyp n (386 / 1000) (638 / 1000) (582 / 1000) (1 / 10 ^ 18))
    (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SCovT n} ≤ 1 / 10 ^ 4 := by
  by_cases hw : winT c τ
  · have h := SCov_charge (t0 := 5) (z0 := 14) (t1 := 8) (lam := 582 / 1000) hn c τ
      (by norm_num : (0 : ℝ) ≤ 1 / 10 ^ 18) (by norm_num : (0 : ℝ) < 1 / 10 ^ 4)
      (hgeo c τ hτ hw) hTI
    have e : (1 / 10 ^ 18 : ℝ) / (1 / 10 ^ 4) = 1 / 10 ^ 14 := by norm_num
    rw [e] at h
    refine le_trans (measureReal_mono (fun θ hθ => ?_) (measure_ne_top _ _)) h
    intro hS
    exact hθ (Or.inr hS)
  · have e : {θ | ((c, τ), θ) ∉ SCovT n} = ∅ := by
      ext θ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact Or.inl hw
    rw [e, measureReal_empty]
    norm_num

/-- **The charge of `SCovT` for the retained data** of the paper's design. -/
theorem SCovT_ret_charge (hn : 22000 ≤ n) (hgeo : GeoT n)
    (hTI : TI_hyp n (386 / 1000) (638 / 1000) (582 / 1000) (1 / 10 ^ 18))
    (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) :
    (retDist (paperCentres n)).real (agentEv (paperDesign n fT wT hf hw) (SCovT n))ᶜ ≤
      1 / 10 ^ 4 := by
  rw [agentEv_compl]
  exact retDist_agent_charge (paperDesign n fT wT hf hw) (paperDesign_tauWorld fT wT hf hw)
    (measurableSet_SCovT n) (by norm_num)
    (fun c τ hτ => SCovT_charge (by omega) hgeo hTI c τ hτ)

end BstLean.Part182

open BstLean.Part182 in
#print axioms SCovT_ret_charge
