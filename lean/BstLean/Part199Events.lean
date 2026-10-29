import BstLean.Part199Geometry
import BstLean.Part199TI
import BstLean.Part182EvW

/-! Part 199: variable-window covariance event charges.
Deterministic overlap cells do not contribute a union charge. -/
namespace BstLean.Part199
open MeasureTheory Real Matrix
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part160 BstLean.Part182
open BstLean.Part153 (nuA)

def CovEvent (n : ℕ) (w : Window) (θlo θhi lam cutoff : ℝ) : Set (AgFam n) :=
  {k | thetaC k.1.1 k.1.2 ∉ Set.Icc θlo θhi} ∪ SCov n w.t w.z w.pair lam cutoff

theorem measurableSet_CovEvent (n : ℕ) (w : Window) (θlo θhi lam cutoff : ℝ) :
    MeasurableSet (CovEvent n w θlo θhi lam cutoff) := by
  have hm : MeasurableSet {k : AgFam n | thetaC k.1.1 k.1.2 ∈ Set.Icc θlo θhi} :=
    (measurableSet_le measurable_const measurable_thetaC_key').inter
      (measurableSet_le measurable_thetaC_key' measurable_const)
  exact hm.compl.union (measurableSet_SCov _ _ _ _ _)

theorem CovEvent_mass {n : ℕ} {w : Window} {θlo θhi lam cutoff : ℝ}
    {c : Fin n → ℝ} {τ : ℝ}
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ}
    {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (hw : thetaC c τ ∈ Set.Icc θlo θhi)
    (h : ((c, τ), (A₁, A₂)) ∈ CovEvent n w θlo θhi lam cutoff) :
    badMass n w.t w.z w.pair lam ((c, τ), (A₁, A₂)) ≤ cutoff := by
  rcases h with h | h
  · exact False.elim (h hw)
  · exact h

/-- Fixed retained centre and scale: geometry and fixed-pair TI give a Markov charge. -/
theorem CovEvent_charge {n : ℕ} (hn : 1 ≤ n) (w : Window)
    {θlo θhi lo hi lam δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε)
    (hgeo : ∀ θ ∈ Set.Icc θlo θhi, OverlapGuard n θ w lo hi)
    (hTI : TI_hyp n lo hi lam δ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real {a | ((c, τ), a) ∉ CovEvent n w θlo θhi lam (δ / ε)} ≤ ε := by
  by_cases hw : thetaC c τ ∈ Set.Icc θlo θhi
  · have h := SCov_charge (t0 := w.t) (z0 := w.z) (t1 := w.pair) (lam := lam)
      hn c τ hδ hε (fun p hp => overlap_of_guard (by omega) hτ w (hgeo _ hw) hp) hTI
    refine le_trans (measureReal_mono (fun a ha => ?_) (measure_ne_top _ _)) h
    intro hmem
    exact ha (Or.inr hmem)
  · have he : {a | ((c, τ), a) ∉ CovEvent n w θlo θhi lam (δ / ε)} = ∅ := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact Or.inl hw
    rw [he, measureReal_empty]
    exact hε.le

/-- Retained-data integration pays the conditional covariance charge once. -/
theorem CovEvent_ret_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n)
    (hτ : TauWorld D) (w : Window) {θlo θhi lo hi lam δ ε : ℝ}
    (hδ : 0 ≤ δ) (hε : 0 < ε)
    (hgeo : ∀ θ ∈ Set.Icc θlo θhi, OverlapGuard n θ w lo hi)
    (hTI : TI_hyp n lo hi lam δ) :
    (retDist D.toCentres).real
      (agentEv D (CovEvent n w θlo θhi lam (δ / ε)))ᶜ ≤ ε := by
  rw [agentEv_compl]
  exact retDist_agent_charge D hτ (measurableSet_CovEvent n w θlo θhi lam (δ / ε)) hε.le
    (fun c τ hτ => CovEvent_charge hn w hδ hε hgeo hTI c hτ)

/-- Two covariance events have one combined complement charge. -/
theorem CovEvents_ret_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n)
    (hτ : TauWorld D) (w₀ w₁ : Window)
    {θlo θhi lo₀ hi₀ lo₁ hi₁ lam₀ lam₁ δ₀ δ₁ ε₀ ε₁ : ℝ}
    (hδ₀ : 0 ≤ δ₀) (hδ₁ : 0 ≤ δ₁) (hε₀ : 0 < ε₀) (hε₁ : 0 < ε₁)
    (hg₀ : ∀ θ ∈ Set.Icc θlo θhi, OverlapGuard n θ w₀ lo₀ hi₀)
    (hg₁ : ∀ θ ∈ Set.Icc θlo θhi, OverlapGuard n θ w₁ lo₁ hi₁)
    (hTI₀ : TI_hyp n lo₀ hi₀ lam₀ δ₀) (hTI₁ : TI_hyp n lo₁ hi₁ lam₁ δ₁) :
    (retDist D.toCentres).real
      ((agentEv D (CovEvent n w₀ θlo θhi lam₀ (δ₀ / ε₀))) ∩
       (agentEv D (CovEvent n w₁ θlo θhi lam₁ (δ₁ / ε₁))))ᶜ ≤ ε₀ + ε₁ := by
  rw [Set.compl_inter]
  exact (measureReal_union_le _ _).trans (add_le_add
    (CovEvent_ret_charge hn D hτ w₀ hδ₀ hε₀ hg₀ hTI₀)
    (CovEvent_ret_charge hn D hτ w₁ hδ₁ hε₁ hg₁ hTI₁))

end BstLean.Part199
