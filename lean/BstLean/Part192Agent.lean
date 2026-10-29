import BstLean.Part192Interfaces

/-! Part 192: adapters for the existing Agent supplies.
The sharp cell interface and the existing supplies remain distinct.
These adapters retain every event premise of the existing frame theorem. -/

namespace BstLean.Part192
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169 BstLean.Part171
open BstLean.Part153 (nuA)

/-- The seven core covariance windows are separate inputs of the existing frame. -/
structure FrameInputs {n : ℕ} (D : Design n) (E : Set (Ret n)) : Prop where
  centre : AgentCentre154 D
  window : ∀ c ∈ E, 0 < D.tau0 c ∧
    46 / 100 ≤ BstLean.Part150.thetaC c.1.2 (D.tau0 c) ∧
    BstLean.Part150.thetaC c.1.2 (D.tau0 c) ≤ 528 / 1000
  centreEvent : E ⊆ EA16 D
  directionEvent : E ⊆ agentEv D (BstLean.Part190.Frame16200.SXM16200 n)
  residualEvent : E ⊆ agentEv D (BstLean.Part188.Sc.SSc97 n)
  meanEvent : E ⊆ agentEv D (SScU n)
  transferEvent : E ⊆ agentEv D (SD' n)
  covarianceEvent : E ⊆ agentEv D (BstLean.Part190.Frame16200.SCovT16200 n)
  core46 : E ⊆ agentEv D (BstLean.Part186.SCovP n (46/100) (47/100) (78/125))
  core47 : E ⊆ agentEv D (BstLean.Part186.SCovP n (47/100) (48/100) (309/500))
  core48 : E ⊆ agentEv D (BstLean.Part186.SCovP n (48/100) (49/100) (613/1000))
  core49 : E ⊆ agentEv D (BstLean.Part186.SCovP n (49/100) (50/100) (76/125))
  core50 : E ⊆ agentEv D (BstLean.Part186.SCovP n (50/100) (51/100) (603/1000))
  core51 : E ⊆ agentEv D (BstLean.Part186.SCovP n (51/100) (52/100) (299/500))
  core52 : E ⊆ agentEv D (BstLean.Part186.SCovP n (52/100) (528/1000) (593/1000))

theorem frame16200 {n : ℕ} (hn : 16200 ≤ n) {D : Design n} {E : Set (Ret n)}
    (h : FrameInputs D E) : FRAME_A_hyp D (193 / 100 / n) E :=
  BstLean.Part190.Frame16200.frameA_K_16200 hn D h.centre h.window
    h.centreEvent h.directionEvent h.residualEvent h.meanEvent h.transferEvent
    h.covarianceEvent h.core46 h.core47 h.core48 h.core49 h.core50 h.core51 h.core52

/-- Full centre and parallel centre retain the same units. -/
theorem full_centre16200 {n : ℕ} (hn : 16200 ≤ n) {D : Design n} {E : Set (Ret n)}
    (h : FrameInputs D E) : CENTRE_hyp D (41 / 400) E := by
  intro c hc
  obtain ⟨hτ, hlo, hhi⟩ := h.window c hc
  have H := BstLean.Part188.Base160_R.centre16_BD hn hτ hlo
    (le_trans hhi (by norm_num)) (h.centreEvent hc hτ) (h.transferEvent hc hτ)
  unfold CENTRE_at
  rw [h.centre c, muStand_eq]
  exact H

theorem parallel_centre16200 {n : ℕ} (hn : 16200 ≤ n) {D : Design n} {E : Set (Ret n)}
    (h : FrameInputs D E) {c : Ret n} (hc : c ∈ E)
    (hb : 0 < normSq (D.bA c.1 c.2.1.1)) :
    BstLean.Part188.ParallelCentre D c (41 / 400) :=
  BstLean.Part188.parallelCentre_of_full (by omega) D c (by norm_num) hb
    (full_centre16200 hn h c hc)

/-- The baseline node statistics have order eight and a conditional World window. -/
structure AgentStatistics (n : ℕ) (charge biasF biasW : ℝ) where
  event : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)
  event_measurable : MeasurableSet event
  conditional_charge : ∀ wr : WRet n, BstLean.Part170.windowW wr →
    (nuA n).real {θ | (wr, θ.1) ∉ event} ≤ charge
  location_moment : BstLean.Part170.BiasMomF (O1n n) event biasF
  energy_moment : BstLean.Part170.BiasMomW (O1n n) event biasW

noncomputable def statistics16200 {n : ℕ} (hn : 16200 ≤ n) (hN : n ≤ 16384) :
    AgentStatistics n (122 / 1000000) (194 / n) (148 / n) := by
  let G := StatEvOpG n (SminN n) (DmN n) (VmN n) (82 * PmN n)
  let Gb := G ∩ {p | p.2 ∈ BstLean.Part170.opSet n (O1n n) ∧
    BstLean.Part170.windowW p.1}
  have hm : MeasurableSet G := measurableSet_StatEvOpG n _ _ _ _
  have H := BstLean.Part190.BiasRA82_16200 hn
    (BstLean.Part190.Chain.M.statOpG_sub hn (SminN n) (DmN n) (VmN n) (82 * PmN n))
  refine ⟨G, hm, ?_, ?_, ?_⟩
  · intro wr hw
    exact BstLean.Part188.Chain.stat_charge21 hn (by exact_mod_cast hN) hw
  · intro wr hw g hg A₁ hA hG
    exact H.1 wr hw g hg A₁ hA ⟨hG, hA, hw⟩
  · intro wr hw g hg A₁ hA hG
    exact H.2 wr hw g hg A₁ hA ⟨hG, hA, hw⟩

/-- The existing latitude energy event has one payment and supplies orders four and 24. -/
theorem energy_event16200 {n : ℕ} (hn : 16200 ≤ n) :
    (retDist (paperCentres n)).real
      (agentEv (paperDesignP n) (BstLean.Part177.SEn n))ᶜ ≤ 1 / 10 ^ 6 :=
  BstLean.Part188.Base177_R.SEn_ret_charge hn
    (BstLean.Part188.Base177_N40_R.hmomN hn)
    passF passW measurable_passF measurable_passW

/-- The conditional mixture root and residual-average root are identical. -/
theorem agent_root_identity {n : ℕ} {P : Program n} {p : AgentParameters} {t : ℝ}
    {window : Set (WRet n)} (A : AgentPackage P p t window) :
    REPL_A_hyp P.design t p.root A.retainedEvent :=
  repla_of_mix P.design t A.replacement_root

end BstLean.Part192
#print axioms BstLean.Part192.frame16200
#print axioms BstLean.Part192.full_centre16200
#print axioms BstLean.Part192.parallel_centre16200
#print axioms BstLean.Part192.statistics16200
#print axioms BstLean.Part192.energy_event16200
#print axioms BstLean.Part192.agent_root_identity
