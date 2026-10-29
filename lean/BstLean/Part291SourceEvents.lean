import BstLean.Part291Band
import BstLean.Part275Charges
import BstLean.Part277Frame
import BstLean.Part289Design

/-! A measurable Agent centre/direction/energy event with one uniform charge.
Numerical source certificates and latitude/mixture fields are separate obligations. -/
namespace BstLean.BlueprintLow
open Real Set MeasureTheory
open scoped ENNReal
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160
open BstLean.Part169 BstLean.Part188 BstLean.Part215 BstLean.Part222

def agentCentreEvent {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) : Set (AgentPair n) :=
  (BstLean.Part211.CentreSource n n c τ 2 ∩
    (sharpErrorEvent c τ ∩ operatorEvent c τ (6 / 1000) (ENNReal.ofReal (1 / 20000)))) ∩
      energyEvent c τ

theorem agentCentreEvent_measurable {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) :
    MeasurableSet (agentCentreEvent c τ) := by
  have hm : Measurable (fun a : AgentPair n => ((c, τ), a)) :=
    measurable_const.prodMk measurable_id
  have hC := (BstLean.Part252.measurableSet_CentreSources hn n).preimage hm
  have hS := (BstLean.Part252.measurableSet_DirectionError n).preimage hm
  have hO := (BstLean.Part252.measurableSet_Operator160 n).preimage hm
  exact (hC.inter (hS.inter hO)).inter (measurableSet_energyEvent c τ)

/-- This smaller measurable event uses the old fixed centre threshold only to
define a source. The paid order-160 event supplies the actual operator bound. -/
theorem agentCentreEvent_charge {n : ℕ} (hn : 8000 ≤ n) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real (agentCentreEvent c τ)ᶜ < (526 / 1000000 : ℝ) := by
  have h := common_event_charge_paper (by omega) c hτ (by norm_num : (0 : ℝ) ≤ 6 / 1000)
    (BstLean.Part211.CentreSource n n c τ 2)
    (BstLean.Part275.centreSources_charge_8000 hn n c hτ)
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hq : (3445 : ℝ) / (n : ℝ) ^ 2 ≤ 3445 / (8000 : ℝ) ^ 2 := by gcongr
  change (nuA n).real (agentCentreEvent c τ)ᶜ ≤
    BstLean.Part275.centreCharge n + 19 / 50000 at h
  apply h.trans_lt
  unfold BstLean.Part275.centreCharge
  linarith

theorem agentCentreEvent_sources {n : ℕ} {c : Ret n}
    (hc : 0 < normSq c.1.2) (hτ : 0 < (paperDesignP n).tau0 c)
    (h : c.2.1.1 ∈ agentCentreEvent c.1.2 ((paperDesignP n).tau0 c)) :
    BstLean.Part262.SourceEvents c where
  world_centre_pos := hc
  scale_pos := hτ
  base_event := ⟨2, by norm_num, h.1.1⟩
  error_event := h.1.2.1
  operator_event := by
    have he : (6 / 1000 : ℝ) = 0.006 := by norm_num
    rw [← he]
    exact h.1.2.2
  energy_event := h.2

/-- The four source fields for the low band, conditional on the explicit
Part277 scalar certificate. This does not assert the latitude or mixture fields. -/
theorem agentCentreFields_of_certificate {n : ℕ} (hn : LowBand n) {c : Ret n}
    {r : BstLean.Part263.CellData} {k k3 MP e0 dlo dhi : ℝ}
    (N : BstLean.Part277.CellSourceNumericsP n r agentDirectionCap
      (agentEnergyMomentCap / n) agentParallelCap k k3 MP e0 dlo dhi)
    (hw : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ Icc r.lower r.upper)
    (hDir : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ Icc dlo dhi)
    (hc : 0 < normSq c.1.2) (hτ : 0 < (paperDesignP n).tau0 c)
    (h : c.2.1.1 ∈ agentCentreEvent c.1.2 ((paperDesignP n).tau0 c))
    (hE : r.energy ≤ agentEnergyCap) :
    0 < normSq ((BstLean.Part289.statedDesign2 n).bA c.1 c.2.1.1) ∧
    WFInterfaces (BstLean.Part289.statedDesign2 n) c agentDirectionCap
      (agentEnergyMomentCap / n) agentParallelCap ∧
    centreEnergy (BstLean.Part289.statedDesign2 n) c ≤ agentEnergyCap ∧
    CENTRE_at (BstLean.Part289.statedDesign2 n) c r.centre := by
  have F := BstLean.Part277.network_from_numericsP hn.1 (by have := hn.2; omega)
    N hw hDir (agentCentreEvent_sources hc hτ h)
  refine ⟨F.centre_pos, ?_, F.centre_energy.trans hE, F.full_centre⟩
  exact ⟨F.interfaces.direction, F.interfaces.energy, F.interfaces.parallel⟩

end BstLean.BlueprintLow
