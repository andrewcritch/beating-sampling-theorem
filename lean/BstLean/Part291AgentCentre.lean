import BstLean.Part291CentreCertificate
import BstLean.Part291Direction
import BstLean.Part291SourceEvents

/-! Actual centre, directional, energy and parallel-centre fields. The latitude
and conditional-mixture fields of node 39 are separate obligations. -/
namespace BstLean.BlueprintLow
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part188
open BstLean.Part169 (paperDesignP)
open BstLean.Part160 (CENTRE_at)

noncomputable def agentSourceData : BstLean.Part263.CellData where
  lower := 0.472
  upper := 0.528
  covariance := 0
  centre := 0.14
  energy := agentEnergyCap
  cutoff := 0
  frame := 0

noncomputable def agentSourceInputs {n : ℕ} (hn : LowBand n) {c : Ret n}
    (hw : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ Icc (0.472 : ℝ) 0.528)
    (F : BstLean.Part262.SourceEvents c) :
    BstLean.Part263.SourceInputs n c agentSourceData agentDirectionCap
      (agentEnergyMomentCap / n) agentParallelCap where
  energy_allowance := energyAllowanceBand hn.1
  parallel_nonneg := by norm_num [agentParallelCap]
  J := n
  J_pos := by have := hn.1; omega
  delta := 0.011
  k := 1.25
  k3 := 1.14
  thetaLo := 0.46
  thetaHi := 0.528
  S := 0.1826
  MP := 1.269
  qWorld := 0.528
  lowerEnergy := 0.665
  eta := 0.006
  v := fun _ => 0.006
  certificate := agentCentreCertificate hn
  world_centre_pos := F.world_centre_pos
  scale_pos := F.scale_pos
  centre_eq := BstLean.Part263.paper_centre_eq c
  lower_pos := by norm_num
  full_nonneg := by norm_num [agentSourceData]
  MP_nonneg := by norm_num
  window := ⟨by linarith [hw.1], hw.2⟩
  world_cap := by linarith [hw.1]
  signal_domain := ⟨by linarith [hw.2], by linarith [hw.1]⟩
  full_scalar := (centreSourceScalarBand hn).1
  parallel_scalar := (centreSourceScalarBand hn).2
  lower_scalar := by
    have h := (centreEnergyLowerBand hn.1
      (θ := BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c))
      ⟨by linarith [hw.1], by linarith [hw.2]⟩).2
    convert h using 1 <;> norm_num [agentSourceData]
  upper_scalar := by
    have h := (centreEnergyUpperBand hn.1 (q := (0.528 : ℝ)) (by norm_num) (by norm_num)).2
    convert h using 1 <;> norm_num [agentSourceData]
  operator_scalar := by
    convert BstLean.Part277.operator_allowance_8000 hn.1 c.1.2 F.scale_pos using 1 <;> norm_num
  direction_scalar := by
    apply agentDirectionBand hn.1 _ _ _ _ _ _ hw (by norm_num) (by norm_num [agentSourceData])
      (by norm_num [agentSourceData])
    convert BstLean.Part277.operator_allowance_8000 hn.1 c.1.2 F.scale_pos using 1 <;> norm_num
  base_event := F.base_event
  error_event := F.error_event
  operator_event := F.operator_event
  energy_event := F.energy_event

theorem agentCentreFieldsBand {n : ℕ} (hn : LowBand n) {c : Ret n}
    (hw : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ Icc (0.472 : ℝ) 0.528)
    (hc : 0 < normSq c.1.2) (hτ : 0 < (paperDesignP n).tau0 c)
    (h : c.2.1.1 ∈ agentCentreEvent c.1.2 ((paperDesignP n).tau0 c)) :
    0 < normSq ((BstLean.Part289.statedDesign2 n).bA c.1 c.2.1.1) ∧
    WFInterfaces (BstLean.Part289.statedDesign2 n) c agentDirectionCap
      (agentEnergyMomentCap / n) agentParallelCap ∧
    centreEnergy (BstLean.Part289.statedDesign2 n) c ≤ agentEnergyCap ∧
    CENTRE_at (BstLean.Part289.statedDesign2 n) c 0.14 := by
  have F := BstLean.Part263.network_from_source (by have := hn.1; omega)
    (by have := hn.2; omega) (agentSourceInputs hn hw (agentCentreEvent_sources hc hτ h))
  exact ⟨F.centre_pos, ⟨F.interfaces.direction, F.interfaces.energy, F.interfaces.parallel⟩,
    F.centre_energy, F.full_centre⟩

end BstLean.BlueprintLow
