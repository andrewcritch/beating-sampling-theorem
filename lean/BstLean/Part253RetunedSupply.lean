import BstLean.Part253CentreCertificate
import BstLean.Part253DirectionSupply

/-! The retuned scalar certificates supply the network fields on source events. -/
namespace BstLean.Part253
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part188
open BstLean.Part169 (paperDesignP)
open BstLean.Part211

structure SourceEvents (c : Ret 12225) : Prop where
  world_centre_pos : 0 < normSq c.1.2
  scale_pos : 0 < (paperDesignP 12225).tau0 c
  base_event : c.2.1.1 ∈ BstLean.Part222.centreBase 12225 12225 c.1.2
    ((paperDesignP 12225).tau0 c)
  error_event : c.2.1.1 ∈ BstLean.Part215.sharpErrorEvent c.1.2
    ((paperDesignP 12225).tau0 c)
  operator_event : c.2.1.1 ∈ BstLean.Part215.operatorEvent c.1.2
    ((paperDesignP 12225).tau0 c) 0.006 (ENNReal.ofReal (1 / 20000))
  energy_event : c.2.1.1 ∈ BstLean.Part222.energyEvent c.1.2
    ((paperDesignP 12225).tau0 c)

structure RetunedNetworkInputs (c : Ret 12225) (i : Fin 60) : Prop where
  scale_pos : 0 < (paperDesignP 12225).tau0 c
  centre_pos : 0 < normSq ((paperDesignP 12225).bA c.1 c.2.1.1)
  interfaces : WFInterfaces (paperDesignP 12225) c directionCap energyCap parallelCap
  centre_energy : centreEnergy (paperDesignP 12225) c ≤ retunedEnergy i
  full_centre : BstLean.Part160.CENTRE_at (paperDesignP 12225) c
    (retunedCentre (centreGroup i))

theorem retuned_network_from_events {c : Ret 12225} {i : Fin 60}
    (hi : needed i)
    (hm : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈ cell i)
    (F : SourceEvents c) : RetunedNetworkInputs c i := by
  have hg := needed_group hi
  have G := group_scalar hg
  have hδ : ENNReal.ofReal (1 / 20000 : ℝ) ≠ 0 := by norm_num
  have hSource := BstLean.Part222.centreSource_on_operator_event c.1.2
    ((paperDesignP 12225).tau0 c) 0.006 1.22 hδ F.base_event F.operator_event
    (BstLean.Part222.operatorXiAllowance_le c.1.2 ((paperDesignP 12225).tau0 c)
      0.006 1.22 _ (operator_allowance_le c.1.2 F.scale_pos))
  have hw := cell_inside_group hi hm
  have hWorld : 1 - BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ≤
      1 - noiseNode i.val := sub_le_sub_left hm.1 1
  have hC := centre_formula_junction (by norm_num) (by norm_num) (by norm_num)
    c.1.2 F.world_centre_pos F.scale_pos (by norm_num : (0 : ℝ) ≤ 1.22)
    (fun _ => 0.006) (localCentreCertificate hi) hw hWorld hSource
  have hF := hC.1.trans G.full_scalar
  rw [BstLean.Part222.fullError_normalization (by norm_num) (paperDesignP 12225) c
    (paper_centre_eq c)] at hF
  have hP := hC.2.1.trans (group_parallel hg)
  have hEL : (0.665 : ℝ) ≤ centreEnergy (paperDesignP 12225) c := by
    rw [BstLean.Part222.energy_normalization (by norm_num) (paperDesignP 12225) c
      F.scale_pos (paper_centre_eq c)]
    have hl : (0.665 : ℝ) ≤ energyLower 12225 (gMinus 12225) (gPlus 12225)
        (finiteEnergy 12225 12225 0.011)
        (BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c)) := by
      convert energy_lower_window ⟨hw.1, hw.2.trans (G.window.2.trans (by norm_num))⟩
        using 1 <;> norm_num
    exact hl.trans hC.2.2.1
  have hEU : centreEnergy (paperDesignP 12225) c ≤ retunedEnergy i := by
    rw [BstLean.Part222.energy_normalization (by norm_num) (paperDesignP 12225) c
      F.scale_pos (paper_centre_eq c)]
    have hu : BstLean.Part206.energyUpper 12225 (gMinus 12225) (gPlus 12225)
        (finiteEnergy 12225 12225 0.011) (1 - noiseNode i.val) ≤ retunedEnergy i := by
      convert (upper_energy_on_needed hi (cell_world_signal hi).1 le_rfl).2
        using 1 <;> norm_num
    exact hC.2.2.2.1.trans hu
  have hbn : (12225 : ℝ) * 0.665 ≤ normSq ((paperDesignP 12225).bA c.1 c.2.1.1) := by
    unfold centreEnergy at hEL
    linarith [(le_div_iff₀ (by norm_num : (0 : ℝ) < 12225)).mp hEL]
  have hbpos : 0 < normSq ((paperDesignP 12225).bA c.1 c.2.1.1) := by linarith
  exact ⟨F.scale_pos, hbpos,
    ⟨direction_on_source_events hi hm F.scale_pos G.centre_nonneg G.centre_le hbn hF
        F.error_event F.operator_event,
      energy_on_event c F.energy_event,
      BstLean.Part222.parallelCentre_of_s12 (by norm_num) (paperDesignP 12225) c
        (paper_centre_eq c) hbpos (by norm_num [parallelCap]) hP⟩,
    hEU, BstLean.Part222.centre_at_of_raw_bound (paperDesignP 12225) c hF⟩

noncomputable def frameInputs_from_retuned_network_general
    {localCell : Fin 60 → Set ℝ} {caps : Fin 60 → ℝ} {cf : ℝ}
    (C : LocalCovariance localCell caps)
    {c : Ret 12225} {i : Fin 60} (hi : needed i)
    (hm : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈ localCell i)
    (F : RetunedNetworkInputs c i) (hcap : 0 ≤ caps i)
    (hframe : (caps i + retunedCentre (centreGroup i)) / retunedCutoff i + massTable i ≤ cf) :
    LocalFrameInputs localCell caps c cf := by
  have S := scalar_on_needed hi
  have R := retuned_on_needed hi
  exact {
    cov_le := C
    index := i
    index_needed := hi
    member := hm
    cutoff := retunedCutoff
    centreAllowance := retunedCentre
    massAllowance := massTable
    M := directionCap
    H := energyCap
    xiP := parallelCap
    E := retunedEnergy i
    u := radiusCutoff
    order := 12
    order_pos := by norm_num
    order_le := by norm_num
    scale_pos := F.scale_pos
    centre_pos := F.centre_pos
    centre_nonneg := paper_centre_nonneg c
    interfaces := F.interfaces
    centre_energy := F.centre_energy
    u_pos := by norm_num [radiusCutoff]
    u_lt := by norm_num [radiusCutoff]
    cutoff_pos := R.cutoff_pos
    cutoff_lt := by have := S.cutoff_lt; unfold retunedCutoff; linarith
    gap_pos := S.gap_pos.trans_le (retuned_gap hi R.energy_lower)
    covariance_nonneg := hcap
    full_centre := F.full_centre
    mass_scalar := retuned_mass hi R.energy_lower
    frame_scalar := hframe }

noncomputable def frameInputs_from_retuned_network (C : LocalCovariance cell capTable)
    {c : Ret 12225} {i : Fin 60} (hi : needed i)
    (hm : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈ cell i)
    (F : RetunedNetworkInputs c i) :
    LocalFrameInputs cell capTable c BstLean.Part249.optionBAgentFrame :=
  frameInputs_from_retuned_network_general C hi hm F
    (scalar_on_needed hi).covariance_nonneg (retuned_on_needed hi).frame_scalar

noncomputable def frameInputs_from_events (C : LocalCovariance cell capTable)
    {c : Ret 12225} {i : Fin 60} (hi : needed i)
    (hm : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈ cell i)
    (F : SourceEvents c) : LocalFrameInputs cell capTable c BstLean.Part249.optionBAgentFrame :=
  frameInputs_from_retuned_network C hi hm (retuned_network_from_events hi hm F)

end BstLean.Part253
