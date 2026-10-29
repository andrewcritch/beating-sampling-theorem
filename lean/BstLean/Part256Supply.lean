import BstLean.Part256Scalar
import BstLean.Part256Bridge
import BstLean.Part253RetunedSupply
import BstLean.Part253Actual

namespace BstLean.Part256
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part188
open BstLean.Part169 (paperDesignP)
open BstLean.Part255 (LocalCovarianceOn)
open BstLean.Part253 hiding LocalFrameInputs covariance_from_contract frame_from_inputs scalar_on_needed

noncomputable def frameInputs_from_retuned_network_general
    {event : Set (AgFam 12225)} {localCell : Fin 60 → Set ℝ} {caps : Fin 60 → ℝ} {cf : ℝ}
    (C : LocalCovarianceOn event localCell caps)
    {c : Ret 12225} {i : Fin 60} (hi : needed i)
    (hm : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈ localCell i)
    (F : RetunedNetworkInputs c i) (hcap : 0 ≤ caps i)
    (hframe : (caps i + retunedCentre (centreGroup i)) / retunedCutoff i + massTable i ≤ cf) :
    LocalFrameInputs event localCell caps c cf := by
  have S := BstLean.Part253.scalar_on_needed hi
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

noncomputable def frameInputs_from_events
    {event : Set (AgFam 12225)} {caps : Fin 60 → ℝ}
    (C : LocalCovarianceOn event BstLean.Part255.cell caps)
    {c : Ret 12225} {i : Fin 60} (hi : needed i)
    (hm : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈
      BstLean.Part255.cell i)
    (F : SourceEvents c) (hcap : 0 ≤ caps i)
    (hframe : (caps i + retunedCentre (centreGroup i)) / retunedCutoff i +
      massTable i ≤ BstLean.Part249.optionBAgentFrame) :
    LocalFrameInputs event BstLean.Part255.cell caps c BstLean.Part249.optionBAgentFrame :=
  frameInputs_from_retuned_network_general C hi hm
    (retuned_network_from_events hi (supplied_cell_subset i hm) F) hcap hframe

noncomputable def selectedFrameInputs {c : Ret 12225} {i : Fin 60}
    (hi : needed i)
    (hm : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈
      BstLean.Part255.cell i) (F : SourceEvents c) :
    LocalFrameInputs (BstLean.Part255.selected BstLean.Part255.parameters
      BstLean.Part255.payment) BstLean.Part255.cell BstLean.Part255.localCapTable c
      BstLean.Part249.optionBAgentFrame :=
  frameInputs_from_events BstLean.Part255.localCov hi hm F
    (scalar_on_needed hi).1 (scalar_on_needed hi).2

end BstLean.Part256
