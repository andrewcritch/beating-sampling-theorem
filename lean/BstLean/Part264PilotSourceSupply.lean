import BstLean.Part264PilotFullGroups
import BstLean.Part264PilotEnergyCells
import BstLean.Part264PilotSourceCells
import BstLean.Part264Source
import BstLean.Part264Centre

/-! The local source numeric instances at 12226 have no network premises. -/
namespace BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12226)

noncomputable def sourceNumerics12226 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12226 (scalarRow12226.table i)
      scalarRow12226.M scalarRow12226.H scalarRow12226.xi := by
  have hg : NeededGroup (centreGroup i) := BstLean.Part253.needed_group hi
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hl,hu,hu532,hc,hE,hq,hcentre⟩ := pilot_source_cell hi
  have E := pilot_upper_energy hi
  exact {
    thetaHi := groupTheta (centreGroup i)
    S := groupProfile (centreGroup i)
    certificate := centreCertificate_from_moment (by norm_num)
      (G.window.2.trans (by norm_num)) (pilot_groupMomentCertificate hg)
      hq E.1 (pilot_group_relative_gap hg) (E.2.trans hE)
    energy_allowance := scalarRow12226.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12226]
    centre_nonneg := (scalarRow12226.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12226]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264
