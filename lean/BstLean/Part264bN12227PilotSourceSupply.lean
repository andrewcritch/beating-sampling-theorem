import BstLean.Part264bN12227PilotFullGroups
import BstLean.Part264bN12227PilotEnergyCells
import BstLean.Part264bN12227PilotSourceCells
import BstLean.Part264Source
import BstLean.Part264Centre

/-! The local source numeric instances at 12227 have no network premises. -/
namespace BstLean.Part264b.N12227
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12227)

noncomputable def sourceNumerics12227 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12227 (scalarRow12227.table i)
      scalarRow12227.M scalarRow12227.H scalarRow12227.xi := by
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
    energy_allowance := scalarRow12227.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12227]
    centre_nonneg := (scalarRow12227.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12227]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12227
