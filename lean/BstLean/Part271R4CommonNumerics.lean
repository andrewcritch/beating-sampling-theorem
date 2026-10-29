import BstLean.Part271R4TableShared
import BstLean.Part271R4EnergyShared
import BstLean.Part271R4DirectionA13225
import BstLean.Part269FrameAdapter

namespace BstLean.Part271.R4.CommonNumerics
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211 BstLean.Part206
open BstLean.Part182 BstLean.Part271.R4.A13225
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part271.R4.SharedTable (table tableCertificate)

theorem energies {n : ℕ} (ha : 13225 ≤ n)
    (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio n (gMinus n) (1 - (table i).lower) ≤ 1 ∧
    energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) (1 - (table i).lower) ≤ (table i).energy := by
  match i with
  | ⟨0,_⟩ => exact False.elim (by norm_num at hi)
  | ⟨1,_⟩ => exact False.elim (by norm_num at hi)
  | ⟨2,_⟩ => exact False.elim (by norm_num at hi)
  | ⟨3,_⟩ => exact False.elim (by norm_num at hi)
  | ⟨4,_⟩ => exact False.elim (by norm_num at hi)
  | ⟨5,_⟩ => exact False.elim (by norm_num at hi)
  | ⟨6,_⟩ => exact False.elim (by norm_num at hi)
  | ⟨7,_⟩ => exact False.elim (by norm_num at hi)
  | ⟨8,_⟩ => exact False.elim (by norm_num at hi)
  | ⟨9,_⟩ => exact False.elim (by norm_num at hi)
  | ⟨10,_⟩ => exact SharedEnergy.energy10 ha (by norm_num [table]) (by norm_num [table])
  | ⟨11,_⟩ => exact SharedEnergy.energy11 ha (by norm_num [table]) (by norm_num [table])
  | ⟨12,_⟩ => exact SharedEnergy.energy12 ha (by norm_num [table]) (by norm_num [table])
  | ⟨13,_⟩ => exact SharedEnergy.energy13 ha (by norm_num [table]) (by norm_num [table])
  | ⟨14,_⟩ => exact SharedEnergy.energy14 ha (by norm_num [table]) (by norm_num [table])
  | ⟨15,_⟩ => exact SharedEnergy.energy15 ha (by norm_num [table]) (by norm_num [table])
  | ⟨16,_⟩ => exact SharedEnergy.energy16 ha (by norm_num [table]) (by norm_num [table])
  | ⟨17,_⟩ => exact SharedEnergy.energy17 ha (by norm_num [table]) (by norm_num [table])
  | ⟨18,_⟩ => exact SharedEnergy.energy18 ha (by norm_num [table]) (by norm_num [table])
  | ⟨19,_⟩ => exact SharedEnergy.energy19 ha (by norm_num [table]) (by norm_num [table])
  | ⟨20,_⟩ => exact SharedEnergy.energy20 ha (by norm_num [table]) (by norm_num [table])
  | ⟨21,_⟩ => exact SharedEnergy.energy21 ha (by norm_num [table]) (by norm_num [table])
  | ⟨22,_⟩ => exact SharedEnergy.energy22 ha (by norm_num [table]) (by norm_num [table])
  | ⟨23,_⟩ => exact SharedEnergy.energy23 ha (by norm_num [table]) (by norm_num [table])
  | ⟨24,_⟩ => exact SharedEnergy.energy24 ha (by norm_num [table]) (by norm_num [table])
  | ⟨25,_⟩ => exact SharedEnergy.energy25 ha (by norm_num [table]) (by norm_num [table])
  | ⟨26,_⟩ => exact SharedEnergy.energy26 ha (by norm_num [table]) (by norm_num [table])
  | ⟨27,_⟩ => exact SharedEnergy.energy27 ha (by norm_num [table]) (by norm_num [table])
  | ⟨28,_⟩ => exact SharedEnergy.energy28 ha (by norm_num [table]) (by norm_num [table])
  | ⟨29,_⟩ => exact SharedEnergy.energy29 ha (by norm_num [table]) (by norm_num [table])
  | ⟨30,_⟩ => exact SharedEnergy.energy30 ha (by norm_num [table]) (by norm_num [table])
  | ⟨31,_⟩ => exact SharedEnergy.energy31 ha (by norm_num [table]) (by norm_num [table])
  | ⟨32,_⟩ => exact SharedEnergy.energy32 ha (by norm_num [table]) (by norm_num [table])
  | ⟨33,_⟩ => exact SharedEnergy.energy33 ha (by norm_num [table]) (by norm_num [table])
  | ⟨34,_⟩ => exact SharedEnergy.energy34 ha (by norm_num [table]) (by norm_num [table])
  | ⟨35,_⟩ => exact SharedEnergy.energy35 ha (by norm_num [table]) (by norm_num [table])
  | ⟨36,_⟩ => exact SharedEnergy.energy36 ha (by norm_num [table]) (by norm_num [table])
  | ⟨37,_⟩ => exact SharedEnergy.energy37 ha (by norm_num [table]) (by norm_num [table])
  | ⟨38,_⟩ => exact SharedEnergy.energy38 ha (by norm_num [table]) (by norm_num [table])
  | ⟨39,_⟩ => exact SharedEnergy.energy39 ha (by norm_num [table]) (by norm_num [table])
  | ⟨40,_⟩ => exact SharedEnergy.energy40 ha (by norm_num [table]) (by norm_num [table])
  | ⟨41,_⟩ => exact SharedEnergy.energy41 ha (by norm_num [table]) (by norm_num [table])
  | ⟨42,_⟩ => exact SharedEnergy.energy42 ha (by norm_num [table]) (by norm_num [table])
  | ⟨43,_⟩ => exact SharedEnergy.energy43 ha (by norm_num [table]) (by norm_num [table])
  | ⟨44,_⟩ => exact SharedEnergy.energy44 ha (by norm_num [table]) (by norm_num [table])
  | ⟨45,_⟩ => exact SharedEnergy.energy45 ha (by norm_num [table]) (by norm_num [table])
  | ⟨46,_⟩ => exact SharedEnergy.energy46 ha (by norm_num [table]) (by norm_num [table])
  | ⟨47,_⟩ => exact SharedEnergy.energy47 ha (by norm_num [table]) (by norm_num [table])
  | ⟨48,_⟩ => exact SharedEnergy.energy48 ha (by norm_num [table]) (by norm_num [table])
  | ⟨49,_⟩ => exact SharedEnergy.energy49 ha (by norm_num [table]) (by norm_num [table])
  | ⟨50,_⟩ => exact SharedEnergy.energy50 ha (by norm_num [table]) (by norm_num [table])
  | ⟨51,_⟩ => exact SharedEnergy.energy51 ha (by norm_num [table]) (by norm_num [table])
  | ⟨52,_⟩ => exact SharedEnergy.energy52 ha (by norm_num [table]) (by norm_num [table])
  | ⟨53,_⟩ => exact False.elim (by norm_num at hi)
  | ⟨54,_⟩ => exact False.elim (by norm_num at hi)
  | ⟨55,_⟩ => exact False.elim (by norm_num at hi)
  | ⟨56,_⟩ => exact False.elim (by norm_num at hi)
  | ⟨57,_⟩ => exact False.elim (by norm_num at hi)
  | ⟨58,_⟩ => exact False.elim (by norm_num at hi)
  | ⟨59,_⟩ => exact False.elim (by norm_num at hi)
  | ⟨j+60,h⟩ => exact False.elim (by omega)

theorem source_cell (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    0.46 ≤ (table i).lower ∧ (table i).upper ≤ groupTheta (centreGroup i) ∧
    (table i).upper ≤ 0.532 ∧ (table i).centre ≤ 0.1 ∧ (table i).energy ≤ 1 ∧
    1 - (table i).lower ∈ Icc (-1 : ℝ) 1 ∧
    (table i).centre = source_centres (centreGroup i) := by
  fin_cases i <;> simp at hi
  all_goals norm_num [table,source_centres,centreGroup,groupTheta]

theorem energy_cap (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (table i).energy ≤ 702 / 1000 := by
  fin_cases i <;> simp at hi
  all_goals norm_num [table]

noncomputable def sourceNumerics {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)
    (H : ℝ) (hH : BstLean.Part222.energyAllowance n ≤ H)
    (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics n (table i) tableCertificate.M H tableCertificate.xi := by
  have hg : NeededGroup (centreGroup i) := BstLean.Part253.needed_group hi
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hl,hu,hu532,hc,hE,hq,hcentre⟩ := source_cell i hi
  have E := energies ha i hi
  exact {
    thetaHi := groupTheta (centreGroup i)
    S := groupProfile (centreGroup i)
    certificate := BstLean.Part264.centreCertificate_from_moment (by omega)
      (G.window.2.trans (by norm_num)) (source_groupMoment ha hb hg)
      hq E.1 (source_group_gap ha hb hg) (E.2.trans hE)
    energy_allowance := hH
    parallel_nonneg := by norm_num [tableCertificate]
    centre_nonneg := (tableCertificate.certificates i).centre_nonneg
    centre_upper := hc
    direction := fun c τ e xi eta δ hw he hxi hxi1 hop =>
      direction ha hb c τ e xi eta δ hw he hxi hxi1 hop
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact source_group_full ha hb hg
    parallel_scalar := source_group_parallel ha hb hg
    upper_scalar := E.2 }

end BstLean.Part271.R4.CommonNumerics
