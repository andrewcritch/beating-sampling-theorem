import BstLean.Part281N11883Core
import BstLean.Part281Direction
namespace BstLean.Part281.N11883
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part281 (scalarRow11883 cell11883)
open BstLean.Part281.Groups (groupTheta groupProfile NeededGroup centreGroup)
theorem sourceCell10 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨10,by decide⟩).lower ∧ (scalarRow11883.table ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (scalarRow11883.table ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy10 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨10,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨10,by decide⟩).lower) ≤ (scalarRow11883.table ⟨10,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy10 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨10,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell11 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨11,by decide⟩).lower ∧ (scalarRow11883.table ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (scalarRow11883.table ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy11 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨11,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨11,by decide⟩).lower) ≤ (scalarRow11883.table ⟨11,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy11 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨11,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell12 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨12,by decide⟩).lower ∧ (scalarRow11883.table ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (scalarRow11883.table ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy12 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨12,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨12,by decide⟩).lower) ≤ (scalarRow11883.table ⟨12,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy12 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨12,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell13 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨13,by decide⟩).lower ∧ (scalarRow11883.table ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (scalarRow11883.table ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy13 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨13,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨13,by decide⟩).lower) ≤ (scalarRow11883.table ⟨13,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy13 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨13,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell14 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨14,by decide⟩).lower ∧ (scalarRow11883.table ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (scalarRow11883.table ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy14 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨14,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨14,by decide⟩).lower) ≤ (scalarRow11883.table ⟨14,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy14 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨14,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell15 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨15,by decide⟩).lower ∧ (scalarRow11883.table ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (scalarRow11883.table ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy15 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨15,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨15,by decide⟩).lower) ≤ (scalarRow11883.table ⟨15,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy15 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨15,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell16 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨16,by decide⟩).lower ∧ (scalarRow11883.table ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (scalarRow11883.table ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy16 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨16,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨16,by decide⟩).lower) ≤ (scalarRow11883.table ⟨16,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy16 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨16,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell17 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨17,by decide⟩).lower ∧ (scalarRow11883.table ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (scalarRow11883.table ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy17 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨17,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨17,by decide⟩).lower) ≤ (scalarRow11883.table ⟨17,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy17 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨17,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell18 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨18,by decide⟩).lower ∧ (scalarRow11883.table ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (scalarRow11883.table ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy18 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨18,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨18,by decide⟩).lower) ≤ (scalarRow11883.table ⟨18,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy18 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨18,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell19 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨19,by decide⟩).lower ∧ (scalarRow11883.table ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (scalarRow11883.table ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy19 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨19,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨19,by decide⟩).lower) ≤ (scalarRow11883.table ⟨19,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy19 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨19,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell20 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨20,by decide⟩).lower ∧ (scalarRow11883.table ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (scalarRow11883.table ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy20 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨20,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨20,by decide⟩).lower) ≤ (scalarRow11883.table ⟨20,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy20 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨20,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell21 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨21,by decide⟩).lower ∧ (scalarRow11883.table ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (scalarRow11883.table ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy21 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨21,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨21,by decide⟩).lower) ≤ (scalarRow11883.table ⟨21,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy21 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨21,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell22 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨22,by decide⟩).lower ∧ (scalarRow11883.table ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (scalarRow11883.table ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy22 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨22,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨22,by decide⟩).lower) ≤ (scalarRow11883.table ⟨22,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy22 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨22,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell23 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨23,by decide⟩).lower ∧ (scalarRow11883.table ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (scalarRow11883.table ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy23 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨23,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨23,by decide⟩).lower) ≤ (scalarRow11883.table ⟨23,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy23 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨23,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell24 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨24,by decide⟩).lower ∧ (scalarRow11883.table ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (scalarRow11883.table ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy24 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨24,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨24,by decide⟩).lower) ≤ (scalarRow11883.table ⟨24,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy24 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨24,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell25 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨25,by decide⟩).lower ∧ (scalarRow11883.table ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (scalarRow11883.table ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy25 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨25,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨25,by decide⟩).lower) ≤ (scalarRow11883.table ⟨25,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy25 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨25,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell26 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨26,by decide⟩).lower ∧ (scalarRow11883.table ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (scalarRow11883.table ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy26 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨26,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨26,by decide⟩).lower) ≤ (scalarRow11883.table ⟨26,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy26 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨26,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell27 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨27,by decide⟩).lower ∧ (scalarRow11883.table ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (scalarRow11883.table ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy27 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨27,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨27,by decide⟩).lower) ≤ (scalarRow11883.table ⟨27,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy27 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨27,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell28 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨28,by decide⟩).lower ∧ (scalarRow11883.table ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (scalarRow11883.table ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy28 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨28,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨28,by decide⟩).lower) ≤ (scalarRow11883.table ⟨28,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy28 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨28,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell29 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨29,by decide⟩).lower ∧ (scalarRow11883.table ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (scalarRow11883.table ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy29 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨29,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨29,by decide⟩).lower) ≤ (scalarRow11883.table ⟨29,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy29 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨29,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell30 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨30,by decide⟩).lower ∧ (scalarRow11883.table ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (scalarRow11883.table ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy30 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨30,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨30,by decide⟩).lower) ≤ (scalarRow11883.table ⟨30,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy30 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨30,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell31 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨31,by decide⟩).lower ∧ (scalarRow11883.table ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (scalarRow11883.table ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy31 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨31,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨31,by decide⟩).lower) ≤ (scalarRow11883.table ⟨31,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy31 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨31,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell32 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨32,by decide⟩).lower ∧ (scalarRow11883.table ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (scalarRow11883.table ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy32 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨32,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨32,by decide⟩).lower) ≤ (scalarRow11883.table ⟨32,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy32 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨32,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell33 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨33,by decide⟩).lower ∧ (scalarRow11883.table ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (scalarRow11883.table ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy33 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨33,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨33,by decide⟩).lower) ≤ (scalarRow11883.table ⟨33,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy33 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨33,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell34 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨34,by decide⟩).lower ∧ (scalarRow11883.table ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (scalarRow11883.table ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy34 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨34,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨34,by decide⟩).lower) ≤ (scalarRow11883.table ⟨34,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy34 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨34,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell35 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨35,by decide⟩).lower ∧ (scalarRow11883.table ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (scalarRow11883.table ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy35 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨35,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨35,by decide⟩).lower) ≤ (scalarRow11883.table ⟨35,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy35 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨35,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell36 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨36,by decide⟩).lower ∧ (scalarRow11883.table ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (scalarRow11883.table ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy36 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨36,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨36,by decide⟩).lower) ≤ (scalarRow11883.table ⟨36,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy36 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨36,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell37 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨37,by decide⟩).lower ∧ (scalarRow11883.table ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (scalarRow11883.table ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy37 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨37,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨37,by decide⟩).lower) ≤ (scalarRow11883.table ⟨37,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy37 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨37,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell38 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨38,by decide⟩).lower ∧ (scalarRow11883.table ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (scalarRow11883.table ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy38 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨38,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨38,by decide⟩).lower) ≤ (scalarRow11883.table ⟨38,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy38 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨38,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell39 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨39,by decide⟩).lower ∧ (scalarRow11883.table ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (scalarRow11883.table ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy39 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨39,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨39,by decide⟩).lower) ≤ (scalarRow11883.table ⟨39,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy39 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨39,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell40 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨40,by decide⟩).lower ∧ (scalarRow11883.table ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (scalarRow11883.table ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy40 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨40,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨40,by decide⟩).lower) ≤ (scalarRow11883.table ⟨40,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy40 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨40,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell41 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨41,by decide⟩).lower ∧ (scalarRow11883.table ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (scalarRow11883.table ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy41 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨41,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨41,by decide⟩).lower) ≤ (scalarRow11883.table ⟨41,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy41 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨41,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell42 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨42,by decide⟩).lower ∧ (scalarRow11883.table ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (scalarRow11883.table ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy42 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨42,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨42,by decide⟩).lower) ≤ (scalarRow11883.table ⟨42,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy42 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨42,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell43 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨43,by decide⟩).lower ∧ (scalarRow11883.table ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (scalarRow11883.table ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy43 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨43,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨43,by decide⟩).lower) ≤ (scalarRow11883.table ⟨43,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy43 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨43,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell44 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨44,by decide⟩).lower ∧ (scalarRow11883.table ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (scalarRow11883.table ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy44 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨44,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨44,by decide⟩).lower) ≤ (scalarRow11883.table ⟨44,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy44 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨44,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell45 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨45,by decide⟩).lower ∧ (scalarRow11883.table ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (scalarRow11883.table ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy45 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨45,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨45,by decide⟩).lower) ≤ (scalarRow11883.table ⟨45,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy45 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨45,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell46 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨46,by decide⟩).lower ∧ (scalarRow11883.table ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (scalarRow11883.table ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy46 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨46,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨46,by decide⟩).lower) ≤ (scalarRow11883.table ⟨46,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy46 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨46,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell47 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨47,by decide⟩).lower ∧ (scalarRow11883.table ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (scalarRow11883.table ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy47 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨47,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨47,by decide⟩).lower) ≤ (scalarRow11883.table ⟨47,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy47 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨47,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell48 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨48,by decide⟩).lower ∧ (scalarRow11883.table ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (scalarRow11883.table ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy48 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨48,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨48,by decide⟩).lower) ≤ (scalarRow11883.table ⟨48,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy48 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨48,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell49 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨49,by decide⟩).lower ∧ (scalarRow11883.table ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (scalarRow11883.table ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy49 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨49,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨49,by decide⟩).lower) ≤ (scalarRow11883.table ⟨49,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy49 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨49,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell50 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨50,by decide⟩).lower ∧ (scalarRow11883.table ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (scalarRow11883.table ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy50 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨50,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨50,by decide⟩).lower) ≤ (scalarRow11883.table ⟨50,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy50 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨50,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell51 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨51,by decide⟩).lower ∧ (scalarRow11883.table ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (scalarRow11883.table ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy51 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨51,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨51,by decide⟩).lower) ≤ (scalarRow11883.table ⟨51,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy51 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨51,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem sourceCell52 :
    (0.46 : ℝ) ≤ (scalarRow11883.table ⟨52,by decide⟩).lower ∧ (scalarRow11883.table ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (scalarRow11883.table ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow11883,cell11883,groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy52 :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table ⟨52,by decide⟩).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table ⟨52,by decide⟩).lower) ≤ (scalarRow11883.table ⟨52,by decide⟩).energy := by
  have E := BstLean.Part281.UE.uniformEnergy52 (n := 11883) (by norm_num)
    (q := 1 - (scalarRow11883.table ⟨52,by decide⟩).lower) (by norm_num [scalarRow11883,cell11883]) (by norm_num [scalarRow11883,cell11883])
  exact ⟨E.1,E.2.trans (by norm_num [scalarRow11883,cell11883])⟩

theorem source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (scalarRow11883.table i).lower ∧ (scalarRow11883.table i).upper ≤ groupTheta (centreGroup i) ∧
    (scalarRow11883.table i).upper ≤ (0.532 : ℝ) ∧ (scalarRow11883.table i).centre ≤ (0.1 : ℝ) ∧ (scalarRow11883.table i).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow11883.table i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow11883.table i).centre = pilotGroupCentre (centreGroup i) := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨2,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨3,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨4,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨5,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨6,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨7,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨8,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨9,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨10,h⟩ => exact sourceCell10
  | ⟨11,h⟩ => exact sourceCell11
  | ⟨12,h⟩ => exact sourceCell12
  | ⟨13,h⟩ => exact sourceCell13
  | ⟨14,h⟩ => exact sourceCell14
  | ⟨15,h⟩ => exact sourceCell15
  | ⟨16,h⟩ => exact sourceCell16
  | ⟨17,h⟩ => exact sourceCell17
  | ⟨18,h⟩ => exact sourceCell18
  | ⟨19,h⟩ => exact sourceCell19
  | ⟨20,h⟩ => exact sourceCell20
  | ⟨21,h⟩ => exact sourceCell21
  | ⟨22,h⟩ => exact sourceCell22
  | ⟨23,h⟩ => exact sourceCell23
  | ⟨24,h⟩ => exact sourceCell24
  | ⟨25,h⟩ => exact sourceCell25
  | ⟨26,h⟩ => exact sourceCell26
  | ⟨27,h⟩ => exact sourceCell27
  | ⟨28,h⟩ => exact sourceCell28
  | ⟨29,h⟩ => exact sourceCell29
  | ⟨30,h⟩ => exact sourceCell30
  | ⟨31,h⟩ => exact sourceCell31
  | ⟨32,h⟩ => exact sourceCell32
  | ⟨33,h⟩ => exact sourceCell33
  | ⟨34,h⟩ => exact sourceCell34
  | ⟨35,h⟩ => exact sourceCell35
  | ⟨36,h⟩ => exact sourceCell36
  | ⟨37,h⟩ => exact sourceCell37
  | ⟨38,h⟩ => exact sourceCell38
  | ⟨39,h⟩ => exact sourceCell39
  | ⟨40,h⟩ => exact sourceCell40
  | ⟨41,h⟩ => exact sourceCell41
  | ⟨42,h⟩ => exact sourceCell42
  | ⟨43,h⟩ => exact sourceCell43
  | ⟨44,h⟩ => exact sourceCell44
  | ⟨45,h⟩ => exact sourceCell45
  | ⟨46,h⟩ => exact sourceCell46
  | ⟨47,h⟩ => exact sourceCell47
  | ⟨48,h⟩ => exact sourceCell48
  | ⟨49,h⟩ => exact sourceCell49
  | ⟨50,h⟩ => exact sourceCell50
  | ⟨51,h⟩ => exact sourceCell51
  | ⟨52,h⟩ => exact sourceCell52
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

theorem upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 11883 (gMinus 11883) (1 - (scalarRow11883.table i).lower) ≤ 1 ∧
    energyUpper 11883 (gMinus 11883) (BstLean.Part211.gPlus 11883)
      (finiteEnergy 11883 11883 0.011) (1 - (scalarRow11883.table i).lower) ≤ (scalarRow11883.table i).energy := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨2,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨3,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨4,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨5,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨6,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨7,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨8,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨9,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨10,h⟩ => exact upperEnergy10
  | ⟨11,h⟩ => exact upperEnergy11
  | ⟨12,h⟩ => exact upperEnergy12
  | ⟨13,h⟩ => exact upperEnergy13
  | ⟨14,h⟩ => exact upperEnergy14
  | ⟨15,h⟩ => exact upperEnergy15
  | ⟨16,h⟩ => exact upperEnergy16
  | ⟨17,h⟩ => exact upperEnergy17
  | ⟨18,h⟩ => exact upperEnergy18
  | ⟨19,h⟩ => exact upperEnergy19
  | ⟨20,h⟩ => exact upperEnergy20
  | ⟨21,h⟩ => exact upperEnergy21
  | ⟨22,h⟩ => exact upperEnergy22
  | ⟨23,h⟩ => exact upperEnergy23
  | ⟨24,h⟩ => exact upperEnergy24
  | ⟨25,h⟩ => exact upperEnergy25
  | ⟨26,h⟩ => exact upperEnergy26
  | ⟨27,h⟩ => exact upperEnergy27
  | ⟨28,h⟩ => exact upperEnergy28
  | ⟨29,h⟩ => exact upperEnergy29
  | ⟨30,h⟩ => exact upperEnergy30
  | ⟨31,h⟩ => exact upperEnergy31
  | ⟨32,h⟩ => exact upperEnergy32
  | ⟨33,h⟩ => exact upperEnergy33
  | ⟨34,h⟩ => exact upperEnergy34
  | ⟨35,h⟩ => exact upperEnergy35
  | ⟨36,h⟩ => exact upperEnergy36
  | ⟨37,h⟩ => exact upperEnergy37
  | ⟨38,h⟩ => exact upperEnergy38
  | ⟨39,h⟩ => exact upperEnergy39
  | ⟨40,h⟩ => exact upperEnergy40
  | ⟨41,h⟩ => exact upperEnergy41
  | ⟨42,h⟩ => exact upperEnergy42
  | ⟨43,h⟩ => exact upperEnergy43
  | ⟨44,h⟩ => exact upperEnergy44
  | ⟨45,h⟩ => exact upperEnergy45
  | ⟨46,h⟩ => exact upperEnergy46
  | ⟨47,h⟩ => exact upperEnergy47
  | ⟨48,h⟩ => exact upperEnergy48
  | ⟨49,h⟩ => exact upperEnergy49
  | ⟨50,h⟩ => exact upperEnergy50
  | ⟨51,h⟩ => exact upperEnergy51
  | ⟨52,h⟩ => exact upperEnergy52
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

noncomputable def sourceNumerics11883 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part277.CellSourceNumericsP 11883 (scalarRow11883.table i) scalarRow11883.M scalarRow11883.H scalarRow11883.xi
      1.22 1.12 1.25 0.665 0.47199 0.52358 := by
  have hg : NeededGroup (centreGroup i) := BstLean.Part253.needed_group hi
  have G := BstLean.Part281.Groups.group_scalar hg
  obtain ⟨hl,hu,hu532,hc,hE,hq,hcentre⟩ := source_cell hi
  have E := upper_energy hi
  exact {
    thetaHi := groupTheta (centreGroup i)
    S := groupProfile (centreGroup i)
    certificate := BstLean.Part277.centreCertificate_from_momentP (by norm_num)
      (pilot_groupMomentCertificate hg) hq E.1 (pilot_group_relative_gap hg) (E.2.trans hE)
      (r := (109.009173925867 : ℝ)) (F := (0.008771 : ℝ))
      (by norm_num) (by norm_num) pilot_finite_centre_upper (by norm_num)
      (fun θ hθ => by
        convert (BstLean.Part281.energy_lower_data (by norm_num : 11883 ≤ 11883)
          ⟨hθ.1,hθ.2.trans G.window.2⟩).1 using 1 <;> norm_num)
    energy_allowance := scalarRow11883.energy_allowance
    parallel_nonneg := by norm_num [scalarRow11883]
    centre_nonneg := (scalarRow11883.certificate i).centre_nonneg
    centre_upper := hc
    MP_nonneg := by norm_num
    e0_pos := by norm_num
    operator := by
      intro c τ hτ
      exact (BstLean.Part277.operator_allowance_11883
        (by norm_num : 11883 ≤ 11883) c hτ).trans (by norm_num)
    lower := fun θ hθ => by
      convert (BstLean.Part281.energy_lower_data
        (by norm_num : 11883 ≤ 11883) ⟨hθ.1,hθ.2.trans G.window.2⟩).2 using 1 <;> norm_num
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part281.Dir11883.direction_budget_11883 (by norm_num : 11883 ≤ 11883)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow11883])
    source_lower := hl
    source_upper := hu
    source_upper_one := hu532.trans (by norm_num)
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }
end BstLean.Part281.N11883
