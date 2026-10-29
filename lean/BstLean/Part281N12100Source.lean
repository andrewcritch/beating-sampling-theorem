import BstLean.Part281N12100Core
import BstLean.Part281Direction
namespace BstLean.Part281.N12100
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part281 (scalarRow12100 cell12100)
open BstLean.Part281.Groups (groupTheta groupProfile NeededGroup centreGroup)
theorem sourceCell10 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨10,by decide⟩).lower ∧ (scalarRow12100.table ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (scalarRow12100.table ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((118002169169625546077993/250000000000000000000000) : ℝ) ∧ ((47320954434635240274317/100000000000000000000000) : ℝ) ≤ (0.474440844 : ℝ) ∧
      ((47320954434635240274317/100000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((43771538213/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((21911045058783/31250000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((118002169169625546077993/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((43771538213/500000000000) : ℝ) = (0.087543076426 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((118002169169625546077993/250000000000000000000000) : ℚ) ∧ ((47320954434635240274317/100000000000000000000000) : ℚ) ≤ (0.474440844 : ℚ) ∧
      ((47320954434635240274317/100000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((43771538213/500000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((21911045058783/31250000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((118002169169625546077993/250000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((43771538213/500000000000) : ℚ) = (0.087543076426 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((118002169169625546077993/250000000000000000000000) : ℝ) ∧ ((47320954434635240274317/100000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
      ((47320954434635240274317/100000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((43771538213/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((21911045058783/31250000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((118002169169625546077993/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((43771538213/500000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨10,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy10 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨10,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨10,by decide⟩).lower) ≤ (scalarRow12100.table ⟨10,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((118002169169625546077993/250000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((118002169169625546077993/250000000000000000000000) : ℝ)) ≤ ((21911045058783/31250000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy10 (n := 12100) (by norm_num)
    (q := 1 - ((118002169169625546077993/250000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell11 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨11,by decide⟩).lower ∧ (scalarRow12100.table ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (scalarRow12100.table ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((473209544346352402743169/1000000000000000000000000) : ℝ) ∧ ((474410412014202621174367/1000000000000000000000000) : ℝ) ≤ (0.474440844 : ℝ) ∧
      ((474410412014202621174367/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((43771538213/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3502843476273641/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((473209544346352402743169/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((43771538213/500000000000) : ℝ) = (0.087543076426 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((473209544346352402743169/1000000000000000000000000) : ℚ) ∧ ((474410412014202621174367/1000000000000000000000000) : ℚ) ≤ (0.474440844 : ℚ) ∧
      ((474410412014202621174367/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((43771538213/500000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((3502843476273641/5000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((473209544346352402743169/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((43771538213/500000000000) : ℚ) = (0.087543076426 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((473209544346352402743169/1000000000000000000000000) : ℝ) ∧ ((474410412014202621174367/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
      ((474410412014202621174367/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((43771538213/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3502843476273641/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((473209544346352402743169/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((43771538213/500000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨11,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy11 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨11,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨11,by decide⟩).lower) ≤ (scalarRow12100.table ⟨11,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((473209544346352402743169/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((473209544346352402743169/1000000000000000000000000) : ℝ)) ≤ ((3502843476273641/5000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy11 (n := 12100) (by norm_num)
    (q := 1 - ((473209544346352402743169/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell12 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨12,by decide⟩).lower ∧ (scalarRow12100.table ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (scalarRow12100.table ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((237205206007101310587183/500000000000000000000000) : ℝ) ∧ ((118902819920513209901391/250000000000000000000000) : ℝ) ≤ (0.481661266 : ℝ) ∧
      ((118902819920513209901391/250000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((88529350899/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3499923042261229/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((237205206007101310587183/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((88529350899/1000000000000) : ℝ) = (0.088529350899 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((237205206007101310587183/500000000000000000000000) : ℚ) ∧ ((118902819920513209901391/250000000000000000000000) : ℚ) ≤ (0.481661266 : ℚ) ∧
      ((118902819920513209901391/250000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((88529350899/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((3499923042261229/5000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((237205206007101310587183/500000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((88529350899/1000000000000) : ℚ) = (0.088529350899 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((237205206007101310587183/500000000000000000000000) : ℝ) ∧ ((118902819920513209901391/250000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
      ((118902819920513209901391/250000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((88529350899/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3499923042261229/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((237205206007101310587183/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((88529350899/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨12,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy12 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨12,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨12,by decide⟩).lower) ≤ (scalarRow12100.table ⟨12,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((237205206007101310587183/500000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((237205206007101310587183/500000000000000000000000) : ℝ)) ≤ ((3499923042261229/5000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy12 (n := 12100) (by norm_num)
    (q := 1 - ((237205206007101310587183/500000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell13 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨13,by decide⟩).lower ∧ (scalarRow12100.table ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (scalarRow12100.table ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((475611279682052839605563/1000000000000000000000000) : ℝ) ∧ ((238406073674951529018381/500000000000000000000000) : ℝ) ≤ (0.481661266 : ℝ) ∧
      ((238406073674951529018381/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((88529350899/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6994011803641153/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((475611279682052839605563/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((88529350899/1000000000000) : ℝ) = (0.088529350899 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((475611279682052839605563/1000000000000000000000000) : ℚ) ∧ ((238406073674951529018381/500000000000000000000000) : ℚ) ≤ (0.481661266 : ℚ) ∧
      ((238406073674951529018381/500000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((88529350899/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6994011803641153/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((475611279682052839605563/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((88529350899/1000000000000) : ℚ) = (0.088529350899 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((475611279682052839605563/1000000000000000000000000) : ℝ) ∧ ((238406073674951529018381/500000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
      ((238406073674951529018381/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((88529350899/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6994011803641153/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((475611279682052839605563/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((88529350899/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨13,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy13 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨13,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨13,by decide⟩).lower) ≤ (scalarRow12100.table ⟨13,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((475611279682052839605563/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((475611279682052839605563/1000000000000000000000000) : ℝ)) ≤ ((6994011803641153/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy13 (n := 12100) (by norm_num)
    (q := 1 - ((475611279682052839605563/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell14 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨14,by decide⟩).lower ∧ (scalarRow12100.table ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (scalarRow12100.table ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((476812147349903058036761/1000000000000000000000000) : ℝ) ∧ ((478013015017753276467959/1000000000000000000000000) : ℝ) ≤ (0.481661266 : ℝ) ∧
      ((478013015017753276467959/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((88529350899/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1747046024713189/2500000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((476812147349903058036761/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((88529350899/1000000000000) : ℝ) = (0.088529350899 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((476812147349903058036761/1000000000000000000000000) : ℚ) ∧ ((478013015017753276467959/1000000000000000000000000) : ℚ) ≤ (0.481661266 : ℚ) ∧
      ((478013015017753276467959/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((88529350899/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((1747046024713189/2500000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((476812147349903058036761/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((88529350899/1000000000000) : ℚ) = (0.088529350899 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((476812147349903058036761/1000000000000000000000000) : ℝ) ∧ ((478013015017753276467959/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
      ((478013015017753276467959/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((88529350899/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1747046024713189/2500000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((476812147349903058036761/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((88529350899/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨14,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy14 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨14,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨14,by decide⟩).lower) ≤ (scalarRow12100.table ⟨14,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((476812147349903058036761/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((476812147349903058036761/1000000000000000000000000) : ℝ)) ≤ ((1747046024713189/2500000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy14 (n := 12100) (by norm_num)
    (q := 1 - ((476812147349903058036761/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell15 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨15,by decide⟩).lower ∧ (scalarRow12100.table ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (scalarRow12100.table ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((239006507508876638233979/500000000000000000000000) : ℝ) ∧ ((119803470671400873724789/250000000000000000000000) : ℝ) ≤ (0.481661266 : ℝ) ∧
      ((119803470671400873724789/250000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((88529350899/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6982362959150711/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((239006507508876638233979/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((88529350899/1000000000000) : ℝ) = (0.088529350899 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((239006507508876638233979/500000000000000000000000) : ℚ) ∧ ((119803470671400873724789/250000000000000000000000) : ℚ) ≤ (0.481661266 : ℚ) ∧
      ((119803470671400873724789/250000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((88529350899/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6982362959150711/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((239006507508876638233979/500000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((88529350899/1000000000000) : ℚ) = (0.088529350899 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((239006507508876638233979/500000000000000000000000) : ℝ) ∧ ((119803470671400873724789/250000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
      ((119803470671400873724789/250000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((88529350899/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6982362959150711/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((239006507508876638233979/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((88529350899/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨15,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy15 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨15,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨15,by decide⟩).lower) ≤ (scalarRow12100.table ⟨15,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((239006507508876638233979/500000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((239006507508876638233979/500000000000000000000000) : ℝ)) ≤ ((6982362959150711/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy15 (n := 12100) (by norm_num)
    (q := 1 - ((239006507508876638233979/500000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell16 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨16,by decide⟩).lower ∧ (scalarRow12100.table ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (scalarRow12100.table ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((95842776537120698979831/200000000000000000000000) : ℝ) ∧ ((480414750353453713330353/1000000000000000000000000) : ℝ) ≤ (0.481661266 : ℝ) ∧
      ((480414750353453713330353/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((88529350899/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6976548373572227/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((95842776537120698979831/200000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((88529350899/1000000000000) : ℝ) = (0.088529350899 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((95842776537120698979831/200000000000000000000000) : ℚ) ∧ ((480414750353453713330353/1000000000000000000000000) : ℚ) ≤ (0.481661266 : ℚ) ∧
      ((480414750353453713330353/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((88529350899/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6976548373572227/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((95842776537120698979831/200000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((88529350899/1000000000000) : ℚ) = (0.088529350899 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((95842776537120698979831/200000000000000000000000) : ℝ) ∧ ((480414750353453713330353/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
      ((480414750353453713330353/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((88529350899/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6976548373572227/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((95842776537120698979831/200000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((88529350899/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨16,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy16 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨16,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨16,by decide⟩).lower) ≤ (scalarRow12100.table ⟨16,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((95842776537120698979831/200000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((95842776537120698979831/200000000000000000000000) : ℝ)) ≤ ((6976548373572227/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy16 (n := 12100) (by norm_num)
    (q := 1 - ((95842776537120698979831/200000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell17 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨17,by decide⟩).lower ∧ (scalarRow12100.table ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (scalarRow12100.table ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((30025921897090857083147/62500000000000000000000) : ℝ) ∧ ((9632312360426078635231/20000000000000000000000) : ℝ) ≤ (0.481661266 : ℝ) ∧
      ((9632312360426078635231/20000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((88529350899/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6970740331198013/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((30025921897090857083147/62500000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((88529350899/1000000000000) : ℝ) = (0.088529350899 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((30025921897090857083147/62500000000000000000000) : ℚ) ∧ ((9632312360426078635231/20000000000000000000000) : ℚ) ≤ (0.481661266 : ℚ) ∧
      ((9632312360426078635231/20000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((88529350899/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6970740331198013/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((30025921897090857083147/62500000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((88529350899/1000000000000) : ℚ) = (0.088529350899 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((30025921897090857083147/62500000000000000000000) : ℝ) ∧ ((9632312360426078635231/20000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
      ((9632312360426078635231/20000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((88529350899/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6970740331198013/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((30025921897090857083147/62500000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((88529350899/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨17,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy17 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨17,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨17,by decide⟩).lower) ≤ (scalarRow12100.table ⟨17,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((30025921897090857083147/62500000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((30025921897090857083147/62500000000000000000000) : ℝ)) ≤ ((6970740331198013/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy17 (n := 12100) (by norm_num)
    (q := 1 - ((30025921897090857083147/62500000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell18 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨18,by decide⟩).lower ∧ (scalarRow12100.table ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (scalarRow12100.table ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((481615618021303931761549/1000000000000000000000000) : ℝ) ∧ ((120704121422288537548187/250000000000000000000000) : ℝ) ≤ (0.488881687 : ℝ) ∧
      ((120704121422288537548187/250000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22380231657/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6964938821151997/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((481615618021303931761549/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((22380231657/250000000000) : ℝ) = (0.089520926628 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((481615618021303931761549/1000000000000000000000000) : ℚ) ∧ ((120704121422288537548187/250000000000000000000000) : ℚ) ≤ (0.488881687 : ℚ) ∧
      ((120704121422288537548187/250000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((22380231657/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6964938821151997/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((481615618021303931761549/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((22380231657/250000000000) : ℚ) = (0.089520926628 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((481615618021303931761549/1000000000000000000000000) : ℝ) ∧ ((120704121422288537548187/250000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
      ((120704121422288537548187/250000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22380231657/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6964938821151997/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((481615618021303931761549/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((22380231657/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨18,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy18 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨18,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨18,by decide⟩).lower) ≤ (scalarRow12100.table ⟨18,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((481615618021303931761549/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((481615618021303931761549/1000000000000000000000000) : ℝ)) ≤ ((6964938821151997/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy18 (n := 12100) (by norm_num)
    (q := 1 - ((481615618021303931761549/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell19 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨19,by decide⟩).lower ∧ (scalarRow12100.table ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (scalarRow12100.table ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((482816485689154150192747/1000000000000000000000000) : ℝ) ∧ ((96803470671400873724789/200000000000000000000000) : ℝ) ≤ (0.488881687 : ℝ) ∧
      ((96803470671400873724789/200000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22380231657/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6959143832601061/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((482816485689154150192747/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((22380231657/250000000000) : ℝ) = (0.089520926628 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((482816485689154150192747/1000000000000000000000000) : ℚ) ∧ ((96803470671400873724789/200000000000000000000000) : ℚ) ≤ (0.488881687 : ℚ) ∧
      ((96803470671400873724789/200000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((22380231657/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6959143832601061/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((482816485689154150192747/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((22380231657/250000000000) : ℚ) = (0.089520926628 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((482816485689154150192747/1000000000000000000000000) : ℝ) ∧ ((96803470671400873724789/200000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
      ((96803470671400873724789/200000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22380231657/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6959143832601061/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((482816485689154150192747/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((22380231657/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨19,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy19 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨19,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨19,by decide⟩).lower) ≤ (scalarRow12100.table ⟨19,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((482816485689154150192747/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((482816485689154150192747/1000000000000000000000000) : ℝ)) ≤ ((6959143832601061/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy19 (n := 12100) (by norm_num)
    (q := 1 - ((482816485689154150192747/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell20 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨20,by decide⟩).lower ∧ (scalarRow12100.table ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (scalarRow12100.table ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((60502169169625546077993/125000000000000000000000) : ℝ) ∧ ((242609110512427293527571/500000000000000000000000) : ℝ) ≤ (0.488881687 : ℝ) ∧
      ((242609110512427293527571/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22380231657/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6953355354754769/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((60502169169625546077993/125000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((22380231657/250000000000) : ℝ) = (0.089520926628 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((60502169169625546077993/125000000000000000000000) : ℚ) ∧ ((242609110512427293527571/500000000000000000000000) : ℚ) ≤ (0.488881687 : ℚ) ∧
      ((242609110512427293527571/500000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((22380231657/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6953355354754769/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((60502169169625546077993/125000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((22380231657/250000000000) : ℚ) = (0.089520926628 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((60502169169625546077993/125000000000000000000000) : ℝ) ∧ ((242609110512427293527571/500000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
      ((242609110512427293527571/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22380231657/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6953355354754769/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((60502169169625546077993/125000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((22380231657/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨20,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy20 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨20,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨20,by decide⟩).lower) ≤ (scalarRow12100.table ⟨20,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((60502169169625546077993/125000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((60502169169625546077993/125000000000000000000000) : ℝ)) ≤ ((6953355354754769/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy20 (n := 12100) (by norm_num)
    (q := 1 - ((60502169169625546077993/125000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell21 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨21,by decide⟩).lower ∧ (scalarRow12100.table ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (scalarRow12100.table ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((485218221024854587055141/1000000000000000000000000) : ℝ) ∧ ((486419088692704805486339/1000000000000000000000000) : ℝ) ≤ (0.488881687 : ℝ) ∧
      ((486419088692704805486339/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22380231657/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6947573376865103/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((485218221024854587055141/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((22380231657/250000000000) : ℝ) = (0.089520926628 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((485218221024854587055141/1000000000000000000000000) : ℚ) ∧ ((486419088692704805486339/1000000000000000000000000) : ℚ) ≤ (0.488881687 : ℚ) ∧
      ((486419088692704805486339/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((22380231657/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6947573376865103/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((485218221024854587055141/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((22380231657/250000000000) : ℚ) = (0.089520926628 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((485218221024854587055141/1000000000000000000000000) : ℝ) ∧ ((486419088692704805486339/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
      ((486419088692704805486339/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22380231657/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6947573376865103/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((485218221024854587055141/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((22380231657/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨21,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy21 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨21,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨21,by decide⟩).lower) ≤ (scalarRow12100.table ⟨21,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((485218221024854587055141/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((485218221024854587055141/1000000000000000000000000) : ℝ)) ≤ ((6947573376865103/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy21 (n := 12100) (by norm_num)
    (q := 1 - ((485218221024854587055141/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell22 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨22,by decide⟩).lower ∧ (scalarRow12100.table ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (scalarRow12100.table ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((243209544346352402743169/500000000000000000000000) : ℝ) ∧ ((15238123636267344497423/31250000000000000000000) : ℝ) ≤ (0.488881687 : ℝ) ∧
      ((15238123636267344497423/31250000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22380231657/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6941797888226199/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((243209544346352402743169/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((22380231657/250000000000) : ℝ) = (0.089520926628 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((243209544346352402743169/500000000000000000000000) : ℚ) ∧ ((15238123636267344497423/31250000000000000000000) : ℚ) ≤ (0.488881687 : ℚ) ∧
      ((15238123636267344497423/31250000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((22380231657/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6941797888226199/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((243209544346352402743169/500000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((22380231657/250000000000) : ℚ) = (0.089520926628 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((243209544346352402743169/500000000000000000000000) : ℝ) ∧ ((15238123636267344497423/31250000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
      ((15238123636267344497423/31250000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22380231657/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6941797888226199/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((243209544346352402743169/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((22380231657/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨22,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy22 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨22,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨22,by decide⟩).lower) ≤ (scalarRow12100.table ⟨22,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((243209544346352402743169/500000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((243209544346352402743169/500000000000000000000000) : ℝ)) ≤ ((6941797888226199/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy22 (n := 12100) (by norm_num)
    (q := 1 - ((243209544346352402743169/500000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell23 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨23,by decide⟩).lower ∧ (scalarRow12100.table ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (scalarRow12100.table ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((97523991272111004783507/200000000000000000000000) : ℝ) ∧ ((244410412014202621174367/500000000000000000000000) : ℝ) ≤ (0.488881687 : ℝ) ∧
      ((244410412014202621174367/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22380231657/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1387205775634817/2000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((97523991272111004783507/200000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((22380231657/250000000000) : ℝ) = (0.089520926628 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((97523991272111004783507/200000000000000000000000) : ℚ) ∧ ((244410412014202621174367/500000000000000000000000) : ℚ) ≤ (0.488881687 : ℚ) ∧
      ((244410412014202621174367/500000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((22380231657/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((1387205775634817/2000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((97523991272111004783507/200000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((22380231657/250000000000) : ℚ) = (0.089520926628 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((97523991272111004783507/200000000000000000000000) : ℝ) ∧ ((244410412014202621174367/500000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
      ((244410412014202621174367/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22380231657/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1387205775634817/2000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((97523991272111004783507/200000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((22380231657/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨23,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy23 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨23,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨23,by decide⟩).lower) ≤ (scalarRow12100.table ⟨23,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((97523991272111004783507/200000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((97523991272111004783507/200000000000000000000000) : ℝ)) ≤ ((1387205775634817/2000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy23 (n := 12100) (by norm_num)
    (q := 1 - ((97523991272111004783507/200000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell24 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨24,by decide⟩).lower ∧ (scalarRow12100.table ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (scalarRow12100.table ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((488820824028405242348733/1000000000000000000000000) : ℝ) ∧ ((490021691696255460779931/1000000000000000000000000) : ℝ) ≤ (0.496102109 : ℝ) ∧
      ((490021691696255460779931/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22630197467/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((277210653443457/400000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((488820824028405242348733/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((22630197467/250000000000) : ℝ) = (0.090520789868 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((488820824028405242348733/1000000000000000000000000) : ℚ) ∧ ((490021691696255460779931/1000000000000000000000000) : ℚ) ≤ (0.496102109 : ℚ) ∧
      ((490021691696255460779931/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((22630197467/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((277210653443457/400000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((488820824028405242348733/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((22630197467/250000000000) : ℚ) = (0.090520789868 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((488820824028405242348733/1000000000000000000000000) : ℝ) ∧ ((490021691696255460779931/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
      ((490021691696255460779931/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22630197467/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((277210653443457/400000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((488820824028405242348733/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((22630197467/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨24,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy24 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨24,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨24,by decide⟩).lower) ≤ (scalarRow12100.table ⟨24,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((488820824028405242348733/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((488820824028405242348733/1000000000000000000000000) : ℝ)) ≤ ((277210653443457/400000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy24 (n := 12100) (by norm_num)
    (q := 1 - ((488820824028405242348733/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell25 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨25,by decide⟩).lower ∧ (scalarRow12100.table ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (scalarRow12100.table ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((49002169169625546077993/100000000000000000000000) : ℝ) ∧ ((61402819920513209901391/125000000000000000000000) : ℝ) ≤ (0.496102109 : ℝ) ∧
      ((61402819920513209901391/125000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22630197467/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6924510251382257/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((49002169169625546077993/100000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((22630197467/250000000000) : ℝ) = (0.090520789868 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((49002169169625546077993/100000000000000000000000) : ℚ) ∧ ((61402819920513209901391/125000000000000000000000) : ℚ) ≤ (0.496102109 : ℚ) ∧
      ((61402819920513209901391/125000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((22630197467/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6924510251382257/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((49002169169625546077993/100000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((22630197467/250000000000) : ℚ) = (0.090520789868 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((49002169169625546077993/100000000000000000000000) : ℝ) ∧ ((61402819920513209901391/125000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
      ((61402819920513209901391/125000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22630197467/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6924510251382257/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((49002169169625546077993/100000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((22630197467/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨25,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy25 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨25,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨25,by decide⟩).lower) ≤ (scalarRow12100.table ⟨25,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((49002169169625546077993/100000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((49002169169625546077993/100000000000000000000000) : ℝ)) ≤ ((6924510251382257/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy25 (n := 12100) (by norm_num)
    (q := 1 - ((49002169169625546077993/100000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell26 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨26,by decide⟩).lower ∧ (scalarRow12100.table ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (scalarRow12100.table ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((491222559364105679211127/1000000000000000000000000) : ℝ) ∧ ((19696937081278235905693/40000000000000000000000) : ℝ) ≤ (0.496102109 : ℝ) ∧
      ((19696937081278235905693/40000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22630197467/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6918760613521743/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((491222559364105679211127/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((22630197467/250000000000) : ℝ) = (0.090520789868 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((491222559364105679211127/1000000000000000000000000) : ℚ) ∧ ((19696937081278235905693/40000000000000000000000) : ℚ) ≤ (0.496102109 : ℚ) ∧
      ((19696937081278235905693/40000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((22630197467/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6918760613521743/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((491222559364105679211127/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((22630197467/250000000000) : ℚ) = (0.090520789868 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((491222559364105679211127/1000000000000000000000000) : ℝ) ∧ ((19696937081278235905693/40000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
      ((19696937081278235905693/40000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22630197467/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6918760613521743/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((491222559364105679211127/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((22630197467/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨26,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy26 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨26,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨26,by decide⟩).lower) ≤ (scalarRow12100.table ⟨26,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((491222559364105679211127/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((491222559364105679211127/1000000000000000000000000) : ℝ)) ≤ ((6918760613521743/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy26 (n := 12100) (by norm_num)
    (q := 1 - ((491222559364105679211127/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell27 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨27,by decide⟩).lower ∧ (scalarRow12100.table ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (scalarRow12100.table ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((123105856757988974410581/250000000000000000000000) : ℝ) ∧ ((493624294699806116073523/1000000000000000000000000) : ℝ) ≤ (0.496102109 : ℝ) ∧
      ((493624294699806116073523/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22630197467/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1728254353001479/2500000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((123105856757988974410581/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((22630197467/250000000000) : ℝ) = (0.090520789868 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((123105856757988974410581/250000000000000000000000) : ℚ) ∧ ((493624294699806116073523/1000000000000000000000000) : ℚ) ≤ (0.496102109 : ℚ) ∧
      ((493624294699806116073523/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((22630197467/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((1728254353001479/2500000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((123105856757988974410581/250000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((22630197467/250000000000) : ℚ) = (0.090520789868 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((123105856757988974410581/250000000000000000000000) : ℝ) ∧ ((493624294699806116073523/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
      ((493624294699806116073523/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22630197467/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1728254353001479/2500000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((123105856757988974410581/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((22630197467/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨27,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy27 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨27,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨27,by decide⟩).lower) ≤ (scalarRow12100.table ⟨27,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((123105856757988974410581/250000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((123105856757988974410581/250000000000000000000000) : ℝ)) ≤ ((1728254353001479/2500000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy27 (n := 12100) (by norm_num)
    (q := 1 - ((123105856757988974410581/250000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell28 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨28,by decide⟩).lower ∧ (scalarRow12100.table ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (scalarRow12100.table ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((246812147349903058036761/500000000000000000000000) : ℝ) ∧ ((6185314529595704181309/12500000000000000000000) : ℝ) ≤ (0.496102109 : ℝ) ∧
      ((6185314529595704181309/12500000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22630197467/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6907280636376429/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((246812147349903058036761/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((22630197467/250000000000) : ℝ) = (0.090520789868 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((246812147349903058036761/500000000000000000000000) : ℚ) ∧ ((6185314529595704181309/12500000000000000000000) : ℚ) ≤ (0.496102109 : ℚ) ∧
      ((6185314529595704181309/12500000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((22630197467/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6907280636376429/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((246812147349903058036761/500000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((22630197467/250000000000) : ℚ) = (0.090520789868 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((246812147349903058036761/500000000000000000000000) : ℝ) ∧ ((6185314529595704181309/12500000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
      ((6185314529595704181309/12500000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22630197467/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6907280636376429/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((246812147349903058036761/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((22630197467/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨28,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy28 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨28,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨28,by decide⟩).lower) ≤ (scalarRow12100.table ⟨28,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((246812147349903058036761/500000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((246812147349903058036761/500000000000000000000000) : ℝ)) ≤ ((6907280636376429/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy28 (n := 12100) (by norm_num)
    (q := 1 - ((246812147349903058036761/500000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell29 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨29,by decide⟩).lower ∧ (scalarRow12100.table ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (scalarRow12100.table ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((494825162367656334504719/1000000000000000000000000) : ℝ) ∧ ((496026030035506552935917/1000000000000000000000000) : ℝ) ≤ (0.496102109 : ℝ) ∧
      ((496026030035506552935917/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22630197467/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1725387569053827/2500000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((494825162367656334504719/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((22630197467/250000000000) : ℝ) = (0.090520789868 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((494825162367656334504719/1000000000000000000000000) : ℚ) ∧ ((496026030035506552935917/1000000000000000000000000) : ℚ) ≤ (0.496102109 : ℚ) ∧
      ((496026030035506552935917/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((22630197467/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((1725387569053827/2500000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((494825162367656334504719/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((22630197467/250000000000) : ℚ) = (0.090520789868 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((494825162367656334504719/1000000000000000000000000) : ℝ) ∧ ((496026030035506552935917/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
      ((496026030035506552935917/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22630197467/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1725387569053827/2500000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((494825162367656334504719/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((22630197467/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨29,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy29 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨29,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨29,by decide⟩).lower) ≤ (scalarRow12100.table ⟨29,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((494825162367656334504719/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((494825162367656334504719/1000000000000000000000000) : ℝ)) ≤ ((1725387569053827/2500000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy29 (n := 12100) (by norm_num)
    (q := 1 - ((494825162367656334504719/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell30 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨30,by decide⟩).lower ∧ (scalarRow12100.table ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (scalarRow12100.table ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((124006507508876638233979/250000000000000000000000) : ℝ) ∧ ((248613448851678385683557/500000000000000000000000) : ℝ) ≤ (0.503322531 : ℝ) ∧
      ((248613448851678385683557/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((45766243273/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6895826321144703/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((124006507508876638233979/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((45766243273/500000000000) : ℝ) = (0.091532486546 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((124006507508876638233979/250000000000000000000000) : ℚ) ∧ ((248613448851678385683557/500000000000000000000000) : ℚ) ≤ (0.503322531 : ℚ) ∧
      ((248613448851678385683557/500000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((45766243273/500000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6895826321144703/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((124006507508876638233979/250000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((45766243273/500000000000) : ℚ) = (0.091532486546 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((124006507508876638233979/250000000000000000000000) : ℝ) ∧ ((248613448851678385683557/500000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
      ((248613448851678385683557/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((45766243273/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6895826321144703/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((124006507508876638233979/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((45766243273/500000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨30,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy30 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨30,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨30,by decide⟩).lower) ≤ (scalarRow12100.table ⟨30,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((124006507508876638233979/250000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((124006507508876638233979/250000000000000000000000) : ℝ)) ≤ ((6895826321144703/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy30 (n := 12100) (by norm_num)
    (q := 1 - ((124006507508876638233979/250000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell31 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨31,by decide⟩).lower ∧ (scalarRow12100.table ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (scalarRow12100.table ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((497226897703356771367113/1000000000000000000000000) : ℝ) ∧ ((498427765371206989798311/1000000000000000000000000) : ℝ) ≤ (0.503322531 : ℝ) ∧
      ((498427765371206989798311/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((45766243273/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6890108760826651/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((497226897703356771367113/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((45766243273/500000000000) : ℝ) = (0.091532486546 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((497226897703356771367113/1000000000000000000000000) : ℚ) ∧ ((498427765371206989798311/1000000000000000000000000) : ℚ) ≤ (0.503322531 : ℚ) ∧
      ((498427765371206989798311/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((45766243273/500000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6890108760826651/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((497226897703356771367113/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((45766243273/500000000000) : ℚ) = (0.091532486546 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((497226897703356771367113/1000000000000000000000000) : ℝ) ∧ ((498427765371206989798311/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
      ((498427765371206989798311/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((45766243273/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6890108760826651/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((497226897703356771367113/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((45766243273/500000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨31,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy31 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨31,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨31,by decide⟩).lower) ≤ (scalarRow12100.table ⟨31,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((497226897703356771367113/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((497226897703356771367113/1000000000000000000000000) : ℝ)) ≤ ((6890108760826651/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy31 (n := 12100) (by norm_num)
    (q := 1 - ((497226897703356771367113/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell32 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨32,by decide⟩).lower ∧ (scalarRow12100.table ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (scalarRow12100.table ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((49842776537120698979831/100000000000000000000000) : ℝ) ∧ ((499628633039057208229509/1000000000000000000000000) : ℝ) ≤ (0.503322531 : ℝ) ∧
      ((499628633039057208229509/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((45766243273/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1721099396240707/2500000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((49842776537120698979831/100000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((45766243273/500000000000) : ℝ) = (0.091532486546 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((49842776537120698979831/100000000000000000000000) : ℚ) ∧ ((499628633039057208229509/1000000000000000000000000) : ℚ) ≤ (0.503322531 : ℚ) ∧
      ((499628633039057208229509/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((45766243273/500000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((1721099396240707/2500000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((49842776537120698979831/100000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((45766243273/500000000000) : ℚ) = (0.091532486546 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((49842776537120698979831/100000000000000000000000) : ℝ) ∧ ((499628633039057208229509/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
      ((499628633039057208229509/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((45766243273/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1721099396240707/2500000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((49842776537120698979831/100000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((45766243273/500000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨32,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy32 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨32,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨32,by decide⟩).lower) ≤ (scalarRow12100.table ⟨32,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((49842776537120698979831/100000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((49842776537120698979831/100000000000000000000000) : ℝ)) ≤ ((1721099396240707/2500000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy32 (n := 12100) (by norm_num)
    (q := 1 - ((49842776537120698979831/100000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell33 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨33,by decide⟩).lower ∧ (scalarRow12100.table ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (scalarRow12100.table ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((124907158259764302057377/250000000000000000000000) : ℝ) ∧ ((250414750353453713330353/500000000000000000000000) : ℝ) ≤ (0.503322531 : ℝ) ∧
      ((250414750353453713330353/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((45766243273/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6878692783294313/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((124907158259764302057377/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((45766243273/500000000000) : ℝ) = (0.091532486546 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((124907158259764302057377/250000000000000000000000) : ℚ) ∧ ((250414750353453713330353/500000000000000000000000) : ℚ) ≤ (0.503322531 : ℚ) ∧
      ((250414750353453713330353/500000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((45766243273/500000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6878692783294313/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((124907158259764302057377/250000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((45766243273/500000000000) : ℚ) = (0.091532486546 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((124907158259764302057377/250000000000000000000000) : ℝ) ∧ ((250414750353453713330353/500000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
      ((250414750353453713330353/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((45766243273/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6878692783294313/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((124907158259764302057377/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((45766243273/500000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨33,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy33 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨33,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨33,by decide⟩).lower) ≤ (scalarRow12100.table ⟨33,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((124907158259764302057377/250000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((124907158259764302057377/250000000000000000000000) : ℝ)) ≤ ((6878692783294313/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy33 (n := 12100) (by norm_num)
    (q := 1 - ((124907158259764302057377/250000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell34 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨34,by decide⟩).lower ∧ (scalarRow12100.table ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (scalarRow12100.table ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((100165900141381485332141/200000000000000000000000) : ℝ) ∧ ((502030368374757645091903/1000000000000000000000000) : ℝ) ≤ (0.503322531 : ℝ) ∧
      ((502030368374757645091903/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((45766243273/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6872994345601349/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((100165900141381485332141/200000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((45766243273/500000000000) : ℝ) = (0.091532486546 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((100165900141381485332141/200000000000000000000000) : ℚ) ∧ ((502030368374757645091903/1000000000000000000000000) : ℚ) ≤ (0.503322531 : ℚ) ∧
      ((502030368374757645091903/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((45766243273/500000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6872994345601349/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((100165900141381485332141/200000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((45766243273/500000000000) : ℚ) = (0.091532486546 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((100165900141381485332141/200000000000000000000000) : ℝ) ∧ ((502030368374757645091903/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
      ((502030368374757645091903/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((45766243273/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6872994345601349/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((100165900141381485332141/200000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((45766243273/500000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨34,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy34 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨34,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨34,by decide⟩).lower) ≤ (scalarRow12100.table ⟨34,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((100165900141381485332141/200000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((100165900141381485332141/200000000000000000000000) : ℝ)) ≤ ((6872994345601349/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy34 (n := 12100) (by norm_num)
    (q := 1 - ((100165900141381485332141/200000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell35 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨35,by decide⟩).lower ∧ (scalarRow12100.table ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (scalarRow12100.table ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((251015184187378822545951/500000000000000000000000) : ℝ) ∧ ((5032312360426078635231/10000000000000000000000) : ℝ) ≤ (0.503322531 : ℝ) ∧
      ((5032312360426078635231/10000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((45766243273/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((686730226170311/1000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((251015184187378822545951/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((45766243273/500000000000) : ℝ) = (0.091532486546 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((251015184187378822545951/500000000000000000000000) : ℚ) ∧ ((5032312360426078635231/10000000000000000000000) : ℚ) ≤ (0.503322531 : ℚ) ∧
      ((5032312360426078635231/10000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((45766243273/500000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((686730226170311/1000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((251015184187378822545951/500000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((45766243273/500000000000) : ℚ) = (0.091532486546 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((251015184187378822545951/500000000000000000000000) : ℝ) ∧ ((5032312360426078635231/10000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
      ((5032312360426078635231/10000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((45766243273/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((686730226170311/1000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((251015184187378822545951/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((45766243273/500000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨35,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy35 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨35,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨35,by decide⟩).lower) ≤ (scalarRow12100.table ⟨35,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((251015184187378822545951/500000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((251015184187378822545951/500000000000000000000000) : ℝ)) ≤ ((686730226170311/1000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy35 (n := 12100) (by norm_num)
    (q := 1 - ((251015184187378822545951/500000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell36 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨36,by decide⟩).lower ∧ (scalarRow12100.table ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (scalarRow12100.table ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((503231236042607863523099/1000000000000000000000000) : ℝ) ∧ ((252216051855229040977149/500000000000000000000000) : ℝ) ≤ (0.510542952 : ℝ) ∧
      ((252216051855229040977149/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((23140049089/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6861616521457463/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((503231236042607863523099/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((23140049089/250000000000) : ℝ) = (0.092560196356 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((503231236042607863523099/1000000000000000000000000) : ℚ) ∧ ((252216051855229040977149/500000000000000000000000) : ℚ) ≤ (0.510542952 : ℚ) ∧
      ((252216051855229040977149/500000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((23140049089/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6861616521457463/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((503231236042607863523099/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((23140049089/250000000000) : ℚ) = (0.092560196356 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((503231236042607863523099/1000000000000000000000000) : ℝ) ∧ ((252216051855229040977149/500000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
      ((252216051855229040977149/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((23140049089/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6861616521457463/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((503231236042607863523099/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((23140049089/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨36,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy36 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨36,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨36,by decide⟩).lower) ≤ (scalarRow12100.table ⟨36,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((503231236042607863523099/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((503231236042607863523099/1000000000000000000000000) : ℝ)) ≤ ((6861616521457463/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy36 (n := 12100) (by norm_num)
    (q := 1 - ((503231236042607863523099/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell37 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨37,by decide⟩).lower ∧ (scalarRow12100.table ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (scalarRow12100.table ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((504432103710458081954297/1000000000000000000000000) : ℝ) ∧ ((101126594275661660077099/200000000000000000000000) : ℝ) ≤ (0.510542952 : ℝ) ∧
      ((101126594275661660077099/200000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((23140049089/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6855937114760743/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((504432103710458081954297/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((23140049089/250000000000) : ℝ) = (0.092560196356 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((504432103710458081954297/1000000000000000000000000) : ℚ) ∧ ((101126594275661660077099/200000000000000000000000) : ℚ) ≤ (0.510542952 : ℚ) ∧
      ((101126594275661660077099/200000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((23140049089/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6855937114760743/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((504432103710458081954297/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((23140049089/250000000000) : ℚ) = (0.092560196356 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((504432103710458081954297/1000000000000000000000000) : ℝ) ∧ ((101126594275661660077099/200000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
      ((101126594275661660077099/200000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((23140049089/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6855937114760743/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((504432103710458081954297/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((23140049089/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨37,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy37 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨37,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨37,by decide⟩).lower) ≤ (scalarRow12100.table ⟨37,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((504432103710458081954297/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((504432103710458081954297/1000000000000000000000000) : ℝ)) ≤ ((6855937114760743/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy37 (n := 12100) (by norm_num)
    (q := 1 - ((504432103710458081954297/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell38 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨38,by decide⟩).lower ∧ (scalarRow12100.table ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (scalarRow12100.table ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((252816485689154150192747/500000000000000000000000) : ℝ) ∧ ((126708459761539629704173/250000000000000000000000) : ℝ) ≤ (0.510542952 : ℝ) ∧
      ((126708459761539629704173/250000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((23140049089/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3425132015773759/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((252816485689154150192747/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((23140049089/250000000000) : ℝ) = (0.092560196356 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((252816485689154150192747/500000000000000000000000) : ℚ) ∧ ((126708459761539629704173/250000000000000000000000) : ℚ) ≤ (0.510542952 : ℚ) ∧
      ((126708459761539629704173/250000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((23140049089/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((3425132015773759/5000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((252816485689154150192747/500000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((23140049089/250000000000) : ℚ) = (0.092560196356 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((252816485689154150192747/500000000000000000000000) : ℝ) ∧ ((126708459761539629704173/250000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
      ((126708459761539629704173/250000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((23140049089/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3425132015773759/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((252816485689154150192747/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((23140049089/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨38,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy38 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨38,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨38,by decide⟩).lower) ≤ (scalarRow12100.table ⟨38,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((252816485689154150192747/500000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((252816485689154150192747/500000000000000000000000) : ℝ)) ≤ ((3425132015773759/5000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy38 (n := 12100) (by norm_num)
    (q := 1 - ((252816485689154150192747/500000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell39 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨39,by decide⟩).lower ∧ (scalarRow12100.table ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (scalarRow12100.table ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((506833839046158518816691/1000000000000000000000000) : ℝ) ∧ ((508034706714008737247889/1000000000000000000000000) : ℝ) ≤ (0.510542952 : ℝ) ∧
      ((508034706714008737247889/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((23140049089/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6844597261790363/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((506833839046158518816691/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((23140049089/250000000000) : ℝ) = (0.092560196356 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((506833839046158518816691/1000000000000000000000000) : ℚ) ∧ ((508034706714008737247889/1000000000000000000000000) : ℚ) ≤ (0.510542952 : ℚ) ∧
      ((508034706714008737247889/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((23140049089/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6844597261790363/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((506833839046158518816691/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((23140049089/250000000000) : ℚ) = (0.092560196356 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((506833839046158518816691/1000000000000000000000000) : ℝ) ∧ ((508034706714008737247889/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
      ((508034706714008737247889/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((23140049089/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6844597261790363/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((506833839046158518816691/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((23140049089/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨39,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy39 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨39,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨39,by decide⟩).lower) ≤ (scalarRow12100.table ⟨39,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((506833839046158518816691/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((506833839046158518816691/1000000000000000000000000) : ℝ)) ≤ ((6844597261790363/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy39 (n := 12100) (by norm_num)
    (q := 1 - ((506833839046158518816691/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell40 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨40,by decide⟩).lower ∧ (scalarRow12100.table ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (scalarRow12100.table ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((31752169169625546077993/62500000000000000000000) : ℝ) ∧ ((254617787190929477839543/500000000000000000000000) : ℝ) ≤ (0.510542952 : ℝ) ∧
      ((254617787190929477839543/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((23140049089/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6838936795499637/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((31752169169625546077993/62500000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((23140049089/250000000000) : ℝ) = (0.092560196356 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((31752169169625546077993/62500000000000000000000) : ℚ) ∧ ((254617787190929477839543/500000000000000000000000) : ℚ) ≤ (0.510542952 : ℚ) ∧
      ((254617787190929477839543/500000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((23140049089/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6838936795499637/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((31752169169625546077993/62500000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((23140049089/250000000000) : ℚ) = (0.092560196356 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((31752169169625546077993/62500000000000000000000) : ℝ) ∧ ((254617787190929477839543/500000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
      ((254617787190929477839543/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((23140049089/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6838936795499637/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((31752169169625546077993/62500000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((23140049089/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨40,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy40 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨40,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨40,by decide⟩).lower) ≤ (scalarRow12100.table ⟨40,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((31752169169625546077993/62500000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((31752169169625546077993/62500000000000000000000) : ℝ)) ≤ ((6838936795499637/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy40 (n := 12100) (by norm_num)
    (q := 1 - ((31752169169625546077993/62500000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell41 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨41,by decide⟩).lower ∧ (scalarRow12100.table ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (scalarRow12100.table ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((101847114876371791135817/200000000000000000000000) : ℝ) ∧ ((127609110512427293527571/250000000000000000000000) : ℝ) ≤ (0.510542952 : ℝ) ∧
      ((127609110512427293527571/250000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((23140049089/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((854160327840407/1250000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((101847114876371791135817/200000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((23140049089/250000000000) : ℝ) = (0.092560196356 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((101847114876371791135817/200000000000000000000000) : ℚ) ∧ ((127609110512427293527571/250000000000000000000000) : ℚ) ≤ (0.510542952 : ℚ) ∧
      ((127609110512427293527571/250000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((23140049089/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((854160327840407/1250000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((101847114876371791135817/200000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((23140049089/250000000000) : ℚ) = (0.092560196356 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((101847114876371791135817/200000000000000000000000) : ℝ) ∧ ((127609110512427293527571/250000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
      ((127609110512427293527571/250000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((23140049089/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((854160327840407/1250000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((101847114876371791135817/200000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((23140049089/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨41,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy41 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨41,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨41,by decide⟩).lower) ≤ (scalarRow12100.table ⟨41,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((101847114876371791135817/200000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((101847114876371791135817/200000000000000000000000) : ℝ)) ≤ ((854160327840407/1250000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy41 (n := 12100) (by norm_num)
    (q := 1 - ((101847114876371791135817/200000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell42 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨42,by decide⟩).lower ∧ (scalarRow12100.table ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (scalarRow12100.table ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((510436442049709174110283/1000000000000000000000000) : ℝ) ∧ ((511637309717559392541481/1000000000000000000000000) : ℝ) ≤ (0.517763374 : ℝ) ∧
      ((511637309717559392541481/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((11701101533/125000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6827634733546473/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((510436442049709174110283/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((11701101533/125000000000) : ℝ) = (0.093608812264 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((510436442049709174110283/1000000000000000000000000) : ℚ) ∧ ((511637309717559392541481/1000000000000000000000000) : ℚ) ≤ (0.517763374 : ℚ) ∧
      ((511637309717559392541481/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((11701101533/125000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6827634733546473/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((510436442049709174110283/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((11701101533/125000000000) : ℚ) = (0.093608812264 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((510436442049709174110283/1000000000000000000000000) : ℝ) ∧ ((511637309717559392541481/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
      ((511637309717559392541481/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((11701101533/125000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6827634733546473/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((510436442049709174110283/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((11701101533/125000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨42,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy42 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨42,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨42,by decide⟩).lower) ≤ (scalarRow12100.table ⟨42,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((510436442049709174110283/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((510436442049709174110283/1000000000000000000000000) : ℝ)) ≤ ((6827634733546473/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy42 (n := 12100) (by norm_num)
    (q := 1 - ((510436442049709174110283/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell43 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨43,by decide⟩).lower ∧ (scalarRow12100.table ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (scalarRow12100.table ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((12790932742938984813537/25000000000000000000000) : ℝ) ∧ ((256419088692704805486339/500000000000000000000000) : ℝ) ≤ (0.517763374 : ℝ) ∧
      ((256419088692704805486339/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((11701101533/125000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3410996559045829/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((12790932742938984813537/25000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((11701101533/125000000000) : ℝ) = (0.093608812264 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((12790932742938984813537/25000000000000000000000) : ℚ) ∧ ((256419088692704805486339/500000000000000000000000) : ℚ) ≤ (0.517763374 : ℚ) ∧
      ((256419088692704805486339/500000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((11701101533/125000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((3410996559045829/5000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((12790932742938984813537/25000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((11701101533/125000000000) : ℚ) = (0.093608812264 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((12790932742938984813537/25000000000000000000000) : ℝ) ∧ ((256419088692704805486339/500000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
      ((256419088692704805486339/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((11701101533/125000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3410996559045829/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((12790932742938984813537/25000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((11701101533/125000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨43,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy43 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨43,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨43,by decide⟩).lower) ≤ (scalarRow12100.table ⟨43,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((12790932742938984813537/25000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((12790932742938984813537/25000000000000000000000) : ℝ)) ≤ ((3410996559045829/5000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy43 (n := 12100) (by norm_num)
    (q := 1 - ((12790932742938984813537/25000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell44 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨44,by decide⟩).lower ∧ (scalarRow12100.table ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (scalarRow12100.table ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((512838177385409610972677/1000000000000000000000000) : ℝ) ∧ ((4112312360426078635231/8000000000000000000000) : ℝ) ≤ (0.517763374 : ℝ) ∧
      ((4112312360426078635231/8000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((11701101533/125000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3408178883259039/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((512838177385409610972677/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((11701101533/125000000000) : ℝ) = (0.093608812264 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((512838177385409610972677/1000000000000000000000000) : ℚ) ∧ ((4112312360426078635231/8000000000000000000000) : ℚ) ≤ (0.517763374 : ℚ) ∧
      ((4112312360426078635231/8000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((11701101533/125000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((3408178883259039/5000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((512838177385409610972677/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((11701101533/125000000000) : ℚ) = (0.093608812264 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((512838177385409610972677/1000000000000000000000000) : ℝ) ∧ ((4112312360426078635231/8000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
      ((4112312360426078635231/8000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((11701101533/125000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3408178883259039/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((512838177385409610972677/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((11701101533/125000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨44,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy44 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨44,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨44,by decide⟩).lower) ≤ (scalarRow12100.table ⟨44,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((512838177385409610972677/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((512838177385409610972677/1000000000000000000000000) : ℝ)) ≤ ((3408178883259039/5000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy44 (n := 12100) (by norm_num)
    (q := 1 - ((512838177385409610972677/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell45 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨45,by decide⟩).lower ∧ (scalarRow12100.table ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (scalarRow12100.table ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((257019522526629914701937/500000000000000000000000) : ℝ) ∧ ((8050623636267344497423/15625000000000000000000) : ℝ) ≤ (0.517763374 : ℝ) ∧
      ((8050623636267344497423/15625000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((11701101533/125000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6810728669021683/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((257019522526629914701937/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((11701101533/125000000000) : ℝ) = (0.093608812264 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((257019522526629914701937/500000000000000000000000) : ℚ) ∧ ((8050623636267344497423/15625000000000000000000) : ℚ) ≤ (0.517763374 : ℚ) ∧
      ((8050623636267344497423/15625000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((11701101533/125000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6810728669021683/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((257019522526629914701937/500000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((11701101533/125000000000) : ℚ) = (0.093608812264 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((257019522526629914701937/500000000000000000000000) : ℝ) ∧ ((8050623636267344497423/15625000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
      ((8050623636267344497423/15625000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((11701101533/125000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6810728669021683/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((257019522526629914701937/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((11701101533/125000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨45,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy45 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨45,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨45,by decide⟩).lower) ≤ (scalarRow12100.table ⟨45,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((257019522526629914701937/500000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((257019522526629914701937/500000000000000000000000) : ℝ)) ≤ ((6810728669021683/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy45 (n := 12100) (by norm_num)
    (q := 1 - ((257019522526629914701937/500000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell46 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨46,by decide⟩).lower ∧ (scalarRow12100.table ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (scalarRow12100.table ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((515239912721110047835071/1000000000000000000000000) : ℝ) ∧ ((51644078038896026626627/100000000000000000000000) : ℝ) ≤ (0.517763374 : ℝ) ∧
      ((51644078038896026626627/100000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((11701101533/125000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1701276453958723/2500000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((515239912721110047835071/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((11701101533/125000000000) : ℝ) = (0.093608812264 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((515239912721110047835071/1000000000000000000000000) : ℚ) ∧ ((51644078038896026626627/100000000000000000000000) : ℚ) ≤ (0.517763374 : ℚ) ∧
      ((51644078038896026626627/100000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((11701101533/125000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((1701276453958723/2500000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((515239912721110047835071/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((11701101533/125000000000) : ℚ) = (0.093608812264 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((515239912721110047835071/1000000000000000000000000) : ℝ) ∧ ((51644078038896026626627/100000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
      ((51644078038896026626627/100000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((11701101533/125000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1701276453958723/2500000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((515239912721110047835071/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((11701101533/125000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨46,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy46 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨46,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨46,by decide⟩).lower) ≤ (scalarRow12100.table ⟨46,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((515239912721110047835071/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((515239912721110047835071/1000000000000000000000000) : ℝ)) ≤ ((1701276453958723/2500000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy46 (n := 12100) (by norm_num)
    (q := 1 - ((515239912721110047835071/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell47 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨47,by decide⟩).lower ∧ (scalarRow12100.table ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (scalarRow12100.table ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((516440780388960266266269/1000000000000000000000000) : ℝ) ∧ ((517641648056810484697467/1000000000000000000000000) : ℝ) ≤ (0.517763374 : ℝ) ∧
      ((517641648056810484697467/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((11701101533/125000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3399744598613189/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((516440780388960266266269/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((11701101533/125000000000) : ℝ) = (0.093608812264 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((516440780388960266266269/1000000000000000000000000) : ℚ) ∧ ((517641648056810484697467/1000000000000000000000000) : ℚ) ≤ (0.517763374 : ℚ) ∧
      ((517641648056810484697467/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((11701101533/125000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((3399744598613189/5000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((516440780388960266266269/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((11701101533/125000000000) : ℚ) = (0.093608812264 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((516440780388960266266269/1000000000000000000000000) : ℝ) ∧ ((517641648056810484697467/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
      ((517641648056810484697467/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((11701101533/125000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3399744598613189/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((516440780388960266266269/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((11701101533/125000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨47,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy47 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨47,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨47,by decide⟩).lower) ≤ (scalarRow12100.table ⟨47,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((516440780388960266266269/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((516440780388960266266269/1000000000000000000000000) : ℝ)) ≤ ((3399744598613189/5000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy47 (n := 12100) (by norm_num)
    (q := 1 - ((516440780388960266266269/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell48 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨48,by decide⟩).lower ∧ (scalarRow12100.table ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (scalarRow12100.table ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((258820824028405242348733/500000000000000000000000) : ℝ) ∧ ((64855314465582587891083/125000000000000000000000) : ℝ) ≤ (0.524983796 : ℝ) ∧
      ((64855314465582587891083/125000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((4734201261/50000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6793878803500857/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((258820824028405242348733/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((4734201261/50000000000) : ℝ) = (0.094684025220 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((258820824028405242348733/500000000000000000000000) : ℚ) ∧ ((64855314465582587891083/125000000000000000000000) : ℚ) ≤ (0.524983796 : ℚ) ∧
      ((64855314465582587891083/125000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((4734201261/50000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6793878803500857/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((258820824028405242348733/500000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((4734201261/50000000000) : ℚ) = (0.094684025220 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((258820824028405242348733/500000000000000000000000) : ℝ) ∧ ((64855314465582587891083/125000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
      ((64855314465582587891083/125000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((4734201261/50000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6793878803500857/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((258820824028405242348733/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((4734201261/50000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨48,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy48 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨48,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨48,by decide⟩).lower) ≤ (scalarRow12100.table ⟨48,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((258820824028405242348733/500000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((258820824028405242348733/500000000000000000000000) : ℝ)) ≤ ((6793878803500857/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy48 (n := 12100) (by norm_num)
    (q := 1 - ((258820824028405242348733/500000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell49 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨49,by decide⟩).lower ∧ (scalarRow12100.table ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (scalarRow12100.table ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((518842515724660703128663/1000000000000000000000000) : ℝ) ∧ ((520043383392510921559861/1000000000000000000000000) : ℝ) ≤ (0.524983796 : ℝ) ∧
      ((520043383392510921559861/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((4734201261/50000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6788274624998881/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((518842515724660703128663/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((4734201261/50000000000) : ℝ) = (0.094684025220 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((518842515724660703128663/1000000000000000000000000) : ℚ) ∧ ((520043383392510921559861/1000000000000000000000000) : ℚ) ≤ (0.524983796 : ℚ) ∧
      ((520043383392510921559861/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((4734201261/50000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6788274624998881/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((518842515724660703128663/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((4734201261/50000000000) : ℚ) = (0.094684025220 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((518842515724660703128663/1000000000000000000000000) : ℝ) ∧ ((520043383392510921559861/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
      ((520043383392510921559861/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((4734201261/50000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6788274624998881/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((518842515724660703128663/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((4734201261/50000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨49,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy49 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨49,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨49,by decide⟩).lower) ≤ (scalarRow12100.table ⟨49,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((518842515724660703128663/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((518842515724660703128663/1000000000000000000000000) : ℝ)) ≤ ((6788274624998881/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy49 (n := 12100) (by norm_num)
    (q := 1 - ((518842515724660703128663/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell50 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨50,by decide⟩).lower ∧ (scalarRow12100.table ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (scalarRow12100.table ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((26002169169625546077993/50000000000000000000000) : ℝ) ∧ ((521244251060361139991059/1000000000000000000000000) : ℝ) ≤ (0.524983796 : ℝ) ∧
      ((521244251060361139991059/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((4734201261/50000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6782676652096631/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((26002169169625546077993/50000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((4734201261/50000000000) : ℝ) = (0.094684025220 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((26002169169625546077993/50000000000000000000000) : ℚ) ∧ ((521244251060361139991059/1000000000000000000000000) : ℚ) ≤ (0.524983796 : ℚ) ∧
      ((521244251060361139991059/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((4734201261/50000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6782676652096631/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((26002169169625546077993/50000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((4734201261/50000000000) : ℚ) = (0.094684025220 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((26002169169625546077993/50000000000000000000000) : ℝ) ∧ ((521244251060361139991059/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
      ((521244251060361139991059/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((4734201261/50000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6782676652096631/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((26002169169625546077993/50000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((4734201261/50000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨50,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy50 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨50,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨50,by decide⟩).lower) ≤ (scalarRow12100.table ⟨50,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((26002169169625546077993/50000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((26002169169625546077993/50000000000000000000000) : ℝ)) ≤ ((6782676652096631/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy50 (n := 12100) (by norm_num)
    (q := 1 - ((26002169169625546077993/50000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell51 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨51,by decide⟩).lower ∧ (scalarRow12100.table ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (scalarRow12100.table ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((260622125530180569995529/500000000000000000000000) : ℝ) ∧ ((32652819920513209901391/62500000000000000000000) : ℝ) ≤ (0.524983796 : ℝ) ∧
      ((32652819920513209901391/62500000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((4734201261/50000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3388542437602853/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((260622125530180569995529/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((4734201261/50000000000) : ℝ) = (0.094684025220 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((260622125530180569995529/500000000000000000000000) : ℚ) ∧ ((32652819920513209901391/62500000000000000000000) : ℚ) ≤ (0.524983796 : ℚ) ∧
      ((32652819920513209901391/62500000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((4734201261/50000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((3388542437602853/5000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((260622125530180569995529/500000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((4734201261/50000000000) : ℚ) = (0.094684025220 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((260622125530180569995529/500000000000000000000000) : ℝ) ∧ ((32652819920513209901391/62500000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
      ((32652819920513209901391/62500000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((4734201261/50000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3388542437602853/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((260622125530180569995529/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((4734201261/50000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨51,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy51 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨51,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨51,by decide⟩).lower) ≤ (scalarRow12100.table ⟨51,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((260622125530180569995529/500000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((260622125530180569995529/500000000000000000000000) : ℝ)) ≤ ((3388542437602853/5000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy51 (n := 12100) (by norm_num)
    (q := 1 - ((260622125530180569995529/500000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell52 :
    (0.46 : ℝ) ≤ (scalarRow12100.table ⟨52,by decide⟩).lower ∧ (scalarRow12100.table ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (scalarRow12100.table ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((104489023745642271684451/200000000000000000000000) : ℝ) ∧ ((523645986396061576853453/1000000000000000000000000) : ℝ) ≤ (0.524983796 : ℝ) ∧
      ((523645986396061576853453/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((4734201261/50000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3385749642386463/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((104489023745642271684451/200000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((4734201261/50000000000) : ℝ) = (0.094684025220 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((104489023745642271684451/200000000000000000000000) : ℚ) ∧ ((523645986396061576853453/1000000000000000000000000) : ℚ) ≤ (0.524983796 : ℚ) ∧
      ((523645986396061576853453/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((4734201261/50000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((3385749642386463/5000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((104489023745642271684451/200000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((4734201261/50000000000) : ℚ) = (0.094684025220 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((104489023745642271684451/200000000000000000000000) : ℝ) ∧ ((523645986396061576853453/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
      ((523645986396061576853453/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((4734201261/50000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3385749642386463/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((104489023745642271684451/200000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((4734201261/50000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨52,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy52 :
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table ⟨52,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table ⟨52,by decide⟩).lower) ≤ (scalarRow12100.table ⟨52,by decide⟩).energy := by
  change energyRatio 12100 (gMinus 12100) (1 - ((104489023745642271684451/200000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - ((104489023745642271684451/200000000000000000000000) : ℝ)) ≤ ((3385749642386463/5000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy52 (n := 12100) (by norm_num)
    (q := 1 - ((104489023745642271684451/200000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (scalarRow12100.table i).lower ∧ (scalarRow12100.table i).upper ≤ groupTheta (centreGroup i) ∧
    (scalarRow12100.table i).upper ≤ (0.532 : ℝ) ∧ (scalarRow12100.table i).centre ≤ (0.1 : ℝ) ∧ (scalarRow12100.table i).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12100.table i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12100.table i).centre = pilotGroupCentre (centreGroup i) := by
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
    energyRatio 12100 (gMinus 12100) (1 - (scalarRow12100.table i).lower) ≤ 1 ∧
    energyUpper 12100 (gMinus 12100) (BstLean.Part211.gPlus 12100)
      (finiteEnergy 12100 12100 0.011) (1 - (scalarRow12100.table i).lower) ≤ (scalarRow12100.table i).energy := by
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

noncomputable def sourceNumerics12100 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part277.CellSourceNumericsP 12100 (scalarRow12100.table i) scalarRow12100.M scalarRow12100.H scalarRow12100.xi
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
      (r := (110.000000000000 : ℝ)) (F := (0.008771 : ℝ))
      (by norm_num) (by norm_num) pilot_finite_centre_upper (by norm_num)
      (fun θ hθ => by
        convert (BstLean.Part281.energy_lower_data (by norm_num : 11883 ≤ 12100)
          ⟨hθ.1,hθ.2.trans G.window.2⟩).1 using 1 <;> norm_num)
    energy_allowance := scalarRow12100.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12100]
    centre_nonneg := (scalarRow12100.certificate i).centre_nonneg
    centre_upper := hc
    MP_nonneg := by norm_num
    e0_pos := by norm_num
    operator := by
      intro c τ hτ
      exact (BstLean.Part277.operator_allowance_11883
        (by norm_num : 11883 ≤ 12100) c hτ).trans (by norm_num)
    lower := fun θ hθ => by
      convert (BstLean.Part281.energy_lower_data
        (by norm_num : 11883 ≤ 12100) ⟨hθ.1,hθ.2.trans G.window.2⟩).2 using 1 <;> norm_num
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part281.Dir11883.direction_budget_11883 (by norm_num : 11883 ≤ 12100)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12100])
    source_lower := hl
    source_upper := hu
    source_upper_one := hu532.trans (by norm_num)
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }
end BstLean.Part281.N12100
