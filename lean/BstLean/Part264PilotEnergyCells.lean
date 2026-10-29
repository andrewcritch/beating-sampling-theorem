import BstLean.Part264PilotEnergyUpper
import BstLean.Part263Coverage

/-! Actual upper energy certificates on all 43 source endpoints at 12226. -/
namespace BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12226 cell12226)
theorem pilot_upperEnergy10 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨10,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨10,by decide⟩).lower) ≤ (scalarRow12226.table ⟨10,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨10,by decide⟩).lower) ≤ 0.627899372017 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528005730870 : ℝ)) (s := (0.849240806938 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.629920817126 : ℝ) ≤ 0.699118008148 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629920817126 : ℝ)) (Q := (0.629920817126 : ℝ))
      (s := (0.776659361723 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨10,by decide⟩).lower)
    (U := (0.792659029167 : ℝ)) (R := (0.793225707067 : ℝ)) (Q2 := (0.629920817126 : ℝ)) (T := (0.836606630481 : ℝ))
    (B := (scalarRow12226.table ⟨10,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy11 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨11,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨11,by decide⟩).lower) ≤ (scalarRow12226.table ⟨11,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨11,by decide⟩).lower) ≤ 0.627086124859 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526806303957 : ℝ)) (s := (0.849985363469 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.629106065147 : ℝ) ≤ 0.698531432595 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629106065147 : ℝ)) (Q := (0.629106065147 : ℝ))
      (s := (0.777319470228 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨11,by decide⟩).lower)
    (U := (0.792145876314 : ℝ)) (R := (0.792712554214 : ℝ)) (Q2 := (0.629106065147 : ℝ)) (T := (0.836255591051 : ℝ))
    (B := (scalarRow12226.table ⟨11,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy12 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨12,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨12,by decide⟩).lower) ≤ (scalarRow12226.table ⟨12,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨12,by decide⟩).lower) ≤ 0.626273436202 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525606877044 : ℝ)) (s := (0.850727577315 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.628291872326 : ℝ) ≤ 0.697945547104 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628291872326 : ℝ)) (Q := (0.628291872326 : ℝ))
      (s := (0.777977713800 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨12,by decide⟩).lower)
    (U := (0.791632743578 : ℝ)) (R := (0.792199421478 : ℝ)) (Q2 := (0.628291872326 : ℝ)) (T := (0.835904817433 : ℝ))
    (B := (scalarRow12226.table ⟨12,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy13 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨13,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨13,by decide⟩).lower) ≤ (scalarRow12226.table ⟨13,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨13,by decide⟩).lower) ≤ 0.625461305378 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524407450131 : ℝ)) (s := (0.851467454603 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.627478237993 : ℝ) ≤ 0.697360350357 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627478237993 : ℝ)) (Q := (0.627478237993 : ℝ))
      (s := (0.778634099463 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨13,by decide⟩).lower)
    (U := (0.791119630575 : ℝ)) (R := (0.791686308475 : ℝ)) (Q2 := (0.627478237993 : ℝ)) (T := (0.835554309172 : ℝ))
    (B := (scalarRow12226.table ⟨13,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy14 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨14,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨14,by decide⟩).lower) ≤ (scalarRow12226.table ⟨14,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨14,by decide⟩).lower) ≤ 0.624649731718 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523208023218 : ℝ)) (s := (0.852205001418 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.626665161477 : ℝ) ≤ 0.696775841037 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626665161477 : ℝ)) (Q := (0.626665161477 : ℝ))
      (s := (0.779288634199 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨14,by decide⟩).lower)
    (U := (0.790606536920 : ℝ)) (R := (0.791173214820 : ℝ)) (Q2 := (0.626665161477 : ℝ)) (T := (0.835204065813 : ℝ))
    (B := (scalarRow12226.table ⟨14,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy15 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨15,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨15,by decide⟩).lower) ≤ (scalarRow12226.table ⟨15,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨15,by decide⟩).lower) ≤ 0.623838714558 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522008596305 : ℝ)) (s := (0.852940223805 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.625852642114 : ℝ) ≤ 0.696192017836 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625852642114 : ℝ)) (Q := (0.625852642114 : ℝ))
      (s := (0.779941324947 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨15,by decide⟩).lower)
    (U := (0.790093462231 : ℝ)) (R := (0.790660140131 : ℝ)) (Q2 := (0.625852642114 : ℝ)) (T := (0.834854086906 : ℝ))
    (B := (scalarRow12226.table ⟨15,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy16 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨16,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨16,by decide⟩).lower) ≤ (scalarRow12226.table ⟨16,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨16,by decide⟩).lower) ≤ 0.623028253235 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520809169392 : ℝ)) (s := (0.853673127771 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.625040679241 : ℝ) ≤ 0.695608879445 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625040679241 : ℝ)) (Q := (0.625040679241 : ℝ))
      (s := (0.780592178602 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨16,by decide⟩).lower)
    (U := (0.789580406126 : ℝ)) (R := (0.790147084026 : ℝ)) (Q2 := (0.625040679241 : ℝ)) (T := (0.834504371996 : ℝ))
    (B := (scalarRow12226.table ⟨16,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy17 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨17,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨17,by decide⟩).lower) ≤ (scalarRow12226.table ⟨17,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨17,by decide⟩).lower) ≤ 0.622218347092 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519609742479 : ℝ)) (s := (0.854403719281 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.624229272197 : ℝ) ≤ 0.695026424562 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624229272197 : ℝ)) (Q := (0.624229272197 : ℝ))
      (s := (0.781241202020 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨17,by decide⟩).lower)
    (U := (0.789067368223 : ℝ)) (R := (0.789634046123 : ℝ)) (Q2 := (0.624229272197 : ℝ)) (T := (0.834154920637 : ℝ))
    (B := (scalarRow12226.table ⟨17,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy18 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨18,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨18,by decide⟩).lower) ≤ (scalarRow12226.table ⟨18,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨18,by decide⟩).lower) ≤ 0.621408995473 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518410315566 : ℝ)) (s := (0.855132004263 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.623418420327 : ℝ) ≤ 0.694444651888 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623418420327 : ℝ)) (Q := (0.623418420327 : ℝ))
      (s := (0.781888402010 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨18,by decide⟩).lower)
    (U := (0.788554348143 : ℝ)) (R := (0.789121026043 : ℝ)) (Q2 := (0.623418420327 : ℝ)) (T := (0.833805732378 : ℝ))
    (B := (scalarRow12226.table ⟨18,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy19 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨19,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨19,by decide⟩).lower) ≤ (scalarRow12226.table ⟨19,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨19,by decide⟩).lower) ≤ 0.620600197727 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517210888653 : ℝ)) (s := (0.855857988605 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.622608122979 : ℝ) ≤ 0.693863560130 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622608122979 : ℝ)) (Q := (0.622608122979 : ℝ))
      (s := (0.782533785342 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨19,by decide⟩).lower)
    (U := (0.788041345508 : ℝ)) (R := (0.788608023408 : ℝ)) (Q2 := (0.622608122979 : ℝ)) (T := (0.833456806774 : ℝ))
    (B := (scalarRow12226.table ⟨19,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy20 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨20,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨20,by decide⟩).lower) ≤ (scalarRow12226.table ⟨20,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨20,by decide⟩).lower) ≤ 0.619791953203 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516011461740 : ℝ)) (s := (0.856581678157 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.621798379498 : ℝ) ≤ 0.693283147994 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621798379498 : ℝ)) (Q := (0.621798379498 : ℝ))
      (s := (0.783177358747 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨20,by decide⟩).lower)
    (U := (0.787528359937 : ℝ)) (R := (0.788095037837 : ℝ)) (Q2 := (0.621798379498 : ℝ)) (T := (0.833108143378 : ℝ))
    (B := (scalarRow12226.table ⟨20,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy21 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨21,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨21,by decide⟩).lower) ≤ (scalarRow12226.table ⟨21,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨21,by decide⟩).lower) ≤ 0.618984261257 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514812034827 : ℝ)) (s := (0.857303078729 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.620989189241 : ℝ) ≤ 0.692703414197 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620989189241 : ℝ)) (Q := (0.620989189241 : ℝ))
      (s := (0.783819128911 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨21,by decide⟩).lower)
    (U := (0.787015391056 : ℝ)) (R := (0.787582068956 : ℝ)) (Q2 := (0.620989189241 : ℝ)) (T := (0.832759741747 : ℝ))
    (B := (scalarRow12226.table ⟨21,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy22 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨22,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨22,by decide⟩).lower) ≤ (scalarRow12226.table ⟨22,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨22,by decide⟩).lower) ≤ 0.618177121246 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513612607914 : ℝ)) (s := (0.858022196096 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.620180551566 : ℝ) ≤ 0.692124357458 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620180551566 : ℝ)) (Q := (0.620180551566 : ℝ))
      (s := (0.784459102478 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨22,by decide⟩).lower)
    (U := (0.786502438489 : ℝ)) (R := (0.787069116389 : ℝ)) (Q2 := (0.620180551566 : ℝ)) (T := (0.832411601441 : ℝ))
    (B := (scalarRow12226.table ⟨22,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy23 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨23,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨23,by decide⟩).lower) ≤ (scalarRow12226.table ⟨23,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨23,by decide⟩).lower) ≤ 0.617370532529 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512413181001 : ℝ)) (s := (0.858739035992 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.619372465826 : ℝ) ≤ 0.691545976495 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619372465826 : ℝ)) (Q := (0.619372465826 : ℝ))
      (s := (0.785097286059 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨23,by decide⟩).lower)
    (U := (0.785989501858 : ℝ)) (R := (0.786556179758 : ℝ)) (Q2 := (0.619372465826 : ℝ)) (T := (0.832063722015 : ℝ))
    (B := (scalarRow12226.table ⟨23,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy24 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨24,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨24,by decide⟩).lower) ≤ (scalarRow12226.table ⟨24,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨24,by decide⟩).lower) ≤ 0.616564494472 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511213754088 : ℝ)) (s := (0.859453604118 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.618564931389 : ℝ) ≤ 0.690968270038 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618564931389 : ℝ)) (Q := (0.618564931389 : ℝ))
      (s := (0.785733686217 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨24,by decide⟩).lower)
    (U := (0.785476580793 : ℝ)) (R := (0.786043258693 : ℝ)) (Q2 := (0.618564931389 : ℝ)) (T := (0.831716103033 : ℝ))
    (B := (scalarRow12226.table ⟨24,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy25 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨25,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨25,by decide⟩).lower) ≤ (scalarRow12226.table ⟨25,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨25,by decide⟩).lower) ≤ 0.615759006440 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510014327175 : ℝ)) (s := (0.860165906135 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.617757947619 : ℝ) ≤ 0.690391236816 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617757947619 : ℝ)) (Q := (0.617757947619 : ℝ))
      (s := (0.786368309480 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨25,by decide⟩).lower)
    (U := (0.784963674919 : ℝ)) (R := (0.785530352819 : ℝ)) (Q2 := (0.617757947619 : ℝ)) (T := (0.831368744056 : ℝ))
    (B := (scalarRow12226.table ⟨25,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy26 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨26,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨26,by decide⟩).lower) ≤ (scalarRow12226.table ⟨26,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨26,by decide⟩).lower) ≤ 0.614954067804 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.508814900262 : ℝ)) (s := (0.860875947667 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.616951513884 : ℝ) ≤ 0.689814875565 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616951513884 : ℝ)) (Q := (0.616951513884 : ℝ))
      (s := (0.787001162335 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨26,by decide⟩).lower)
    (U := (0.784450783865 : ℝ)) (R := (0.785017461765 : ℝ)) (Q2 := (0.616951513884 : ℝ)) (T := (0.831021644649 : ℝ))
    (B := (scalarRow12226.table ⟨26,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy27 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨27,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨27,by decide⟩).lower) ≤ (scalarRow12226.table ⟨27,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨27,by decide⟩).lower) ≤ 0.614149677936 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507615473349 : ℝ)) (s := (0.861583734304 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.616145629558 : ℝ) ≤ 0.689239185023 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616145629558 : ℝ)) (Q := (0.616145629558 : ℝ))
      (s := (0.787632251230 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨27,by decide⟩).lower)
    (U := (0.783937907260 : ℝ)) (R := (0.784504585160 : ℝ)) (Q2 := (0.616145629558 : ℝ)) (T := (0.830674804377 : ℝ))
    (B := (scalarRow12226.table ⟨27,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy28 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨28,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨28,by decide⟩).lower) ≤ (scalarRow12226.table ⟨28,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨28,by decide⟩).lower) ≤ 0.613345836214 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506416046435 : ℝ)) (s := (0.862289271599 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.615340294013 : ℝ) ≤ 0.688664163934 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615340294013 : ℝ)) (Q := (0.615340294013 : ℝ))
      (s := (0.788261582576 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨28,by decide⟩).lower)
    (U := (0.783425044734 : ℝ)) (R := (0.783991722634 : ℝ)) (Q2 := (0.615340294013 : ℝ)) (T := (0.830328222807 : ℝ))
    (B := (scalarRow12226.table ⟨28,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy29 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨29,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨29,by decide⟩).lower) ≤ (scalarRow12226.table ⟨29,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨29,by decide⟩).lower) ≤ 0.612542542016 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505216619522 : ℝ)) (s := (0.862992565066 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.614535506631 : ℝ) ≤ 0.688089811045 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614535506631 : ℝ)) (Q := (0.614535506631 : ℝ))
      (s := (0.788889162741 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨29,by decide⟩).lower)
    (U := (0.782912195919 : ℝ)) (R := (0.783478873819 : ℝ)) (Q2 := (0.614535506631 : ℝ)) (T := (0.829981899509 : ℝ))
    (B := (scalarRow12226.table ⟨29,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy30 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨30,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨30,by decide⟩).lower) ≤ (scalarRow12226.table ⟨30,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨30,by decide⟩).lower) ≤ 0.611739794725 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504017192609 : ℝ)) (s := (0.863693620189 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.613731266790 : ℝ) ≤ 0.687516125108 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613731266790 : ℝ)) (Q := (0.613731266790 : ℝ))
      (s := (0.789514998062 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨30,by decide⟩).lower)
    (U := (0.782399360447 : ℝ)) (R := (0.782966038347 : ℝ)) (Q2 := (0.613731266790 : ℝ)) (T := (0.829635834051 : ℝ))
    (B := (scalarRow12226.table ⟨30,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy31 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨31,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨31,by decide⟩).lower) ≤ (scalarRow12226.table ⟨31,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨31,by decide⟩).lower) ≤ 0.610937593728 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.502817765696 : ℝ)) (s := (0.864392442413 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.612927573878 : ℝ) ≤ 0.686943104881 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612927573878 : ℝ)) (Q := (0.612927573878 : ℝ))
      (s := (0.790139094831 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨31,by decide⟩).lower)
    (U := (0.781886537952 : ℝ)) (R := (0.782453215852 : ℝ)) (Q2 := (0.612927573878 : ℝ)) (T := (0.829290026007 : ℝ))
    (B := (scalarRow12226.table ⟨31,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy32 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨32,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨32,by decide⟩).lower) ≤ (scalarRow12226.table ⟨32,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨32,by decide⟩).lower) ≤ 0.610135938413 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501618338783 : ℝ)) (s := (0.865089037150 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.612124427281 : ℝ) ≤ 0.686370749123 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612124427281 : ℝ)) (Q := (0.612124427281 : ℝ))
      (s := (0.790761459308 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨32,by decide⟩).lower)
    (U := (0.781373728068 : ℝ)) (R := (0.781940405968 : ℝ)) (Q2 := (0.612124427281 : ℝ)) (T := (0.828944474951 : ℝ))
    (B := (scalarRow12226.table ⟨32,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy33 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨33,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨33,by decide⟩).lower) ≤ (scalarRow12226.table ⟨33,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨33,by decide⟩).lower) ≤ 0.609334828173 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500418911870 : ℝ)) (s := (0.865783409776 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.611321826392 : ℝ) ≤ 0.685799056600 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611321826392 : ℝ)) (Q := (0.611321826392 : ℝ))
      (s := (0.791382097711 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨33,by decide⟩).lower)
    (U := (0.780860930432 : ℝ)) (R := (0.781427608332 : ℝ)) (Q2 := (0.611321826392 : ℝ)) (T := (0.828599180458 : ℝ))
    (B := (scalarRow12226.table ⟨33,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy34 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨34,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨34,by decide⟩).lower) ≤ (scalarRow12226.table ⟨34,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨34,by decide⟩).lower) ≤ 0.608534262403 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499219484957 : ℝ)) (s := (0.866475565634 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.610519770604 : ℝ) ≤ 0.685228026080 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610519770604 : ℝ)) (Q := (0.610519770604 : ℝ))
      (s := (0.792001016226 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨34,by decide⟩).lower)
    (U := (0.780348144680 : ℝ)) (R := (0.780914822580 : ℝ)) (Q2 := (0.610519770604 : ℝ)) (T := (0.828254142104 : ℝ))
    (B := (scalarRow12226.table ⟨34,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy35 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨35,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨35,by decide⟩).lower) ≤ (scalarRow12226.table ⟨35,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨35,by decide⟩).lower) ≤ 0.607734240501 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498020058044 : ℝ)) (s := (0.867165510031 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.609718259313 : ℝ) ≤ 0.684657656337 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609718259313 : ℝ)) (Q := (0.609718259313 : ℝ))
      (s := (0.792618221000 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨35,by decide⟩).lower)
    (U := (0.779835370449 : ℝ)) (R := (0.780402048349 : ℝ)) (Q2 := (0.609718259313 : ℝ)) (T := (0.827909359468 : ℝ))
    (B := (scalarRow12226.table ⟨35,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy36 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨36,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨36,by decide⟩).lower) ≤ (scalarRow12226.table ⟨36,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨36,by decide⟩).lower) ≤ 0.606934761870 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.496820631131 : ℝ)) (s := (0.867853248242 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.608917291923 : ℝ) ≤ 0.684087946149 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608917291923 : ℝ)) (Q := (0.608917291923 : ℝ))
      (s := (0.793233718142 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨36,by decide⟩).lower)
    (U := (0.779322607379 : ℝ)) (R := (0.779889285279 : ℝ)) (Q2 := (0.608917291923 : ℝ)) (T := (0.827564832132 : ℝ))
    (B := (scalarRow12226.table ⟨36,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy37 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨37,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨37,by decide⟩).lower) ≤ (scalarRow12226.table ⟨37,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨37,by decide⟩).lower) ≤ 0.606135825913 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495621204218 : ℝ)) (s := (0.868538785507 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.608116867834 : ℝ) ≤ 0.683518894297 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608116867834 : ℝ)) (Q := (0.608116867834 : ℝ))
      (s := (0.793847513731 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨37,by decide⟩).lower)
    (U := (0.778809855109 : ℝ)) (R := (0.779376533009 : ℝ)) (Q2 := (0.608116867834 : ℝ)) (T := (0.827220559675 : ℝ))
    (B := (scalarRow12226.table ⟨37,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy38 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨38,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨38,by decide⟩).lower) ≤ (scalarRow12226.table ⟨38,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨38,by decide⟩).lower) ≤ 0.605337432041 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494421777305 : ℝ)) (s := (0.869222127035 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.607316986458 : ℝ) ≤ 0.682950499571 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607316986458 : ℝ)) (Q := (0.607316986458 : ℝ))
      (s := (0.794459613801 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨38,by decide⟩).lower)
    (U := (0.778297113282 : ℝ)) (R := (0.778863791182 : ℝ)) (Q2 := (0.607316986458 : ℝ)) (T := (0.826876541685 : ℝ))
    (B := (scalarRow12226.table ⟨38,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy39 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨39,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨39,by decide⟩).lower) ≤ (scalarRow12226.table ⟨39,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨39,by decide⟩).lower) ≤ 0.604539579663 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493222350392 : ℝ)) (s := (0.869903278000 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.606517647202 : ℝ) ≤ 0.682382760759 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606517647202 : ℝ)) (Q := (0.606517647202 : ℝ))
      (s := (0.795070024358 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨39,by decide⟩).lower)
    (U := (0.777784381539 : ℝ)) (R := (0.778351059439 : ℝ)) (Q2 := (0.606517647202 : ℝ)) (T := (0.826532777745 : ℝ))
    (B := (scalarRow12226.table ⟨39,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy40 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨40,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨40,by decide⟩).lower) ≤ (scalarRow12226.table ⟨40,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨40,by decide⟩).lower) ≤ 0.603742268195 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492022923479 : ℝ)) (s := (0.870582243543 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.605718849480 : ℝ) ≤ 0.681815676657 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605718849480 : ℝ)) (Q := (0.605718849480 : ℝ))
      (s := (0.795678751372 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨40,by decide⟩).lower)
    (U := (0.777271659523 : ℝ)) (R := (0.777838337423 : ℝ)) (Q2 := (0.605718849480 : ℝ)) (T := (0.826189267442 : ℝ))
    (B := (scalarRow12226.table ⟨40,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy41 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨41,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨41,by decide⟩).lower) ≤ (scalarRow12226.table ⟨41,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨41,by decide⟩).lower) ≤ 0.602945497053 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.490823496566 : ℝ)) (s := (0.871259028774 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.604920592707 : ℝ) ≤ 0.681249246063 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604920592707 : ℝ)) (Q := (0.604920592707 : ℝ))
      (s := (0.796285800777 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨41,by decide⟩).lower)
    (U := (0.776758946878 : ℝ)) (R := (0.777325624778 : ℝ)) (Q2 := (0.604920592707 : ℝ)) (T := (0.825846010364 : ℝ))
    (B := (scalarRow12226.table ⟨41,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy42 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨42,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨42,by decide⟩).lower) ≤ (scalarRow12226.table ⟨42,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨42,by decide⟩).lower) ≤ 0.602149265659 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489624069653 : ℝ)) (s := (0.871933638769 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.604122876305 : ℝ) ≤ 0.680683467784 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604122876305 : ℝ)) (Q := (0.604122876305 : ℝ))
      (s := (0.796891178472 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨42,by decide⟩).lower)
    (U := (0.776246243251 : ℝ)) (R := (0.776812921151 : ℝ)) (Q2 := (0.604122876305 : ℝ)) (T := (0.825503006104 : ℝ))
    (B := (scalarRow12226.table ⟨42,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy43 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨43,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨43,by decide⟩).lower) ≤ (scalarRow12226.table ⟨43,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨43,by decide⟩).lower) ≤ 0.601353573437 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488424642740 : ℝ)) (s := (0.872606078575 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.603325699697 : ℝ) ≤ 0.680118340626 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603325699697 : ℝ)) (Q := (0.603325699697 : ℝ))
      (s := (0.797494890320 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨43,by decide⟩).lower)
    (U := (0.775733548288 : ℝ)) (R := (0.776300226188 : ℝ)) (Q2 := (0.603325699697 : ℝ)) (T := (0.825160254253 : ℝ))
    (B := (scalarRow12226.table ⟨43,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy44 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨44,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨44,by decide⟩).lower) ≤ (scalarRow12226.table ⟨44,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨44,by decide⟩).lower) ≤ 0.600558419814 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487225215827 : ℝ)) (s := (0.873276353203 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.602529062308 : ℝ) ≤ 0.679553863403 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602529062308 : ℝ)) (Q := (0.602529062308 : ℝ))
      (s := (0.798096942154 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨44,by decide⟩).lower)
    (U := (0.775220861637 : ℝ)) (R := (0.775787539537 : ℝ)) (Q2 := (0.602529062308 : ℝ)) (T := (0.824817754406 : ℝ))
    (B := (scalarRow12226.table ⟨44,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy45 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨45,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨45,by decide⟩).lower) ≤ (scalarRow12226.table ⟨45,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨45,by decide⟩).lower) ≤ 0.599763804219 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486025788914 : ℝ)) (s := (0.873944467636 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.601732963566 : ℝ) ≤ 0.678990034930 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601732963566 : ℝ)) (Q := (0.601732963566 : ℝ))
      (s := (0.798697339772 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨45,by decide⟩).lower)
    (U := (0.774708182945 : ℝ)) (R := (0.775274860845 : ℝ)) (Q2 := (0.601732963566 : ℝ)) (T := (0.824475506157 : ℝ))
    (B := (scalarRow12226.table ⟨45,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy46 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨46,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨46,by decide⟩).lower) ≤ (scalarRow12226.table ⟨46,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨46,by decide⟩).lower) ≤ 0.598969726088 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.484826362001 : ℝ)) (s := (0.874610426824 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.600937402907 : ℝ) ≤ 0.678426854032 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600937402907 : ℝ)) (Q := (0.600937402907 : ℝ))
      (s := (0.799296088936 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨46,by decide⟩).lower)
    (U := (0.774195511864 : ℝ)) (R := (0.774762189764 : ℝ)) (Q2 := (0.600937402907 : ℝ)) (T := (0.824133509106 : ℝ))
    (B := (scalarRow12226.table ⟨46,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy47 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨47,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨47,by decide⟩).lower) ≤ (scalarRow12226.table ⟨47,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨47,by decide⟩).lower) ≤ 0.598176184855 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483626935088 : ℝ)) (s := (0.875274235687 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.600142379763 : ℝ) ≤ 0.677864319531 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600142379763 : ℝ)) (Q := (0.600142379763 : ℝ))
      (s := (0.799893195379 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨47,by decide⟩).lower)
    (U := (0.773682848044 : ℝ)) (R := (0.774249525944 : ℝ)) (Q2 := (0.600142379763 : ℝ)) (T := (0.823791762850 : ℝ))
    (B := (scalarRow12226.table ⟨47,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy48 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨48,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨48,by decide⟩).lower) ≤ (scalarRow12226.table ⟨48,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨48,by decide⟩).lower) ≤ 0.597383179962 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482427508175 : ℝ)) (s := (0.875935899114 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.599347893575 : ℝ) ≤ 0.677302430259 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599347893575 : ℝ)) (Q := (0.599347893575 : ℝ))
      (s := (0.800488664797 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨48,by decide⟩).lower)
    (U := (0.773170191138 : ℝ)) (R := (0.773736869038 : ℝ)) (Q2 := (0.599347893575 : ℝ)) (T := (0.823450266992 : ℝ))
    (B := (scalarRow12226.table ⟨48,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy49 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨49,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨49,by decide⟩).lower) ≤ (scalarRow12226.table ⟨49,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨49,by decide⟩).lower) ≤ 0.596590710850 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481228081262 : ℝ)) (s := (0.876595421963 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.598553943783 : ℝ) ≤ 0.676741185049 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598553943783 : ℝ)) (Q := (0.598553943783 : ℝ))
      (s := (0.801082502856 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨49,by decide⟩).lower)
    (U := (0.772657540798 : ℝ)) (R := (0.773224218698 : ℝ)) (Q2 := (0.598553943783 : ℝ)) (T := (0.823109021133 : ℝ))
    (B := (scalarRow12226.table ⟨49,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy50 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨50,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨50,by decide⟩).lower) ≤ (scalarRow12226.table ⟨50,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨50,by decide⟩).lower) ≤ 0.595798776966 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480028654349 : ℝ)) (s := (0.877252809061 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.597760529835 : ℝ) ≤ 0.676180582743 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597760529835 : ℝ)) (Q := (0.597760529835 : ℝ))
      (s := (0.801674715188 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨50,by decide⟩).lower)
    (U := (0.772144896680 : ℝ)) (R := (0.772711574580 : ℝ)) (Q2 := (0.597760529835 : ℝ)) (T := (0.822768024880 : ℝ))
    (B := (scalarRow12226.table ⟨50,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy51 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨51,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨51,by decide⟩).lower) ≤ (scalarRow12226.table ⟨51,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨51,by decide⟩).lower) ≤ 0.595007377758 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.478829227436 : ℝ)) (s := (0.877908065206 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.596967651174 : ℝ) ≤ 0.675620622180 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596967651174 : ℝ)) (Q := (0.596967651174 : ℝ))
      (s := (0.802265307397 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨51,by decide⟩).lower)
    (U := (0.771632258437 : ℝ)) (R := (0.772198936337 : ℝ)) (Q2 := (0.596967651174 : ℝ)) (T := (0.822427277837 : ℝ))
    (B := (scalarRow12226.table ⟨51,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy52 :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table ⟨52,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table ⟨52,by decide⟩).lower) ≤ (scalarRow12226.table ⟨52,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12226.table ⟨52,by decide⟩).lower) ≤ 0.594216512680 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.477629800523 : ℝ)) (s := (0.878561195167 : ℝ))
      <;> norm_num [scalarRow12226,cell12226]
  have hk2 : kappa (0.596175307257 : ℝ) ≤ 0.675061302211 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596175307257 : ℝ)) (Q := (0.596175307257 : ℝ))
      (s := (0.802854285047 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12226.table ⟨52,by decide⟩).lower)
    (U := (0.771119625728 : ℝ)) (R := (0.771686303628 : ℝ)) (Q2 := (0.596175307257 : ℝ)) (T := (0.822086779613 : ℝ))
    (B := (scalarRow12226.table ⟨52,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12226,cell12226])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12226 (gMinus 12226) (1 - (scalarRow12226.table i).lower) ≤ 1 ∧
    energyUpper 12226 (gMinus 12226) (BstLean.Part211.gPlus 12226)
      (finiteEnergy 12226 12226 0.011) (1 - (scalarRow12226.table i).lower) ≤
      (scalarRow12226.table i).energy := by
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
  | ⟨10,h⟩ => exact pilot_upperEnergy10
  | ⟨11,h⟩ => exact pilot_upperEnergy11
  | ⟨12,h⟩ => exact pilot_upperEnergy12
  | ⟨13,h⟩ => exact pilot_upperEnergy13
  | ⟨14,h⟩ => exact pilot_upperEnergy14
  | ⟨15,h⟩ => exact pilot_upperEnergy15
  | ⟨16,h⟩ => exact pilot_upperEnergy16
  | ⟨17,h⟩ => exact pilot_upperEnergy17
  | ⟨18,h⟩ => exact pilot_upperEnergy18
  | ⟨19,h⟩ => exact pilot_upperEnergy19
  | ⟨20,h⟩ => exact pilot_upperEnergy20
  | ⟨21,h⟩ => exact pilot_upperEnergy21
  | ⟨22,h⟩ => exact pilot_upperEnergy22
  | ⟨23,h⟩ => exact pilot_upperEnergy23
  | ⟨24,h⟩ => exact pilot_upperEnergy24
  | ⟨25,h⟩ => exact pilot_upperEnergy25
  | ⟨26,h⟩ => exact pilot_upperEnergy26
  | ⟨27,h⟩ => exact pilot_upperEnergy27
  | ⟨28,h⟩ => exact pilot_upperEnergy28
  | ⟨29,h⟩ => exact pilot_upperEnergy29
  | ⟨30,h⟩ => exact pilot_upperEnergy30
  | ⟨31,h⟩ => exact pilot_upperEnergy31
  | ⟨32,h⟩ => exact pilot_upperEnergy32
  | ⟨33,h⟩ => exact pilot_upperEnergy33
  | ⟨34,h⟩ => exact pilot_upperEnergy34
  | ⟨35,h⟩ => exact pilot_upperEnergy35
  | ⟨36,h⟩ => exact pilot_upperEnergy36
  | ⟨37,h⟩ => exact pilot_upperEnergy37
  | ⟨38,h⟩ => exact pilot_upperEnergy38
  | ⟨39,h⟩ => exact pilot_upperEnergy39
  | ⟨40,h⟩ => exact pilot_upperEnergy40
  | ⟨41,h⟩ => exact pilot_upperEnergy41
  | ⟨42,h⟩ => exact pilot_upperEnergy42
  | ⟨43,h⟩ => exact pilot_upperEnergy43
  | ⟨44,h⟩ => exact pilot_upperEnergy44
  | ⟨45,h⟩ => exact pilot_upperEnergy45
  | ⟨46,h⟩ => exact pilot_upperEnergy46
  | ⟨47,h⟩ => exact pilot_upperEnergy47
  | ⟨48,h⟩ => exact pilot_upperEnergy48
  | ⟨49,h⟩ => exact pilot_upperEnergy49
  | ⟨50,h⟩ => exact pilot_upperEnergy50
  | ⟨51,h⟩ => exact pilot_upperEnergy51
  | ⟨52,h⟩ => exact pilot_upperEnergy52
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264
