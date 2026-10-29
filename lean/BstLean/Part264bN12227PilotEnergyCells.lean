import BstLean.Part264bN12227PilotEnergyUpper
import BstLean.Part263Coverage

/-! Actual upper energy certificates on all 43 source endpoints at 12227. -/
namespace BstLean.Part264b.N12227
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12227 cell12227)
theorem pilot_upperEnergy10 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨10,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨10,by decide⟩).lower) ≤ (scalarRow12227.table ⟨10,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨10,by decide⟩).lower) ≤ 0.627899448957 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528005844306 : ℝ)) (s := (0.849240736411 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.629920787089 : ℝ) ≤ 0.699117986517 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629920787089 : ℝ)) (Q := (0.629920787089 : ℝ))
      (s := (0.776659386085 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨10,by decide⟩).lower)
    (U := (0.792659056601 : ℝ)) (R := (0.793225688155 : ℝ)) (Q2 := (0.629920787089 : ℝ)) (T := (0.836606617538 : ℝ))
    (B := (scalarRow12227.table ⟨10,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy11 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨11,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨11,by decide⟩).lower) ≤ (scalarRow12227.table ⟨11,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨11,by decide⟩).lower) ≤ 0.627086209433 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526806428736 : ℝ)) (s := (0.849985286133 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.629106042807 : ℝ) ≤ 0.698531416515 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629106042807 : ℝ)) (Q := (0.629106042807 : ℝ))
      (s := (0.777319488309 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨11,by decide⟩).lower)
    (U := (0.792145908585 : ℝ)) (R := (0.792712540139 : ℝ)) (Q2 := (0.629106042807 : ℝ)) (T := (0.836255581425 : ℝ))
    (B := (scalarRow12227.table ⟨11,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy12 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨12,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨12,by decide⟩).lower) ≤ (scalarRow12227.table ⟨12,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨12,by decide⟩).lower) ≤ 0.626273528403 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525607013167 : ℝ)) (s := (0.850727493214 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.628291857674 : ℝ) ≤ 0.697945536563 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628291857674 : ℝ)) (Q := (0.628291857674 : ℝ))
      (s := (0.777977725633 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨12,by decide⟩).lower)
    (U := (0.791632780687 : ℝ)) (R := (0.792199412241 : ℝ)) (Q2 := (0.628291857674 : ℝ)) (T := (0.835904811120 : ℝ))
    (B := (scalarRow12227.table ⟨12,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy13 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨13,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨13,by decide⟩).lower) ≤ (scalarRow12227.table ⟨13,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨13,by decide⟩).lower) ≤ 0.625461405193 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524407597597 : ℝ)) (s := (0.851467363781 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.627478231016 : ℝ) ≤ 0.697360345340 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627478231016 : ℝ)) (Q := (0.627478231016 : ℝ))
      (s := (0.778634105085 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨13,by decide⟩).lower)
    (U := (0.791119672520 : ℝ)) (R := (0.791686304074 : ℝ)) (Q2 := (0.627478231016 : ℝ)) (T := (0.835554306166 : ℝ))
    (B := (scalarRow12227.table ⟨13,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy14 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨14,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨14,by decide⟩).lower) ≤ (scalarRow12227.table ⟨14,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨14,by decide⟩).lower) ≤ 0.624649839138 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523208182028 : ℝ)) (s := (0.852204903917 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.626665162168 : ℝ) ≤ 0.696775841534 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626665162168 : ℝ)) (Q := (0.626665162168 : ℝ))
      (s := (0.779288633643 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨14,by decide⟩).lower)
    (U := (0.790606583702 : ℝ)) (R := (0.791173215256 : ℝ)) (Q2 := (0.626665162168 : ℝ)) (T := (0.835204066111 : ℝ))
    (B := (scalarRow12227.table ⟨14,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy15 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨15,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨15,by decide⟩).lower) ≤ (scalarRow12227.table ⟨15,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨15,by decide⟩).lower) ≤ 0.623838829571 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522008766458 : ℝ)) (s := (0.852940119670 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.625852650460 : ℝ) ≤ 0.696192023831 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625852650460 : ℝ)) (Q := (0.625852650460 : ℝ))
      (s := (0.779941318250 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨15,by decide⟩).lower)
    (U := (0.790093513849 : ℝ)) (R := (0.790660145403 : ℝ)) (Q2 := (0.625852650460 : ℝ)) (T := (0.834854090500 : ℝ))
    (B := (scalarRow12227.table ⟨15,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy16 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨16,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨16,by decide⟩).lower) ≤ (scalarRow12227.table ⟨16,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨16,by decide⟩).lower) ≤ 0.623028375832 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520809350889 : ℝ)) (s := (0.853673017043 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.625040695231 : ℝ) ≤ 0.695608890926 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625040695231 : ℝ)) (Q := (0.625040695231 : ℝ))
      (s := (0.780592165798 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨16,by decide⟩).lower)
    (U := (0.789580462579 : ℝ)) (R := (0.790147094133 : ℝ)) (Q2 := (0.625040695231 : ℝ)) (T := (0.834504378883 : ℝ))
    (B := (scalarRow12227.table ⟨16,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy17 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨17,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨17,by decide⟩).lower) ≤ (scalarRow12227.table ⟨17,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨17,by decide⟩).lower) ≤ 0.622218477262 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519609935319 : ℝ)) (s := (0.854403602005 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.624229295823 : ℝ) ≤ 0.695026441517 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624229295823 : ℝ)) (Q := (0.624229295823 : ℝ))
      (s := (0.781241183142 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨17,by decide⟩).lower)
    (U := (0.789067429512 : ℝ)) (R := (0.789634061066 : ℝ)) (Q2 := (0.624229295823 : ℝ)) (T := (0.834154930811 : ℝ))
    (B := (scalarRow12227.table ⟨17,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy18 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨18,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨18,by decide⟩).lower) ≤ (scalarRow12227.table ⟨18,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨18,by decide⟩).lower) ≤ 0.621409133206 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518410519750 : ℝ)) (s := (0.855131880480 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.623418451578 : ℝ) ≤ 0.694444674305 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623418451578 : ℝ)) (Q := (0.623418451578 : ℝ))
      (s := (0.781888377093 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨18,by decide⟩).lower)
    (U := (0.788554414268 : ℝ)) (R := (0.789121045822 : ℝ)) (Q2 := (0.623418451578 : ℝ)) (T := (0.833805745836 : ℝ))
    (B := (scalarRow12227.table ⟨18,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy19 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨19,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨19,by decide⟩).lower) ≤ (scalarRow12227.table ⟨19,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨19,by decide⟩).lower) ≤ 0.620600343011 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517211104180 : ℝ)) (s := (0.855857858358 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.622608161841 : ℝ) ≤ 0.693863587993 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622608161841 : ℝ)) (Q := (0.622608161841 : ℝ))
      (s := (0.782533754422 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨19,by decide⟩).lower)
    (U := (0.788041416466 : ℝ)) (R := (0.788608048020 : ℝ)) (Q2 := (0.622608161841 : ℝ)) (T := (0.833456823508 : ℝ))
    (B := (scalarRow12227.table ⟨19,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy20 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨20,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨20,by decide⟩).lower) ≤ (scalarRow12227.table ⟨20,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨20,by decide⟩).lower) ≤ 0.619792106030 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516011688611 : ℝ)) (s := (0.856581541488 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.621798425966 : ℝ) ≤ 0.693283181294 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621798425966 : ℝ)) (Q := (0.621798425966 : ℝ))
      (s := (0.783177321854 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨20,by decide⟩).lower)
    (U := (0.787528435731 : ℝ)) (R := (0.788095067285 : ℝ)) (Q2 := (0.621798425966 : ℝ)) (T := (0.833108163386 : ℝ))
    (B := (scalarRow12227.table ⟨20,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy21 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨21,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨21,by decide⟩).lower) ≤ (scalarRow12227.table ⟨21,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨21,by decide⟩).lower) ≤ 0.618984421615 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514812273041 : ℝ)) (s := (0.857302935681 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.620989243302 : ℝ) ≤ 0.692703452919 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620989243302 : ℝ)) (Q := (0.620989243302 : ℝ))
      (s := (0.783819086080 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨21,by decide⟩).lower)
    (U := (0.787015471684 : ℝ)) (R := (0.787582103238 : ℝ)) (Q2 := (0.620989243302 : ℝ)) (T := (0.832759765023 : ℝ))
    (B := (scalarRow12227.table ⟨21,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy22 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨22,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨22,by decide⟩).lower) ≤ (scalarRow12227.table ⟨22,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨22,by decide⟩).lower) ≤ 0.618177289125 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513612857472 : ℝ)) (s := (0.858022046710 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.620180613208 : ℝ) ≤ 0.692124401589 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620180613208 : ℝ)) (Q := (0.620180613208 : ℝ))
      (s := (0.784459053745 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨22,by decide⟩).lower)
    (U := (0.786502523950 : ℝ)) (R := (0.787069155504 : ℝ)) (Q2 := (0.620180613208 : ℝ)) (T := (0.832411627979 : ℝ))
    (B := (scalarRow12227.table ⟨22,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy23 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨23,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨23,by decide⟩).lower) ≤ (scalarRow12227.table ⟨23,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨23,by decide⟩).lower) ≤ 0.617370707920 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512413441902 : ℝ)) (s := (0.858738880312 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.619372535042 : ℝ) ≤ 0.691546026024 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619372535042 : ℝ)) (Q := (0.619372535042 : ℝ))
      (s := (0.785097231454 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨23,by decide⟩).lower)
    (U := (0.785989592154 : ℝ)) (R := (0.786556223708 : ℝ)) (Q2 := (0.619372535042 : ℝ)) (T := (0.832063751811 : ℝ))
    (B := (scalarRow12227.table ⟨23,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy24 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨24,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨24,by decide⟩).lower) ≤ (scalarRow12227.table ⟨24,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨24,by decide⟩).lower) ≤ 0.616564677364 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511214026333 : ℝ)) (s := (0.859453442184 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.618565008169 : ℝ) ≤ 0.690968324953 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618565008169 : ℝ)) (Q := (0.618565008169 : ℝ))
      (s := (0.785733625773 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨24,by decide⟩).lower)
    (U := (0.785476675923 : ℝ)) (R := (0.786043307477 : ℝ)) (Q2 := (0.618565008169 : ℝ)) (T := (0.831716136083 : ℝ))
    (B := (scalarRow12227.table ⟨24,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy25 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨25,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨25,by decide⟩).lower) ≤ (scalarRow12227.table ⟨25,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨25,by decide⟩).lower) ≤ 0.615759196822 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510014610763 : ℝ)) (s := (0.860165737988 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.617758031950 : ℝ) ≤ 0.690391297103 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617758031950 : ℝ)) (Q := (0.617758031950 : ℝ))
      (s := (0.786368243231 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨25,by decide⟩).lower)
    (U := (0.784963774882 : ℝ)) (R := (0.785530406436 : ℝ)) (Q2 := (0.617758031950 : ℝ)) (T := (0.831368780355 : ℝ))
    (B := (scalarRow12227.table ⟨25,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy26 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨26,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨26,by decide⟩).lower) ≤ (scalarRow12227.table ⟨26,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨26,by decide⟩).lower) ≤ 0.614954265666 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.508815195194 : ℝ)) (s := (0.860875773350 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.616951605757 : ℝ) ≤ 0.689814941211 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616951605757 : ℝ)) (Q := (0.616951605757 : ℝ))
      (s := (0.787001090314 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨26,by decide⟩).lower)
    (U := (0.784450888661 : ℝ)) (R := (0.785017520215 : ℝ)) (Q2 := (0.616951605757 : ℝ)) (T := (0.831021684191 : ℝ))
    (B := (scalarRow12227.table ⟨26,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy27 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨27,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨27,by decide⟩).lower) ≤ (scalarRow12227.table ⟨27,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨27,by decide⟩).lower) ≤ 0.614149883268 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507615779624 : ℝ)) (s := (0.861583553857 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.616145728960 : ℝ) ≤ 0.689239256015 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616145728960 : ℝ)) (Q := (0.616145728960 : ℝ))
      (s := (0.787632173470 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨27,by decide⟩).lower)
    (U := (0.783938016888 : ℝ)) (R := (0.784504648442 : ℝ)) (Q2 := (0.616145728960 : ℝ)) (T := (0.830674847157 : ℝ))
    (B := (scalarRow12227.table ⟨27,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy28 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨28,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨28,by decide⟩).lower) ≤ (scalarRow12227.table ⟨28,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨28,by decide⟩).lower) ≤ 0.613346049006 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506416364055 : ℝ)) (s := (0.862289085063 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.615340400939 : ℝ) ≤ 0.688664240262 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615340400939 : ℝ)) (Q := (0.615340400939 : ℝ))
      (s := (0.788261499106 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨28,by decide⟩).lower)
    (U := (0.783425159196 : ℝ)) (R := (0.783991790750 : ℝ)) (Q2 := (0.615340400939 : ℝ)) (T := (0.830328268822 : ℝ))
    (B := (scalarRow12227.table ⟨28,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy29 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨29,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨29,by decide⟩).lower) ≤ (scalarRow12227.table ⟨29,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨29,by decide⟩).lower) ≤ 0.612542762258 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505216948485 : ℝ)) (s := (0.862992372483 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.614535621068 : ℝ) ≤ 0.688089892696 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614535621068 : ℝ)) (Q := (0.614535621068 : ℝ))
      (s := (0.788889073596 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨29,by decide⟩).lower)
    (U := (0.782912315214 : ℝ)) (R := (0.783478946768 : ℝ)) (Q2 := (0.614535621068 : ℝ)) (T := (0.829981948753 : ℝ))
    (B := (scalarRow12227.table ⟨29,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy30 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨30,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨30,by decide⟩).lower) ≤ (scalarRow12227.table ⟨30,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨30,by decide⟩).lower) ≤ 0.611740022407 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504017532916 : ℝ)) (s := (0.863693421599 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.613731388728 : ℝ) ≤ 0.687516212069 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613731388728 : ℝ)) (Q := (0.613731388728 : ℝ))
      (s := (0.789514903273 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨30,by decide⟩).lower)
    (U := (0.782399484574 : ℝ)) (R := (0.782966116128 : ℝ)) (Q2 := (0.613731388728 : ℝ)) (T := (0.829635886519 : ℝ))
    (B := (scalarRow12227.table ⟨30,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy31 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨31,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨31,by decide⟩).lower) ≤ (scalarRow12227.table ⟨31,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨31,by decide⟩).lower) ≤ 0.610937828839 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.502818117346 : ℝ)) (s := (0.864392237858 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.612927703308 : ℝ) ≤ 0.686943197141 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612927703308 : ℝ)) (Q := (0.612927703308 : ℝ))
      (s := (0.790138994430 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨31,by decide⟩).lower)
    (U := (0.781886666912 : ℝ)) (R := (0.782453298466 : ℝ)) (Q2 := (0.612927703308 : ℝ)) (T := (0.829290081696 : ℝ))
    (B := (scalarRow12227.table ⟨31,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy32 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨32,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨32,by decide⟩).lower) ≤ (scalarRow12227.table ⟨32,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨32,by decide⟩).lower) ≤ 0.610136180944 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501618701777 : ℝ)) (s := (0.865088826670 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.612124564193 : ℝ) ≤ 0.686370846669 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612124564193 : ℝ)) (Q := (0.612124564193 : ℝ))
      (s := (0.790761353325 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨32,by decide⟩).lower)
    (U := (0.781373861861 : ℝ)) (R := (0.781940493415 : ℝ)) (Q2 := (0.612124564193 : ℝ)) (T := (0.828944533855 : ℝ))
    (B := (scalarRow12227.table ⟨32,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy33 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨33,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨33,by decide⟩).lower) ≤ (scalarRow12227.table ⟨33,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨33,by decide⟩).lower) ≤ 0.609335078112 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500419286207 : ℝ)) (s := (0.865783193411 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.611321970772 : ℝ) ≤ 0.685799159417 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611321970772 : ℝ)) (Q := (0.611321970772 : ℝ))
      (s := (0.791381986181 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨33,by decide⟩).lower)
    (U := (0.780861069056 : ℝ)) (R := (0.781427700610 : ℝ)) (Q2 := (0.611321970772 : ℝ)) (T := (0.828599242571 : ℝ))
    (B := (scalarRow12227.table ⟨33,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy34 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨34,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨34,by decide⟩).lower) ≤ (scalarRow12227.table ⟨34,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨34,by decide⟩).lower) ≤ 0.608534519741 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499219870638 : ℝ)) (s := (0.866475343424 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.610519922443 : ℝ) ≤ 0.685228134157 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610519922443 : ℝ)) (Q := (0.610519922443 : ℝ))
      (s := (0.792000899179 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨34,by decide⟩).lower)
    (U := (0.780348288135 : ℝ)) (R := (0.780914919689 : ℝ)) (Q2 := (0.610519922443 : ℝ)) (T := (0.828254207422 : ℝ))
    (B := (scalarRow12227.table ⟨34,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy35 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨35,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨35,by decide⟩).lower) ≤ (scalarRow12227.table ⟨35,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨35,by decide⟩).lower) ≤ 0.607734505227 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498020455068 : ℝ)) (s := (0.867165282016 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.609718418604 : ℝ) ≤ 0.684657769664 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609718418604 : ℝ)) (Q := (0.609718418604 : ℝ))
      (s := (0.792618098466 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨35,by decide⟩).lower)
    (U := (0.779835518736 : ℝ)) (R := (0.780402150290 : ℝ)) (Q2 := (0.609718418604 : ℝ)) (T := (0.827909427988 : ℝ))
    (B := (scalarRow12227.table ⟨35,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy36 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨36,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨36,by decide⟩).lower) ≤ (scalarRow12227.table ⟨36,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨36,by decide⟩).lower) ≤ 0.606935033975 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.496821039499 : ℝ)) (s := (0.867853014463 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.608917458654 : ℝ) ≤ 0.684088064713 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608917458654 : ℝ)) (Q := (0.608917458654 : ℝ))
      (s := (0.793233590153 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨36,by decide⟩).lower)
    (U := (0.779322760498 : ℝ)) (R := (0.779889392052 : ℝ)) (Q2 := (0.608917458654 : ℝ)) (T := (0.827564903847 : ℝ))
    (B := (scalarRow12227.table ⟨36,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy37 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨37,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨37,by decide⟩).lower) ≤ (scalarRow12227.table ⟨37,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨37,by decide⟩).lower) ≤ 0.606136105387 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495621623929 : ℝ)) (s := (0.868538546004 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.608117041996 : ℝ) ≤ 0.683519018086 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608117041996 : ℝ)) (Q := (0.608117041996 : ℝ))
      (s := (0.793847380316 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨37,by decide⟩).lower)
    (U := (0.778810013060 : ℝ)) (R := (0.779376644614 : ℝ)) (Q2 := (0.608117041996 : ℝ)) (T := (0.827220634583 : ℝ))
    (B := (scalarRow12227.table ⟨37,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy38 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨38,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨38,by decide⟩).lower) ≤ (scalarRow12227.table ⟨38,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨38,by decide⟩).lower) ≤ 0.605337718874 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494422208360 : ℝ)) (s := (0.869221881847 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.607317168039 : ℝ) ≤ 0.682950628571 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607317168039 : ℝ)) (Q := (0.607317168039 : ℝ))
      (s := (0.794459474993 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨38,by decide⟩).lower)
    (U := (0.778297276064 : ℝ)) (R := (0.778863907618 : ℝ)) (Q2 := (0.607317168039 : ℝ)) (T := (0.826876619778 : ℝ))
    (B := (scalarRow12227.table ⟨38,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy39 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨39,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨39,by decide⟩).lower) ≤ (scalarRow12227.table ⟨39,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨39,by decide⟩).lower) ≤ 0.604539873844 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493222792790 : ℝ)) (s := (0.869903027166 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.606517836193 : ℝ) ≤ 0.682382894960 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606517836193 : ℝ)) (Q := (0.606517836193 : ℝ))
      (s := (0.795069880187 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨39,by decide⟩).lower)
    (U := (0.777784549152 : ℝ)) (R := (0.778351180706 : ℝ)) (Q2 := (0.606517836193 : ℝ)) (T := (0.826532859020 : ℝ))
    (B := (scalarRow12227.table ⟨39,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy40 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨40,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨40,by decide⟩).lower) ≤ (scalarRow12227.table ⟨40,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨40,by decide⟩).lower) ≤ 0.603742569714 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492023377221 : ℝ)) (s := (0.870581987103 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.605719045870 : ℝ) ≤ 0.681815816045 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605719045870 : ℝ)) (Q := (0.605719045870 : ℝ))
      (s := (0.795678601868 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨40,by decide⟩).lower)
    (U := (0.777271831967 : ℝ)) (R := (0.777838463521 : ℝ)) (Q2 := (0.605719045870 : ℝ)) (T := (0.826189351893 : ℝ))
    (B := (scalarRow12227.table ⟨40,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy41 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨41,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨41,by decide⟩).lower) ≤ (scalarRow12227.table ⟨41,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨41,by decide⟩).lower) ≤ 0.602945805902 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.490823961652 : ℝ)) (s := (0.871258766767 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.604920796488 : ℝ) ≤ 0.681249390629 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604920796488 : ℝ)) (Q := (0.604920796488 : ℝ))
      (s := (0.796285645970 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨41,by decide⟩).lower)
    (U := (0.776759124154 : ℝ)) (R := (0.777325755708 : ℝ)) (Q2 := (0.604920796488 : ℝ)) (T := (0.825846097989 : ℝ))
    (B := (scalarRow12227.table ⟨41,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy42 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨42,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨42,by decide⟩).lower) ≤ (scalarRow12227.table ⟨42,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨42,by decide⟩).lower) ≤ 0.602149581826 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489624546082 : ℝ)) (s := (0.871933371236 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.604123087466 : ℝ) ≤ 0.680683617513 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604123087466 : ℝ)) (Q := (0.604123087466 : ℝ))
      (s := (0.796891018390 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨42,by decide⟩).lower)
    (U := (0.776246425358 : ℝ)) (R := (0.776813056912 : ℝ)) (Q2 := (0.604123087466 : ℝ)) (T := (0.825503096896 : ℝ))
    (B := (scalarRow12227.table ⟨42,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy43 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨43,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨43,by decide⟩).lower) ≤ (scalarRow12227.table ⟨43,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨43,by decide⟩).lower) ≤ 0.601353896913 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488425130513 : ℝ)) (s := (0.872605805553 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.603325918228 : ℝ) ≤ 0.680118495508 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603325918228 : ℝ)) (Q := (0.603325918228 : ℝ))
      (s := (0.797494724995 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨43,by decide⟩).lower)
    (U := (0.775733735226 : ℝ)) (R := (0.776300366780 : ℝ)) (Q2 := (0.603325918228 : ℝ)) (T := (0.825160348209 : ℝ))
    (B := (scalarRow12227.table ⟨43,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy44 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨44,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨44,by decide⟩).lower) ≤ (scalarRow12227.table ⟨44,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨44,by decide⟩).lower) ≤ 0.600558750588 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487225714943 : ℝ)) (s := (0.873276074732 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.602529288197 : ℝ) ≤ 0.679554023424 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602529288197 : ℝ)) (Q := (0.602529288197 : ℝ))
      (s := (0.798096771617 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨44,by decide⟩).lower)
    (U := (0.775221053405 : ℝ)) (R := (0.775787684959 : ℝ)) (Q2 := (0.602529288197 : ℝ)) (T := (0.824817851520 : ℝ))
    (B := (scalarRow12227.table ⟨44,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy45 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨45,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨45,by decide⟩).lower) ≤ (scalarRow12227.table ⟨45,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨45,by decide⟩).lower) ≤ 0.599764142283 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486026299374 : ℝ)) (s := (0.873944183754 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.601733196807 : ℝ) ≤ 0.678990200082 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601733196807 : ℝ)) (Q := (0.601733196807 : ℝ))
      (s := (0.798697164050 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨45,by decide⟩).lower)
    (U := (0.774708379545 : ℝ)) (R := (0.775275011099 : ℝ)) (Q2 := (0.601733196807 : ℝ)) (T := (0.824475606426 : ℝ))
    (B := (scalarRow12227.table ⟨45,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy46 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨46,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨46,by decide⟩).lower) ≤ (scalarRow12227.table ⟨46,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨46,by decide⟩).lower) ≤ 0.598970071430 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.484826883804 : ℝ)) (s := (0.874610137571 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.600937643487 : ℝ) ≤ 0.678427024299 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600937643487 : ℝ)) (Q := (0.600937643487 : ℝ))
      (s := (0.799295908060 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨46,by decide⟩).lower)
    (U := (0.774195713295 : ℝ)) (R := (0.774762344849 : ℝ)) (Q2 := (0.600937643487 : ℝ)) (T := (0.824133612524 : ℝ))
    (B := (scalarRow12227.table ⟨46,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy47 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨47,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨47,by decide⟩).lower) ≤ (scalarRow12227.table ⟨47,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨47,by decide⟩).lower) ≤ 0.598176537466 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483627468235 : ℝ)) (s := (0.875273941100 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.600142627673 : ℝ) ≤ 0.677864494903 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600142627673 : ℝ)) (Q := (0.600142627673 : ℝ))
      (s := (0.799893009377 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨47,by decide⟩).lower)
    (U := (0.773683054306 : ℝ)) (R := (0.774249685860 : ℝ)) (Q2 := (0.600142627673 : ℝ)) (T := (0.823791869413 : ℝ))
    (B := (scalarRow12227.table ⟨47,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy48 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨48,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨48,by decide⟩).lower) ≤ (scalarRow12227.table ⟨48,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨48,by decide⟩).lower) ≤ 0.597383539831 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482428052665 : ℝ)) (s := (0.875935599232 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.599348148806 : ℝ) ≤ 0.677302610725 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599348148806 : ℝ)) (Q := (0.599348148806 : ℝ))
      (s := (0.800488473698 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨48,by decide⟩).lower)
    (U := (0.773170402231 : ℝ)) (R := (0.773737033785 : ℝ)) (Q2 := (0.599348148806 : ℝ)) (T := (0.823450376695 : ℝ))
    (B := (scalarRow12227.table ⟨48,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy49 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨49,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨49,by decide⟩).lower) ≤ (scalarRow12227.table ⟨49,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨49,by decide⟩).lower) ≤ 0.596591077969 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481228637096 : ℝ)) (s := (0.876595116824 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.598554206326 : ℝ) ≤ 0.676741370598 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598554206326 : ℝ)) (Q := (0.598554206326 : ℝ))
      (s := (0.801082306689 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨49,by decide⟩).lower)
    (U := (0.772657756723 : ℝ)) (R := (0.773224388277 : ℝ)) (Q2 := (0.598554206326 : ℝ)) (T := (0.823109133973 : ℝ))
    (B := (scalarRow12227.table ⟨49,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy50 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨50,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨50,by decide⟩).lower) ≤ (scalarRow12227.table ⟨50,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨50,by decide⟩).lower) ≤ 0.595799151324 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480029221526 : ℝ)) (s := (0.877252498704 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.597760799676 : ℝ) ≤ 0.676180773360 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597760799676 : ℝ)) (Q := (0.597760799676 : ℝ))
      (s := (0.801674513984 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨50,by decide⟩).lower)
    (U := (0.772145117435 : ℝ)) (R := (0.772711748989 : ℝ)) (Q2 := (0.597760799676 : ℝ)) (T := (0.822768140850 : ℝ))
    (B := (scalarRow12227.table ⟨50,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy51 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨51,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨51,by decide⟩).lower) ≤ (scalarRow12227.table ⟨51,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨51,by decide⟩).lower) ≤ 0.595007759346 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.478829805957 : ℝ)) (s := (0.877907749669 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.596967928308 : ℝ) ≤ 0.675620817856 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596967928308 : ℝ)) (Q := (0.596967928308 : ℝ))
      (s := (0.802265101181 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨51,by decide⟩).lower)
    (U := (0.771632484024 : ℝ)) (R := (0.772199115578 : ℝ)) (Q2 := (0.596967928308 : ℝ)) (T := (0.822427396934 : ℝ))
    (B := (scalarRow12227.table ⟨51,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy52 :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table ⟨52,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table ⟨52,by decide⟩).lower) ≤ (scalarRow12227.table ⟨52,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12227.table ⟨52,by decide⟩).lower) ≤ 0.594216901486 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.477630390387 : ℝ)) (s := (0.878560874487 : ℝ))
      <;> norm_num [scalarRow12227,cell12227]
  have hk2 : kappa (0.596175591669 : ℝ) ≤ 0.675061502932 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596175591669 : ℝ)) (Q := (0.596175591669 : ℝ))
      (s := (0.802854073851 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12227.table ⟨52,by decide⟩).lower)
    (U := (0.771119856145 : ℝ)) (R := (0.771686487699 : ℝ)) (Q2 := (0.596175591669 : ℝ)) (T := (0.822086901832 : ℝ))
    (B := (scalarRow12227.table ⟨52,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12227,cell12227])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12227 (gMinus 12227) (1 - (scalarRow12227.table i).lower) ≤ 1 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 0.011) (1 - (scalarRow12227.table i).lower) ≤
      (scalarRow12227.table i).energy := by
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

end BstLean.Part264b.N12227
