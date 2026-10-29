import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part281Scalar8
namespace BstLean.Part281.WorldRow12059
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12059 = 192570400246037 := by
  have hu : mW 12059 ≤ 192570400246037 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12059 ≤ 192570400246036 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12059)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24118 ^ 2)
    ((25000000000000000000/3788446580963931666270973))
    ((25000000000000000000/3788289501331252176596991)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24118) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24118 : ℝ)^2 / (mW 12059 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2146181/1000000000000))/2) * ((1-firstRatio 24118) * √(1-firstRatio 24118) *
      sixthConstant (e1CovarianceRatio 24118 (mW 12059) (1/10^6) rowEps))) /
    (712/10000 - 24118*(1+1/10^6)*((2146181/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24118 (mW 12059) /
    ((1/10^5) * ((mW 12059 : ℝ)*24118*((mW 12059 : ℝ)+24118+1)))^2 +
  8*(mW 12059 : ℝ)*24118*(24118+2)*(24118+3) /
    ((1/1000)*((mW 12059 : ℝ)*24118*(24118+2)))^2 +
  covarianceVarianceBound 24118 (mW 12059) /
    ((1/1000)*covarianceMeanBound 24118 (mW 12059))^2 +
  normVarianceBound 24118 (mW 12059) / (3*inputVarianceMean 24118 (mW 12059))^2

end BstLean.Part281.WorldRow12059
namespace BstLean.Part281.WorldRow12060
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12060 = 192626297606366 := by
  have hu : mW 12060 ≤ 192626297606366 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12060 ≤ 192626297606365 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12060)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24120 ^ 2)
    ((1250000000000000000/189438037011464532279741))
    ((25000000000000000000/3788603660596611155920837)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24120) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24120 : ℝ)^2 / (mW 12060 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2146001/1000000000000))/2) * ((1-firstRatio 24120) * √(1-firstRatio 24120) *
      sixthConstant (e1CovarianceRatio 24120 (mW 12060) (1/10^6) rowEps))) /
    (712/10000 - 24120*(1+1/10^6)*((2146001/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24120 (mW 12060) /
    ((1/10^5) * ((mW 12060 : ℝ)*24120*((mW 12060 : ℝ)+24120+1)))^2 +
  8*(mW 12060 : ℝ)*24120*(24120+2)*(24120+3) /
    ((1/1000)*((mW 12060 : ℝ)*24120*(24120+2)))^2 +
  covarianceVarianceBound 24120 (mW 12060) /
    ((1/1000)*covarianceMeanBound 24120 (mW 12060))^2 +
  normVarianceBound 24120 (mW 12060) / (3*inputVarianceMean 24120 (mW 12060))^2

end BstLean.Part281.WorldRow12060
namespace BstLean.Part281.WorldRow12061
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12061 = 192682206555244 := by
  have hu : mW 12061 ≤ 192682206555244 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12061 ≤ 192682206555243 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12061)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24122 ^ 2)
    ((25000000000000000000/3789074899494649624918667))
    ((25000000000000000000/3788917819861970135244683)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24122) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24122 : ℝ)^2 / (mW 12061 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2145821/1000000000000))/2) * ((1-firstRatio 24122) * √(1-firstRatio 24122) *
      sixthConstant (e1CovarianceRatio 24122 (mW 12061) (1/10^6) rowEps))) /
    (712/10000 - 24122*(1+1/10^6)*((2145821/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24122 (mW 12061) /
    ((1/10^5) * ((mW 12061 : ℝ)*24122*((mW 12061 : ℝ)+24122+1)))^2 +
  8*(mW 12061 : ℝ)*24122*(24122+2)*(24122+3) /
    ((1/1000)*((mW 12061 : ℝ)*24122*(24122+2)))^2 +
  covarianceVarianceBound 24122 (mW 12061) /
    ((1/1000)*covarianceMeanBound 24122 (mW 12061))^2 +
  normVarianceBound 24122 (mW 12061) / (3*inputVarianceMean 24122 (mW 12061))^2

end BstLean.Part281.WorldRow12061
namespace BstLean.Part281.WorldRow12062
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12062 = 192738127094110 := by
  have hu : mW 12062 ≤ 192738127094110 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12062 ≤ 192738127094109 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12062)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24124 ^ 2)
    ((12500000000000000000/1894694529380004302121257))
    ((25000000000000000000/3789231979127329114568529)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24124) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24124 : ℝ)^2 / (mW 12062 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1072821/500000000000))/2) * ((1-firstRatio 24124) * √(1-firstRatio 24124) *
      sixthConstant (e1CovarianceRatio 24124 (mW 12062) (1/10^6) rowEps))) /
    (712/10000 - 24124*(1+1/10^6)*((1072821/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24124 (mW 12062) /
    ((1/10^5) * ((mW 12062 : ℝ)*24124*((mW 12062 : ℝ)+24124+1)))^2 +
  8*(mW 12062 : ℝ)*24124*(24124+2)*(24124+3) /
    ((1/1000)*((mW 12062 : ℝ)*24124*(24124+2)))^2 +
  covarianceVarianceBound 24124 (mW 12062) /
    ((1/1000)*covarianceMeanBound 24124 (mW 12062))^2 +
  normVarianceBound 24124 (mW 12062) / (3*inputVarianceMean 24124 (mW 12062))^2

end BstLean.Part281.WorldRow12062
namespace BstLean.Part281.WorldRow12063
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12063 = 192794059224408 := by
  have hu : mW 12063 ≤ 192794059224408 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12063 ≤ 192794059224407 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12063)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24126 ^ 2)
    ((25000000000000000000/3789703218025367583566361))
    ((200000000000000000/30316369107141504751139)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24126) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24126 : ℝ)^2 / (mW 12063 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1072731/500000000000))/2) * ((1-firstRatio 24126) * √(1-firstRatio 24126) *
      sixthConstant (e1CovarianceRatio 24126 (mW 12063) (1/10^6) rowEps))) /
    (712/10000 - 24126*(1+1/10^6)*((1072731/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24126 (mW 12063) /
    ((1/10^5) * ((mW 12063 : ℝ)*24126*((mW 12063 : ℝ)+24126+1)))^2 +
  8*(mW 12063 : ℝ)*24126*(24126+2)*(24126+3) /
    ((1/1000)*((mW 12063 : ℝ)*24126*(24126+2)))^2 +
  covarianceVarianceBound 24126 (mW 12063) /
    ((1/1000)*covarianceMeanBound 24126 (mW 12063))^2 +
  normVarianceBound 24126 (mW 12063) / (3*inputVarianceMean 24126 (mW 12063))^2

end BstLean.Part281.WorldRow12063
namespace BstLean.Part281.WorldRow12064
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12064 = 192850002947577 := by
  have hu : mW 12064 ≤ 192850002947577 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12064 ≤ 192850002947576 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12064)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24128 ^ 2)
    ((781250000000000000/118438043040335205090319))
    ((25000000000000000000/3789860297658047073216221)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24128) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24128 : ℝ)^2 / (mW 12064 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1072641/500000000000))/2) * ((1-firstRatio 24128) * √(1-firstRatio 24128) *
      sixthConstant (e1CovarianceRatio 24128 (mW 12064) (1/10^6) rowEps))) /
    (712/10000 - 24128*(1+1/10^6)*((1072641/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24128 (mW 12064) /
    ((1/10^5) * ((mW 12064 : ℝ)*24128*((mW 12064 : ℝ)+24128+1)))^2 +
  8*(mW 12064 : ℝ)*24128*(24128+2)*(24128+3) /
    ((1/1000)*((mW 12064 : ℝ)*24128*(24128+2)))^2 +
  covarianceVarianceBound 24128 (mW 12064) /
    ((1/1000)*covarianceMeanBound 24128 (mW 12064))^2 +
  normVarianceBound 24128 (mW 12064) / (3*inputVarianceMean 24128 (mW 12064))^2

end BstLean.Part281.WorldRow12064
namespace BstLean.Part281.WorldRow12065
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12065 = 192905958265060 := by
  have hu : mW 12065 ≤ 192905958265060 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12065 ≤ 192905958265059 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12065)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24130 ^ 2)
    ((5000000000000000000/758066307311217108442811))
    ((25000000000000000000/3790174456923406052540067)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24130) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24130 : ℝ)^2 / (mW 12065 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1072551/500000000000))/2) * ((1-firstRatio 24130) * √(1-firstRatio 24130) *
      sixthConstant (e1CovarianceRatio 24130 (mW 12065) (1/10^6) rowEps))) /
    (712/10000 - 24130*(1+1/10^6)*((1072551/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24130 (mW 12065) /
    ((1/10^5) * ((mW 12065 : ℝ)*24130*((mW 12065 : ℝ)+24130+1)))^2 +
  8*(mW 12065 : ℝ)*24130*(24130+2)*(24130+3) /
    ((1/1000)*((mW 12065 : ℝ)*24130*(24130+2)))^2 +
  covarianceVarianceBound 24130 (mW 12065) /
    ((1/1000)*covarianceMeanBound 24130 (mW 12065))^2 +
  normVarianceBound 24130 (mW 12065) / (3*inputVarianceMean 24130 (mW 12065))^2

end BstLean.Part281.WorldRow12065
namespace BstLean.Part281.WorldRow12066
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12066 = 192961925178298 := by
  have hu : mW 12066 ≤ 192961925178298 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12066 ≤ 192961925178297 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12066)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24132 ^ 2)
    ((12500000000000000000/1895322847910722260768951))
    ((25000000000000000000/3790488616188765031863913)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24132) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24132 : ℝ)^2 / (mW 12066 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1072461/500000000000))/2) * ((1-firstRatio 24132) * √(1-firstRatio 24132) *
      sixthConstant (e1CovarianceRatio 24132 (mW 12066) (1/10^6) rowEps))) /
    (712/10000 - 24132*(1+1/10^6)*((1072461/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24132 (mW 12066) /
    ((1/10^5) * ((mW 12066 : ℝ)*24132*((mW 12066 : ℝ)+24132+1)))^2 +
  8*(mW 12066 : ℝ)*24132*(24132+2)*(24132+3) /
    ((1/1000)*((mW 12066 : ℝ)*24132*(24132+2)))^2 +
  covarianceVarianceBound 24132 (mW 12066) /
    ((1/1000)*covarianceMeanBound 24132 (mW 12066))^2 +
  normVarianceBound 24132 (mW 12066) / (3*inputVarianceMean 24132 (mW 12066))^2

end BstLean.Part281.WorldRow12066
namespace BstLean.Part281.WorldRow12067
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12067 = 193017903688734 := by
  have hu : mW 12067 ≤ 193017903688734 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12067 ≤ 193017903688733 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12067)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24134 ^ 2)
    ((25000000000000000000/3790959855086803500861749))
    ((25000000000000000000/3790802775454124011187759)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24134) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24134 : ℝ)^2 / (mW 12067 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1072371/500000000000))/2) * ((1-firstRatio 24134) * √(1-firstRatio 24134) *
      sixthConstant (e1CovarianceRatio 24134 (mW 12067) (1/10^6) rowEps))) /
    (712/10000 - 24134*(1+1/10^6)*((1072371/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24134 (mW 12067) /
    ((1/10^5) * ((mW 12067 : ℝ)*24134*((mW 12067 : ℝ)+24134+1)))^2 +
  8*(mW 12067 : ℝ)*24134*(24134+2)*(24134+3) /
    ((1/1000)*((mW 12067 : ℝ)*24134*(24134+2)))^2 +
  covarianceVarianceBound 24134 (mW 12067) /
    ((1/1000)*covarianceMeanBound 24134 (mW 12067))^2 +
  normVarianceBound 24134 (mW 12067) / (3*inputVarianceMean 24134 (mW 12067))^2

end BstLean.Part281.WorldRow12067
namespace BstLean.Part281.WorldRow12068
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12068 = 193073893797808 := by
  have hu : mW 12068 ≤ 193073893797808 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12068 ≤ 193073893797807 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12068)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24136 ^ 2)
    ((6250000000000000000/947818503588040620046399))
    ((5000000000000000000/758223386943896598102321)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24136) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24136 : ℝ)^2 / (mW 12068 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2144563/1000000000000))/2) * ((1-firstRatio 24136) * √(1-firstRatio 24136) *
      sixthConstant (e1CovarianceRatio 24136 (mW 12068) (1/10^6) rowEps))) /
    (712/10000 - 24136*(1+1/10^6)*((2144563/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24136 (mW 12068) /
    ((1/10^5) * ((mW 12068 : ℝ)*24136*((mW 12068 : ℝ)+24136+1)))^2 +
  8*(mW 12068 : ℝ)*24136*(24136+2)*(24136+3) /
    ((1/1000)*((mW 12068 : ℝ)*24136*(24136+2)))^2 +
  covarianceVarianceBound 24136 (mW 12068) /
    ((1/1000)*covarianceMeanBound 24136 (mW 12068))^2 +
  normVarianceBound 24136 (mW 12068) / (3*inputVarianceMean 24136 (mW 12068))^2

end BstLean.Part281.WorldRow12068
namespace BstLean.Part281.WorldRow12069
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12069 = 193129895506962 := by
  have hu : mW 12069 ≤ 193129895506962 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12069 ≤ 193129895506961 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12069)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24138 ^ 2)
    ((25000000000000000000/3791588173617521459509443))
    ((25000000000000000000/3791431093984841969835451)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24138) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24138 : ℝ)^2 / (mW 12069 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2144383/1000000000000))/2) * ((1-firstRatio 24138) * √(1-firstRatio 24138) *
      sixthConstant (e1CovarianceRatio 24138 (mW 12069) (1/10^6) rowEps))) /
    (712/10000 - 24138*(1+1/10^6)*((2144383/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24138 (mW 12069) /
    ((1/10^5) * ((mW 12069 : ℝ)*24138*((mW 12069 : ℝ)+24138+1)))^2 +
  8*(mW 12069 : ℝ)*24138*(24138+2)*(24138+3) /
    ((1/1000)*((mW 12069 : ℝ)*24138*(24138+2)))^2 +
  covarianceVarianceBound 24138 (mW 12069) /
    ((1/1000)*covarianceMeanBound 24138 (mW 12069))^2 +
  normVarianceBound 24138 (mW 12069) / (3*inputVarianceMean 24138 (mW 12069))^2

end BstLean.Part281.WorldRow12069
namespace BstLean.Part281.WorldRow12070
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12070 = 193185908817639 := by
  have hu : mW 12070 ≤ 193185908817639 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12070 ≤ 193185908817638 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12070)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24140 ^ 2)
    ((2500000000000000000/379190233288288043883329))
    ((25000000000000000000/3791745253250200949159297)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24140) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24140 : ℝ)^2 / (mW 12070 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2144203/1000000000000))/2) * ((1-firstRatio 24140) * √(1-firstRatio 24140) *
      sixthConstant (e1CovarianceRatio 24140 (mW 12070) (1/10^6) rowEps))) /
    (712/10000 - 24140*(1+1/10^6)*((2144203/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24140 (mW 12070) /
    ((1/10^5) * ((mW 12070 : ℝ)*24140*((mW 12070 : ℝ)+24140+1)))^2 +
  8*(mW 12070 : ℝ)*24140*(24140+2)*(24140+3) /
    ((1/1000)*((mW 12070 : ℝ)*24140*(24140+2)))^2 +
  covarianceVarianceBound 24140 (mW 12070) /
    ((1/1000)*covarianceMeanBound 24140 (mW 12070))^2 +
  normVarianceBound 24140 (mW 12070) / (3*inputVarianceMean 24140 (mW 12070))^2

end BstLean.Part281.WorldRow12070
namespace BstLean.Part281.WorldRow12071
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12071 = 193241933731281 := by
  have hu : mW 12071 ≤ 193241933731281 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12071 ≤ 193241933731280 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12071)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24142 ^ 2)
    ((25000000000000000000/3792216492148239418157137))
    ((25000000000000000000/3792059412515559928483143)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24142) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24142 : ℝ)^2 / (mW 12071 : ℝ)) * (1 + 1/10^6)^2 *
    √(((268003/125000000000))/2) * ((1-firstRatio 24142) * √(1-firstRatio 24142) *
      sixthConstant (e1CovarianceRatio 24142 (mW 12071) (1/10^6) rowEps))) /
    (712/10000 - 24142*(1+1/10^6)*((268003/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24142 (mW 12071) /
    ((1/10^5) * ((mW 12071 : ℝ)*24142*((mW 12071 : ℝ)+24142+1)))^2 +
  8*(mW 12071 : ℝ)*24142*(24142+2)*(24142+3) /
    ((1/1000)*((mW 12071 : ℝ)*24142*(24142+2)))^2 +
  covarianceVarianceBound 24142 (mW 12071) /
    ((1/1000)*covarianceMeanBound 24142 (mW 12071))^2 +
  normVarianceBound 24142 (mW 12071) / (3*inputVarianceMean 24142 (mW 12071))^2

end BstLean.Part281.WorldRow12071
namespace BstLean.Part281.WorldRow12072
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12072 = 193297970249329 := by
  have hu : mW 12072 ≤ 193297970249329 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12072 ≤ 193297970249328 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12072)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24144 ^ 2)
    ((3125000000000000000/474066331426699799685123))
    ((25000000000000000000/3792373571780918907806989)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24144) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24144 : ℝ)^2 / (mW 12072 : ℝ)) * (1 + 1/10^6)^2 *
    √(((535961/250000000000))/2) * ((1-firstRatio 24144) * √(1-firstRatio 24144) *
      sixthConstant (e1CovarianceRatio 24144 (mW 12072) (1/10^6) rowEps))) /
    (712/10000 - 24144*(1+1/10^6)*((535961/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24144 (mW 12072) /
    ((1/10^5) * ((mW 12072 : ℝ)*24144*((mW 12072 : ℝ)+24144+1)))^2 +
  8*(mW 12072 : ℝ)*24144*(24144+2)*(24144+3) /
    ((1/1000)*((mW 12072 : ℝ)*24144*(24144+2)))^2 +
  covarianceVarianceBound 24144 (mW 12072) /
    ((1/1000)*covarianceMeanBound 24144 (mW 12072))^2 +
  normVarianceBound 24144 (mW 12072) / (3*inputVarianceMean 24144 (mW 12072))^2

end BstLean.Part281.WorldRow12072
namespace BstLean.Part281.WorldRow12073
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12073 = 193354018373225 := by
  have hu : mW 12073 ≤ 193354018373225 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12073 ≤ 193354018373224 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12073)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24146 ^ 2)
    ((25000000000000000000/3792844810678957376804831))
    ((5000000000000000000/758537546209255577426167)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24146) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24146 : ℝ)^2 / (mW 12073 : ℝ)) * (1 + 1/10^6)^2 *
    √(((133979/62500000000))/2) * ((1-firstRatio 24146) * √(1-firstRatio 24146) *
      sixthConstant (e1CovarianceRatio 24146 (mW 12073) (1/10^6) rowEps))) /
    (712/10000 - 24146*(1+1/10^6)*((133979/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24146 (mW 12073) /
    ((1/10^5) * ((mW 12073 : ℝ)*24146*((mW 12073 : ℝ)+24146+1)))^2 +
  8*(mW 12073 : ℝ)*24146*(24146+2)*(24146+3) /
    ((1/1000)*((mW 12073 : ℝ)*24146*(24146+2)))^2 +
  covarianceVarianceBound 24146 (mW 12073) /
    ((1/1000)*covarianceMeanBound 24146 (mW 12073))^2 +
  normVarianceBound 24146 (mW 12073) / (3*inputVarianceMean 24146 (mW 12073))^2

end BstLean.Part281.WorldRow12073
namespace BstLean.Part281.WorldRow12074
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12074 = 193410078104412 := by
  have hu : mW 12074 ≤ 193410078104412 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12074 ≤ 193410078104411 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12074)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24148 ^ 2)
    ((12500000000000000000/1896579484972158178064339))
    ((25000000000000000000/3793001890311636866454681)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24148) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24148 : ℝ)^2 / (mW 12074 : ℝ)) * (1 + 1/10^6)^2 *
    √(((428697/200000000000))/2) * ((1-firstRatio 24148) * √(1-firstRatio 24148) *
      sixthConstant (e1CovarianceRatio 24148 (mW 12074) (1/10^6) rowEps))) /
    (712/10000 - 24148*(1+1/10^6)*((428697/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24148 (mW 12074) /
    ((1/10^5) * ((mW 12074 : ℝ)*24148*((mW 12074 : ℝ)+24148+1)))^2 +
  8*(mW 12074 : ℝ)*24148*(24148+2)*(24148+3) /
    ((1/1000)*((mW 12074 : ℝ)*24148*(24148+2)))^2 +
  covarianceVarianceBound 24148 (mW 12074) /
    ((1/1000)*covarianceMeanBound 24148 (mW 12074))^2 +
  normVarianceBound 24148 (mW 12074) / (3*inputVarianceMean 24148 (mW 12074))^2

end BstLean.Part281.WorldRow12074
namespace BstLean.Part281.WorldRow12075
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12075 = 193466149444331 := by
  have hu : mW 12075 ≤ 193466149444331 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12075 ≤ 193466149444330 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12075)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24150 ^ 2)
    ((1000000000000000000/151738925168387013418101))
    ((25000000000000000000/3793316049576995845778527)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24150) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24150 : ℝ)^2 / (mW 12075 : ℝ)) * (1 + 1/10^6)^2 *
    √(((428661/200000000000))/2) * ((1-firstRatio 24150) * √(1-firstRatio 24150) *
      sixthConstant (e1CovarianceRatio 24150 (mW 12075) (1/10^6) rowEps))) /
    (712/10000 - 24150*(1+1/10^6)*((428661/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24150 (mW 12075) /
    ((1/10^5) * ((mW 12075 : ℝ)*24150*((mW 12075 : ℝ)+24150+1)))^2 +
  8*(mW 12075 : ℝ)*24150*(24150+2)*(24150+3) /
    ((1/1000)*((mW 12075 : ℝ)*24150*(24150+2)))^2 +
  covarianceVarianceBound 24150 (mW 12075) /
    ((1/1000)*covarianceMeanBound 24150 (mW 12075))^2 +
  normVarianceBound 24150 (mW 12075) / (3*inputVarianceMean 24150 (mW 12075))^2

end BstLean.Part281.WorldRow12075
namespace BstLean.Part281.WorldRow12076
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12076 = 193522232394425 := by
  have hu : mW 12076 ≤ 193522232394425 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12076 ≤ 193522232394424 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12076)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24152 ^ 2)
    ((6250000000000000000/948446822118758578694093))
    ((25000000000000000000/3793630208842354825102373)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24152) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24152 : ℝ)^2 / (mW 12076 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1071563/500000000000))/2) * ((1-firstRatio 24152) * √(1-firstRatio 24152) *
      sixthConstant (e1CovarianceRatio 24152 (mW 12076) (1/10^6) rowEps))) /
    (712/10000 - 24152*(1+1/10^6)*((1071563/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24152 (mW 12076) /
    ((1/10^5) * ((mW 12076 : ℝ)*24152*((mW 12076 : ℝ)+24152+1)))^2 +
  8*(mW 12076 : ℝ)*24152*(24152+2)*(24152+3) /
    ((1/1000)*((mW 12076 : ℝ)*24152*(24152+2)))^2 +
  covarianceVarianceBound 24152 (mW 12076) /
    ((1/1000)*covarianceMeanBound 24152 (mW 12076))^2 +
  normVarianceBound 24152 (mW 12076) / (3*inputVarianceMean 24152 (mW 12076))^2

end BstLean.Part281.WorldRow12076
namespace BstLean.Part281.WorldRow12077
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12077 = 193578326956137 := by
  have hu : mW 12077 ≤ 193578326956137 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12077 ≤ 193578326956136 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12077)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24154 ^ 2)
    ((25000000000000000000/3794101447740393294100219))
    ((25000000000000000000/3793944368107713804426219)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24154) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24154 : ℝ)^2 / (mW 12077 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1071473/500000000000))/2) * ((1-firstRatio 24154) * √(1-firstRatio 24154) *
      sixthConstant (e1CovarianceRatio 24154 (mW 12077) (1/10^6) rowEps))) /
    (712/10000 - 24154*(1+1/10^6)*((1071473/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24154 (mW 12077) /
    ((1/10^5) * ((mW 12077 : ℝ)*24154*((mW 12077 : ℝ)+24154+1)))^2 +
  8*(mW 12077 : ℝ)*24154*(24154+2)*(24154+3) /
    ((1/1000)*((mW 12077 : ℝ)*24154*(24154+2)))^2 +
  covarianceVarianceBound 24154 (mW 12077) /
    ((1/1000)*covarianceMeanBound 24154 (mW 12077))^2 +
  normVarianceBound 24154 (mW 12077) / (3*inputVarianceMean 24154 (mW 12077))^2

end BstLean.Part281.WorldRow12077
namespace BstLean.Part281.WorldRow12078
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12078 = 193634433130908 := by
  have hu : mW 12078 ≤ 193634433130908 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12078 ≤ 193634433130907 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12078)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24156 ^ 2)
    ((12500000000000000000/1897207803502876136712033))
    ((5000000000000000000/758851705474614556750013)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24156) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24156 : ℝ)^2 / (mW 12078 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2142767/1000000000000))/2) * ((1-firstRatio 24156) * √(1-firstRatio 24156) *
      sixthConstant (e1CovarianceRatio 24156 (mW 12078) (1/10^6) rowEps))) /
    (712/10000 - 24156*(1+1/10^6)*((2142767/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24156 (mW 12078) /
    ((1/10^5) * ((mW 12078 : ℝ)*24156*((mW 12078 : ℝ)+24156+1)))^2 +
  8*(mW 12078 : ℝ)*24156*(24156+2)*(24156+3) /
    ((1/1000)*((mW 12078 : ℝ)*24156*(24156+2)))^2 +
  covarianceVarianceBound 24156 (mW 12078) /
    ((1/1000)*covarianceMeanBound 24156 (mW 12078))^2 +
  normVarianceBound 24156 (mW 12078) / (3*inputVarianceMean 24156 (mW 12078))^2

end BstLean.Part281.WorldRow12078
namespace BstLean.Part281.WorldRow12079
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12079 = 193690550920181 := by
  have hu : mW 12079 ≤ 193690550920181 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12079 ≤ 193690550920180 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12079)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24158 ^ 2)
    ((25000000000000000000/3794729766271111252747913))
    ((25000000000000000000/3794572686638431763073911)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24158) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24158 : ℝ)^2 / (mW 12079 : ℝ)) * (1 + 1/10^6)^2 *
    √(((535647/250000000000))/2) * ((1-firstRatio 24158) * √(1-firstRatio 24158) *
      sixthConstant (e1CovarianceRatio 24158 (mW 12079) (1/10^6) rowEps))) /
    (712/10000 - 24158*(1+1/10^6)*((535647/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24158 (mW 12079) /
    ((1/10^5) * ((mW 12079 : ℝ)*24158*((mW 12079 : ℝ)+24158+1)))^2 +
  8*(mW 12079 : ℝ)*24158*(24158+2)*(24158+3) /
    ((1/1000)*((mW 12079 : ℝ)*24158*(24158+2)))^2 +
  covarianceVarianceBound 24158 (mW 12079) /
    ((1/1000)*covarianceMeanBound 24158 (mW 12079))^2 +
  normVarianceBound 24158 (mW 12079) / (3*inputVarianceMean 24158 (mW 12079))^2

end BstLean.Part281.WorldRow12079
namespace BstLean.Part281.WorldRow12080
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12080 = 193746680325398 := by
  have hu : mW 12080 ≤ 193746680325398 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12080 ≤ 193746680325397 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12080)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24160 ^ 2)
    ((312500000000000000/47438049069205877900897))
    ((25000000000000000000/3794886845903790742397757)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24160) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24160 : ℝ)^2 / (mW 12080 : ℝ)) * (1 + 1/10^6)^2 *
    √(((267801/125000000000))/2) * ((1-firstRatio 24160) * √(1-firstRatio 24160) *
      sixthConstant (e1CovarianceRatio 24160 (mW 12080) (1/10^6) rowEps))) /
    (712/10000 - 24160*(1+1/10^6)*((267801/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24160 (mW 12080) /
    ((1/10^5) * ((mW 12080 : ℝ)*24160*((mW 12080 : ℝ)+24160+1)))^2 +
  8*(mW 12080 : ℝ)*24160*(24160+2)*(24160+3) /
    ((1/1000)*((mW 12080 : ℝ)*24160*(24160+2)))^2 +
  covarianceVarianceBound 24160 (mW 12080) /
    ((1/1000)*covarianceMeanBound 24160 (mW 12080))^2 +
  normVarianceBound 24160 (mW 12080) / (3*inputVarianceMean 24160 (mW 12080))^2

end BstLean.Part281.WorldRow12080
namespace BstLean.Part281.WorldRow12081
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12081 = 193802821348003 := by
  have hu : mW 12081 ≤ 193802821348003 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12081 ≤ 193802821348002 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12081)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24162 ^ 2)
    ((25000000000000000000/3795358084801829211395607))
    ((25000000000000000000/3795201005169149721721603)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24162) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24162 : ℝ)^2 / (mW 12081 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2142229/1000000000000))/2) * ((1-firstRatio 24162) * √(1-firstRatio 24162) *
      sixthConstant (e1CovarianceRatio 24162 (mW 12081) (1/10^6) rowEps))) /
    (712/10000 - 24162*(1+1/10^6)*((2142229/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24162 (mW 12081) /
    ((1/10^5) * ((mW 12081 : ℝ)*24162*((mW 12081 : ℝ)+24162+1)))^2 +
  8*(mW 12081 : ℝ)*24162*(24162+2)*(24162+3) /
    ((1/1000)*((mW 12081 : ℝ)*24162*(24162+2)))^2 +
  covarianceVarianceBound 24162 (mW 12081) /
    ((1/1000)*covarianceMeanBound 24162 (mW 12081))^2 +
  normVarianceBound 24162 (mW 12081) / (3*inputVarianceMean 24162 (mW 12081))^2

end BstLean.Part281.WorldRow12081
namespace BstLean.Part281.WorldRow12082
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12082 = 193858973989436 := by
  have hu : mW 12082 ≤ 193858973989436 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12082 ≤ 193858973989435 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12082)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24164 ^ 2)
    ((12500000000000000000/1897836122033594095359727))
    ((25000000000000000000/3795515164434508701045449)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24164) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24164 : ℝ)^2 / (mW 12082 : ℝ)) * (1 + 1/10^6)^2 *
    √(((42841/20000000000))/2) * ((1-firstRatio 24164) * √(1-firstRatio 24164) *
      sixthConstant (e1CovarianceRatio 24164 (mW 12082) (1/10^6) rowEps))) /
    (712/10000 - 24164*(1+1/10^6)*((42841/20000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24164 (mW 12082) /
    ((1/10^5) * ((mW 12082 : ℝ)*24164*((mW 12082 : ℝ)+24164+1)))^2 +
  8*(mW 12082 : ℝ)*24164*(24164+2)*(24164+3) /
    ((1/1000)*((mW 12082 : ℝ)*24164*(24164+2)))^2 +
  covarianceVarianceBound 24164 (mW 12082) /
    ((1/1000)*covarianceMeanBound 24164 (mW 12082))^2 +
  normVarianceBound 24164 (mW 12082) / (3*inputVarianceMean 24164 (mW 12082))^2

end BstLean.Part281.WorldRow12082
namespace BstLean.Part281.WorldRow12083
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12083 = 193915138251143 := by
  have hu : mW 12083 ≤ 193915138251143 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12083 ≤ 193915138251142 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12083)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24166 ^ 2)
    ((25000000000000000000/3795986403332547170043301))
    ((5000000000000000000/759165864739973536073859)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24166) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24166 : ℝ)^2 / (mW 12083 : ℝ)) * (1 + 1/10^6)^2 *
    √(((214187/100000000000))/2) * ((1-firstRatio 24166) * √(1-firstRatio 24166) *
      sixthConstant (e1CovarianceRatio 24166 (mW 12083) (1/10^6) rowEps))) /
    (712/10000 - 24166*(1+1/10^6)*((214187/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24166 (mW 12083) /
    ((1/10^5) * ((mW 12083 : ℝ)*24166*((mW 12083 : ℝ)+24166+1)))^2 +
  8*(mW 12083 : ℝ)*24166*(24166+2)*(24166+3) /
    ((1/1000)*((mW 12083 : ℝ)*24166*(24166+2)))^2 +
  covarianceVarianceBound 24166 (mW 12083) /
    ((1/1000)*covarianceMeanBound 24166 (mW 12083))^2 +
  normVarianceBound 24166 (mW 12083) / (3*inputVarianceMean 24166 (mW 12083))^2

end BstLean.Part281.WorldRow12083
