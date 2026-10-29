import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part281Scalar10
namespace BstLean.Part281.WorldRow12109
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12109 = 195379492498557 := by
  have hu : mW 12109 ≤ 195379492498557 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12109 ≤ 195379492498556 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12109)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24218 ^ 2)
    ((25000000000000000000/3804154544231880632463323))
    ((25000000000000000000/3803997464599201142789291)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24218) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24218 : ℝ)^2 / (mW 12109 : ℝ)) * (1 + 1/10^6)^2 *
    √(((106861/50000000000))/2) * ((1-firstRatio 24218) * √(1-firstRatio 24218) *
      sixthConstant (e1CovarianceRatio 24218 (mW 12109) (1/10^6) rowEps))) /
    (712/10000 - 24218*(1+1/10^6)*((106861/50000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24218 (mW 12109) /
    ((1/10^5) * ((mW 12109 : ℝ)*24218*((mW 12109 : ℝ)+24218+1)))^2 +
  8*(mW 12109 : ℝ)*24218*(24218+2)*(24218+3) /
    ((1/1000)*((mW 12109 : ℝ)*24218*(24218+2)))^2 +
  covarianceVarianceBound 24218 (mW 12109) /
    ((1/1000)*covarianceMeanBound 24218 (mW 12109))^2 +
  normVarianceBound 24218 (mW 12109) / (3*inputVarianceMean 24218 (mW 12109))^2

end BstLean.Part281.WorldRow12109
namespace BstLean.Part281.WorldRow12110
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12110 = 195435971053150 := by
  have hu : mW 12110 ≤ 195435971053150 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12110 ≤ 195435971053149 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12110)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24220 ^ 2)
    ((2500000000000000000/380446870349723961178717))
    ((25000000000000000000/3804311623864560122113137)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24220) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24220 : ℝ)^2 / (mW 12110 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2137041/1000000000000))/2) * ((1-firstRatio 24220) * √(1-firstRatio 24220) *
      sixthConstant (e1CovarianceRatio 24220 (mW 12110) (1/10^6) rowEps))) /
    (712/10000 - 24220*(1+1/10^6)*((2137041/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24220 (mW 12110) /
    ((1/10^5) * ((mW 12110 : ℝ)*24220*((mW 12110 : ℝ)+24220+1)))^2 +
  8*(mW 12110 : ℝ)*24220*(24220+2)*(24220+3) /
    ((1/1000)*((mW 12110 : ℝ)*24220*(24220+2)))^2 +
  covarianceVarianceBound 24220 (mW 12110) /
    ((1/1000)*covarianceMeanBound 24220 (mW 12110))^2 +
  normVarianceBound 24220 (mW 12110) / (3*inputVarianceMean 24220 (mW 12110))^2

end BstLean.Part281.WorldRow12110
namespace BstLean.Part281.WorldRow12111
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12111 = 195492461268434 := by
  have hu : mW 12111 ≤ 195492461268434 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12111 ≤ 195492461268433 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12111)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24222 ^ 2)
    ((25000000000000000000/3804782862762598591111017))
    ((25000000000000000000/3804625783129919101436983)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24222) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24222 : ℝ)^2 / (mW 12111 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2136863/1000000000000))/2) * ((1-firstRatio 24222) * √(1-firstRatio 24222) *
      sixthConstant (e1CovarianceRatio 24222 (mW 12111) (1/10^6) rowEps))) /
    (712/10000 - 24222*(1+1/10^6)*((2136863/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24222 (mW 12111) /
    ((1/10^5) * ((mW 12111 : ℝ)*24222*((mW 12111 : ℝ)+24222+1)))^2 +
  8*(mW 12111 : ℝ)*24222*(24222+2)*(24222+3) /
    ((1/1000)*((mW 12111 : ℝ)*24222*(24222+2)))^2 +
  covarianceVarianceBound 24222 (mW 12111) /
    ((1/1000)*covarianceMeanBound 24222 (mW 12111))^2 +
  normVarianceBound 24222 (mW 12111) / (3*inputVarianceMean 24222 (mW 12111))^2

end BstLean.Part281.WorldRow12111
namespace BstLean.Part281.WorldRow12112
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12112 = 195548963145852 := by
  have hu : mW 12112 ≤ 195548963145852 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12112 ≤ 195548963145851 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12112)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24224 ^ 2)
    ((1562500000000000000/237818563876747348152179))
    ((25000000000000000000/3804939942395278080760829)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24224) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24224 : ℝ)^2 / (mW 12112 : ℝ)) * (1 + 1/10^6)^2 *
    √(((534171/250000000000))/2) * ((1-firstRatio 24224) * √(1-firstRatio 24224) *
      sixthConstant (e1CovarianceRatio 24224 (mW 12112) (1/10^6) rowEps))) /
    (712/10000 - 24224*(1+1/10^6)*((534171/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24224 (mW 12112) /
    ((1/10^5) * ((mW 12112 : ℝ)*24224*((mW 12112 : ℝ)+24224+1)))^2 +
  8*(mW 12112 : ℝ)*24224*(24224+2)*(24224+3) /
    ((1/1000)*((mW 12112 : ℝ)*24224*(24224+2)))^2 +
  covarianceVarianceBound 24224 (mW 12112) /
    ((1/1000)*covarianceMeanBound 24224 (mW 12112))^2 +
  normVarianceBound 24224 (mW 12112) / (3*inputVarianceMean 24224 (mW 12112))^2

end BstLean.Part281.WorldRow12112
namespace BstLean.Part281.WorldRow12113
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12113 = 195605476686850 := by
  have hu : mW 12113 ≤ 195605476686850 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12113 ≤ 195605476686849 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12113)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24226 ^ 2)
    ((25000000000000000000/3805411181293316549758711))
    ((1000000000000000000/152210164066425482403387)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24226) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24226 : ℝ)^2 / (mW 12113 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1068253/500000000000))/2) * ((1-firstRatio 24226) * √(1-firstRatio 24226) *
      sixthConstant (e1CovarianceRatio 24226 (mW 12113) (1/10^6) rowEps))) /
    (712/10000 - 24226*(1+1/10^6)*((1068253/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24226 (mW 12113) /
    ((1/10^5) * ((mW 12113 : ℝ)*24226*((mW 12113 : ℝ)+24226+1)))^2 +
  8*(mW 12113 : ℝ)*24226*(24226+2)*(24226+3) /
    ((1/1000)*((mW 12113 : ℝ)*24226*(24226+2)))^2 +
  covarianceVarianceBound 24226 (mW 12113) /
    ((1/1000)*covarianceMeanBound 24226 (mW 12113))^2 +
  normVarianceBound 24226 (mW 12113) / (3*inputVarianceMean 24226 (mW 12113))^2

end BstLean.Part281.WorldRow12113
namespace BstLean.Part281.WorldRow12114
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12114 = 195662001892871 := by
  have hu : mW 12114 ≤ 195662001892871 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12114 ≤ 195662001892870 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12114)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24228 ^ 2)
    ((12500000000000000000/1902862670279337764541279))
    ((25000000000000000000/3805568260925996039408521)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24228) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24228 : ℝ)^2 / (mW 12114 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2136327/1000000000000))/2) * ((1-firstRatio 24228) * √(1-firstRatio 24228) *
      sixthConstant (e1CovarianceRatio 24228 (mW 12114) (1/10^6) rowEps))) /
    (712/10000 - 24228*(1+1/10^6)*((2136327/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24228 (mW 12114) /
    ((1/10^5) * ((mW 12114 : ℝ)*24228*((mW 12114 : ℝ)+24228+1)))^2 +
  8*(mW 12114 : ℝ)*24228*(24228+2)*(24228+3) /
    ((1/1000)*((mW 12114 : ℝ)*24228*(24228+2)))^2 +
  covarianceVarianceBound 24228 (mW 12114) /
    ((1/1000)*covarianceMeanBound 24228 (mW 12114))^2 +
  normVarianceBound 24228 (mW 12114) / (3*inputVarianceMean 24228 (mW 12114))^2

end BstLean.Part281.WorldRow12114
namespace BstLean.Part281.WorldRow12115
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12115 = 195718538765361 := by
  have hu : mW 12115 ≤ 195718538765361 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12115 ≤ 195718538765360 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12115)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24230 ^ 2)
    ((5000000000000000000/761207899964806901681281))
    ((25000000000000000000/3805882420191355018732367)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24230) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24230 : ℝ)^2 / (mW 12115 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2136149/1000000000000))/2) * ((1-firstRatio 24230) * √(1-firstRatio 24230) *
      sixthConstant (e1CovarianceRatio 24230 (mW 12115) (1/10^6) rowEps))) /
    (712/10000 - 24230*(1+1/10^6)*((2136149/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24230 (mW 12115) /
    ((1/10^5) * ((mW 12115 : ℝ)*24230*((mW 12115 : ℝ)+24230+1)))^2 +
  8*(mW 12115 : ℝ)*24230*(24230+2)*(24230+3) /
    ((1/1000)*((mW 12115 : ℝ)*24230*(24230+2)))^2 +
  covarianceVarianceBound 24230 (mW 12115) /
    ((1/1000)*covarianceMeanBound 24230 (mW 12115))^2 +
  normVarianceBound 24230 (mW 12115) / (3*inputVarianceMean 24230 (mW 12115))^2

end BstLean.Part281.WorldRow12115
namespace BstLean.Part281.WorldRow12116
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12116 = 195775087305763 := by
  have hu : mW 12116 ≤ 195775087305763 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12116 ≤ 195775087305762 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12116)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24232 ^ 2)
    ((6250000000000000000/951588414772348371932563))
    ((25000000000000000000/3806196579456713998056213)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24232) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24232 : ℝ)^2 / (mW 12116 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2135971/1000000000000))/2) * ((1-firstRatio 24232) * √(1-firstRatio 24232) *
      sixthConstant (e1CovarianceRatio 24232 (mW 12116) (1/10^6) rowEps))) /
    (712/10000 - 24232*(1+1/10^6)*((2135971/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24232 (mW 12116) /
    ((1/10^5) * ((mW 12116 : ℝ)*24232*((mW 12116 : ℝ)+24232+1)))^2 +
  8*(mW 12116 : ℝ)*24232*(24232+2)*(24232+3) /
    ((1/1000)*((mW 12116 : ℝ)*24232*(24232+2)))^2 +
  covarianceVarianceBound 24232 (mW 12116) /
    ((1/1000)*covarianceMeanBound 24232 (mW 12116))^2 +
  normVarianceBound 24232 (mW 12116) / (3*inputVarianceMean 24232 (mW 12116))^2

end BstLean.Part281.WorldRow12116
namespace BstLean.Part281.WorldRow12117
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12117 = 195831647515524 := by
  have hu : mW 12117 ≤ 195831647515524 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12117 ≤ 195831647515523 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12117)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24234 ^ 2)
    ((25000000000000000000/3806667818354752467054099))
    ((25000000000000000000/3806510738722072977380059)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24234) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24234 : ℝ)^2 / (mW 12117 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2135793/1000000000000))/2) * ((1-firstRatio 24234) * √(1-firstRatio 24234) *
      sixthConstant (e1CovarianceRatio 24234 (mW 12117) (1/10^6) rowEps))) /
    (712/10000 - 24234*(1+1/10^6)*((2135793/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24234 (mW 12117) /
    ((1/10^5) * ((mW 12117 : ℝ)*24234*((mW 12117 : ℝ)+24234+1)))^2 +
  8*(mW 12117 : ℝ)*24234*(24234+2)*(24234+3) /
    ((1/1000)*((mW 12117 : ℝ)*24234*(24234+2)))^2 +
  covarianceVarianceBound 24234 (mW 12117) /
    ((1/1000)*covarianceMeanBound 24234 (mW 12117))^2 +
  normVarianceBound 24234 (mW 12117) / (3*inputVarianceMean 24234 (mW 12117))^2

end BstLean.Part281.WorldRow12117
namespace BstLean.Part281.WorldRow12118
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12118 = 195888219396086 := by
  have hu : mW 12118 ≤ 195888219396086 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12118 ≤ 195888219396085 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12118)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24236 ^ 2)
    ((12500000000000000000/1903490988810055723188973))
    ((5000000000000000000/761364979597486391340781)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24236) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24236 : ℝ)^2 / (mW 12118 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1067807/500000000000))/2) * ((1-firstRatio 24236) * √(1-firstRatio 24236) *
      sixthConstant (e1CovarianceRatio 24236 (mW 12118) (1/10^6) rowEps))) /
    (712/10000 - 24236*(1+1/10^6)*((1067807/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24236 (mW 12118) /
    ((1/10^5) * ((mW 12118 : ℝ)*24236*((mW 12118 : ℝ)+24236+1)))^2 +
  8*(mW 12118 : ℝ)*24236*(24236+2)*(24236+3) /
    ((1/1000)*((mW 12118 : ℝ)*24236*(24236+2)))^2 +
  covarianceVarianceBound 24236 (mW 12118) /
    ((1/1000)*covarianceMeanBound 24236 (mW 12118))^2 +
  normVarianceBound 24236 (mW 12118) / (3*inputVarianceMean 24236 (mW 12118))^2

end BstLean.Part281.WorldRow12118
namespace BstLean.Part281.WorldRow12119
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12119 = 195944802948896 := by
  have hu : mW 12119 ≤ 195944802948896 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12119 ≤ 195944802948895 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12119)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24238 ^ 2)
    ((25000000000000000000/3807296136885470425701793))
    ((25000000000000000000/3807139057252790936027751)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24238) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24238 : ℝ)^2 / (mW 12119 : ℝ)) * (1 + 1/10^6)^2 *
    √(((533859/250000000000))/2) * ((1-firstRatio 24238) * √(1-firstRatio 24238) *
      sixthConstant (e1CovarianceRatio 24238 (mW 12119) (1/10^6) rowEps))) /
    (712/10000 - 24238*(1+1/10^6)*((533859/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24238 (mW 12119) /
    ((1/10^5) * ((mW 12119 : ℝ)*24238*((mW 12119 : ℝ)+24238+1)))^2 +
  8*(mW 12119 : ℝ)*24238*(24238+2)*(24238+3) /
    ((1/1000)*((mW 12119 : ℝ)*24238*(24238+2)))^2 +
  covarianceVarianceBound 24238 (mW 12119) /
    ((1/1000)*covarianceMeanBound 24238 (mW 12119))^2 +
  normVarianceBound 24238 (mW 12119) / (3*inputVarianceMean 24238 (mW 12119))^2

end BstLean.Part281.WorldRow12119
namespace BstLean.Part281.WorldRow12120
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12120 = 196001398175398 := by
  have hu : mW 12120 ≤ 196001398175398 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12120 ≤ 196001398175397 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12120)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24240 ^ 2)
    ((625000000000000000/95190257403770735125641))
    ((25000000000000000000/3807453216518149915351597)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24240) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24240 : ℝ)^2 / (mW 12120 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1067629/500000000000))/2) * ((1-firstRatio 24240) * √(1-firstRatio 24240) *
      sixthConstant (e1CovarianceRatio 24240 (mW 12120) (1/10^6) rowEps))) /
    (712/10000 - 24240*(1+1/10^6)*((1067629/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24240 (mW 12120) /
    ((1/10^5) * ((mW 12120 : ℝ)*24240*((mW 12120 : ℝ)+24240+1)))^2 +
  8*(mW 12120 : ℝ)*24240*(24240+2)*(24240+3) /
    ((1/1000)*((mW 12120 : ℝ)*24240*(24240+2)))^2 +
  covarianceVarianceBound 24240 (mW 12120) /
    ((1/1000)*covarianceMeanBound 24240 (mW 12120))^2 +
  normVarianceBound 24240 (mW 12120) / (3*inputVarianceMean 24240 (mW 12120))^2

end BstLean.Part281.WorldRow12120
namespace BstLean.Part281.WorldRow12121
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12121 = 196058005077037 := by
  have hu : mW 12121 ≤ 196058005077037 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12121 ≤ 196058005077036 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12121)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24242 ^ 2)
    ((25000000000000000000/3807924455416188384349487))
    ((25000000000000000000/3807767375783508894675443)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24242) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24242 : ℝ)^2 / (mW 12121 : ℝ)) * (1 + 1/10^6)^2 *
    √(((53377/25000000000))/2) * ((1-firstRatio 24242) * √(1-firstRatio 24242) *
      sixthConstant (e1CovarianceRatio 24242 (mW 12121) (1/10^6) rowEps))) /
    (712/10000 - 24242*(1+1/10^6)*((53377/25000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24242 (mW 12121) /
    ((1/10^5) * ((mW 12121 : ℝ)*24242*((mW 12121 : ℝ)+24242+1)))^2 +
  8*(mW 12121 : ℝ)*24242*(24242+2)*(24242+3) /
    ((1/1000)*((mW 12121 : ℝ)*24242*(24242+2)))^2 +
  covarianceVarianceBound 24242 (mW 12121) /
    ((1/1000)*covarianceMeanBound 24242 (mW 12121))^2 +
  normVarianceBound 24242 (mW 12121) / (3*inputVarianceMean 24242 (mW 12121))^2

end BstLean.Part281.WorldRow12121
namespace BstLean.Part281.WorldRow12122
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12122 = 196114623655258 := by
  have hu : mW 12122 ≤ 196114623655258 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12122 ≤ 196114623655257 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12122)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24244 ^ 2)
    ((12500000000000000000/1904119307340773681836667))
    ((25000000000000000000/3808081535048867873999289)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24244) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24244 : ℝ)^2 / (mW 12122 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1067451/500000000000))/2) * ((1-firstRatio 24244) * √(1-firstRatio 24244) *
      sixthConstant (e1CovarianceRatio 24244 (mW 12122) (1/10^6) rowEps))) /
    (712/10000 - 24244*(1+1/10^6)*((1067451/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24244 (mW 12122) /
    ((1/10^5) * ((mW 12122 : ℝ)*24244*((mW 12122 : ℝ)+24244+1)))^2 +
  8*(mW 12122 : ℝ)*24244*(24244+2)*(24244+3) /
    ((1/1000)*((mW 12122 : ℝ)*24244*(24244+2)))^2 +
  covarianceVarianceBound 24244 (mW 12122) /
    ((1/1000)*covarianceMeanBound 24244 (mW 12122))^2 +
  normVarianceBound 24244 (mW 12122) / (3*inputVarianceMean 24244 (mW 12122))^2

end BstLean.Part281.WorldRow12122
namespace BstLean.Part281.WorldRow12123
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12123 = 196171253911505 := by
  have hu : mW 12123 ≤ 196171253911505 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12123 ≤ 196171253911504 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12123)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24246 ^ 2)
    ((25000000000000000000/3808552773946906342997181))
    ((5000000000000000000/761679138862845370664627)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24246) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24246 : ℝ)^2 / (mW 12123 : ℝ)) * (1 + 1/10^6)^2 *
    √(((533681/250000000000))/2) * ((1-firstRatio 24246) * √(1-firstRatio 24246) *
      sixthConstant (e1CovarianceRatio 24246 (mW 12123) (1/10^6) rowEps))) /
    (712/10000 - 24246*(1+1/10^6)*((533681/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24246 (mW 12123) /
    ((1/10^5) * ((mW 12123 : ℝ)*24246*((mW 12123 : ℝ)+24246+1)))^2 +
  8*(mW 12123 : ℝ)*24246*(24246+2)*(24246+3) /
    ((1/1000)*((mW 12123 : ℝ)*24246*(24246+2)))^2 +
  covarianceVarianceBound 24246 (mW 12123) /
    ((1/1000)*covarianceMeanBound 24246 (mW 12123))^2 +
  normVarianceBound 24246 (mW 12123) / (3*inputVarianceMean 24246 (mW 12123))^2

end BstLean.Part281.WorldRow12123
namespace BstLean.Part281.WorldRow12124
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12124 = 196227895847225 := by
  have hu : mW 12124 ≤ 196227895847225 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12124 ≤ 196227895847224 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12124)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24248 ^ 2)
    ((6250000000000000000/952216733303066330580257))
    ((25000000000000000000/3808709853579585832646981)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24248) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24248 : ℝ)^2 / (mW 12124 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1067273/500000000000))/2) * ((1-firstRatio 24248) * √(1-firstRatio 24248) *
      sixthConstant (e1CovarianceRatio 24248 (mW 12124) (1/10^6) rowEps))) /
    (712/10000 - 24248*(1+1/10^6)*((1067273/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24248 (mW 12124) /
    ((1/10^5) * ((mW 12124 : ℝ)*24248*((mW 12124 : ℝ)+24248+1)))^2 +
  8*(mW 12124 : ℝ)*24248*(24248+2)*(24248+3) /
    ((1/1000)*((mW 12124 : ℝ)*24248*(24248+2)))^2 +
  covarianceVarianceBound 24248 (mW 12124) /
    ((1/1000)*covarianceMeanBound 24248 (mW 12124))^2 +
  normVarianceBound 24248 (mW 12124) / (3*inputVarianceMean 24248 (mW 12124))^2

end BstLean.Part281.WorldRow12124
namespace BstLean.Part281.WorldRow12125
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12125 = 196284549463862 := by
  have hu : mW 12125 ≤ 196284549463862 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12125 ≤ 196284549463861 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12125)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24250 ^ 2)
    ((200000000000000000/30473448739820994413159))
    ((25000000000000000000/3809024012844944811970827)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24250) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24250 : ℝ)^2 / (mW 12125 : ℝ)) * (1 + 1/10^6)^2 *
    √(((66699/31250000000))/2) * ((1-firstRatio 24250) * √(1-firstRatio 24250) *
      sixthConstant (e1CovarianceRatio 24250 (mW 12125) (1/10^6) rowEps))) /
    (712/10000 - 24250*(1+1/10^6)*((66699/31250000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24250 (mW 12125) /
    ((1/10^5) * ((mW 12125 : ℝ)*24250*((mW 12125 : ℝ)+24250+1)))^2 +
  8*(mW 12125 : ℝ)*24250*(24250+2)*(24250+3) /
    ((1/1000)*((mW 12125 : ℝ)*24250*(24250+2)))^2 +
  covarianceVarianceBound 24250 (mW 12125) /
    ((1/1000)*covarianceMeanBound 24250 (mW 12125))^2 +
  normVarianceBound 24250 (mW 12125) / (3*inputVarianceMean 24250 (mW 12125))^2

end BstLean.Part281.WorldRow12125
namespace BstLean.Part281.WorldRow12126
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12126 = 196341214762861 := by
  have hu : mW 12126 ≤ 196341214762861 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12126 ≤ 196341214762860 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12126)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24252 ^ 2)
    ((12500000000000000000/1904747625871491640484361))
    ((25000000000000000000/3809338172110303791294673)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24252) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24252 : ℝ)^2 / (mW 12126 : ℝ)) * (1 + 1/10^6)^2 *
    √(((213419/100000000000))/2) * ((1-firstRatio 24252) * √(1-firstRatio 24252) *
      sixthConstant (e1CovarianceRatio 24252 (mW 12126) (1/10^6) rowEps))) /
    (712/10000 - 24252*(1+1/10^6)*((213419/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24252 (mW 12126) /
    ((1/10^5) * ((mW 12126 : ℝ)*24252*((mW 12126 : ℝ)+24252+1)))^2 +
  8*(mW 12126 : ℝ)*24252*(24252+2)*(24252+3) /
    ((1/1000)*((mW 12126 : ℝ)*24252*(24252+2)))^2 +
  covarianceVarianceBound 24252 (mW 12126) /
    ((1/1000)*covarianceMeanBound 24252 (mW 12126))^2 +
  normVarianceBound 24252 (mW 12126) / (3*inputVarianceMean 24252 (mW 12126))^2

end BstLean.Part281.WorldRow12126
namespace BstLean.Part281.WorldRow12127
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12127 = 196397891745668 := by
  have hu : mW 12127 ≤ 196397891745668 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12127 ≤ 196397891745667 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12127)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24254 ^ 2)
    ((25000000000000000000/3809809411008342260292569))
    ((25000000000000000000/3809652331375662770618519)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24254) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24254 : ℝ)^2 / (mW 12127 : ℝ)) * (1 + 1/10^6)^2 *
    √(((533503/250000000000))/2) * ((1-firstRatio 24254) * √(1-firstRatio 24254) *
      sixthConstant (e1CovarianceRatio 24254 (mW 12127) (1/10^6) rowEps))) /
    (712/10000 - 24254*(1+1/10^6)*((533503/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24254 (mW 12127) /
    ((1/10^5) * ((mW 12127 : ℝ)*24254*((mW 12127 : ℝ)+24254+1)))^2 +
  8*(mW 12127 : ℝ)*24254*(24254+2)*(24254+3) /
    ((1/1000)*((mW 12127 : ℝ)*24254*(24254+2)))^2 +
  covarianceVarianceBound 24254 (mW 12127) /
    ((1/1000)*covarianceMeanBound 24254 (mW 12127))^2 +
  normVarianceBound 24254 (mW 12127) / (3*inputVarianceMean 24254 (mW 12127))^2

end BstLean.Part281.WorldRow12127
namespace BstLean.Part281.WorldRow12128
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12128 = 196454580413728 := by
  have hu : mW 12128 ≤ 196454580413728 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12128 ≤ 196454580413727 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12128)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24256 ^ 2)
    ((781250000000000000/119066361571053163738013))
    ((5000000000000000000/761993298128204349988473)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24256) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24256 : ℝ)^2 / (mW 12128 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1066917/500000000000))/2) * ((1-firstRatio 24256) * √(1-firstRatio 24256) *
      sixthConstant (e1CovarianceRatio 24256 (mW 12128) (1/10^6) rowEps))) /
    (712/10000 - 24256*(1+1/10^6)*((1066917/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24256 (mW 12128) /
    ((1/10^5) * ((mW 12128 : ℝ)*24256*((mW 12128 : ℝ)+24256+1)))^2 +
  8*(mW 12128 : ℝ)*24256*(24256+2)*(24256+3) /
    ((1/1000)*((mW 12128 : ℝ)*24256*(24256+2)))^2 +
  covarianceVarianceBound 24256 (mW 12128) /
    ((1/1000)*covarianceMeanBound 24256 (mW 12128))^2 +
  normVarianceBound 24256 (mW 12128) / (3*inputVarianceMean 24256 (mW 12128))^2

end BstLean.Part281.WorldRow12128
namespace BstLean.Part281.WorldRow12129
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12129 = 196511280768486 := by
  have hu : mW 12129 ≤ 196511280768486 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12129 ≤ 196511280768485 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12129)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24258 ^ 2)
    ((25000000000000000000/3810437729539060218940263))
    ((25000000000000000000/3810280649906380729266211)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24258) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24258 : ℝ)^2 / (mW 12129 : ℝ)) * (1 + 1/10^6)^2 *
    √(((266707/125000000000))/2) * ((1-firstRatio 24258) * √(1-firstRatio 24258) *
      sixthConstant (e1CovarianceRatio 24258 (mW 12129) (1/10^6) rowEps))) /
    (712/10000 - 24258*(1+1/10^6)*((266707/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24258 (mW 12129) /
    ((1/10^5) * ((mW 12129 : ℝ)*24258*((mW 12129 : ℝ)+24258+1)))^2 +
  8*(mW 12129 : ℝ)*24258*(24258+2)*(24258+3) /
    ((1/1000)*((mW 12129 : ℝ)*24258*(24258+2)))^2 +
  covarianceVarianceBound 24258 (mW 12129) /
    ((1/1000)*covarianceMeanBound 24258 (mW 12129))^2 +
  normVarianceBound 24258 (mW 12129) / (3*inputVarianceMean 24258 (mW 12129))^2

end BstLean.Part281.WorldRow12129
namespace BstLean.Part281.WorldRow12130
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12130 = 196567992811388 := by
  have hu : mW 12130 ≤ 196567992811388 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12130 ≤ 196567992811387 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12130)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24260 ^ 2)
    ((2500000000000000000/381075188880441919826411))
    ((25000000000000000000/3810594809171739708590057)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24260) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24260 : ℝ)^2 / (mW 12130 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1066739/500000000000))/2) * ((1-firstRatio 24260) * √(1-firstRatio 24260) *
      sixthConstant (e1CovarianceRatio 24260 (mW 12130) (1/10^6) rowEps))) /
    (712/10000 - 24260*(1+1/10^6)*((1066739/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24260 (mW 12130) /
    ((1/10^5) * ((mW 12130 : ℝ)*24260*((mW 12130 : ℝ)+24260+1)))^2 +
  8*(mW 12130 : ℝ)*24260*(24260+2)*(24260+3) /
    ((1/1000)*((mW 12130 : ℝ)*24260*(24260+2)))^2 +
  covarianceVarianceBound 24260 (mW 12130) /
    ((1/1000)*covarianceMeanBound 24260 (mW 12130))^2 +
  normVarianceBound 24260 (mW 12130) / (3*inputVarianceMean 24260 (mW 12130))^2

end BstLean.Part281.WorldRow12130
namespace BstLean.Part281.WorldRow12131
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12131 = 196624716543880 := by
  have hu : mW 12131 ≤ 196624716543880 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12131 ≤ 196624716543879 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12131)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24262 ^ 2)
    ((25000000000000000000/3811066048069778177587957))
    ((25000000000000000000/3810908968437098687913903)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24262) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24262 : ℝ)^2 / (mW 12131 : ℝ)) * (1 + 1/10^6)^2 *
    √(((21333/10000000000))/2) * ((1-firstRatio 24262) * √(1-firstRatio 24262) *
      sixthConstant (e1CovarianceRatio 24262 (mW 12131) (1/10^6) rowEps))) /
    (712/10000 - 24262*(1+1/10^6)*((21333/10000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24262 (mW 12131) /
    ((1/10^5) * ((mW 12131 : ℝ)*24262*((mW 12131 : ℝ)+24262+1)))^2 +
  8*(mW 12131 : ℝ)*24262*(24262+2)*(24262+3) /
    ((1/1000)*((mW 12131 : ℝ)*24262*(24262+2)))^2 +
  covarianceVarianceBound 24262 (mW 12131) /
    ((1/1000)*covarianceMeanBound 24262 (mW 12131))^2 +
  normVarianceBound 24262 (mW 12131) / (3*inputVarianceMean 24262 (mW 12131))^2

end BstLean.Part281.WorldRow12131
namespace BstLean.Part281.WorldRow12132
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12132 = 196681451967406 := by
  have hu : mW 12132 ≤ 196681451967406 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12132 ≤ 196681451967405 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12132)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24264 ^ 2)
    ((6250000000000000000/952845051833784289227951))
    ((25000000000000000000/3811223127702457667237749)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24264) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24264 : ℝ)^2 / (mW 12132 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1066561/500000000000))/2) * ((1-firstRatio 24264) * √(1-firstRatio 24264) *
      sixthConstant (e1CovarianceRatio 24264 (mW 12132) (1/10^6) rowEps))) /
    (712/10000 - 24264*(1+1/10^6)*((1066561/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24264 (mW 12132) /
    ((1/10^5) * ((mW 12132 : ℝ)*24264*((mW 12132 : ℝ)+24264+1)))^2 +
  8*(mW 12132 : ℝ)*24264*(24264+2)*(24264+3) /
    ((1/1000)*((mW 12132 : ℝ)*24264*(24264+2)))^2 +
  covarianceVarianceBound 24264 (mW 12132) /
    ((1/1000)*covarianceMeanBound 24264 (mW 12132))^2 +
  normVarianceBound 24264 (mW 12132) / (3*inputVarianceMean 24264 (mW 12132))^2

end BstLean.Part281.WorldRow12132
namespace BstLean.Part281.WorldRow12133
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12133 = 196738199083413 := by
  have hu : mW 12133 ≤ 196738199083413 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12133 ≤ 196738199083412 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12133)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24266 ^ 2)
    ((25000000000000000000/3811694366600496136235651))
    ((5000000000000000000/762307457393563329312319)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24266) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24266 : ℝ)^2 / (mW 12133 : ℝ)) * (1 + 1/10^6)^2 *
    √(((133309/62500000000))/2) * ((1-firstRatio 24266) * √(1-firstRatio 24266) *
      sixthConstant (e1CovarianceRatio 24266 (mW 12133) (1/10^6) rowEps))) /
    (712/10000 - 24266*(1+1/10^6)*((133309/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24266 (mW 12133) /
    ((1/10^5) * ((mW 12133 : ℝ)*24266*((mW 12133 : ℝ)+24266+1)))^2 +
  8*(mW 12133 : ℝ)*24266*(24266+2)*(24266+3) /
    ((1/1000)*((mW 12133 : ℝ)*24266*(24266+2)))^2 +
  covarianceVarianceBound 24266 (mW 12133) /
    ((1/1000)*covarianceMeanBound 24266 (mW 12133))^2 +
  normVarianceBound 24266 (mW 12133) / (3*inputVarianceMean 24266 (mW 12133))^2

end BstLean.Part281.WorldRow12133
