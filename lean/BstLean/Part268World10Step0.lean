import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar10
namespace BstLean.Part268.WorldRow12600
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12600 = 224541649101760 := by
  have hu : mW 12600 ≤ 224541649101760 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12600 ≤ 224541649101759 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12600)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25200 ^ 2)
    ((125000000000000000/19792033717615697402361))
    ((25000000000000000000/3958249663890459990797677)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25200) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25200 : ℝ)^2 / (mW 12600 : ℝ)) * (1 + 1/10^6)^2 *
    √(((410609/200000000000))/2) * ((1-firstRatio 25200) * √(1-firstRatio 25200) *
      sixthConstant (e1CovarianceRatio 25200 (mW 12600) (1/10^6) rowEps))) /
    (712/10000 - 25200*(1+1/10^6)*((410609/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25200 (mW 12600) /
    ((1/10^5) * ((mW 12600 : ℝ)*25200*((mW 12600 : ℝ)+25200+1)))^2 +
  8*(mW 12600 : ℝ)*25200*(25200+2)*(25200+3) /
    ((1/1000)*((mW 12600 : ℝ)*25200*(25200+2)))^2 +
  covarianceVarianceBound 25200 (mW 12600) /
    ((1/1000)*covarianceMeanBound 25200 (mW 12600))^2 +
  normVarianceBound 25200 (mW 12600) / (3*inputVarianceMean 25200 (mW 12600))^2

end BstLean.Part268.WorldRow12600
namespace BstLean.Part268.WorldRow12601
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12601 = 224604027970077 := by
  have hu : mW 12601 ≤ 224604027970077 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12601 ≤ 224604027970076 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12601)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25202 ^ 2)
    ((25000000000000000000/3958720902788498459796047))
    ((25000000000000000000/3958563823155818970121523)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25202) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25202 : ℝ)^2 / (mW 12601 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2052881/1000000000000))/2) * ((1-firstRatio 25202) * √(1-firstRatio 25202) *
      sixthConstant (e1CovarianceRatio 25202 (mW 12601) (1/10^6) rowEps))) /
    (712/10000 - 25202*(1+1/10^6)*((2052881/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25202 (mW 12601) /
    ((1/10^5) * ((mW 12601 : ℝ)*25202*((mW 12601 : ℝ)+25202+1)))^2 +
  8*(mW 12601 : ℝ)*25202*(25202+2)*(25202+3) /
    ((1/1000)*((mW 12601 : ℝ)*25202*(25202+2)))^2 +
  covarianceVarianceBound 25202 (mW 12601) /
    ((1/1000)*covarianceMeanBound 25202 (mW 12601))^2 +
  normVarianceBound 25202 (mW 12601) / (3*inputVarianceMean 25202 (mW 12601))^2

end BstLean.Part268.WorldRow12601
namespace BstLean.Part268.WorldRow12602
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12602 = 224666419215400 := by
  have hu : mW 12602 ≤ 224666419215400 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12602 ≤ 224666419215399 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12602)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25204 ^ 2)
    ((12500000000000000000/1979517531026928719559947))
    ((25000000000000000000/3958877982421177949445369)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25204) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25204 : ℝ)^2 / (mW 12602 : ℝ)) * (1 + 1/10^6)^2 *
    √(((513179/250000000000))/2) * ((1-firstRatio 25204) * √(1-firstRatio 25204) *
      sixthConstant (e1CovarianceRatio 25204 (mW 12602) (1/10^6) rowEps))) /
    (712/10000 - 25204*(1+1/10^6)*((513179/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25204 (mW 12602) /
    ((1/10^5) * ((mW 12602 : ℝ)*25204*((mW 12602 : ℝ)+25204+1)))^2 +
  8*(mW 12602 : ℝ)*25204*(25204+2)*(25204+3) /
    ((1/1000)*((mW 12602 : ℝ)*25204*(25204+2)))^2 +
  covarianceVarianceBound 25204 (mW 12602) /
    ((1/1000)*covarianceMeanBound 25204 (mW 12602))^2 +
  normVarianceBound 25204 (mW 12602) / (3*inputVarianceMean 25204 (mW 12602))^2

end BstLean.Part268.WorldRow12602
namespace BstLean.Part268.WorldRow12603
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12603 = 224728822839201 := by
  have hu : mW 12603 ≤ 224728822839201 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12603 ≤ 224728822839200 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12603)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25206 ^ 2)
    ((25000000000000000000/3959349221319216418443741))
    ((5000000000000000000/791838428337307385753843)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25206) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25206 : ℝ)^2 / (mW 12603 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2052551/1000000000000))/2) * ((1-firstRatio 25206) * √(1-firstRatio 25206) *
      sixthConstant (e1CovarianceRatio 25206 (mW 12603) (1/10^6) rowEps))) /
    (712/10000 - 25206*(1+1/10^6)*((2052551/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25206 (mW 12603) /
    ((1/10^5) * ((mW 12603 : ℝ)*25206*((mW 12603 : ℝ)+25206+1)))^2 +
  8*(mW 12603 : ℝ)*25206*(25206+2)*(25206+3) /
    ((1/1000)*((mW 12603 : ℝ)*25206*(25206+2)))^2 +
  covarianceVarianceBound 25206 (mW 12603) /
    ((1/1000)*covarianceMeanBound 25206 (mW 12603))^2 +
  normVarianceBound 25206 (mW 12603) / (3*inputVarianceMean 25206 (mW 12603))^2

end BstLean.Part268.WorldRow12603
namespace BstLean.Part268.WorldRow12604
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12604 = 224791238842954 := by
  have hu : mW 12604 ≤ 224791238842954 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12604 ≤ 224791238842953 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12604)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25208 ^ 2)
    ((6250000000000000000/989915845146143849441897))
    ((25000000000000000000/3959506300951895908093061)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25208) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25208 : ℝ)^2 / (mW 12604 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2052387/1000000000000))/2) * ((1-firstRatio 25208) * √(1-firstRatio 25208) *
      sixthConstant (e1CovarianceRatio 25208 (mW 12604) (1/10^6) rowEps))) /
    (712/10000 - 25208*(1+1/10^6)*((2052387/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25208 (mW 12604) /
    ((1/10^5) * ((mW 12604 : ℝ)*25208*((mW 12604 : ℝ)+25208+1)))^2 +
  8*(mW 12604 : ℝ)*25208*(25208+2)*(25208+3) /
    ((1/1000)*((mW 12604 : ℝ)*25208*(25208+2)))^2 +
  covarianceVarianceBound 25208 (mW 12604) /
    ((1/1000)*covarianceMeanBound 25208 (mW 12604))^2 +
  normVarianceBound 25208 (mW 12604) / (3*inputVarianceMean 25208 (mW 12604))^2

end BstLean.Part268.WorldRow12604
namespace BstLean.Part268.WorldRow12605
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12605 = 224853667228132 := by
  have hu : mW 12605 ≤ 224853667228132 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12605 ≤ 224853667228131 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12605)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25210 ^ 2)
    ((5000000000000000000/791995507969986875418287))
    ((25000000000000000000/3959820460217254887416907)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25210) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25210 : ℝ)^2 / (mW 12605 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1026111/500000000000))/2) * ((1-firstRatio 25210) * √(1-firstRatio 25210) *
      sixthConstant (e1CovarianceRatio 25210 (mW 12605) (1/10^6) rowEps))) /
    (712/10000 - 25210*(1+1/10^6)*((1026111/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25210 (mW 12605) /
    ((1/10^5) * ((mW 12605 : ℝ)*25210*((mW 12605 : ℝ)+25210+1)))^2 +
  8*(mW 12605 : ℝ)*25210*(25210+2)*(25210+3) /
    ((1/1000)*((mW 12605 : ℝ)*25210*(25210+2)))^2 +
  covarianceVarianceBound 25210 (mW 12605) /
    ((1/1000)*covarianceMeanBound 25210 (mW 12605))^2 +
  normVarianceBound 25210 (mW 12605) / (3*inputVarianceMean 25210 (mW 12605))^2

end BstLean.Part268.WorldRow12605
namespace BstLean.Part268.WorldRow12606
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12606 = 224916107996210 := by
  have hu : mW 12606 ≤ 224916107996210 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12606 ≤ 224916107996209 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12606)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25212 ^ 2)
    ((12500000000000000000/1980145849557646678207641))
    ((25000000000000000000/3960134619482613866740753)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25212) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25212 : ℝ)^2 / (mW 12606 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1026029/500000000000))/2) * ((1-firstRatio 25212) * √(1-firstRatio 25212) *
      sixthConstant (e1CovarianceRatio 25212 (mW 12606) (1/10^6) rowEps))) /
    (712/10000 - 25212*(1+1/10^6)*((1026029/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25212 (mW 12606) /
    ((1/10^5) * ((mW 12606 : ℝ)*25212*((mW 12606 : ℝ)+25212+1)))^2 +
  8*(mW 12606 : ℝ)*25212*(25212+2)*(25212+3) /
    ((1/1000)*((mW 12606 : ℝ)*25212*(25212+2)))^2 +
  covarianceVarianceBound 25212 (mW 12606) /
    ((1/1000)*covarianceMeanBound 25212 (mW 12606))^2 +
  normVarianceBound 25212 (mW 12606) / (3*inputVarianceMean 25212 (mW 12606))^2

end BstLean.Part268.WorldRow12606
namespace BstLean.Part268.WorldRow12607
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12607 = 224978561148660 := by
  have hu : mW 12607 ≤ 224978561148660 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12607 ≤ 224978561148659 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12607)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25214 ^ 2)
    ((25000000000000000000/3960605858380652335739129))
    ((25000000000000000000/3960448778747972846064599)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25214) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25214 : ℝ)^2 / (mW 12607 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2051893/1000000000000))/2) * ((1-firstRatio 25214) * √(1-firstRatio 25214) *
      sixthConstant (e1CovarianceRatio 25214 (mW 12607) (1/10^6) rowEps))) /
    (712/10000 - 25214*(1+1/10^6)*((2051893/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25214 (mW 12607) /
    ((1/10^5) * ((mW 12607 : ℝ)*25214*((mW 12607 : ℝ)+25214+1)))^2 +
  8*(mW 12607 : ℝ)*25214*(25214+2)*(25214+3) /
    ((1/1000)*((mW 12607 : ℝ)*25214*(25214+2)))^2 +
  covarianceVarianceBound 25214 (mW 12607) /
    ((1/1000)*covarianceMeanBound 25214 (mW 12607))^2 +
  normVarianceBound 25214 (mW 12607) / (3*inputVarianceMean 25214 (mW 12607))^2

end BstLean.Part268.WorldRow12607
namespace BstLean.Part268.WorldRow12608
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12608 = 225041026686956 := by
  have hu : mW 12608 ≤ 225041026686956 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12608 ≤ 225041026686955 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12608)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25216 ^ 2)
    ((390625000000000000/61889375275718926797859))
    ((5000000000000000000/792152587602666365077689)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25216) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25216 : ℝ)^2 / (mW 12608 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2051729/1000000000000))/2) * ((1-firstRatio 25216) * √(1-firstRatio 25216) *
      sixthConstant (e1CovarianceRatio 25216 (mW 12608) (1/10^6) rowEps))) /
    (712/10000 - 25216*(1+1/10^6)*((2051729/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25216 (mW 12608) /
    ((1/10^5) * ((mW 12608 : ℝ)*25216*((mW 12608 : ℝ)+25216+1)))^2 +
  8*(mW 12608 : ℝ)*25216*(25216+2)*(25216+3) /
    ((1/1000)*((mW 12608 : ℝ)*25216*(25216+2)))^2 +
  covarianceVarianceBound 25216 (mW 12608) /
    ((1/1000)*covarianceMeanBound 25216 (mW 12608))^2 +
  normVarianceBound 25216 (mW 12608) / (3*inputVarianceMean 25216 (mW 12608))^2

end BstLean.Part268.WorldRow12608
namespace BstLean.Part268.WorldRow12609
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12609 = 225103504612572 := by
  have hu : mW 12609 ≤ 225103504612572 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12609 ≤ 225103504612571 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12609)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25218 ^ 2)
    ((25000000000000000000/3961234176911370294386823))
    ((25000000000000000000/3961077097278690804712291)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25218) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25218 : ℝ)^2 / (mW 12609 : ℝ)) * (1 + 1/10^6)^2 *
    √(((512891/250000000000))/2) * ((1-firstRatio 25218) * √(1-firstRatio 25218) *
      sixthConstant (e1CovarianceRatio 25218 (mW 12609) (1/10^6) rowEps))) /
    (712/10000 - 25218*(1+1/10^6)*((512891/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25218 (mW 12609) /
    ((1/10^5) * ((mW 12609 : ℝ)*25218*((mW 12609 : ℝ)+25218+1)))^2 +
  8*(mW 12609 : ℝ)*25218*(25218+2)*(25218+3) /
    ((1/1000)*((mW 12609 : ℝ)*25218*(25218+2)))^2 +
  covarianceVarianceBound 25218 (mW 12609) /
    ((1/1000)*covarianceMeanBound 25218 (mW 12609))^2 +
  normVarianceBound 25218 (mW 12609) / (3*inputVarianceMean 25218 (mW 12609))^2

end BstLean.Part268.WorldRow12609
namespace BstLean.Part268.WorldRow12610
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12610 = 225165994926981 := by
  have hu : mW 12610 ≤ 225165994926981 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12610 ≤ 225165994926980 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12610)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25220 ^ 2)
    ((2500000000000000000/396154833617672927371067))
    ((25000000000000000000/3961391256544049784036137)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25220) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25220 : ℝ)^2 / (mW 12610 : ℝ)) * (1 + 1/10^6)^2 *
    √(((10257/5000000000))/2) * ((1-firstRatio 25220) * √(1-firstRatio 25220) *
      sixthConstant (e1CovarianceRatio 25220 (mW 12610) (1/10^6) rowEps))) /
    (712/10000 - 25220*(1+1/10^6)*((10257/5000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25220 (mW 12610) /
    ((1/10^5) * ((mW 12610 : ℝ)*25220*((mW 12610 : ℝ)+25220+1)))^2 +
  8*(mW 12610 : ℝ)*25220*(25220+2)*(25220+3) /
    ((1/1000)*((mW 12610 : ℝ)*25220*(25220+2)))^2 +
  covarianceVarianceBound 25220 (mW 12610) /
    ((1/1000)*covarianceMeanBound 25220 (mW 12610))^2 +
  normVarianceBound 25220 (mW 12610) / (3*inputVarianceMean 25220 (mW 12610))^2

end BstLean.Part268.WorldRow12610
namespace BstLean.Part268.WorldRow12611
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12611 = 225228497631658 := by
  have hu : mW 12611 ≤ 225228497631658 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12611 ≤ 225228497631657 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12611)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25222 ^ 2)
    ((25000000000000000000/3961862495442088253034517))
    ((25000000000000000000/3961705415809408763359983)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25222) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25222 : ℝ)^2 / (mW 12611 : ℝ)) * (1 + 1/10^6)^2 *
    √(((410247/200000000000))/2) * ((1-firstRatio 25222) * √(1-firstRatio 25222) *
      sixthConstant (e1CovarianceRatio 25222 (mW 12611) (1/10^6) rowEps))) /
    (712/10000 - 25222*(1+1/10^6)*((410247/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25222 (mW 12611) /
    ((1/10^5) * ((mW 12611 : ℝ)*25222*((mW 12611 : ℝ)+25222+1)))^2 +
  8*(mW 12611 : ℝ)*25222*(25222+2)*(25222+3) /
    ((1/1000)*((mW 12611 : ℝ)*25222*(25222+2)))^2 +
  covarianceVarianceBound 25222 (mW 12611) /
    ((1/1000)*covarianceMeanBound 25222 (mW 12611))^2 +
  normVarianceBound 25222 (mW 12611) / (3*inputVarianceMean 25222 (mW 12611))^2

end BstLean.Part268.WorldRow12611
namespace BstLean.Part268.WorldRow12612
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12612 = 225291012728077 := by
  have hu : mW 12612 ≤ 225291012728077 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12612 ≤ 225291012728076 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12612)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25224 ^ 2)
    ((6250000000000000000/990544163676861808089591))
    ((25000000000000000000/3962019575074767742683829)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25224) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25224 : ℝ)^2 / (mW 12612 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2051071/1000000000000))/2) * ((1-firstRatio 25224) * √(1-firstRatio 25224) *
      sixthConstant (e1CovarianceRatio 25224 (mW 12612) (1/10^6) rowEps))) /
    (712/10000 - 25224*(1+1/10^6)*((2051071/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25224 (mW 12612) /
    ((1/10^5) * ((mW 12612 : ℝ)*25224*((mW 12612 : ℝ)+25224+1)))^2 +
  8*(mW 12612 : ℝ)*25224*(25224+2)*(25224+3) /
    ((1/1000)*((mW 12612 : ℝ)*25224*(25224+2)))^2 +
  covarianceVarianceBound 25224 (mW 12612) /
    ((1/1000)*covarianceMeanBound 25224 (mW 12612))^2 +
  normVarianceBound 25224 (mW 12612) / (3*inputVarianceMean 25224 (mW 12612))^2

end BstLean.Part268.WorldRow12612
namespace BstLean.Part268.WorldRow12613
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12613 = 225353540217711 := by
  have hu : mW 12613 ≤ 225353540217711 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12613 ≤ 225353540217710 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12613)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25226 ^ 2)
    ((25000000000000000000/3962490813972806211682211))
    ((1000000000000000000/158493349373605068880307)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25226) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25226 : ℝ)^2 / (mW 12613 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2050907/1000000000000))/2) * ((1-firstRatio 25226) * √(1-firstRatio 25226) *
      sixthConstant (e1CovarianceRatio 25226 (mW 12613) (1/10^6) rowEps))) /
    (712/10000 - 25226*(1+1/10^6)*((2050907/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25226 (mW 12613) /
    ((1/10^5) * ((mW 12613 : ℝ)*25226*((mW 12613 : ℝ)+25226+1)))^2 +
  8*(mW 12613 : ℝ)*25226*(25226+2)*(25226+3) /
    ((1/1000)*((mW 12613 : ℝ)*25226*(25226+2)))^2 +
  covarianceVarianceBound 25226 (mW 12613) /
    ((1/1000)*covarianceMeanBound 25226 (mW 12613))^2 +
  normVarianceBound 25226 (mW 12613) / (3*inputVarianceMean 25226 (mW 12613))^2

end BstLean.Part268.WorldRow12613
namespace BstLean.Part268.WorldRow12614
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12614 = 225416080102034 := by
  have hu : mW 12614 ≤ 225416080102034 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12614 ≤ 225416080102033 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12614)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25228 ^ 2)
    ((12500000000000000000/1981402486619082595503029))
    ((25000000000000000000/3962647893605485701331521)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25228) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25228 : ℝ)^2 / (mW 12614 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1025371/500000000000))/2) * ((1-firstRatio 25228) * √(1-firstRatio 25228) *
      sixthConstant (e1CovarianceRatio 25228 (mW 12614) (1/10^6) rowEps))) /
    (712/10000 - 25228*(1+1/10^6)*((1025371/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25228 (mW 12614) /
    ((1/10^5) * ((mW 12614 : ℝ)*25228*((mW 12614 : ℝ)+25228+1)))^2 +
  8*(mW 12614 : ℝ)*25228*(25228+2)*(25228+3) /
    ((1/1000)*((mW 12614 : ℝ)*25228*(25228+2)))^2 +
  covarianceVarianceBound 25228 (mW 12614) /
    ((1/1000)*covarianceMeanBound 25228 (mW 12614))^2 +
  normVarianceBound 25228 (mW 12614) / (3*inputVarianceMean 25228 (mW 12614))^2

end BstLean.Part268.WorldRow12614
namespace BstLean.Part268.WorldRow12615
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12615 = 225478632382521 := by
  have hu : mW 12615 ≤ 225478632382521 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12615 ≤ 225478632382520 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12615)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25230 ^ 2)
    ((5000000000000000000/792623826500704834065981))
    ((25000000000000000000/3962962052870844680655367)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25230) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25230 : ℝ)^2 / (mW 12615 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1025289/500000000000))/2) * ((1-firstRatio 25230) * √(1-firstRatio 25230) *
      sixthConstant (e1CovarianceRatio 25230 (mW 12615) (1/10^6) rowEps))) /
    (712/10000 - 25230*(1+1/10^6)*((1025289/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25230 (mW 12615) /
    ((1/10^5) * ((mW 12615 : ℝ)*25230*((mW 12615 : ℝ)+25230+1)))^2 +
  8*(mW 12615 : ℝ)*25230*(25230+2)*(25230+3) /
    ((1/1000)*((mW 12615 : ℝ)*25230*(25230+2)))^2 +
  covarianceVarianceBound 25230 (mW 12615) /
    ((1/1000)*covarianceMeanBound 25230 (mW 12615))^2 +
  normVarianceBound 25230 (mW 12615) / (3*inputVarianceMean 25230 (mW 12615))^2

end BstLean.Part268.WorldRow12615
namespace BstLean.Part268.WorldRow12616
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12616 = 225541197060645 := by
  have hu : mW 12616 ≤ 225541197060645 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12616 ≤ 225541197060644 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12616)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25232 ^ 2)
    ((3125000000000000000/495429161471110393706719))
    ((25000000000000000000/3963276212136203659979213)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25232) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25232 : ℝ)^2 / (mW 12616 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1025207/500000000000))/2) * ((1-firstRatio 25232) * √(1-firstRatio 25232) *
      sixthConstant (e1CovarianceRatio 25232 (mW 12616) (1/10^6) rowEps))) /
    (712/10000 - 25232*(1+1/10^6)*((1025207/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25232 (mW 12616) /
    ((1/10^5) * ((mW 12616 : ℝ)*25232*((mW 12616 : ℝ)+25232+1)))^2 +
  8*(mW 12616 : ℝ)*25232*(25232+2)*(25232+3) /
    ((1/1000)*((mW 12616 : ℝ)*25232*(25232+2)))^2 +
  covarianceVarianceBound 25232 (mW 12616) /
    ((1/1000)*covarianceMeanBound 25232 (mW 12616))^2 +
  normVarianceBound 25232 (mW 12616) / (3*inputVarianceMean 25232 (mW 12616))^2

end BstLean.Part268.WorldRow12616
namespace BstLean.Part268.WorldRow12617
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12617 = 225603774137881 := by
  have hu : mW 12617 ≤ 225603774137881 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12617 ≤ 225603774137880 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12617)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25234 ^ 2)
    ((25000000000000000000/3963747451034242128977599))
    ((25000000000000000000/3963590371401562639303059)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25234) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25234 : ℝ)^2 / (mW 12617 : ℝ)) * (1 + 1/10^6)^2 *
    √(((8201/4000000000))/2) * ((1-firstRatio 25234) * √(1-firstRatio 25234) *
      sixthConstant (e1CovarianceRatio 25234 (mW 12617) (1/10^6) rowEps))) /
    (712/10000 - 25234*(1+1/10^6)*((8201/4000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25234 (mW 12617) /
    ((1/10^5) * ((mW 12617 : ℝ)*25234*((mW 12617 : ℝ)+25234+1)))^2 +
  8*(mW 12617 : ℝ)*25234*(25234+2)*(25234+3) /
    ((1/1000)*((mW 12617 : ℝ)*25234*(25234+2)))^2 +
  covarianceVarianceBound 25234 (mW 12617) /
    ((1/1000)*covarianceMeanBound 25234 (mW 12617))^2 +
  normVarianceBound 25234 (mW 12617) / (3*inputVarianceMean 25234 (mW 12617))^2

end BstLean.Part268.WorldRow12617
namespace BstLean.Part268.WorldRow12618
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12618 = 225666363615703 := by
  have hu : mW 12618 ≤ 225666363615703 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12618 ≤ 225666363615702 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12618)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25236 ^ 2)
    ((12500000000000000000/1982030805149800554150723))
    ((5000000000000000000/792780906133384323725381)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25236) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25236 : ℝ)^2 / (mW 12618 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1025043/500000000000))/2) * ((1-firstRatio 25236) * √(1-firstRatio 25236) *
      sixthConstant (e1CovarianceRatio 25236 (mW 12618) (1/10^6) rowEps))) /
    (712/10000 - 25236*(1+1/10^6)*((1025043/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25236 (mW 12618) /
    ((1/10^5) * ((mW 12618 : ℝ)*25236*((mW 12618 : ℝ)+25236+1)))^2 +
  8*(mW 12618 : ℝ)*25236*(25236+2)*(25236+3) /
    ((1/1000)*((mW 12618 : ℝ)*25236*(25236+2)))^2 +
  covarianceVarianceBound 25236 (mW 12618) /
    ((1/1000)*covarianceMeanBound 25236 (mW 12618))^2 +
  normVarianceBound 25236 (mW 12618) / (3*inputVarianceMean 25236 (mW 12618))^2

end BstLean.Part268.WorldRow12618
namespace BstLean.Part268.WorldRow12619
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12619 = 225728965495585 := by
  have hu : mW 12619 ≤ 225728965495585 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12619 ≤ 225728965495584 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12619)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25238 ^ 2)
    ((25000000000000000000/3964375769564960087625293))
    ((25000000000000000000/3964218689932280597950751)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25238) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25238 : ℝ)^2 / (mW 12619 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2049921/1000000000000))/2) * ((1-firstRatio 25238) * √(1-firstRatio 25238) *
      sixthConstant (e1CovarianceRatio 25238 (mW 12619) (1/10^6) rowEps))) /
    (712/10000 - 25238*(1+1/10^6)*((2049921/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25238 (mW 12619) /
    ((1/10^5) * ((mW 12619 : ℝ)*25238*((mW 12619 : ℝ)+25238+1)))^2 +
  8*(mW 12619 : ℝ)*25238*(25238+2)*(25238+3) /
    ((1/1000)*((mW 12619 : ℝ)*25238*(25238+2)))^2 +
  covarianceVarianceBound 25238 (mW 12619) /
    ((1/1000)*covarianceMeanBound 25238 (mW 12619))^2 +
  normVarianceBound 25238 (mW 12619) / (3*inputVarianceMean 25238 (mW 12619))^2

end BstLean.Part268.WorldRow12619
namespace BstLean.Part268.WorldRow12620
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12620 = 225791579779002 := by
  have hu : mW 12620 ≤ 225791579779002 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12620 ≤ 225791579779001 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12620)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25240 ^ 2)
    ((1250000000000000000/198234496441515953347457))
    ((25000000000000000000/3964532849197639577274597)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25240) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25240 : ℝ)^2 / (mW 12620 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2049757/1000000000000))/2) * ((1-firstRatio 25240) * √(1-firstRatio 25240) *
      sixthConstant (e1CovarianceRatio 25240 (mW 12620) (1/10^6) rowEps))) /
    (712/10000 - 25240*(1+1/10^6)*((2049757/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25240 (mW 12620) /
    ((1/10^5) * ((mW 12620 : ℝ)*25240*((mW 12620 : ℝ)+25240+1)))^2 +
  8*(mW 12620 : ℝ)*25240*(25240+2)*(25240+3) /
    ((1/1000)*((mW 12620 : ℝ)*25240*(25240+2)))^2 +
  covarianceVarianceBound 25240 (mW 12620) /
    ((1/1000)*covarianceMeanBound 25240 (mW 12620))^2 +
  normVarianceBound 25240 (mW 12620) / (3*inputVarianceMean 25240 (mW 12620))^2

end BstLean.Part268.WorldRow12620
namespace BstLean.Part268.WorldRow12621
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12621 = 225854206467428 := by
  have hu : mW 12621 ≤ 225854206467428 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12621 ≤ 225854206467427 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12621)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25242 ^ 2)
    ((25000000000000000000/3965004088095678046272987))
    ((25000000000000000000/3964847008462998556598443)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25242) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25242 : ℝ)^2 / (mW 12621 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2049593/1000000000000))/2) * ((1-firstRatio 25242) * √(1-firstRatio 25242) *
      sixthConstant (e1CovarianceRatio 25242 (mW 12621) (1/10^6) rowEps))) /
    (712/10000 - 25242*(1+1/10^6)*((2049593/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25242 (mW 12621) /
    ((1/10^5) * ((mW 12621 : ℝ)*25242*((mW 12621 : ℝ)+25242+1)))^2 +
  8*(mW 12621 : ℝ)*25242*(25242+2)*(25242+3) /
    ((1/1000)*((mW 12621 : ℝ)*25242*(25242+2)))^2 +
  covarianceVarianceBound 25242 (mW 12621) /
    ((1/1000)*covarianceMeanBound 25242 (mW 12621))^2 +
  normVarianceBound 25242 (mW 12621) / (3*inputVarianceMean 25242 (mW 12621))^2

end BstLean.Part268.WorldRow12621
namespace BstLean.Part268.WorldRow12622
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12622 = 225916845562337 := by
  have hu : mW 12622 ≤ 225916845562337 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12622 ≤ 225916845562336 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12622)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25244 ^ 2)
    ((12500000000000000000/1982659123680518512798417))
    ((25000000000000000000/3965161167728357535922289)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25244) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25244 : ℝ)^2 / (mW 12622 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2049429/1000000000000))/2) * ((1-firstRatio 25244) * √(1-firstRatio 25244) *
      sixthConstant (e1CovarianceRatio 25244 (mW 12622) (1/10^6) rowEps))) /
    (712/10000 - 25244*(1+1/10^6)*((2049429/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25244 (mW 12622) /
    ((1/10^5) * ((mW 12622 : ℝ)*25244*((mW 12622 : ℝ)+25244+1)))^2 +
  8*(mW 12622 : ℝ)*25244*(25244+2)*(25244+3) /
    ((1/1000)*((mW 12622 : ℝ)*25244*(25244+2)))^2 +
  covarianceVarianceBound 25244 (mW 12622) /
    ((1/1000)*covarianceMeanBound 25244 (mW 12622))^2 +
  normVarianceBound 25244 (mW 12622) / (3*inputVarianceMean 25244 (mW 12622))^2

end BstLean.Part268.WorldRow12622
namespace BstLean.Part268.WorldRow12623
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12623 = 225979497065205 := by
  have hu : mW 12623 ≤ 225979497065205 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12623 ≤ 225979497065204 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12623)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25246 ^ 2)
    ((25000000000000000000/3965632406626396004920681))
    ((5000000000000000000/793095065398743303049227)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25246) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25246 : ℝ)^2 / (mW 12623 : ℝ)) * (1 + 1/10^6)^2 *
    √(((409853/200000000000))/2) * ((1-firstRatio 25246) * √(1-firstRatio 25246) *
      sixthConstant (e1CovarianceRatio 25246 (mW 12623) (1/10^6) rowEps))) /
    (712/10000 - 25246*(1+1/10^6)*((409853/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25246 (mW 12623) /
    ((1/10^5) * ((mW 12623 : ℝ)*25246*((mW 12623 : ℝ)+25246+1)))^2 +
  8*(mW 12623 : ℝ)*25246*(25246+2)*(25246+3) /
    ((1/1000)*((mW 12623 : ℝ)*25246*(25246+2)))^2 +
  covarianceVarianceBound 25246 (mW 12623) /
    ((1/1000)*covarianceMeanBound 25246 (mW 12623))^2 +
  normVarianceBound 25246 (mW 12623) / (3*inputVarianceMean 25246 (mW 12623))^2

end BstLean.Part268.WorldRow12623
namespace BstLean.Part268.WorldRow12624
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12624 = 226042160977505 := by
  have hu : mW 12624 ≤ 226042160977505 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12624 ≤ 226042160977504 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12624)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25248 ^ 2)
    ((1562500000000000000/247871660368234686515283))
    ((25000000000000000000/3965789486259075494569981)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25248) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25248 : ℝ)^2 / (mW 12624 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2049101/1000000000000))/2) * ((1-firstRatio 25248) * √(1-firstRatio 25248) *
      sixthConstant (e1CovarianceRatio 25248 (mW 12624) (1/10^6) rowEps))) /
    (712/10000 - 25248*(1+1/10^6)*((2049101/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25248 (mW 12624) /
    ((1/10^5) * ((mW 12624 : ℝ)*25248*((mW 12624 : ℝ)+25248+1)))^2 +
  8*(mW 12624 : ℝ)*25248*(25248+2)*(25248+3) /
    ((1/1000)*((mW 12624 : ℝ)*25248*(25248+2)))^2 +
  covarianceVarianceBound 25248 (mW 12624) /
    ((1/1000)*covarianceMeanBound 25248 (mW 12624))^2 +
  normVarianceBound 25248 (mW 12624) / (3*inputVarianceMean 25248 (mW 12624))^2

end BstLean.Part268.WorldRow12624
