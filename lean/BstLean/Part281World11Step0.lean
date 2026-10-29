import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part281Scalar11
namespace BstLean.Part281.WorldRow12134
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12134 = 196794957893346 := by
  have hu : mW 12134 ≤ 196794957893346 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12134 ≤ 196794957893345 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12134)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24268 ^ 2)
    ((12500000000000000000/1906004262932927557779749))
    ((25000000000000000000/3811851446233175625885441)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24268) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24268 : ℝ)^2 / (mW 12134 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2132767/1000000000000))/2) * ((1-firstRatio 24268) * √(1-firstRatio 24268) *
      sixthConstant (e1CovarianceRatio 24268 (mW 12134) (1/10^6) rowEps))) /
    (712/10000 - 24268*(1+1/10^6)*((2132767/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24268 (mW 12134) /
    ((1/10^5) * ((mW 12134 : ℝ)*24268*((mW 12134 : ℝ)+24268+1)))^2 +
  8*(mW 12134 : ℝ)*24268*(24268+2)*(24268+3) /
    ((1/1000)*((mW 12134 : ℝ)*24268*(24268+2)))^2 +
  covarianceVarianceBound 24268 (mW 12134) /
    ((1/1000)*covarianceMeanBound 24268 (mW 12134))^2 +
  normVarianceBound 24268 (mW 12134) / (3*inputVarianceMean 24268 (mW 12134))^2

end BstLean.Part281.WorldRow12134
namespace BstLean.Part281.WorldRow12135
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12135 = 196851728398652 := by
  have hu : mW 12135 ≤ 196851728398652 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12135 ≤ 196851728398651 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12135)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24270 ^ 2)
    ((5000000000000000000/762464537026242818976669))
    ((25000000000000000000/3812165605498534605209287)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24270) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24270 : ℝ)^2 / (mW 12135 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2132589/1000000000000))/2) * ((1-firstRatio 24270) * √(1-firstRatio 24270) *
      sixthConstant (e1CovarianceRatio 24270 (mW 12135) (1/10^6) rowEps))) /
    (712/10000 - 24270*(1+1/10^6)*((2132589/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24270 (mW 12135) /
    ((1/10^5) * ((mW 12135 : ℝ)*24270*((mW 12135 : ℝ)+24270+1)))^2 +
  8*(mW 12135 : ℝ)*24270*(24270+2)*(24270+3) /
    ((1/1000)*((mW 12135 : ℝ)*24270*(24270+2)))^2 +
  covarianceVarianceBound 24270 (mW 12135) /
    ((1/1000)*covarianceMeanBound 24270 (mW 12135))^2 +
  normVarianceBound 24270 (mW 12135) / (3*inputVarianceMean 24270 (mW 12135))^2

end BstLean.Part281.WorldRow12135
namespace BstLean.Part281.WorldRow12136
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12136 = 196908510600774 := by
  have hu : mW 12136 ≤ 196908510600774 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12136 ≤ 196908510600773 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12136)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24272 ^ 2)
    ((3125000000000000000/476579605549571634275899))
    ((25000000000000000000/3812479764763893584533133)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24272) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24272 : ℝ)^2 / (mW 12136 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2132411/1000000000000))/2) * ((1-firstRatio 24272) * √(1-firstRatio 24272) *
      sixthConstant (e1CovarianceRatio 24272 (mW 12136) (1/10^6) rowEps))) /
    (712/10000 - 24272*(1+1/10^6)*((2132411/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24272 (mW 12136) /
    ((1/10^5) * ((mW 12136 : ℝ)*24272*((mW 12136 : ℝ)+24272+1)))^2 +
  8*(mW 12136 : ℝ)*24272*(24272+2)*(24272+3) /
    ((1/1000)*((mW 12136 : ℝ)*24272*(24272+2)))^2 +
  covarianceVarianceBound 24272 (mW 12136) /
    ((1/1000)*covarianceMeanBound 24272 (mW 12136))^2 +
  normVarianceBound 24272 (mW 12136) / (3*inputVarianceMean 24272 (mW 12136))^2

end BstLean.Part281.WorldRow12136
namespace BstLean.Part281.WorldRow12137
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12137 = 196965304501161 := by
  have hu : mW 12137 ≤ 196965304501161 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12137 ≤ 196965304501160 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12137)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24274 ^ 2)
    ((25000000000000000000/3812951003661932053531039))
    ((25000000000000000000/3812793924029252563856979)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24274) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24274 : ℝ)^2 / (mW 12137 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1066117/500000000000))/2) * ((1-firstRatio 24274) * √(1-firstRatio 24274) *
      sixthConstant (e1CovarianceRatio 24274 (mW 12137) (1/10^6) rowEps))) /
    (712/10000 - 24274*(1+1/10^6)*((1066117/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24274 (mW 12137) /
    ((1/10^5) * ((mW 12137 : ℝ)*24274*((mW 12137 : ℝ)+24274+1)))^2 +
  8*(mW 12137 : ℝ)*24274*(24274+2)*(24274+3) /
    ((1/1000)*((mW 12137 : ℝ)*24274*(24274+2)))^2 +
  covarianceVarianceBound 24274 (mW 12137) /
    ((1/1000)*covarianceMeanBound 24274 (mW 12137))^2 +
  normVarianceBound 24274 (mW 12137) / (3*inputVarianceMean 24274 (mW 12137))^2

end BstLean.Part281.WorldRow12137
namespace BstLean.Part281.WorldRow12138
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12138 = 197022110101257 := by
  have hu : mW 12138 ≤ 197022110101257 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12138 ≤ 197022110101256 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12138)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24276 ^ 2)
    ((12500000000000000000/1906632581463645516427443))
    ((1000000000000000000/152524323331784461727233)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24276) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24276 : ℝ)^2 / (mW 12138 : ℝ)) * (1 + 1/10^6)^2 *
    √(((266507/125000000000))/2) * ((1-firstRatio 24276) * √(1-firstRatio 24276) *
      sixthConstant (e1CovarianceRatio 24276 (mW 12138) (1/10^6) rowEps))) /
    (712/10000 - 24276*(1+1/10^6)*((266507/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24276 (mW 12138) /
    ((1/10^5) * ((mW 12138 : ℝ)*24276*((mW 12138 : ℝ)+24276+1)))^2 +
  8*(mW 12138 : ℝ)*24276*(24276+2)*(24276+3) /
    ((1/1000)*((mW 12138 : ℝ)*24276*(24276+2)))^2 +
  covarianceVarianceBound 24276 (mW 12138) /
    ((1/1000)*covarianceMeanBound 24276 (mW 12138))^2 +
  normVarianceBound 24276 (mW 12138) / (3*inputVarianceMean 24276 (mW 12138))^2

end BstLean.Part281.WorldRow12138
namespace BstLean.Part281.WorldRow12139
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12139 = 197078927402509 := by
  have hu : mW 12139 ≤ 197078927402509 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12139 ≤ 197078927402508 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12139)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24278 ^ 2)
    ((25000000000000000000/3813579322192650012178733))
    ((25000000000000000000/3813422242559970522504671)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24278) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24278 : ℝ)^2 / (mW 12139 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1065939/500000000000))/2) * ((1-firstRatio 24278) * √(1-firstRatio 24278) *
      sixthConstant (e1CovarianceRatio 24278 (mW 12139) (1/10^6) rowEps))) /
    (712/10000 - 24278*(1+1/10^6)*((1065939/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24278 (mW 12139) /
    ((1/10^5) * ((mW 12139 : ℝ)*24278*((mW 12139 : ℝ)+24278+1)))^2 +
  8*(mW 12139 : ℝ)*24278*(24278+2)*(24278+3) /
    ((1/1000)*((mW 12139 : ℝ)*24278*(24278+2)))^2 +
  covarianceVarianceBound 24278 (mW 12139) /
    ((1/1000)*covarianceMeanBound 24278 (mW 12139))^2 +
  normVarianceBound 24278 (mW 12139) / (3*inputVarianceMean 24278 (mW 12139))^2

end BstLean.Part281.WorldRow12139
namespace BstLean.Part281.WorldRow12140
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12140 = 197135756406362 := by
  have hu : mW 12140 ≤ 197135756406362 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12140 ≤ 197135756406361 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12140)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24280 ^ 2)
    ((1250000000000000000/190694674072900449575129))
    ((25000000000000000000/3813736401825329501828517)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24280) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24280 : ℝ)^2 / (mW 12140 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2131701/1000000000000))/2) * ((1-firstRatio 24280) * √(1-firstRatio 24280) *
      sixthConstant (e1CovarianceRatio 24280 (mW 12140) (1/10^6) rowEps))) /
    (712/10000 - 24280*(1+1/10^6)*((2131701/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24280 (mW 12140) /
    ((1/10^5) * ((mW 12140 : ℝ)*24280*((mW 12140 : ℝ)+24280+1)))^2 +
  8*(mW 12140 : ℝ)*24280*(24280+2)*(24280+3) /
    ((1/1000)*((mW 12140 : ℝ)*24280*(24280+2)))^2 +
  covarianceVarianceBound 24280 (mW 12140) /
    ((1/1000)*covarianceMeanBound 24280 (mW 12140))^2 +
  normVarianceBound 24280 (mW 12140) / (3*inputVarianceMean 24280 (mW 12140))^2

end BstLean.Part281.WorldRow12140
namespace BstLean.Part281.WorldRow12141
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12141 = 197192597114263 := by
  have hu : mW 12141 ≤ 197192597114263 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12141 ≤ 197192597114262 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12141)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24282 ^ 2)
    ((25000000000000000000/3814207640723367970826427))
    ((25000000000000000000/3814050561090688481152363)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24282) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24282 : ℝ)^2 / (mW 12141 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2131523/1000000000000))/2) * ((1-firstRatio 24282) * √(1-firstRatio 24282) *
      sixthConstant (e1CovarianceRatio 24282 (mW 12141) (1/10^6) rowEps))) /
    (712/10000 - 24282*(1+1/10^6)*((2131523/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24282 (mW 12141) /
    ((1/10^5) * ((mW 12141 : ℝ)*24282*((mW 12141 : ℝ)+24282+1)))^2 +
  8*(mW 12141 : ℝ)*24282*(24282+2)*(24282+3) /
    ((1/1000)*((mW 12141 : ℝ)*24282*(24282+2)))^2 +
  covarianceVarianceBound 24282 (mW 12141) /
    ((1/1000)*covarianceMeanBound 24282 (mW 12141))^2 +
  normVarianceBound 24282 (mW 12141) / (3*inputVarianceMean 24282 (mW 12141))^2

end BstLean.Part281.WorldRow12141
namespace BstLean.Part281.WorldRow12142
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12142 = 197249449527658 := by
  have hu : mW 12142 ≤ 197249449527658 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12142 ≤ 197249449527657 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12142)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24284 ^ 2)
    ((12500000000000000000/1907260899994363475075137))
    ((25000000000000000000/3814364720356047460476209)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24284) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24284 : ℝ)^2 / (mW 12142 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1065673/500000000000))/2) * ((1-firstRatio 24284) * √(1-firstRatio 24284) *
      sixthConstant (e1CovarianceRatio 24284 (mW 12142) (1/10^6) rowEps))) /
    (712/10000 - 24284*(1+1/10^6)*((1065673/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24284 (mW 12142) /
    ((1/10^5) * ((mW 12142 : ℝ)*24284*((mW 12142 : ℝ)+24284+1)))^2 +
  8*(mW 12142 : ℝ)*24284*(24284+2)*(24284+3) /
    ((1/1000)*((mW 12142 : ℝ)*24284*(24284+2)))^2 +
  covarianceVarianceBound 24284 (mW 12142) /
    ((1/1000)*covarianceMeanBound 24284 (mW 12142))^2 +
  normVarianceBound 24284 (mW 12142) / (3*inputVarianceMean 24284 (mW 12142))^2

end BstLean.Part281.WorldRow12142
namespace BstLean.Part281.WorldRow12143
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12143 = 197306313647993 := by
  have hu : mW 12143 ≤ 197306313647993 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12143 ≤ 197306313647992 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12143)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24286 ^ 2)
    ((25000000000000000000/3814835959254085929474121))
    ((5000000000000000000/762935775924281287960011)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24286) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24286 : ℝ)^2 / (mW 12143 : ℝ)) * (1 + 1/10^6)^2 *
    √(((66599/31250000000))/2) * ((1-firstRatio 24286) * √(1-firstRatio 24286) *
      sixthConstant (e1CovarianceRatio 24286 (mW 12143) (1/10^6) rowEps))) /
    (712/10000 - 24286*(1+1/10^6)*((66599/31250000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24286 (mW 12143) /
    ((1/10^5) * ((mW 12143 : ℝ)*24286*((mW 12143 : ℝ)+24286+1)))^2 +
  8*(mW 12143 : ℝ)*24286*(24286+2)*(24286+3) /
    ((1/1000)*((mW 12143 : ℝ)*24286*(24286+2)))^2 +
  covarianceVarianceBound 24286 (mW 12143) /
    ((1/1000)*covarianceMeanBound 24286 (mW 12143))^2 +
  normVarianceBound 24286 (mW 12143) / (3*inputVarianceMean 24286 (mW 12143))^2

end BstLean.Part281.WorldRow12143
namespace BstLean.Part281.WorldRow12144
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12144 = 197363189476714 := by
  have hu : mW 12144 ≤ 197363189476714 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12144 ≤ 197363189476713 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12144)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24288 ^ 2)
    ((1562500000000000000/238446882407465306799873))
    ((25000000000000000000/3814993038886765419123901)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24288) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24288 : ℝ)^2 / (mW 12144 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2130991/1000000000000))/2) * ((1-firstRatio 24288) * √(1-firstRatio 24288) *
      sixthConstant (e1CovarianceRatio 24288 (mW 12144) (1/10^6) rowEps))) /
    (712/10000 - 24288*(1+1/10^6)*((2130991/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24288 (mW 12144) /
    ((1/10^5) * ((mW 12144 : ℝ)*24288*((mW 12144 : ℝ)+24288+1)))^2 +
  8*(mW 12144 : ℝ)*24288*(24288+2)*(24288+3) /
    ((1/1000)*((mW 12144 : ℝ)*24288*(24288+2)))^2 +
  covarianceVarianceBound 24288 (mW 12144) /
    ((1/1000)*covarianceMeanBound 24288 (mW 12144))^2 +
  normVarianceBound 24288 (mW 12144) / (3*inputVarianceMean 24288 (mW 12144))^2

end BstLean.Part281.WorldRow12144
namespace BstLean.Part281.WorldRow12145
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12145 = 197420077015268 := by
  have hu : mW 12145 ≤ 197420077015268 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12145 ≤ 197420077015267 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12145)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24290 ^ 2)
    ((5000000000000000000/763092855556960777624363))
    ((25000000000000000000/3815307198152124398447747)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24290) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24290 : ℝ)^2 / (mW 12145 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2130813/1000000000000))/2) * ((1-firstRatio 24290) * √(1-firstRatio 24290) *
      sixthConstant (e1CovarianceRatio 24290 (mW 12145) (1/10^6) rowEps))) /
    (712/10000 - 24290*(1+1/10^6)*((2130813/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24290 (mW 12145) /
    ((1/10^5) * ((mW 12145 : ℝ)*24290*((mW 12145 : ℝ)+24290+1)))^2 +
  8*(mW 12145 : ℝ)*24290*(24290+2)*(24290+3) /
    ((1/1000)*((mW 12145 : ℝ)*24290*(24290+2)))^2 +
  covarianceVarianceBound 24290 (mW 12145) /
    ((1/1000)*covarianceMeanBound 24290 (mW 12145))^2 +
  normVarianceBound 24290 (mW 12145) / (3*inputVarianceMean 24290 (mW 12145))^2

end BstLean.Part281.WorldRow12145
namespace BstLean.Part281.WorldRow12146
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12146 = 197476976265101 := by
  have hu : mW 12146 ≤ 197476976265101 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12146 ≤ 197476976265100 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12146)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24292 ^ 2)
    ((12500000000000000000/1907889218525081433722831))
    ((25000000000000000000/3815621357417483377771593)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24292) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24292 : ℝ)^2 / (mW 12146 : ℝ)) * (1 + 1/10^6)^2 *
    √(((532659/250000000000))/2) * ((1-firstRatio 24292) * √(1-firstRatio 24292) *
      sixthConstant (e1CovarianceRatio 24292 (mW 12146) (1/10^6) rowEps))) /
    (712/10000 - 24292*(1+1/10^6)*((532659/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24292 (mW 12146) /
    ((1/10^5) * ((mW 12146 : ℝ)*24292*((mW 12146 : ℝ)+24292+1)))^2 +
  8*(mW 12146 : ℝ)*24292*(24292+2)*(24292+3) /
    ((1/1000)*((mW 12146 : ℝ)*24292*(24292+2)))^2 +
  covarianceVarianceBound 24292 (mW 12146) /
    ((1/1000)*covarianceMeanBound 24292 (mW 12146))^2 +
  normVarianceBound 24292 (mW 12146) / (3*inputVarianceMean 24292 (mW 12146))^2

end BstLean.Part281.WorldRow12146
namespace BstLean.Part281.WorldRow12147
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12147 = 197533887227660 := by
  have hu : mW 12147 ≤ 197533887227660 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12147 ≤ 197533887227659 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12147)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24294 ^ 2)
    ((25000000000000000000/3816092596315521846769509))
    ((25000000000000000000/3815935516682842357095439)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24294) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24294 : ℝ)^2 / (mW 12147 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2130459/1000000000000))/2) * ((1-firstRatio 24294) * √(1-firstRatio 24294) *
      sixthConstant (e1CovarianceRatio 24294 (mW 12147) (1/10^6) rowEps))) /
    (712/10000 - 24294*(1+1/10^6)*((2130459/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24294 (mW 12147) /
    ((1/10^5) * ((mW 12147 : ℝ)*24294*((mW 12147 : ℝ)+24294+1)))^2 +
  8*(mW 12147 : ℝ)*24294*(24294+2)*(24294+3) /
    ((1/1000)*((mW 12147 : ℝ)*24294*(24294+2)))^2 +
  covarianceVarianceBound 24294 (mW 12147) /
    ((1/1000)*covarianceMeanBound 24294 (mW 12147))^2 +
  normVarianceBound 24294 (mW 12147) / (3*inputVarianceMean 24294 (mW 12147))^2

end BstLean.Part281.WorldRow12147
namespace BstLean.Part281.WorldRow12148
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12148 = 197590809904391 := by
  have hu : mW 12148 ≤ 197590809904391 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12148 ≤ 197590809904390 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12148)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24296 ^ 2)
    ((6250000000000000000/954101688895220206523339))
    ((5000000000000000000/763249935189640267283857)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24296) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24296 : ℝ)^2 / (mW 12148 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2130281/1000000000000))/2) * ((1-firstRatio 24296) * √(1-firstRatio 24296) *
      sixthConstant (e1CovarianceRatio 24296 (mW 12148) (1/10^6) rowEps))) /
    (712/10000 - 24296*(1+1/10^6)*((2130281/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24296 (mW 12148) /
    ((1/10^5) * ((mW 12148 : ℝ)*24296*((mW 12148 : ℝ)+24296+1)))^2 +
  8*(mW 12148 : ℝ)*24296*(24296+2)*(24296+3) /
    ((1/1000)*((mW 12148 : ℝ)*24296*(24296+2)))^2 +
  covarianceVarianceBound 24296 (mW 12148) /
    ((1/1000)*covarianceMeanBound 24296 (mW 12148))^2 +
  normVarianceBound 24296 (mW 12148) / (3*inputVarianceMean 24296 (mW 12148))^2

end BstLean.Part281.WorldRow12148
namespace BstLean.Part281.WorldRow12149
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12149 = 197647744296740 := by
  have hu : mW 12149 ≤ 197647744296740 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12149 ≤ 197647744296739 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12149)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24298 ^ 2)
    ((25000000000000000000/3816720914846239805417203))
    ((25000000000000000000/3816563835213560315743131)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24298) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24298 : ℝ)^2 / (mW 12149 : ℝ)) * (1 + 1/10^6)^2 *
    √(((266263/125000000000))/2) * ((1-firstRatio 24298) * √(1-firstRatio 24298) *
      sixthConstant (e1CovarianceRatio 24298 (mW 12149) (1/10^6) rowEps))) /
    (712/10000 - 24298*(1+1/10^6)*((266263/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24298 (mW 12149) /
    ((1/10^5) * ((mW 12149 : ℝ)*24298*((mW 12149 : ℝ)+24298+1)))^2 +
  8*(mW 12149 : ℝ)*24298*(24298+2)*(24298+3) /
    ((1/1000)*((mW 12149 : ℝ)*24298*(24298+2)))^2 +
  covarianceVarianceBound 24298 (mW 12149) /
    ((1/1000)*covarianceMeanBound 24298 (mW 12149))^2 +
  normVarianceBound 24298 (mW 12149) / (3*inputVarianceMean 24298 (mW 12149))^2

end BstLean.Part281.WorldRow12149
namespace BstLean.Part281.WorldRow12150
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12150 = 197704690406155 := by
  have hu : mW 12150 ≤ 197704690406155 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12150 ≤ 197704690406154 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12150)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24300 ^ 2)
    ((500000000000000000/76340701482231975694821))
    ((25000000000000000000/3816877994478919295066977)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24300) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24300 : ℝ)^2 / (mW 12150 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2129927/1000000000000))/2) * ((1-firstRatio 24300) * √(1-firstRatio 24300) *
      sixthConstant (e1CovarianceRatio 24300 (mW 12150) (1/10^6) rowEps))) /
    (712/10000 - 24300*(1+1/10^6)*((2129927/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24300 (mW 12150) /
    ((1/10^5) * ((mW 12150 : ℝ)*24300*((mW 12150 : ℝ)+24300+1)))^2 +
  8*(mW 12150 : ℝ)*24300*(24300+2)*(24300+3) /
    ((1/1000)*((mW 12150 : ℝ)*24300*(24300+2)))^2 +
  covarianceVarianceBound 24300 (mW 12150) /
    ((1/1000)*covarianceMeanBound 24300 (mW 12150))^2 +
  normVarianceBound 24300 (mW 12150) / (3*inputVarianceMean 24300 (mW 12150))^2

end BstLean.Part281.WorldRow12150
namespace BstLean.Part281.WorldRow12151
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12151 = 197761648234082 := by
  have hu : mW 12151 ≤ 197761648234082 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12151 ≤ 197761648234081 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12151)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24302 ^ 2)
    ((25000000000000000000/3817349233376957764064897))
    ((25000000000000000000/3817192153744278274390823)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24302) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24302 : ℝ)^2 / (mW 12151 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2129749/1000000000000))/2) * ((1-firstRatio 24302) * √(1-firstRatio 24302) *
      sixthConstant (e1CovarianceRatio 24302 (mW 12151) (1/10^6) rowEps))) /
    (712/10000 - 24302*(1+1/10^6)*((2129749/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24302 (mW 12151) /
    ((1/10^5) * ((mW 12151 : ℝ)*24302*((mW 12151 : ℝ)+24302+1)))^2 +
  8*(mW 12151 : ℝ)*24302*(24302+2)*(24302+3) /
    ((1/1000)*((mW 12151 : ℝ)*24302*(24302+2)))^2 +
  covarianceVarianceBound 24302 (mW 12151) /
    ((1/1000)*covarianceMeanBound 24302 (mW 12151))^2 +
  normVarianceBound 24302 (mW 12151) / (3*inputVarianceMean 24302 (mW 12151))^2

end BstLean.Part281.WorldRow12151
namespace BstLean.Part281.WorldRow12152
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12152 = 197818617781968 := by
  have hu : mW 12152 ≤ 197818617781968 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12152 ≤ 197818617781967 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12152)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24304 ^ 2)
    ((3125000000000000000/477207924080289592923593))
    ((25000000000000000000/3817506313009637253714669)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24304) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24304 : ℝ)^2 / (mW 12152 : ℝ)) * (1 + 1/10^6)^2 *
    √(((532393/250000000000))/2) * ((1-firstRatio 24304) * √(1-firstRatio 24304) *
      sixthConstant (e1CovarianceRatio 24304 (mW 12152) (1/10^6) rowEps))) /
    (712/10000 - 24304*(1+1/10^6)*((532393/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24304 (mW 12152) /
    ((1/10^5) * ((mW 12152 : ℝ)*24304*((mW 12152 : ℝ)+24304+1)))^2 +
  8*(mW 12152 : ℝ)*24304*(24304+2)*(24304+3) /
    ((1/1000)*((mW 12152 : ℝ)*24304*(24304+2)))^2 +
  covarianceVarianceBound 24304 (mW 12152) /
    ((1/1000)*covarianceMeanBound 24304 (mW 12152))^2 +
  normVarianceBound 24304 (mW 12152) / (3*inputVarianceMean 24304 (mW 12152))^2

end BstLean.Part281.WorldRow12152
namespace BstLean.Part281.WorldRow12153
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12153 = 197875599051259 := by
  have hu : mW 12153 ≤ 197875599051259 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12153 ≤ 197875599051258 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12153)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24306 ^ 2)
    ((25000000000000000000/3817977551907675722712591))
    ((5000000000000000000/763564094454999246607703)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24306) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24306 : ℝ)^2 / (mW 12153 : ℝ)) * (1 + 1/10^6)^2 *
    √(((425879/200000000000))/2) * ((1-firstRatio 24306) * √(1-firstRatio 24306) *
      sixthConstant (e1CovarianceRatio 24306 (mW 12153) (1/10^6) rowEps))) /
    (712/10000 - 24306*(1+1/10^6)*((425879/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24306 (mW 12153) /
    ((1/10^5) * ((mW 12153 : ℝ)*24306*((mW 12153 : ℝ)+24306+1)))^2 +
  8*(mW 12153 : ℝ)*24306*(24306+2)*(24306+3) /
    ((1/1000)*((mW 12153 : ℝ)*24306*(24306+2)))^2 +
  covarianceVarianceBound 24306 (mW 12153) /
    ((1/1000)*covarianceMeanBound 24306 (mW 12153))^2 +
  normVarianceBound 24306 (mW 12153) / (3*inputVarianceMean 24306 (mW 12153))^2

end BstLean.Part281.WorldRow12153
namespace BstLean.Part281.WorldRow12154
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12154 = 197932592043403 := by
  have hu : mW 12154 ≤ 197932592043403 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12154 ≤ 197932592043402 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12154)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24308 ^ 2)
    ((12500000000000000000/1909145855586517351018219))
    ((25000000000000000000/3818134631540355212362361)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24308) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24308 : ℝ)^2 / (mW 12154 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1064609/500000000000))/2) * ((1-firstRatio 24308) * √(1-firstRatio 24308) *
      sixthConstant (e1CovarianceRatio 24308 (mW 12154) (1/10^6) rowEps))) /
    (712/10000 - 24308*(1+1/10^6)*((1064609/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24308 (mW 12154) /
    ((1/10^5) * ((mW 12154 : ℝ)*24308*((mW 12154 : ℝ)+24308+1)))^2 +
  8*(mW 12154 : ℝ)*24308*(24308+2)*(24308+3) /
    ((1/1000)*((mW 12154 : ℝ)*24308*(24308+2)))^2 +
  covarianceVarianceBound 24308 (mW 12154) /
    ((1/1000)*covarianceMeanBound 24308 (mW 12154))^2 +
  normVarianceBound 24308 (mW 12154) / (3*inputVarianceMean 24308 (mW 12154))^2

end BstLean.Part281.WorldRow12154
namespace BstLean.Part281.WorldRow12155
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12155 = 197989596759846 := by
  have hu : mW 12155 ≤ 197989596759846 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12155 ≤ 197989596759845 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12155)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24310 ^ 2)
    ((5000000000000000000/763721174087678736272057))
    ((25000000000000000000/3818448790805714191686207)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24310) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24310 : ℝ)^2 / (mW 12155 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2129041/1000000000000))/2) * ((1-firstRatio 24310) * √(1-firstRatio 24310) *
      sixthConstant (e1CovarianceRatio 24310 (mW 12155) (1/10^6) rowEps))) /
    (712/10000 - 24310*(1+1/10^6)*((2129041/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24310 (mW 12155) /
    ((1/10^5) * ((mW 12155 : ℝ)*24310*((mW 12155 : ℝ)+24310+1)))^2 +
  8*(mW 12155 : ℝ)*24310*(24310+2)*(24310+3) /
    ((1/1000)*((mW 12155 : ℝ)*24310*(24310+2)))^2 +
  covarianceVarianceBound 24310 (mW 12155) /
    ((1/1000)*covarianceMeanBound 24310 (mW 12155))^2 +
  normVarianceBound 24310 (mW 12155) / (3*inputVarianceMean 24310 (mW 12155))^2

end BstLean.Part281.WorldRow12155
namespace BstLean.Part281.WorldRow12156
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12156 = 198046613202036 := by
  have hu : mW 12156 ≤ 198046613202036 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12156 ≤ 198046613202035 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12156)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24312 ^ 2)
    ((6250000000000000000/954730007425938165171033))
    ((25000000000000000000/3818762950071073171010053)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24312) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24312 : ℝ)^2 / (mW 12156 : ℝ)) * (1 + 1/10^6)^2 *
    √(((66527/31250000000))/2) * ((1-firstRatio 24312) * √(1-firstRatio 24312) *
      sixthConstant (e1CovarianceRatio 24312 (mW 12156) (1/10^6) rowEps))) /
    (712/10000 - 24312*(1+1/10^6)*((66527/31250000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24312 (mW 12156) /
    ((1/10^5) * ((mW 12156 : ℝ)*24312*((mW 12156 : ℝ)+24312+1)))^2 +
  8*(mW 12156 : ℝ)*24312*(24312+2)*(24312+3) /
    ((1/1000)*((mW 12156 : ℝ)*24312*(24312+2)))^2 +
  covarianceVarianceBound 24312 (mW 12156) /
    ((1/1000)*covarianceMeanBound 24312 (mW 12156))^2 +
  normVarianceBound 24312 (mW 12156) / (3*inputVarianceMean 24312 (mW 12156))^2

end BstLean.Part281.WorldRow12156
namespace BstLean.Part281.WorldRow12157
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12157 = 198103641371419 := by
  have hu : mW 12157 ≤ 198103641371419 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12157 ≤ 198103641371418 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12157)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24314 ^ 2)
    ((25000000000000000000/3819234188969111640007979))
    ((25000000000000000000/3819077109336432150333899)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24314) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24314 : ℝ)^2 / (mW 12157 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2128687/1000000000000))/2) * ((1-firstRatio 24314) * √(1-firstRatio 24314) *
      sixthConstant (e1CovarianceRatio 24314 (mW 12157) (1/10^6) rowEps))) /
    (712/10000 - 24314*(1+1/10^6)*((2128687/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24314 (mW 12157) /
    ((1/10^5) * ((mW 12157 : ℝ)*24314*((mW 12157 : ℝ)+24314+1)))^2 +
  8*(mW 12157 : ℝ)*24314*(24314+2)*(24314+3) /
    ((1/1000)*((mW 12157 : ℝ)*24314*(24314+2)))^2 +
  covarianceVarianceBound 24314 (mW 12157) /
    ((1/1000)*covarianceMeanBound 24314 (mW 12157))^2 +
  normVarianceBound 24314 (mW 12157) / (3*inputVarianceMean 24314 (mW 12157))^2

end BstLean.Part281.WorldRow12157
namespace BstLean.Part281.WorldRow12158
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12158 = 198160681269443 := by
  have hu : mW 12158 ≤ 198160681269443 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12158 ≤ 198160681269442 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12158)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24316 ^ 2)
    ((12500000000000000000/1909774174117235309665913))
    ((5000000000000000000/763878253720358225931549)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24316) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24316 : ℝ)^2 / (mW 12158 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2128509/1000000000000))/2) * ((1-firstRatio 24316) * √(1-firstRatio 24316) *
      sixthConstant (e1CovarianceRatio 24316 (mW 12158) (1/10^6) rowEps))) /
    (712/10000 - 24316*(1+1/10^6)*((2128509/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24316 (mW 12158) /
    ((1/10^5) * ((mW 12158 : ℝ)*24316*((mW 12158 : ℝ)+24316+1)))^2 +
  8*(mW 12158 : ℝ)*24316*(24316+2)*(24316+3) /
    ((1/1000)*((mW 12158 : ℝ)*24316*(24316+2)))^2 +
  covarianceVarianceBound 24316 (mW 12158) /
    ((1/1000)*covarianceMeanBound 24316 (mW 12158))^2 +
  normVarianceBound 24316 (mW 12158) / (3*inputVarianceMean 24316 (mW 12158))^2

end BstLean.Part281.WorldRow12158
