import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar29
namespace BstLean.Part268.WorldRow13075
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13075 = 255591226126964 := by
  have hu : mW 13075 ≤ 255591226126964 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13075 ≤ 255591226126963 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13075)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26150 ^ 2)
    ((1000000000000000000/164305295782746186371981))
    ((25000000000000000000/4107475314935975169624527)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26150) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26150 : ℝ)^2 / (mW 13075 : ℝ)) * (1 + 1/10^6)^2 *
    √(((494427/250000000000))/2) * ((1-firstRatio 26150) * √(1-firstRatio 26150) *
      sixthConstant (e1CovarianceRatio 26150 (mW 13075) (1/10^6) rowEps))) /
    (712/10000 - 26150*(1+1/10^6)*((494427/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26150 (mW 13075) /
    ((1/10^5) * ((mW 13075 : ℝ)*26150*((mW 13075 : ℝ)+26150+1)))^2 +
  8*(mW 13075 : ℝ)*26150*(26150+2)*(26150+3) /
    ((1/1000)*((mW 13075 : ℝ)*26150*(26150+2)))^2 +
  covarianceVarianceBound 26150 (mW 13075) /
    ((1/1000)*covarianceMeanBound 26150 (mW 13075))^2 +
  normVarianceBound 26150 (mW 13075) / (3*inputVarianceMean 26150 (mW 13075))^2

end BstLean.Part268.WorldRow13075
namespace BstLean.Part268.WorldRow13076
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13076 = 255659650969610 := by
  have hu : mW 13076 ≤ 255659650969610 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13076 ≤ 255659650969609 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13076)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26152 ^ 2)
    ((6250000000000000000/1026986638458503409655843))
    ((25000000000000000000/4107789474201334148948373)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26152) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26152 : ℝ)^2 / (mW 13076 : ℝ)) * (1 + 1/10^6)^2 *
    √(((494389/250000000000))/2) * ((1-firstRatio 26152) * √(1-firstRatio 26152) *
      sixthConstant (e1CovarianceRatio 26152 (mW 13076) (1/10^6) rowEps))) /
    (712/10000 - 26152*(1+1/10^6)*((494389/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26152 (mW 13076) /
    ((1/10^5) * ((mW 13076 : ℝ)*26152*((mW 13076 : ℝ)+26152+1)))^2 +
  8*(mW 13076 : ℝ)*26152*(26152+2)*(26152+3) /
    ((1/1000)*((mW 13076 : ℝ)*26152*(26152+2)))^2 +
  covarianceVarianceBound 26152 (mW 13076) /
    ((1/1000)*covarianceMeanBound 26152 (mW 13076))^2 +
  normVarianceBound 26152 (mW 13076) / (3*inputVarianceMean 26152 (mW 13076))^2

end BstLean.Part268.WorldRow13076
namespace BstLean.Part268.WorldRow13077
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13077 = 255728088895649 := by
  have hu : mW 13077 ≤ 255728088895649 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13077 ≤ 255728088895648 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13077)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26154 ^ 2)
    ((25000000000000000000/4108260713099372617947219))
    ((25000000000000000000/4108103633466693128272219)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26154) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26154 : ℝ)^2 / (mW 13077 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1977403/1000000000000))/2) * ((1-firstRatio 26154) * √(1-firstRatio 26154) *
      sixthConstant (e1CovarianceRatio 26154 (mW 13077) (1/10^6) rowEps))) /
    (712/10000 - 26154*(1+1/10^6)*((1977403/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26154 (mW 13077) /
    ((1/10^5) * ((mW 13077 : ℝ)*26154*((mW 13077 : ℝ)+26154+1)))^2 +
  8*(mW 13077 : ℝ)*26154*(26154+2)*(26154+3) /
    ((1/1000)*((mW 13077 : ℝ)*26154*(26154+2)))^2 +
  covarianceVarianceBound 26154 (mW 13077) /
    ((1/1000)*covarianceMeanBound 26154 (mW 13077))^2 +
  normVarianceBound 26154 (mW 13077) / (3*inputVarianceMean 26154 (mW 13077))^2

end BstLean.Part268.WorldRow13077
namespace BstLean.Part268.WorldRow13078
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13078 = 255796539906584 := by
  have hu : mW 13078 ≤ 255796539906584 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13078 ≤ 255796539906583 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13078)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26156 ^ 2)
    ((12500000000000000000/2054287436182365798635533))
    ((5000000000000000000/821683558546410421519213)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26156) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26156 : ℝ)^2 / (mW 13078 : ℝ)) * (1 + 1/10^6)^2 *
    √(((7909/4000000000))/2) * ((1-firstRatio 26156) * √(1-firstRatio 26156) *
      sixthConstant (e1CovarianceRatio 26156 (mW 13078) (1/10^6) rowEps))) /
    (712/10000 - 26156*(1+1/10^6)*((7909/4000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26156 (mW 13078) /
    ((1/10^5) * ((mW 13078 : ℝ)*26156*((mW 13078 : ℝ)+26156+1)))^2 +
  8*(mW 13078 : ℝ)*26156*(26156+2)*(26156+3) /
    ((1/1000)*((mW 13078 : ℝ)*26156*(26156+2)))^2 +
  covarianceVarianceBound 26156 (mW 13078) /
    ((1/1000)*covarianceMeanBound 26156 (mW 13078))^2 +
  normVarianceBound 26156 (mW 13078) / (3*inputVarianceMean 26156 (mW 13078))^2

end BstLean.Part268.WorldRow13078
namespace BstLean.Part268.WorldRow13079
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13079 = 255865004003914 := by
  have hu : mW 13079 ≤ 255865004003914 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13079 ≤ 255865004003913 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13079)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26158 ^ 2)
    ((25000000000000000000/4108889031630090576594913))
    ((25000000000000000000/4108731951997411086919911)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26158) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26158 : ℝ)^2 / (mW 13079 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1977097/1000000000000))/2) * ((1-firstRatio 26158) * √(1-firstRatio 26158) *
      sixthConstant (e1CovarianceRatio 26158 (mW 13079) (1/10^6) rowEps))) /
    (712/10000 - 26158*(1+1/10^6)*((1977097/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26158 (mW 13079) /
    ((1/10^5) * ((mW 13079 : ℝ)*26158*((mW 13079 : ℝ)+26158+1)))^2 +
  8*(mW 13079 : ℝ)*26158*(26158+2)*(26158+3) /
    ((1/1000)*((mW 13079 : ℝ)*26158*(26158+2)))^2 +
  covarianceVarianceBound 26158 (mW 13079) /
    ((1/1000)*covarianceMeanBound 26158 (mW 13079))^2 +
  normVarianceBound 26158 (mW 13079) / (3*inputVarianceMean 26158 (mW 13079))^2

end BstLean.Part268.WorldRow13079
namespace BstLean.Part268.WorldRow13080
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13080 = 255933481189142 := by
  have hu : mW 13080 ≤ 255933481189142 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13080 ≤ 255933481189141 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13080)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26160 ^ 2)
    ((625000000000000000/102730079772386238897969))
    ((25000000000000000000/4109046111262770066243757)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26160) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26160 : ℝ)^2 / (mW 13080 : ℝ)) * (1 + 1/10^6)^2 *
    √(((395389/200000000000))/2) * ((1-firstRatio 26160) * √(1-firstRatio 26160) *
      sixthConstant (e1CovarianceRatio 26160 (mW 13080) (1/10^6) rowEps))) /
    (712/10000 - 26160*(1+1/10^6)*((395389/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26160 (mW 13080) /
    ((1/10^5) * ((mW 13080 : ℝ)*26160*((mW 13080 : ℝ)+26160+1)))^2 +
  8*(mW 13080 : ℝ)*26160*(26160+2)*(26160+3) /
    ((1/1000)*((mW 13080 : ℝ)*26160*(26160+2)))^2 +
  covarianceVarianceBound 26160 (mW 13080) /
    ((1/1000)*covarianceMeanBound 26160 (mW 13080))^2 +
  normVarianceBound 26160 (mW 13080) / (3*inputVarianceMean 26160 (mW 13080))^2

end BstLean.Part268.WorldRow13080
namespace BstLean.Part268.WorldRow13081
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13081 = 256001971463767 := by
  have hu : mW 13081 ≤ 256001971463767 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13081 ≤ 256001971463766 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13081)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26162 ^ 2)
    ((25000000000000000000/4109517350160808535242607))
    ((25000000000000000000/4109360270528129045567603)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26162) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26162 : ℝ)^2 / (mW 13081 : ℝ)) * (1 + 1/10^6)^2 *
    √(((247099/125000000000))/2) * ((1-firstRatio 26162) * √(1-firstRatio 26162) *
      sixthConstant (e1CovarianceRatio 26162 (mW 13081) (1/10^6) rowEps))) /
    (712/10000 - 26162*(1+1/10^6)*((247099/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26162 (mW 13081) /
    ((1/10^5) * ((mW 13081 : ℝ)*26162*((mW 13081 : ℝ)+26162+1)))^2 +
  8*(mW 13081 : ℝ)*26162*(26162+2)*(26162+3) /
    ((1/1000)*((mW 13081 : ℝ)*26162*(26162+2)))^2 +
  covarianceVarianceBound 26162 (mW 13081) /
    ((1/1000)*covarianceMeanBound 26162 (mW 13081))^2 +
  normVarianceBound 26162 (mW 13081) / (3*inputVarianceMean 26162 (mW 13081))^2

end BstLean.Part268.WorldRow13081
namespace BstLean.Part268.WorldRow13082
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13082 = 256070474829291 := by
  have hu : mW 13082 ≤ 256070474829291 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13082 ≤ 256070474829290 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13082)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26164 ^ 2)
    ((12500000000000000000/2054915754713083757283227))
    ((25000000000000000000/4109674429793488024891449)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26164) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26164 : ℝ)^2 / (mW 13082 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1976639/1000000000000))/2) * ((1-firstRatio 26164) * √(1-firstRatio 26164) *
      sixthConstant (e1CovarianceRatio 26164 (mW 13082) (1/10^6) rowEps))) /
    (712/10000 - 26164*(1+1/10^6)*((1976639/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26164 (mW 13082) /
    ((1/10^5) * ((mW 13082 : ℝ)*26164*((mW 13082 : ℝ)+26164+1)))^2 +
  8*(mW 13082 : ℝ)*26164*(26164+2)*(26164+3) /
    ((1/1000)*((mW 13082 : ℝ)*26164*(26164+2)))^2 +
  covarianceVarianceBound 26164 (mW 13082) /
    ((1/1000)*covarianceMeanBound 26164 (mW 13082))^2 +
  normVarianceBound 26164 (mW 13082) / (3*inputVarianceMean 26164 (mW 13082))^2

end BstLean.Part268.WorldRow13082
namespace BstLean.Part268.WorldRow13083
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13083 = 256138991287215 := by
  have hu : mW 13083 ≤ 256138991287215 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13083 ≤ 256138991287214 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13083)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26166 ^ 2)
    ((25000000000000000000/4110145668691526493890301))
    ((5000000000000000000/821997717811769400843059)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26166) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26166 : ℝ)^2 / (mW 13083 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1976487/1000000000000))/2) * ((1-firstRatio 26166) * √(1-firstRatio 26166) *
      sixthConstant (e1CovarianceRatio 26166 (mW 13083) (1/10^6) rowEps))) /
    (712/10000 - 26166*(1+1/10^6)*((1976487/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26166 (mW 13083) /
    ((1/10^5) * ((mW 13083 : ℝ)*26166*((mW 13083 : ℝ)+26166+1)))^2 +
  8*(mW 13083 : ℝ)*26166*(26166+2)*(26166+3) /
    ((1/1000)*((mW 13083 : ℝ)*26166*(26166+2)))^2 +
  covarianceVarianceBound 26166 (mW 13083) /
    ((1/1000)*covarianceMeanBound 26166 (mW 13083))^2 +
  normVarianceBound 26166 (mW 13083) / (3*inputVarianceMean 26166 (mW 13083))^2

end BstLean.Part268.WorldRow13083
namespace BstLean.Part268.WorldRow13084
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13084 = 256207520839041 := by
  have hu : mW 13084 ≤ 256207520839041 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13084 ≤ 256207520839040 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13084)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26168 ^ 2)
    ((6250000000000000000/1027614956989221368303537))
    ((25000000000000000000/4110302748324205983539141)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26168) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26168 : ℝ)^2 / (mW 13084 : ℝ)) * (1 + 1/10^6)^2 *
    √(((988167/500000000000))/2) * ((1-firstRatio 26168) * √(1-firstRatio 26168) *
      sixthConstant (e1CovarianceRatio 26168 (mW 13084) (1/10^6) rowEps))) /
    (712/10000 - 26168*(1+1/10^6)*((988167/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26168 (mW 13084) /
    ((1/10^5) * ((mW 13084 : ℝ)*26168*((mW 13084 : ℝ)+26168+1)))^2 +
  8*(mW 13084 : ℝ)*26168*(26168+2)*(26168+3) /
    ((1/1000)*((mW 13084 : ℝ)*26168*(26168+2)))^2 +
  covarianceVarianceBound 26168 (mW 13084) /
    ((1/1000)*covarianceMeanBound 26168 (mW 13084))^2 +
  normVarianceBound 26168 (mW 13084) / (3*inputVarianceMean 26168 (mW 13084))^2

end BstLean.Part268.WorldRow13084
namespace BstLean.Part268.WorldRow13085
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13085 = 256276063486269 := by
  have hu : mW 13085 ≤ 256276063486269 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13085 ≤ 256276063486268 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13085)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26170 ^ 2)
    ((5000000000000000000/822154797444448890507599))
    ((25000000000000000000/4110616907589564962862987)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26170) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26170 : ℝ)^2 / (mW 13085 : ℝ)) * (1 + 1/10^6)^2 *
    √(((988091/500000000000))/2) * ((1-firstRatio 26170) * √(1-firstRatio 26170) *
      sixthConstant (e1CovarianceRatio 26170 (mW 13085) (1/10^6) rowEps))) /
    (712/10000 - 26170*(1+1/10^6)*((988091/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26170 (mW 13085) /
    ((1/10^5) * ((mW 13085 : ℝ)*26170*((mW 13085 : ℝ)+26170+1)))^2 +
  8*(mW 13085 : ℝ)*26170*(26170+2)*(26170+3) /
    ((1/1000)*((mW 13085 : ℝ)*26170*(26170+2)))^2 +
  covarianceVarianceBound 26170 (mW 13085) /
    ((1/1000)*covarianceMeanBound 26170 (mW 13085))^2 +
  normVarianceBound 26170 (mW 13085) / (3*inputVarianceMean 26170 (mW 13085))^2

end BstLean.Part268.WorldRow13085
namespace BstLean.Part268.WorldRow13086
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13086 = 256344619230401 := by
  have hu : mW 13086 ≤ 256344619230401 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13086 ≤ 256344619230400 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13086)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26172 ^ 2)
    ((12500000000000000000/2055544073243801715930921))
    ((25000000000000000000/4110931066854923942186833)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26172) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26172 : ℝ)^2 / (mW 13086 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1976029/1000000000000))/2) * ((1-firstRatio 26172) * √(1-firstRatio 26172) *
      sixthConstant (e1CovarianceRatio 26172 (mW 13086) (1/10^6) rowEps))) /
    (712/10000 - 26172*(1+1/10^6)*((1976029/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26172 (mW 13086) /
    ((1/10^5) * ((mW 13086 : ℝ)*26172*((mW 13086 : ℝ)+26172+1)))^2 +
  8*(mW 13086 : ℝ)*26172*(26172+2)*(26172+3) /
    ((1/1000)*((mW 13086 : ℝ)*26172*(26172+2)))^2 +
  covarianceVarianceBound 26172 (mW 13086) /
    ((1/1000)*covarianceMeanBound 26172 (mW 13086))^2 +
  normVarianceBound 26172 (mW 13086) / (3*inputVarianceMean 26172 (mW 13086))^2

end BstLean.Part268.WorldRow13086
namespace BstLean.Part268.WorldRow13087
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13087 = 256413188072939 := by
  have hu : mW 13087 ≤ 256413188072939 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13087 ≤ 256413188072938 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13087)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26174 ^ 2)
    ((25000000000000000000/4111402305752962411185689))
    ((25000000000000000000/4111245226120282921510679)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26174) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26174 : ℝ)^2 / (mW 13087 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1975877/1000000000000))/2) * ((1-firstRatio 26174) * √(1-firstRatio 26174) *
      sixthConstant (e1CovarianceRatio 26174 (mW 13087) (1/10^6) rowEps))) /
    (712/10000 - 26174*(1+1/10^6)*((1975877/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26174 (mW 13087) /
    ((1/10^5) * ((mW 13087 : ℝ)*26174*((mW 13087 : ℝ)+26174+1)))^2 +
  8*(mW 13087 : ℝ)*26174*(26174+2)*(26174+3) /
    ((1/1000)*((mW 13087 : ℝ)*26174*(26174+2)))^2 +
  covarianceVarianceBound 26174 (mW 13087) /
    ((1/1000)*covarianceMeanBound 26174 (mW 13087))^2 +
  normVarianceBound 26174 (mW 13087) / (3*inputVarianceMean 26174 (mW 13087))^2

end BstLean.Part268.WorldRow13087
namespace BstLean.Part268.WorldRow13088
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13088 = 256481770015383 := by
  have hu : mW 13088 ≤ 256481770015383 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13088 ≤ 256481770015382 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13088)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26176 ^ 2)
    ((781250000000000000/128491139531822543453423))
    ((1000000000000000000/164462375415425676033381)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26176) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26176 : ℝ)^2 / (mW 13088 : ℝ)) * (1 + 1/10^6)^2 *
    √(((493931/250000000000))/2) * ((1-firstRatio 26176) * √(1-firstRatio 26176) *
      sixthConstant (e1CovarianceRatio 26176 (mW 13088) (1/10^6) rowEps))) /
    (712/10000 - 26176*(1+1/10^6)*((493931/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26176 (mW 13088) /
    ((1/10^5) * ((mW 13088 : ℝ)*26176*((mW 13088 : ℝ)+26176+1)))^2 +
  8*(mW 13088 : ℝ)*26176*(26176+2)*(26176+3) /
    ((1/1000)*((mW 13088 : ℝ)*26176*(26176+2)))^2 +
  covarianceVarianceBound 26176 (mW 13088) /
    ((1/1000)*covarianceMeanBound 26176 (mW 13088))^2 +
  normVarianceBound 26176 (mW 13088) / (3*inputVarianceMean 26176 (mW 13088))^2

end BstLean.Part268.WorldRow13088
namespace BstLean.Part268.WorldRow13089
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13089 = 256550365059236 := by
  have hu : mW 13089 ≤ 256550365059236 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13089 ≤ 256550365059235 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13089)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26178 ^ 2)
    ((25000000000000000000/4112030624283680369833383))
    ((25000000000000000000/4111873544651000880158371)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26178) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26178 : ℝ)^2 / (mW 13089 : ℝ)) * (1 + 1/10^6)^2 *
    √(((493893/250000000000))/2) * ((1-firstRatio 26178) * √(1-firstRatio 26178) *
      sixthConstant (e1CovarianceRatio 26178 (mW 13089) (1/10^6) rowEps))) /
    (712/10000 - 26178*(1+1/10^6)*((493893/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26178 (mW 13089) /
    ((1/10^5) * ((mW 13089 : ℝ)*26178*((mW 13089 : ℝ)+26178+1)))^2 +
  8*(mW 13089 : ℝ)*26178*(26178+2)*(26178+3) /
    ((1/1000)*((mW 13089 : ℝ)*26178*(26178+2)))^2 +
  covarianceVarianceBound 26178 (mW 13089) /
    ((1/1000)*covarianceMeanBound 26178 (mW 13089))^2 +
  normVarianceBound 26178 (mW 13089) / (3*inputVarianceMean 26178 (mW 13089))^2

end BstLean.Part268.WorldRow13089
namespace BstLean.Part268.WorldRow13090
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13090 = 256618973205999 := by
  have hu : mW 13090 ≤ 256618973205999 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13090 ≤ 256618973205998 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13090)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26180 ^ 2)
    ((2500000000000000000/411234478354903934915723))
    ((25000000000000000000/4112187703916359859482217)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26180) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26180 : ℝ)^2 / (mW 13090 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1975419/1000000000000))/2) * ((1-firstRatio 26180) * √(1-firstRatio 26180) *
      sixthConstant (e1CovarianceRatio 26180 (mW 13090) (1/10^6) rowEps))) /
    (712/10000 - 26180*(1+1/10^6)*((1975419/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26180 (mW 13090) /
    ((1/10^5) * ((mW 13090 : ℝ)*26180*((mW 13090 : ℝ)+26180+1)))^2 +
  8*(mW 13090 : ℝ)*26180*(26180+2)*(26180+3) /
    ((1/1000)*((mW 13090 : ℝ)*26180*(26180+2)))^2 +
  covarianceVarianceBound 26180 (mW 13090) /
    ((1/1000)*covarianceMeanBound 26180 (mW 13090))^2 +
  normVarianceBound 26180 (mW 13090) / (3*inputVarianceMean 26180 (mW 13090))^2

end BstLean.Part268.WorldRow13090
namespace BstLean.Part268.WorldRow13091
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13091 = 256687594457173 := by
  have hu : mW 13091 ≤ 256687594457173 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13091 ≤ 256687594457172 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13091)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26182 ^ 2)
    ((25000000000000000000/4112658942814398328481077))
    ((25000000000000000000/4112501863181718838806063)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26182) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26182 : ℝ)^2 / (mW 13091 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1975267/1000000000000))/2) * ((1-firstRatio 26182) * √(1-firstRatio 26182) *
      sixthConstant (e1CovarianceRatio 26182 (mW 13091) (1/10^6) rowEps))) /
    (712/10000 - 26182*(1+1/10^6)*((1975267/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26182 (mW 13091) /
    ((1/10^5) * ((mW 13091 : ℝ)*26182*((mW 13091 : ℝ)+26182+1)))^2 +
  8*(mW 13091 : ℝ)*26182*(26182+2)*(26182+3) /
    ((1/1000)*((mW 13091 : ℝ)*26182*(26182+2)))^2 +
  covarianceVarianceBound 26182 (mW 13091) /
    ((1/1000)*covarianceMeanBound 26182 (mW 13091))^2 +
  normVarianceBound 26182 (mW 13091) / (3*inputVarianceMean 26182 (mW 13091))^2

end BstLean.Part268.WorldRow13091
namespace BstLean.Part268.WorldRow13092
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13092 = 256756228814260 := by
  have hu : mW 13092 ≤ 256756228814260 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13092 ≤ 256756228814259 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13092)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26184 ^ 2)
    ((6250000000000000000/1028243275519939326951231))
    ((25000000000000000000/4112816022447077818129909)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26184) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26184 : ℝ)^2 / (mW 13092 : ℝ)) * (1 + 1/10^6)^2 *
    √(((395023/200000000000))/2) * ((1-firstRatio 26184) * √(1-firstRatio 26184) *
      sixthConstant (e1CovarianceRatio 26184 (mW 13092) (1/10^6) rowEps))) /
    (712/10000 - 26184*(1+1/10^6)*((395023/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26184 (mW 13092) /
    ((1/10^5) * ((mW 13092 : ℝ)*26184*((mW 13092 : ℝ)+26184+1)))^2 +
  8*(mW 13092 : ℝ)*26184*(26184+2)*(26184+3) /
    ((1/1000)*((mW 13092 : ℝ)*26184*(26184+2)))^2 +
  covarianceVarianceBound 26184 (mW 13092) /
    ((1/1000)*covarianceMeanBound 26184 (mW 13092))^2 +
  normVarianceBound 26184 (mW 13092) / (3*inputVarianceMean 26184 (mW 13092))^2

end BstLean.Part268.WorldRow13092
namespace BstLean.Part268.WorldRow13093
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13093 = 256824876278763 := by
  have hu : mW 13093 ≤ 256824876278763 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13093 ≤ 256824876278762 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13093)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26186 ^ 2)
    ((25000000000000000000/4113287261345116287128771))
    ((5000000000000000000/822626036342487359490751)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26186) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26186 : ℝ)^2 / (mW 13093 : ℝ)) * (1 + 1/10^6)^2 *
    √(((987481/500000000000))/2) * ((1-firstRatio 26186) * √(1-firstRatio 26186) *
      sixthConstant (e1CovarianceRatio 26186 (mW 13093) (1/10^6) rowEps))) /
    (712/10000 - 26186*(1+1/10^6)*((987481/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26186 (mW 13093) /
    ((1/10^5) * ((mW 13093 : ℝ)*26186*((mW 13093 : ℝ)+26186+1)))^2 +
  8*(mW 13093 : ℝ)*26186*(26186+2)*(26186+3) /
    ((1/1000)*((mW 13093 : ℝ)*26186*(26186+2)))^2 +
  covarianceVarianceBound 26186 (mW 13093) /
    ((1/1000)*covarianceMeanBound 26186 (mW 13093))^2 +
  normVarianceBound 26186 (mW 13093) / (3*inputVarianceMean 26186 (mW 13093))^2

end BstLean.Part268.WorldRow13093
namespace BstLean.Part268.WorldRow13094
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13094 = 256893536852182 := by
  have hu : mW 13094 ≤ 256893536852182 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13094 ≤ 256893536852181 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13094)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26188 ^ 2)
    ((12500000000000000000/2056800710305237633226309))
    ((25000000000000000000/4113444340977795776777601)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26188) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26188 : ℝ)^2 / (mW 13094 : ℝ)) * (1 + 1/10^6)^2 *
    √(((197481/100000000000))/2) * ((1-firstRatio 26188) * √(1-firstRatio 26188) *
      sixthConstant (e1CovarianceRatio 26188 (mW 13094) (1/10^6) rowEps))) /
    (712/10000 - 26188*(1+1/10^6)*((197481/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26188 (mW 13094) /
    ((1/10^5) * ((mW 13094 : ℝ)*26188*((mW 13094 : ℝ)+26188+1)))^2 +
  8*(mW 13094 : ℝ)*26188*(26188+2)*(26188+3) /
    ((1/1000)*((mW 13094 : ℝ)*26188*(26188+2)))^2 +
  covarianceVarianceBound 26188 (mW 13094) /
    ((1/1000)*covarianceMeanBound 26188 (mW 13094))^2 +
  normVarianceBound 26188 (mW 13094) / (3*inputVarianceMean 26188 (mW 13094))^2

end BstLean.Part268.WorldRow13094
namespace BstLean.Part268.WorldRow13095
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13095 = 256962210536020 := by
  have hu : mW 13095 ≤ 256962210536020 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13095 ≤ 256962210536019 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13095)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26190 ^ 2)
    ((5000000000000000000/822783115975166849155293))
    ((25000000000000000000/4113758500243154756101447)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26190) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26190 : ℝ)^2 / (mW 13095 : ℝ)) * (1 + 1/10^6)^2 *
    √(((987329/500000000000))/2) * ((1-firstRatio 26190) * √(1-firstRatio 26190) *
      sixthConstant (e1CovarianceRatio 26190 (mW 13095) (1/10^6) rowEps))) /
    (712/10000 - 26190*(1+1/10^6)*((987329/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26190 (mW 13095) /
    ((1/10^5) * ((mW 13095 : ℝ)*26190*((mW 13095 : ℝ)+26190+1)))^2 +
  8*(mW 13095 : ℝ)*26190*(26190+2)*(26190+3) /
    ((1/1000)*((mW 13095 : ℝ)*26190*(26190+2)))^2 +
  covarianceVarianceBound 26190 (mW 13095) /
    ((1/1000)*covarianceMeanBound 26190 (mW 13095))^2 +
  normVarianceBound 26190 (mW 13095) / (3*inputVarianceMean 26190 (mW 13095))^2

end BstLean.Part268.WorldRow13095
namespace BstLean.Part268.WorldRow13096
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13096 = 257030897331778 := by
  have hu : mW 13096 ≤ 257030897331778 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13096 ≤ 257030897331777 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13096)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26192 ^ 2)
    ((3125000000000000000/514278717392649153137539))
    ((25000000000000000000/4114072659508513735425293)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26192) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26192 : ℝ)^2 / (mW 13096 : ℝ)) * (1 + 1/10^6)^2 *
    √(((394901/200000000000))/2) * ((1-firstRatio 26192) * √(1-firstRatio 26192) *
      sixthConstant (e1CovarianceRatio 26192 (mW 13096) (1/10^6) rowEps))) /
    (712/10000 - 26192*(1+1/10^6)*((394901/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26192 (mW 13096) /
    ((1/10^5) * ((mW 13096 : ℝ)*26192*((mW 13096 : ℝ)+26192+1)))^2 +
  8*(mW 13096 : ℝ)*26192*(26192+2)*(26192+3) /
    ((1/1000)*((mW 13096 : ℝ)*26192*(26192+2)))^2 +
  covarianceVarianceBound 26192 (mW 13096) /
    ((1/1000)*covarianceMeanBound 26192 (mW 13096))^2 +
  normVarianceBound 26192 (mW 13096) / (3*inputVarianceMean 26192 (mW 13096))^2

end BstLean.Part268.WorldRow13096
namespace BstLean.Part268.WorldRow13097
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13097 = 257099597240958 := by
  have hu : mW 13097 ≤ 257099597240958 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13097 ≤ 257099597240957 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13097)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26194 ^ 2)
    ((25000000000000000000/4114543898406552204424159))
    ((25000000000000000000/4114386818773872714749139)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26194) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26194 : ℝ)^2 / (mW 13097 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1974353/1000000000000))/2) * ((1-firstRatio 26194) * √(1-firstRatio 26194) *
      sixthConstant (e1CovarianceRatio 26194 (mW 13097) (1/10^6) rowEps))) /
    (712/10000 - 26194*(1+1/10^6)*((1974353/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26194 (mW 13097) /
    ((1/10^5) * ((mW 13097 : ℝ)*26194*((mW 13097 : ℝ)+26194+1)))^2 +
  8*(mW 13097 : ℝ)*26194*(26194+2)*(26194+3) /
    ((1/1000)*((mW 13097 : ℝ)*26194*(26194+2)))^2 +
  covarianceVarianceBound 26194 (mW 13097) /
    ((1/1000)*covarianceMeanBound 26194 (mW 13097))^2 +
  normVarianceBound 26194 (mW 13097) / (3*inputVarianceMean 26194 (mW 13097))^2

end BstLean.Part268.WorldRow13097
namespace BstLean.Part268.WorldRow13098
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13098 = 257168310265064 := by
  have hu : mW 13098 ≤ 257168310265064 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13098 ≤ 257168310265063 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13098)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26196 ^ 2)
    ((12500000000000000000/2057429028835955591874003))
    ((5000000000000000000/822940195607846338814597)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26196) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26196 : ℝ)^2 / (mW 13098 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1974201/1000000000000))/2) * ((1-firstRatio 26196) * √(1-firstRatio 26196) *
      sixthConstant (e1CovarianceRatio 26196 (mW 13098) (1/10^6) rowEps))) /
    (712/10000 - 26196*(1+1/10^6)*((1974201/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26196 (mW 13098) /
    ((1/10^5) * ((mW 13098 : ℝ)*26196*((mW 13098 : ℝ)+26196+1)))^2 +
  8*(mW 13098 : ℝ)*26196*(26196+2)*(26196+3) /
    ((1/1000)*((mW 13098 : ℝ)*26196*(26196+2)))^2 +
  covarianceVarianceBound 26196 (mW 13098) /
    ((1/1000)*covarianceMeanBound 26196 (mW 13098))^2 +
  normVarianceBound 26196 (mW 13098) / (3*inputVarianceMean 26196 (mW 13098))^2

end BstLean.Part268.WorldRow13098
namespace BstLean.Part268.WorldRow13099
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13099 = 257237036405595 := by
  have hu : mW 13099 ≤ 257237036405595 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13099 ≤ 257237036405594 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13099)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26198 ^ 2)
    ((25000000000000000000/4115172216937270163071853))
    ((25000000000000000000/4115015137304590673396831)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26198) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26198 : ℝ)^2 / (mW 13099 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1974049/1000000000000))/2) * ((1-firstRatio 26198) * √(1-firstRatio 26198) *
      sixthConstant (e1CovarianceRatio 26198 (mW 13099) (1/10^6) rowEps))) /
    (712/10000 - 26198*(1+1/10^6)*((1974049/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26198 (mW 13099) /
    ((1/10^5) * ((mW 13099 : ℝ)*26198*((mW 13099 : ℝ)+26198+1)))^2 +
  8*(mW 13099 : ℝ)*26198*(26198+2)*(26198+3) /
    ((1/1000)*((mW 13099 : ℝ)*26198*(26198+2)))^2 +
  covarianceVarianceBound 26198 (mW 13099) /
    ((1/1000)*covarianceMeanBound 26198 (mW 13099))^2 +
  normVarianceBound 26198 (mW 13099) / (3*inputVarianceMean 26198 (mW 13099))^2

end BstLean.Part268.WorldRow13099
