import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar33
namespace BstLean.Part268.WorldRow13175
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13175 = 262498716108617 := by
  have hu : mW 13175 ≤ 262498716108617 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13175 ≤ 262498716108616 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13175)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26350 ^ 2)
    ((1000000000000000000/165561932844182103667369))
    ((25000000000000000000/4138891241471873102009127)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26350) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26350 : ℝ)^2 / (mW 13175 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1962549/1000000000000))/2) * ((1-firstRatio 26350) * √(1-firstRatio 26350) *
      sixthConstant (e1CovarianceRatio 26350 (mW 13175) (1/10^6) rowEps))) /
    (712/10000 - 26350*(1+1/10^6)*((1962549/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26350 (mW 13175) /
    ((1/10^5) * ((mW 13175 : ℝ)*26350*((mW 13175 : ℝ)+26350+1)))^2 +
  8*(mW 13175 : ℝ)*26350*(26350+2)*(26350+3) /
    ((1/1000)*((mW 13175 : ℝ)*26350*(26350+2)))^2 +
  covarianceVarianceBound 26350 (mW 13175) /
    ((1/1000)*covarianceMeanBound 26350 (mW 13175))^2 +
  normVarianceBound 26350 (mW 13175) / (3*inputVarianceMean 26350 (mW 13175))^2

end BstLean.Part268.WorldRow13175
namespace BstLean.Part268.WorldRow13176
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13176 = 262568456729277 := by
  have hu : mW 13176 ≤ 262568456729277 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13176 ≤ 262568456729276 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13176)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26352 ^ 2)
    ((3125000000000000000/517420310046238946376009))
    ((25000000000000000000/4139205400737232081332973)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26352) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26352 : ℝ)^2 / (mW 13176 : ℝ)) * (1 + 1/10^6)^2 *
    √(((981199/500000000000))/2) * ((1-firstRatio 26352) * √(1-firstRatio 26352) *
      sixthConstant (e1CovarianceRatio 26352 (mW 13176) (1/10^6) rowEps))) /
    (712/10000 - 26352*(1+1/10^6)*((981199/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26352 (mW 13176) /
    ((1/10^5) * ((mW 13176 : ℝ)*26352*((mW 13176 : ℝ)+26352+1)))^2 +
  8*(mW 13176 : ℝ)*26352*(26352+2)*(26352+3) /
    ((1/1000)*((mW 13176 : ℝ)*26352*(26352+2)))^2 +
  covarianceVarianceBound 26352 (mW 13176) /
    ((1/1000)*covarianceMeanBound 26352 (mW 13176))^2 +
  normVarianceBound 26352 (mW 13176) / (3*inputVarianceMean 26352 (mW 13176))^2

end BstLean.Part268.WorldRow13176
namespace BstLean.Part268.WorldRow13177
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13177 = 262638210583702 := by
  have hu : mW 13177 ≤ 262638210583702 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13177 ≤ 262638210583701 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13177)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26354 ^ 2)
    ((25000000000000000000/4139676639635270550331919))
    ((25000000000000000000/4139519560002591060656819)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26354) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26354 : ℝ)^2 / (mW 13177 : ℝ)) * (1 + 1/10^6)^2 *
    √(((245281/125000000000))/2) * ((1-firstRatio 26354) * √(1-firstRatio 26354) *
      sixthConstant (e1CovarianceRatio 26354 (mW 13177) (1/10^6) rowEps))) /
    (712/10000 - 26354*(1+1/10^6)*((245281/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26354 (mW 13177) /
    ((1/10^5) * ((mW 13177 : ℝ)*26354*((mW 13177 : ℝ)+26354+1)))^2 +
  8*(mW 13177 : ℝ)*26354*(26354+2)*(26354+3) /
    ((1/1000)*((mW 13177 : ℝ)*26354*(26354+2)))^2 +
  covarianceVarianceBound 26354 (mW 13177) /
    ((1/1000)*covarianceMeanBound 26354 (mW 13177))^2 +
  normVarianceBound 26354 (mW 13177) / (3*inputVarianceMean 26354 (mW 13177))^2

end BstLean.Part268.WorldRow13177
namespace BstLean.Part268.WorldRow13178
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13178 = 262707977673399 := by
  have hu : mW 13178 ≤ 262707977673399 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13178 ≤ 262707977673398 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13178)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26356 ^ 2)
    ((12500000000000000000/2069995399450314764827883))
    ((5000000000000000000/827966743853590007996133)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26356) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26356 : ℝ)^2 / (mW 13178 : ℝ)) * (1 + 1/10^6)^2 *
    √(((981049/500000000000))/2) * ((1-firstRatio 26356) * √(1-firstRatio 26356) *
      sixthConstant (e1CovarianceRatio 26356 (mW 13178) (1/10^6) rowEps))) /
    (712/10000 - 26356*(1+1/10^6)*((981049/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26356 (mW 13178) /
    ((1/10^5) * ((mW 13178 : ℝ)*26356*((mW 13178 : ℝ)+26356+1)))^2 +
  8*(mW 13178 : ℝ)*26356*(26356+2)*(26356+3) /
    ((1/1000)*((mW 13178 : ℝ)*26356*(26356+2)))^2 +
  covarianceVarianceBound 26356 (mW 13178) /
    ((1/1000)*covarianceMeanBound 26356 (mW 13178))^2 +
  normVarianceBound 26356 (mW 13178) / (3*inputVarianceMean 26356 (mW 13178))^2

end BstLean.Part268.WorldRow13178
namespace BstLean.Part268.WorldRow13179
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13179 = 262777757999875 := by
  have hu : mW 13179 ≤ 262777757999875 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13179 ≤ 262777757999874 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13179)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26358 ^ 2)
    ((25000000000000000000/4140304958165988508979613))
    ((25000000000000000000/4140147878533309019304511)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26358) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26358 : ℝ)^2 / (mW 13179 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1961947/1000000000000))/2) * ((1-firstRatio 26358) * √(1-firstRatio 26358) *
      sixthConstant (e1CovarianceRatio 26358 (mW 13179) (1/10^6) rowEps))) /
    (712/10000 - 26358*(1+1/10^6)*((1961947/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26358 (mW 13179) /
    ((1/10^5) * ((mW 13179 : ℝ)*26358*((mW 13179 : ℝ)+26358+1)))^2 +
  8*(mW 13179 : ℝ)*26358*(26358+2)*(26358+3) /
    ((1/1000)*((mW 13179 : ℝ)*26358*(26358+2)))^2 +
  covarianceVarianceBound 26358 (mW 13179) /
    ((1/1000)*covarianceMeanBound 26358 (mW 13179))^2 +
  normVarianceBound 26358 (mW 13179) / (3*inputVarianceMean 26358 (mW 13179))^2

end BstLean.Part268.WorldRow13179
namespace BstLean.Part268.WorldRow13180
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13180 = 262847551564637 := by
  have hu : mW 13180 ≤ 262847551564637 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13180 ≤ 262847551564636 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13180)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26360 ^ 2)
    ((1250000000000000000/207030955871567374415173))
    ((25000000000000000000/4140462037798667998628357)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26360) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26360 : ℝ)^2 / (mW 13180 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1961797/1000000000000))/2) * ((1-firstRatio 26360) * √(1-firstRatio 26360) *
      sixthConstant (e1CovarianceRatio 26360 (mW 13180) (1/10^6) rowEps))) /
    (712/10000 - 26360*(1+1/10^6)*((1961797/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26360 (mW 13180) /
    ((1/10^5) * ((mW 13180 : ℝ)*26360*((mW 13180 : ℝ)+26360+1)))^2 +
  8*(mW 13180 : ℝ)*26360*(26360+2)*(26360+3) /
    ((1/1000)*((mW 13180 : ℝ)*26360*(26360+2)))^2 +
  covarianceVarianceBound 26360 (mW 13180) /
    ((1/1000)*covarianceMeanBound 26360 (mW 13180))^2 +
  normVarianceBound 26360 (mW 13180) / (3*inputVarianceMean 26360 (mW 13180))^2

end BstLean.Part268.WorldRow13180
namespace BstLean.Part268.WorldRow13181
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13181 = 262917358369190 := by
  have hu : mW 13181 ≤ 262917358369190 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13181 ≤ 262917358369189 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13181)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26362 ^ 2)
    ((25000000000000000000/4140933276696706467627307))
    ((25000000000000000000/4140776197064026977952203)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26362) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26362 : ℝ)^2 / (mW 13181 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1961647/1000000000000))/2) * ((1-firstRatio 26362) * √(1-firstRatio 26362) *
      sixthConstant (e1CovarianceRatio 26362 (mW 13181) (1/10^6) rowEps))) /
    (712/10000 - 26362*(1+1/10^6)*((1961647/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26362 (mW 13181) /
    ((1/10^5) * ((mW 13181 : ℝ)*26362*((mW 13181 : ℝ)+26362+1)))^2 +
  8*(mW 13181 : ℝ)*26362*(26362+2)*(26362+3) /
    ((1/1000)*((mW 13181 : ℝ)*26362*(26362+2)))^2 +
  covarianceVarianceBound 26362 (mW 13181) /
    ((1/1000)*covarianceMeanBound 26362 (mW 13181))^2 +
  normVarianceBound 26362 (mW 13181) / (3*inputVarianceMean 26362 (mW 13181))^2

end BstLean.Part268.WorldRow13181
namespace BstLean.Part268.WorldRow13182
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13182 = 262987178415043 := by
  have hu : mW 13182 ≤ 262987178415043 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13182 ≤ 262987178415042 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13182)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26364 ^ 2)
    ((12500000000000000000/2070623717981032723475577))
    ((25000000000000000000/4141090356329385957276049)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26364) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26364 : ℝ)^2 / (mW 13182 : ℝ)) * (1 + 1/10^6)^2 *
    √(((245187/125000000000))/2) * ((1-firstRatio 26364) * √(1-firstRatio 26364) *
      sixthConstant (e1CovarianceRatio 26364 (mW 13182) (1/10^6) rowEps))) /
    (712/10000 - 26364*(1+1/10^6)*((245187/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26364 (mW 13182) /
    ((1/10^5) * ((mW 13182 : ℝ)*26364*((mW 13182 : ℝ)+26364+1)))^2 +
  8*(mW 13182 : ℝ)*26364*(26364+2)*(26364+3) /
    ((1/1000)*((mW 13182 : ℝ)*26364*(26364+2)))^2 +
  covarianceVarianceBound 26364 (mW 13182) /
    ((1/1000)*covarianceMeanBound 26364 (mW 13182))^2 +
  normVarianceBound 26364 (mW 13182) / (3*inputVarianceMean 26364 (mW 13182))^2

end BstLean.Part268.WorldRow13182
namespace BstLean.Part268.WorldRow13183
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13183 = 263057011703702 := by
  have hu : mW 13183 ≤ 263057011703702 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13183 ≤ 263057011703701 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13183)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26366 ^ 2)
    ((25000000000000000000/4141561595227424426275001))
    ((5000000000000000000/828280903118948987319979)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26366) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26366 : ℝ)^2 / (mW 13183 : ℝ)) * (1 + 1/10^6)^2 *
    √(((980673/500000000000))/2) * ((1-firstRatio 26366) * √(1-firstRatio 26366) *
      sixthConstant (e1CovarianceRatio 26366 (mW 13183) (1/10^6) rowEps))) /
    (712/10000 - 26366*(1+1/10^6)*((980673/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26366 (mW 13183) /
    ((1/10^5) * ((mW 13183 : ℝ)*26366*((mW 13183 : ℝ)+26366+1)))^2 +
  8*(mW 13183 : ℝ)*26366*(26366+2)*(26366+3) /
    ((1/1000)*((mW 13183 : ℝ)*26366*(26366+2)))^2 +
  covarianceVarianceBound 26366 (mW 13183) /
    ((1/1000)*covarianceMeanBound 26366 (mW 13183))^2 +
  normVarianceBound 26366 (mW 13183) / (3*inputVarianceMean 26366 (mW 13183))^2

end BstLean.Part268.WorldRow13183
namespace BstLean.Part268.WorldRow13184
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13184 = 263126858236673 := by
  have hu : mW 13184 ≤ 263126858236673 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13184 ≤ 263126858236672 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13184)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26368 ^ 2)
    ((195312500000000000/32358404331974870356241))
    ((25000000000000000000/4141718674860103915923741)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26368) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26368 : ℝ)^2 / (mW 13184 : ℝ)) * (1 + 1/10^6)^2 *
    √(((490299/250000000000))/2) * ((1-firstRatio 26368) * √(1-firstRatio 26368) *
      sixthConstant (e1CovarianceRatio 26368 (mW 13184) (1/10^6) rowEps))) /
    (712/10000 - 26368*(1+1/10^6)*((490299/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26368 (mW 13184) /
    ((1/10^5) * ((mW 13184 : ℝ)*26368*((mW 13184 : ℝ)+26368+1)))^2 +
  8*(mW 13184 : ℝ)*26368*(26368+2)*(26368+3) /
    ((1/1000)*((mW 13184 : ℝ)*26368*(26368+2)))^2 +
  covarianceVarianceBound 26368 (mW 13184) /
    ((1/1000)*covarianceMeanBound 26368 (mW 13184))^2 +
  normVarianceBound 26368 (mW 13184) / (3*inputVarianceMean 26368 (mW 13184))^2

end BstLean.Part268.WorldRow13184
namespace BstLean.Part268.WorldRow13185
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13185 = 263196718015464 := by
  have hu : mW 13185 ≤ 263196718015464 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13185 ≤ 263196718015463 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13185)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26370 ^ 2)
    ((5000000000000000000/828437982751628476984539))
    ((25000000000000000000/4142032834125462895247587)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26370) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26370 : ℝ)^2 / (mW 13185 : ℝ)) * (1 + 1/10^6)^2 *
    √(((980523/500000000000))/2) * ((1-firstRatio 26370) * √(1-firstRatio 26370) *
      sixthConstant (e1CovarianceRatio 26370 (mW 13185) (1/10^6) rowEps))) /
    (712/10000 - 26370*(1+1/10^6)*((980523/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26370 (mW 13185) /
    ((1/10^5) * ((mW 13185 : ℝ)*26370*((mW 13185 : ℝ)+26370+1)))^2 +
  8*(mW 13185 : ℝ)*26370*(26370+2)*(26370+3) /
    ((1/1000)*((mW 13185 : ℝ)*26370*(26370+2)))^2 +
  covarianceVarianceBound 26370 (mW 13185) /
    ((1/1000)*covarianceMeanBound 26370 (mW 13185))^2 +
  normVarianceBound 26370 (mW 13185) / (3*inputVarianceMean 26370 (mW 13185))^2

end BstLean.Part268.WorldRow13185
namespace BstLean.Part268.WorldRow13186
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13186 = 263266591041583 := by
  have hu : mW 13186 ≤ 263266591041583 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13186 ≤ 263266591041582 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13186)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26372 ^ 2)
    ((12500000000000000000/2071252036511750682123271))
    ((25000000000000000000/4142346993390821874571433)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26372) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26372 : ℝ)^2 / (mW 13186 : ℝ)) * (1 + 1/10^6)^2 *
    √(((392179/200000000000))/2) * ((1-firstRatio 26372) * √(1-firstRatio 26372) *
      sixthConstant (e1CovarianceRatio 26372 (mW 13186) (1/10^6) rowEps))) /
    (712/10000 - 26372*(1+1/10^6)*((392179/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26372 (mW 13186) /
    ((1/10^5) * ((mW 13186 : ℝ)*26372*((mW 13186 : ℝ)+26372+1)))^2 +
  8*(mW 13186 : ℝ)*26372*(26372+2)*(26372+3) /
    ((1/1000)*((mW 13186 : ℝ)*26372*(26372+2)))^2 +
  covarianceVarianceBound 26372 (mW 13186) /
    ((1/1000)*covarianceMeanBound 26372 (mW 13186))^2 +
  normVarianceBound 26372 (mW 13186) / (3*inputVarianceMean 26372 (mW 13186))^2

end BstLean.Part268.WorldRow13186
namespace BstLean.Part268.WorldRow13187
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13187 = 263336477316535 := by
  have hu : mW 13187 ≤ 263336477316535 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13187 ≤ 263336477316534 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13187)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26374 ^ 2)
    ((25000000000000000000/4142818232288860343570389))
    ((25000000000000000000/4142661152656180853895279)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26374) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26374 : ℝ)^2 / (mW 13187 : ℝ)) * (1 + 1/10^6)^2 *
    √(((392149/200000000000))/2) * ((1-firstRatio 26374) * √(1-firstRatio 26374) *
      sixthConstant (e1CovarianceRatio 26374 (mW 13187) (1/10^6) rowEps))) /
    (712/10000 - 26374*(1+1/10^6)*((392149/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26374 (mW 13187) /
    ((1/10^5) * ((mW 13187 : ℝ)*26374*((mW 13187 : ℝ)+26374+1)))^2 +
  8*(mW 13187 : ℝ)*26374*(26374+2)*(26374+3) /
    ((1/1000)*((mW 13187 : ℝ)*26374*(26374+2)))^2 +
  covarianceVarianceBound 26374 (mW 13187) /
    ((1/1000)*covarianceMeanBound 26374 (mW 13187))^2 +
  normVarianceBound 26374 (mW 13187) / (3*inputVarianceMean 26374 (mW 13187))^2

end BstLean.Part268.WorldRow13187
namespace BstLean.Part268.WorldRow13188
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13188 = 263406376841828 := by
  have hu : mW 13188 ≤ 263406376841828 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13188 ≤ 263406376841827 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13188)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26376 ^ 2)
    ((6250000000000000000/1035783097888554830723559))
    ((200000000000000000/33143802495372318665753)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26376) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26376 : ℝ)^2 / (mW 13188 : ℝ)) * (1 + 1/10^6)^2 *
    √(((392119/200000000000))/2) * ((1-firstRatio 26376) * √(1-firstRatio 26376) *
      sixthConstant (e1CovarianceRatio 26376 (mW 13188) (1/10^6) rowEps))) /
    (712/10000 - 26376*(1+1/10^6)*((392119/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26376 (mW 13188) /
    ((1/10^5) * ((mW 13188 : ℝ)*26376*((mW 13188 : ℝ)+26376+1)))^2 +
  8*(mW 13188 : ℝ)*26376*(26376+2)*(26376+3) /
    ((1/1000)*((mW 13188 : ℝ)*26376*(26376+2)))^2 +
  covarianceVarianceBound 26376 (mW 13188) /
    ((1/1000)*covarianceMeanBound 26376 (mW 13188))^2 +
  normVarianceBound 26376 (mW 13188) / (3*inputVarianceMean 26376 (mW 13188))^2

end BstLean.Part268.WorldRow13188
namespace BstLean.Part268.WorldRow13189
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13189 = 263476289618970 := by
  have hu : mW 13189 ≤ 263476289618970 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13189 ≤ 263476289618969 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13189)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26378 ^ 2)
    ((25000000000000000000/4143446550819578302218083))
    ((25000000000000000000/4143289471186898812542971)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26378) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26378 : ℝ)^2 / (mW 13189 : ℝ)) * (1 + 1/10^6)^2 *
    √(((392089/200000000000))/2) * ((1-firstRatio 26378) * √(1-firstRatio 26378) *
      sixthConstant (e1CovarianceRatio 26378 (mW 13189) (1/10^6) rowEps))) /
    (712/10000 - 26378*(1+1/10^6)*((392089/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26378 (mW 13189) /
    ((1/10^5) * ((mW 13189 : ℝ)*26378*((mW 13189 : ℝ)+26378+1)))^2 +
  8*(mW 13189 : ℝ)*26378*(26378+2)*(26378+3) /
    ((1/1000)*((mW 13189 : ℝ)*26378*(26378+2)))^2 +
  covarianceVarianceBound 26378 (mW 13189) /
    ((1/1000)*covarianceMeanBound 26378 (mW 13189))^2 +
  normVarianceBound 26378 (mW 13189) / (3*inputVarianceMean 26378 (mW 13189))^2

end BstLean.Part268.WorldRow13189
namespace BstLean.Part268.WorldRow13190
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13190 = 263546215649468 := by
  have hu : mW 13190 ≤ 263546215649468 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13190 ≤ 263546215649467 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13190)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26380 ^ 2)
    ((2500000000000000000/414376071008493728154193))
    ((25000000000000000000/4143603630452257791866817)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26380) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26380 : ℝ)^2 / (mW 13190 : ℝ)) * (1 + 1/10^6)^2 *
    √(((392059/200000000000))/2) * ((1-firstRatio 26380) * √(1-firstRatio 26380) *
      sixthConstant (e1CovarianceRatio 26380 (mW 13190) (1/10^6) rowEps))) /
    (712/10000 - 26380*(1+1/10^6)*((392059/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26380 (mW 13190) /
    ((1/10^5) * ((mW 13190 : ℝ)*26380*((mW 13190 : ℝ)+26380+1)))^2 +
  8*(mW 13190 : ℝ)*26380*(26380+2)*(26380+3) /
    ((1/1000)*((mW 13190 : ℝ)*26380*(26380+2)))^2 +
  covarianceVarianceBound 26380 (mW 13190) /
    ((1/1000)*covarianceMeanBound 26380 (mW 13190))^2 +
  normVarianceBound 26380 (mW 13190) / (3*inputVarianceMean 26380 (mW 13190))^2

end BstLean.Part268.WorldRow13190
namespace BstLean.Part268.WorldRow13191
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13191 = 263616154934829 := by
  have hu : mW 13191 ≤ 263616154934829 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13191 ≤ 263616154934828 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13191)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26382 ^ 2)
    ((25000000000000000000/4144074869350296260865777))
    ((25000000000000000000/4143917789717616771190663)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26382) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26382 : ℝ)^2 / (mW 13191 : ℝ)) * (1 + 1/10^6)^2 *
    √(((392029/200000000000))/2) * ((1-firstRatio 26382) * √(1-firstRatio 26382) *
      sixthConstant (e1CovarianceRatio 26382 (mW 13191) (1/10^6) rowEps))) /
    (712/10000 - 26382*(1+1/10^6)*((392029/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26382 (mW 13191) /
    ((1/10^5) * ((mW 13191 : ℝ)*26382*((mW 13191 : ℝ)+26382+1)))^2 +
  8*(mW 13191 : ℝ)*26382*(26382+2)*(26382+3) /
    ((1/1000)*((mW 13191 : ℝ)*26382*(26382+2)))^2 +
  covarianceVarianceBound 26382 (mW 13191) /
    ((1/1000)*covarianceMeanBound 26382 (mW 13191))^2 +
  normVarianceBound 26382 (mW 13191) / (3*inputVarianceMean 26382 (mW 13191))^2

end BstLean.Part268.WorldRow13191
namespace BstLean.Part268.WorldRow13192
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13192 = 263686107476560 := by
  have hu : mW 13192 ≤ 263686107476560 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13192 ≤ 263686107476559 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13192)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26384 ^ 2)
    ((3125000000000000000/518048628576956905023703))
    ((25000000000000000000/4144231948982975750514509)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26384) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26384 : ℝ)^2 / (mW 13192 : ℝ)) * (1 + 1/10^6)^2 *
    √(((391999/200000000000))/2) * ((1-firstRatio 26384) * √(1-firstRatio 26384) *
      sixthConstant (e1CovarianceRatio 26384 (mW 13192) (1/10^6) rowEps))) /
    (712/10000 - 26384*(1+1/10^6)*((391999/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26384 (mW 13192) /
    ((1/10^5) * ((mW 13192 : ℝ)*26384*((mW 13192 : ℝ)+26384+1)))^2 +
  8*(mW 13192 : ℝ)*26384*(26384+2)*(26384+3) /
    ((1/1000)*((mW 13192 : ℝ)*26384*(26384+2)))^2 +
  covarianceVarianceBound 26384 (mW 13192) /
    ((1/1000)*covarianceMeanBound 26384 (mW 13192))^2 +
  normVarianceBound 26384 (mW 13192) / (3*inputVarianceMean 26384 (mW 13192))^2

end BstLean.Part268.WorldRow13192
namespace BstLean.Part268.WorldRow13193
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13193 = 263756073276169 := by
  have hu : mW 13193 ≤ 263756073276169 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13193 ≤ 263756073276168 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13193)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26386 ^ 2)
    ((25000000000000000000/4144703187881014219513471))
    ((5000000000000000000/828909221649666945967671)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26386) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26386 : ℝ)^2 / (mW 13193 : ℝ)) * (1 + 1/10^6)^2 *
    √(((391969/200000000000))/2) * ((1-firstRatio 26386) * √(1-firstRatio 26386) *
      sixthConstant (e1CovarianceRatio 26386 (mW 13193) (1/10^6) rowEps))) /
    (712/10000 - 26386*(1+1/10^6)*((391969/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26386 (mW 13193) /
    ((1/10^5) * ((mW 13193 : ℝ)*26386*((mW 13193 : ℝ)+26386+1)))^2 +
  8*(mW 13193 : ℝ)*26386*(26386+2)*(26386+3) /
    ((1/1000)*((mW 13193 : ℝ)*26386*(26386+2)))^2 +
  covarianceVarianceBound 26386 (mW 13193) /
    ((1/1000)*covarianceMeanBound 26386 (mW 13193))^2 +
  normVarianceBound 26386 (mW 13193) / (3*inputVarianceMean 26386 (mW 13193))^2

end BstLean.Part268.WorldRow13193
namespace BstLean.Part268.WorldRow13194
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13194 = 263826052335164 := by
  have hu : mW 13194 ≤ 263826052335164 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13194 ≤ 263826052335163 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13194)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26388 ^ 2)
    ((12500000000000000000/2072508673573186599418659))
    ((25000000000000000000/4144860267513693709162201)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26388) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26388 : ℝ)^2 / (mW 13194 : ℝ)) * (1 + 1/10^6)^2 *
    √(((391939/200000000000))/2) * ((1-firstRatio 26388) * √(1-firstRatio 26388) *
      sixthConstant (e1CovarianceRatio 26388 (mW 13194) (1/10^6) rowEps))) /
    (712/10000 - 26388*(1+1/10^6)*((391939/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26388 (mW 13194) /
    ((1/10^5) * ((mW 13194 : ℝ)*26388*((mW 13194 : ℝ)+26388+1)))^2 +
  8*(mW 13194 : ℝ)*26388*(26388+2)*(26388+3) /
    ((1/1000)*((mW 13194 : ℝ)*26388*(26388+2)))^2 +
  covarianceVarianceBound 26388 (mW 13194) /
    ((1/1000)*covarianceMeanBound 26388 (mW 13194))^2 +
  normVarianceBound 26388 (mW 13194) / (3*inputVarianceMean 26388 (mW 13194))^2

end BstLean.Part268.WorldRow13194
namespace BstLean.Part268.WorldRow13195
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13195 = 263896044655052 := by
  have hu : mW 13195 ≤ 263896044655052 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13195 ≤ 263896044655051 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13195)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26390 ^ 2)
    ((5000000000000000000/829066301282346435632233))
    ((25000000000000000000/4145174426779052688486047)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26390) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26390 : ℝ)^2 / (mW 13195 : ℝ)) * (1 + 1/10^6)^2 *
    √(((391909/200000000000))/2) * ((1-firstRatio 26390) * √(1-firstRatio 26390) *
      sixthConstant (e1CovarianceRatio 26390 (mW 13195) (1/10^6) rowEps))) /
    (712/10000 - 26390*(1+1/10^6)*((391909/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26390 (mW 13195) /
    ((1/10^5) * ((mW 13195 : ℝ)*26390*((mW 13195 : ℝ)+26390+1)))^2 +
  8*(mW 13195 : ℝ)*26390*(26390+2)*(26390+3) /
    ((1/1000)*((mW 13195 : ℝ)*26390*(26390+2)))^2 +
  covarianceVarianceBound 26390 (mW 13195) /
    ((1/1000)*covarianceMeanBound 26390 (mW 13195))^2 +
  normVarianceBound 26390 (mW 13195) / (3*inputVarianceMean 26390 (mW 13195))^2

end BstLean.Part268.WorldRow13195
namespace BstLean.Part268.WorldRow13196
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13196 = 263966050237340 := by
  have hu : mW 13196 ≤ 263966050237340 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13196 ≤ 263966050237339 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13196)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26392 ^ 2)
    ((6250000000000000000/1036411416419272789371253))
    ((25000000000000000000/4145488586044411667809893)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26392) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26392 : ℝ)^2 / (mW 13196 : ℝ)) * (1 + 1/10^6)^2 *
    √(((391879/200000000000))/2) * ((1-firstRatio 26392) * √(1-firstRatio 26392) *
      sixthConstant (e1CovarianceRatio 26392 (mW 13196) (1/10^6) rowEps))) /
    (712/10000 - 26392*(1+1/10^6)*((391879/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26392 (mW 13196) /
    ((1/10^5) * ((mW 13196 : ℝ)*26392*((mW 13196 : ℝ)+26392+1)))^2 +
  8*(mW 13196 : ℝ)*26392*(26392+2)*(26392+3) /
    ((1/1000)*((mW 13196 : ℝ)*26392*(26392+2)))^2 +
  covarianceVarianceBound 26392 (mW 13196) /
    ((1/1000)*covarianceMeanBound 26392 (mW 13196))^2 +
  normVarianceBound 26392 (mW 13196) / (3*inputVarianceMean 26392 (mW 13196))^2

end BstLean.Part268.WorldRow13196
namespace BstLean.Part268.WorldRow13197
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13197 = 264036069083537 := by
  have hu : mW 13197 ≤ 264036069083537 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13197 ≤ 264036069083536 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13197)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26394 ^ 2)
    ((25000000000000000000/4145959824942450136808859))
    ((25000000000000000000/4145802745309770647133739)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26394) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26394 : ℝ)^2 / (mW 13197 : ℝ)) * (1 + 1/10^6)^2 *
    √(((391849/200000000000))/2) * ((1-firstRatio 26394) * √(1-firstRatio 26394) *
      sixthConstant (e1CovarianceRatio 26394 (mW 13197) (1/10^6) rowEps))) /
    (712/10000 - 26394*(1+1/10^6)*((391849/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26394 (mW 13197) /
    ((1/10^5) * ((mW 13197 : ℝ)*26394*((mW 13197 : ℝ)+26394+1)))^2 +
  8*(mW 13197 : ℝ)*26394*(26394+2)*(26394+3) /
    ((1/1000)*((mW 13197 : ℝ)*26394*(26394+2)))^2 +
  covarianceVarianceBound 26394 (mW 13197) /
    ((1/1000)*covarianceMeanBound 26394 (mW 13197))^2 +
  normVarianceBound 26394 (mW 13197) / (3*inputVarianceMean 26394 (mW 13197))^2

end BstLean.Part268.WorldRow13197
namespace BstLean.Part268.WorldRow13198
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13198 = 264106101195150 := by
  have hu : mW 13198 ≤ 264106101195150 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13198 ≤ 264106101195149 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13198)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26396 ^ 2)
    ((12500000000000000000/2073136992103904558066353))
    ((5000000000000000000/829223380915025925291517)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26396) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26396 : ℝ)^2 / (mW 13198 : ℝ)) * (1 + 1/10^6)^2 *
    √(((391819/200000000000))/2) * ((1-firstRatio 26396) * √(1-firstRatio 26396) *
      sixthConstant (e1CovarianceRatio 26396 (mW 13198) (1/10^6) rowEps))) /
    (712/10000 - 26396*(1+1/10^6)*((391819/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26396 (mW 13198) /
    ((1/10^5) * ((mW 13198 : ℝ)*26396*((mW 13198 : ℝ)+26396+1)))^2 +
  8*(mW 13198 : ℝ)*26396*(26396+2)*(26396+3) /
    ((1/1000)*((mW 13198 : ℝ)*26396*(26396+2)))^2 +
  covarianceVarianceBound 26396 (mW 13198) /
    ((1/1000)*covarianceMeanBound 26396 (mW 13198))^2 +
  normVarianceBound 26396 (mW 13198) / (3*inputVarianceMean 26396 (mW 13198))^2

end BstLean.Part268.WorldRow13198
namespace BstLean.Part268.WorldRow13199
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13199 = 264176146573687 := by
  have hu : mW 13199 ≤ 264176146573687 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13199 ≤ 264176146573686 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13199)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26398 ^ 2)
    ((25000000000000000000/4146588143473168095456553))
    ((25000000000000000000/4146431063840488605781431)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26398) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26398 : ℝ)^2 / (mW 13199 : ℝ)) * (1 + 1/10^6)^2 *
    √(((391789/200000000000))/2) * ((1-firstRatio 26398) * √(1-firstRatio 26398) *
      sixthConstant (e1CovarianceRatio 26398 (mW 13199) (1/10^6) rowEps))) /
    (712/10000 - 26398*(1+1/10^6)*((391789/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26398 (mW 13199) /
    ((1/10^5) * ((mW 13199 : ℝ)*26398*((mW 13199 : ℝ)+26398+1)))^2 +
  8*(mW 13199 : ℝ)*26398*(26398+2)*(26398+3) /
    ((1/1000)*((mW 13199 : ℝ)*26398*(26398+2)))^2 +
  covarianceVarianceBound 26398 (mW 13199) /
    ((1/1000)*covarianceMeanBound 26398 (mW 13199))^2 +
  normVarianceBound 26398 (mW 13199) / (3*inputVarianceMean 26398 (mW 13199))^2

end BstLean.Part268.WorldRow13199
