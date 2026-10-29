import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar15
namespace BstLean.Part268.WorldRow12725
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12725 = 232435398158938 := by
  have hu : mW 12725 ≤ 232435398158938 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12725 ≤ 232435398158937 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12725)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25450 ^ 2)
    ((1000000000000000000/159907066067720475838123))
    ((25000000000000000000/3997519572060332406278427)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25450) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25450 : ℝ)^2 / (mW 12725 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2032667/1000000000000))/2) * ((1-firstRatio 25450) * √(1-firstRatio 25450) *
      sixthConstant (e1CovarianceRatio 25450 (mW 12725) (1/10^6) rowEps))) /
    (712/10000 - 25450*(1+1/10^6)*((2032667/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25450 (mW 12725) /
    ((1/10^5) * ((mW 12725 : ℝ)*25450*((mW 12725 : ℝ)+25450+1)))^2 +
  8*(mW 12725 : ℝ)*25450*(25450+2)*(25450+3) /
    ((1/1000)*((mW 12725 : ℝ)*25450*(25450+2)))^2 +
  covarianceVarianceBound 25450 (mW 12725) /
    ((1/1000)*covarianceMeanBound 25450 (mW 12725))^2 +
  normVarianceBound 25450 (mW 12725) / (3*inputVarianceMean 25450 (mW 12725))^2

end BstLean.Part268.WorldRow12725
namespace BstLean.Part268.WorldRow12726
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12726 = 232499335590029 := by
  have hu : mW 12726 ≤ 232499335590029 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12726 ≤ 232499335590028 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12726)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25452 ^ 2)
    ((12500000000000000000/1998995405479185437638461))
    ((25000000000000000000/3997833731325691385602273)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25452) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25452 : ℝ)^2 / (mW 12726 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1016253/500000000000))/2) * ((1-firstRatio 25452) * √(1-firstRatio 25452) *
      sixthConstant (e1CovarianceRatio 25452 (mW 12726) (1/10^6) rowEps))) /
    (712/10000 - 25452*(1+1/10^6)*((1016253/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25452 (mW 12726) /
    ((1/10^5) * ((mW 12726 : ℝ)*25452*((mW 12726 : ℝ)+25452+1)))^2 +
  8*(mW 12726 : ℝ)*25452*(25452+2)*(25452+3) /
    ((1/1000)*((mW 12726 : ℝ)*25452*(25452+2)))^2 +
  covarianceVarianceBound 25452 (mW 12726) /
    ((1/1000)*covarianceMeanBound 25452 (mW 12726))^2 +
  normVarianceBound 25452 (mW 12726) / (3*inputVarianceMean 25452 (mW 12726))^2

end BstLean.Part268.WorldRow12726
namespace BstLean.Part268.WorldRow12727
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12727 = 232563285582749 := by
  have hu : mW 12727 ≤ 232563285582749 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12727 ≤ 232563285582748 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12727)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25454 ^ 2)
    ((25000000000000000000/3998304970223729854600769))
    ((25000000000000000000/3998147890591050364926119)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25454) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25454 : ℝ)^2 / (mW 12727 : ℝ)) * (1 + 1/10^6)^2 *
    √(((254043/125000000000))/2) * ((1-firstRatio 25454) * √(1-firstRatio 25454) *
      sixthConstant (e1CovarianceRatio 25454 (mW 12727) (1/10^6) rowEps))) /
    (712/10000 - 25454*(1+1/10^6)*((254043/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25454 (mW 12727) /
    ((1/10^5) * ((mW 12727 : ℝ)*25454*((mW 12727 : ℝ)+25454+1)))^2 +
  8*(mW 12727 : ℝ)*25454*(25454+2)*(25454+3) /
    ((1/1000)*((mW 12727 : ℝ)*25454*(25454+2)))^2 +
  covarianceVarianceBound 25454 (mW 12727) /
    ((1/1000)*covarianceMeanBound 25454 (mW 12727))^2 +
  normVarianceBound 25454 (mW 12727) / (3*inputVarianceMean 25454 (mW 12727))^2

end BstLean.Part268.WorldRow12727
namespace BstLean.Part268.WorldRow12728
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12728 = 232627248138577 := by
  have hu : mW 12728 ≤ 232627248138577 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12728 ≤ 232627248138576 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12728)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25456 ^ 2)
    ((3125000000000000000/499827391186136104240577))
    ((5000000000000000000/799692409971281868849993)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25456) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25456 : ℝ)^2 / (mW 12728 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2032183/1000000000000))/2) * ((1-firstRatio 25456) * √(1-firstRatio 25456) *
      sixthConstant (e1CovarianceRatio 25456 (mW 12728) (1/10^6) rowEps))) /
    (712/10000 - 25456*(1+1/10^6)*((2032183/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25456 (mW 12728) /
    ((1/10^5) * ((mW 12728 : ℝ)*25456*((mW 12728 : ℝ)+25456+1)))^2 +
  8*(mW 12728 : ℝ)*25456*(25456+2)*(25456+3) /
    ((1/1000)*((mW 12728 : ℝ)*25456*(25456+2)))^2 +
  covarianceVarianceBound 25456 (mW 12728) /
    ((1/1000)*covarianceMeanBound 25456 (mW 12728))^2 +
  normVarianceBound 25456 (mW 12728) / (3*inputVarianceMean 25456 (mW 12728))^2

end BstLean.Part268.WorldRow12728
namespace BstLean.Part268.WorldRow12729
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12729 = 232691223258994 := by
  have hu : mW 12729 ≤ 232691223258994 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12729 ≤ 232691223258993 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12729)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25458 ^ 2)
    ((25000000000000000000/3998933288754447813248463))
    ((25000000000000000000/3998776209121768323573811)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25458) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25458 : ℝ)^2 / (mW 12729 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1016011/500000000000))/2) * ((1-firstRatio 25458) * √(1-firstRatio 25458) *
      sixthConstant (e1CovarianceRatio 25458 (mW 12729) (1/10^6) rowEps))) /
    (712/10000 - 25458*(1+1/10^6)*((1016011/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25458 (mW 12729) /
    ((1/10^5) * ((mW 12729 : ℝ)*25458*((mW 12729 : ℝ)+25458+1)))^2 +
  8*(mW 12729 : ℝ)*25458*(25458+2)*(25458+3) /
    ((1/1000)*((mW 12729 : ℝ)*25458*(25458+2)))^2 +
  covarianceVarianceBound 25458 (mW 12729) /
    ((1/1000)*covarianceMeanBound 25458 (mW 12729))^2 +
  normVarianceBound 25458 (mW 12729) / (3*inputVarianceMean 25458 (mW 12729))^2

end BstLean.Part268.WorldRow12729
namespace BstLean.Part268.WorldRow12730
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12730 = 232755210945482 := by
  have hu : mW 12730 ≤ 232755210945482 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12730 ≤ 232755210945481 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12730)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25460 ^ 2)
    ((2500000000000000000/399924744801980679257231))
    ((25000000000000000000/3999090368387127302897657)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25460) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25460 : ℝ)^2 / (mW 12730 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2031861/1000000000000))/2) * ((1-firstRatio 25460) * √(1-firstRatio 25460) *
      sixthConstant (e1CovarianceRatio 25460 (mW 12730) (1/10^6) rowEps))) /
    (712/10000 - 25460*(1+1/10^6)*((2031861/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25460 (mW 12730) /
    ((1/10^5) * ((mW 12730 : ℝ)*25460*((mW 12730 : ℝ)+25460+1)))^2 +
  8*(mW 12730 : ℝ)*25460*(25460+2)*(25460+3) /
    ((1/1000)*((mW 12730 : ℝ)*25460*(25460+2)))^2 +
  covarianceVarianceBound 25460 (mW 12730) /
    ((1/1000)*covarianceMeanBound 25460 (mW 12730))^2 +
  normVarianceBound 25460 (mW 12730) / (3*inputVarianceMean 25460 (mW 12730))^2

end BstLean.Part268.WorldRow12730
namespace BstLean.Part268.WorldRow12731
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12731 = 232819211199521 := by
  have hu : mW 12731 ≤ 232819211199521 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12731 ≤ 232819211199520 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12731)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25462 ^ 2)
    ((25000000000000000000/3999561607285165771896157))
    ((25000000000000000000/3999404527652486282221503)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25462) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25462 : ℝ)^2 / (mW 12731 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2031699/1000000000000))/2) * ((1-firstRatio 25462) * √(1-firstRatio 25462) *
      sixthConstant (e1CovarianceRatio 25462 (mW 12731) (1/10^6) rowEps))) /
    (712/10000 - 25462*(1+1/10^6)*((2031699/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25462 (mW 12731) /
    ((1/10^5) * ((mW 12731 : ℝ)*25462*((mW 12731 : ℝ)+25462+1)))^2 +
  8*(mW 12731 : ℝ)*25462*(25462+2)*(25462+3) /
    ((1/1000)*((mW 12731 : ℝ)*25462*(25462+2)))^2 +
  covarianceVarianceBound 25462 (mW 12731) /
    ((1/1000)*covarianceMeanBound 25462 (mW 12731))^2 +
  normVarianceBound 25462 (mW 12731) / (3*inputVarianceMean 25462 (mW 12731))^2

end BstLean.Part268.WorldRow12731
namespace BstLean.Part268.WorldRow12732
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12732 = 232883224022591 := by
  have hu : mW 12732 ≤ 232883224022591 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12732 ≤ 232883224022590 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12732)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25464 ^ 2)
    ((6250000000000000000/999968941637631187805001))
    ((25000000000000000000/3999718686917845261545349)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25464) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25464 : ℝ)^2 / (mW 12732 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1015769/500000000000))/2) * ((1-firstRatio 25464) * √(1-firstRatio 25464) *
      sixthConstant (e1CovarianceRatio 25464 (mW 12732) (1/10^6) rowEps))) /
    (712/10000 - 25464*(1+1/10^6)*((1015769/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25464 (mW 12732) /
    ((1/10^5) * ((mW 12732 : ℝ)*25464*((mW 12732 : ℝ)+25464+1)))^2 +
  8*(mW 12732 : ℝ)*25464*(25464+2)*(25464+3) /
    ((1/1000)*((mW 12732 : ℝ)*25464*(25464+2)))^2 +
  covarianceVarianceBound 25464 (mW 12732) /
    ((1/1000)*covarianceMeanBound 25464 (mW 12732))^2 +
  normVarianceBound 25464 (mW 12732) / (3*inputVarianceMean 25464 (mW 12732))^2

end BstLean.Part268.WorldRow12732
namespace BstLean.Part268.WorldRow12733
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12733 = 232947249416175 := by
  have hu : mW 12733 ≤ 232947249416175 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12733 ≤ 232947249416174 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12733)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25466 ^ 2)
    ((25000000000000000000/4000189925815883730543851))
    ((5000000000000000000/800006569236640848173839)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25466) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25466 : ℝ)^2 / (mW 12733 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2031377/1000000000000))/2) * ((1-firstRatio 25466) * √(1-firstRatio 25466) *
      sixthConstant (e1CovarianceRatio 25466 (mW 12733) (1/10^6) rowEps))) /
    (712/10000 - 25466*(1+1/10^6)*((2031377/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25466 (mW 12733) /
    ((1/10^5) * ((mW 12733 : ℝ)*25466*((mW 12733 : ℝ)+25466+1)))^2 +
  8*(mW 12733 : ℝ)*25466*(25466+2)*(25466+3) /
    ((1/1000)*((mW 12733 : ℝ)*25466*(25466+2)))^2 +
  covarianceVarianceBound 25466 (mW 12733) /
    ((1/1000)*covarianceMeanBound 25466 (mW 12733))^2 +
  normVarianceBound 25466 (mW 12733) / (3*inputVarianceMean 25466 (mW 12733))^2

end BstLean.Part268.WorldRow12733
namespace BstLean.Part268.WorldRow12734
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12734 = 233011287381753 := by
  have hu : mW 12734 ≤ 233011287381753 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12734 ≤ 233011287381752 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12734)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25468 ^ 2)
    ((12500000000000000000/2000252042540621354933849))
    ((25000000000000000000/4000347005448563220193041)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25468) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25468 : ℝ)^2 / (mW 12734 : ℝ)) * (1 + 1/10^6)^2 *
    √(((126951/62500000000))/2) * ((1-firstRatio 25468) * √(1-firstRatio 25468) *
      sixthConstant (e1CovarianceRatio 25468 (mW 12734) (1/10^6) rowEps))) /
    (712/10000 - 25468*(1+1/10^6)*((126951/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25468 (mW 12734) /
    ((1/10^5) * ((mW 12734 : ℝ)*25468*((mW 12734 : ℝ)+25468+1)))^2 +
  8*(mW 12734 : ℝ)*25468*(25468+2)*(25468+3) /
    ((1/1000)*((mW 12734 : ℝ)*25468*(25468+2)))^2 +
  covarianceVarianceBound 25468 (mW 12734) /
    ((1/1000)*covarianceMeanBound 25468 (mW 12734))^2 +
  normVarianceBound 25468 (mW 12734) / (3*inputVarianceMean 25468 (mW 12734))^2

end BstLean.Part268.WorldRow12734
namespace BstLean.Part268.WorldRow12735
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12735 = 233075337920805 := by
  have hu : mW 12735 ≤ 233075337920805 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12735 ≤ 233075337920804 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12735)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25470 ^ 2)
    ((5000000000000000000/800163648869320337838309))
    ((25000000000000000000/4000661164713922199516887)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25470) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25470 : ℝ)^2 / (mW 12735 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1015527/500000000000))/2) * ((1-firstRatio 25470) * √(1-firstRatio 25470) *
      sixthConstant (e1CovarianceRatio 25470 (mW 12735) (1/10^6) rowEps))) /
    (712/10000 - 25470*(1+1/10^6)*((1015527/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25470 (mW 12735) /
    ((1/10^5) * ((mW 12735 : ℝ)*25470*((mW 12735 : ℝ)+25470+1)))^2 +
  8*(mW 12735 : ℝ)*25470*(25470+2)*(25470+3) /
    ((1/1000)*((mW 12735 : ℝ)*25470*(25470+2)))^2 +
  covarianceVarianceBound 25470 (mW 12735) /
    ((1/1000)*covarianceMeanBound 25470 (mW 12735))^2 +
  normVarianceBound 25470 (mW 12735) / (3*inputVarianceMean 25470 (mW 12735))^2

end BstLean.Part268.WorldRow12735
namespace BstLean.Part268.WorldRow12736
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12736 = 233139401034814 := by
  have hu : mW 12736 ≤ 233139401034814 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12736 ≤ 233139401034813 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12736)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25472 ^ 2)
    ((390625000000000000/62517693806436885445553))
    ((25000000000000000000/4000975323979281178840733)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25472) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25472 : ℝ)^2 / (mW 12736 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2030893/1000000000000))/2) * ((1-firstRatio 25472) * √(1-firstRatio 25472) *
      sixthConstant (e1CovarianceRatio 25472 (mW 12736) (1/10^6) rowEps))) /
    (712/10000 - 25472*(1+1/10^6)*((2030893/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25472 (mW 12736) /
    ((1/10^5) * ((mW 12736 : ℝ)*25472*((mW 12736 : ℝ)+25472+1)))^2 +
  8*(mW 12736 : ℝ)*25472*(25472+2)*(25472+3) /
    ((1/1000)*((mW 12736 : ℝ)*25472*(25472+2)))^2 +
  covarianceVarianceBound 25472 (mW 12736) /
    ((1/1000)*covarianceMeanBound 25472 (mW 12736))^2 +
  normVarianceBound 25472 (mW 12736) / (3*inputVarianceMean 25472 (mW 12736))^2

end BstLean.Part268.WorldRow12736
namespace BstLean.Part268.WorldRow12737
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12737 = 233203476725259 := by
  have hu : mW 12737 ≤ 233203476725259 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12737 ≤ 233203476725258 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12737)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25474 ^ 2)
    ((25000000000000000000/4001446562877319647839239))
    ((25000000000000000000/4001289483244640158164579)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25474) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25474 : ℝ)^2 / (mW 12737 : ℝ)) * (1 + 1/10^6)^2 *
    √(((507683/250000000000))/2) * ((1-firstRatio 25474) * √(1-firstRatio 25474) *
      sixthConstant (e1CovarianceRatio 25474 (mW 12737) (1/10^6) rowEps))) /
    (712/10000 - 25474*(1+1/10^6)*((507683/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25474 (mW 12737) /
    ((1/10^5) * ((mW 12737 : ℝ)*25474*((mW 12737 : ℝ)+25474+1)))^2 +
  8*(mW 12737 : ℝ)*25474*(25474+2)*(25474+3) /
    ((1/1000)*((mW 12737 : ℝ)*25474*(25474+2)))^2 +
  covarianceVarianceBound 25474 (mW 12737) /
    ((1/1000)*covarianceMeanBound 25474 (mW 12737))^2 +
  normVarianceBound 25474 (mW 12737) / (3*inputVarianceMean 25474 (mW 12737))^2

end BstLean.Part268.WorldRow12737
namespace BstLean.Part268.WorldRow12738
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12738 = 233267564993624 := by
  have hu : mW 12738 ≤ 233267564993624 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12738 ≤ 233267564993623 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12738)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25476 ^ 2)
    ((12500000000000000000/2000880361071339313581543))
    ((1000000000000000000/160064145700399965499537)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25476) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25476 : ℝ)^2 / (mW 12738 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2030571/1000000000000))/2) * ((1-firstRatio 25476) * √(1-firstRatio 25476) *
      sixthConstant (e1CovarianceRatio 25476 (mW 12738) (1/10^6) rowEps))) /
    (712/10000 - 25476*(1+1/10^6)*((2030571/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25476 (mW 12738) /
    ((1/10^5) * ((mW 12738 : ℝ)*25476*((mW 12738 : ℝ)+25476+1)))^2 +
  8*(mW 12738 : ℝ)*25476*(25476+2)*(25476+3) /
    ((1/1000)*((mW 12738 : ℝ)*25476*(25476+2)))^2 +
  covarianceVarianceBound 25476 (mW 12738) /
    ((1/1000)*covarianceMeanBound 25476 (mW 12738))^2 +
  normVarianceBound 25476 (mW 12738) / (3*inputVarianceMean 25476 (mW 12738))^2

end BstLean.Part268.WorldRow12738
namespace BstLean.Part268.WorldRow12739
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12739 = 233331665841388 := by
  have hu : mW 12739 ≤ 233331665841388 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12739 ≤ 233331665841387 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12739)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25478 ^ 2)
    ((25000000000000000000/4002074881408037606486933))
    ((25000000000000000000/4001917801775358116812271)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25478) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25478 : ℝ)^2 / (mW 12739 : ℝ)) * (1 + 1/10^6)^2 *
    √(((203041/100000000000))/2) * ((1-firstRatio 25478) * √(1-firstRatio 25478) *
      sixthConstant (e1CovarianceRatio 25478 (mW 12739) (1/10^6) rowEps))) /
    (712/10000 - 25478*(1+1/10^6)*((203041/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25478 (mW 12739) /
    ((1/10^5) * ((mW 12739 : ℝ)*25478*((mW 12739 : ℝ)+25478+1)))^2 +
  8*(mW 12739 : ℝ)*25478*(25478+2)*(25478+3) /
    ((1/1000)*((mW 12739 : ℝ)*25478*(25478+2)))^2 +
  covarianceVarianceBound 25478 (mW 12739) /
    ((1/1000)*covarianceMeanBound 25478 (mW 12739))^2 +
  normVarianceBound 25478 (mW 12739) / (3*inputVarianceMean 25478 (mW 12739))^2

end BstLean.Part268.WorldRow12739
namespace BstLean.Part268.WorldRow12740
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12740 = 233395779270033 := by
  have hu : mW 12740 ≤ 233395779270033 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12740 ≤ 233395779270032 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12740)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25480 ^ 2)
    ((1250000000000000000/200119452033669829290539))
    ((25000000000000000000/4002231961040717096136117)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25480) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25480 : ℝ)^2 / (mW 12740 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2030249/1000000000000))/2) * ((1-firstRatio 25480) * √(1-firstRatio 25480) *
      sixthConstant (e1CovarianceRatio 25480 (mW 12740) (1/10^6) rowEps))) /
    (712/10000 - 25480*(1+1/10^6)*((2030249/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25480 (mW 12740) /
    ((1/10^5) * ((mW 12740 : ℝ)*25480*((mW 12740 : ℝ)+25480+1)))^2 +
  8*(mW 12740 : ℝ)*25480*(25480+2)*(25480+3) /
    ((1/1000)*((mW 12740 : ℝ)*25480*(25480+2)))^2 +
  covarianceVarianceBound 25480 (mW 12740) /
    ((1/1000)*covarianceMeanBound 25480 (mW 12740))^2 +
  normVarianceBound 25480 (mW 12740) / (3*inputVarianceMean 25480 (mW 12740))^2

end BstLean.Part268.WorldRow12740
namespace BstLean.Part268.WorldRow12741
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12741 = 233459905281041 := by
  have hu : mW 12741 ≤ 233459905281041 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12741 ≤ 233459905281040 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12741)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25482 ^ 2)
    ((25000000000000000000/4002703199938755565134627))
    ((25000000000000000000/4002546120306076075459963)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25482) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25482 : ℝ)^2 / (mW 12741 : ℝ)) * (1 + 1/10^6)^2 *
    √(((253761/125000000000))/2) * ((1-firstRatio 25482) * √(1-firstRatio 25482) *
      sixthConstant (e1CovarianceRatio 25482 (mW 12741) (1/10^6) rowEps))) /
    (712/10000 - 25482*(1+1/10^6)*((253761/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25482 (mW 12741) /
    ((1/10^5) * ((mW 12741 : ℝ)*25482*((mW 12741 : ℝ)+25482+1)))^2 +
  8*(mW 12741 : ℝ)*25482*(25482+2)*(25482+3) /
    ((1/1000)*((mW 12741 : ℝ)*25482*(25482+2)))^2 +
  covarianceVarianceBound 25482 (mW 12741) /
    ((1/1000)*covarianceMeanBound 25482 (mW 12741))^2 +
  normVarianceBound 25482 (mW 12741) / (3*inputVarianceMean 25482 (mW 12741))^2

end BstLean.Part268.WorldRow12741
namespace BstLean.Part268.WorldRow12742
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12742 = 233524043875893 := by
  have hu : mW 12742 ≤ 233524043875893 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12742 ≤ 233524043875892 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12742)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25484 ^ 2)
    ((12500000000000000000/2001508679602057272229237))
    ((25000000000000000000/4002860279571435054783809)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25484) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25484 : ℝ)^2 / (mW 12742 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2029927/1000000000000))/2) * ((1-firstRatio 25484) * √(1-firstRatio 25484) *
      sixthConstant (e1CovarianceRatio 25484 (mW 12742) (1/10^6) rowEps))) /
    (712/10000 - 25484*(1+1/10^6)*((2029927/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25484 (mW 12742) /
    ((1/10^5) * ((mW 12742 : ℝ)*25484*((mW 12742 : ℝ)+25484+1)))^2 +
  8*(mW 12742 : ℝ)*25484*(25484+2)*(25484+3) /
    ((1/1000)*((mW 12742 : ℝ)*25484*(25484+2)))^2 +
  covarianceVarianceBound 25484 (mW 12742) /
    ((1/1000)*covarianceMeanBound 25484 (mW 12742))^2 +
  normVarianceBound 25484 (mW 12742) / (3*inputVarianceMean 25484 (mW 12742))^2

end BstLean.Part268.WorldRow12742
namespace BstLean.Part268.WorldRow12743
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12743 = 233588195056071 := by
  have hu : mW 12743 ≤ 233588195056071 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12743 ≤ 233588195056070 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12743)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25486 ^ 2)
    ((25000000000000000000/4003331518469473523782321))
    ((5000000000000000000/800634887767358806821531)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25486) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25486 : ℝ)^2 / (mW 12743 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1014883/500000000000))/2) * ((1-firstRatio 25486) * √(1-firstRatio 25486) *
      sixthConstant (e1CovarianceRatio 25486 (mW 12743) (1/10^6) rowEps))) /
    (712/10000 - 25486*(1+1/10^6)*((1014883/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25486 (mW 12743) /
    ((1/10^5) * ((mW 12743 : ℝ)*25486*((mW 12743 : ℝ)+25486+1)))^2 +
  8*(mW 12743 : ℝ)*25486*(25486+2)*(25486+3) /
    ((1/1000)*((mW 12743 : ℝ)*25486*(25486+2)))^2 +
  covarianceVarianceBound 25486 (mW 12743) /
    ((1/1000)*covarianceMeanBound 25486 (mW 12743))^2 +
  normVarianceBound 25486 (mW 12743) / (3*inputVarianceMean 25486 (mW 12743))^2

end BstLean.Part268.WorldRow12743
namespace BstLean.Part268.WorldRow12744
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12744 = 233652358823055 := by
  have hu : mW 12744 ≤ 233652358823055 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12744 ≤ 233652358823054 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12744)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25488 ^ 2)
    ((3125000000000000000/500455709716854062888271))
    ((25000000000000000000/4003488598102153013431501)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25488) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25488 : ℝ)^2 / (mW 12744 : ℝ)) * (1 + 1/10^6)^2 *
    √(((405921/200000000000))/2) * ((1-firstRatio 25488) * √(1-firstRatio 25488) *
      sixthConstant (e1CovarianceRatio 25488 (mW 12744) (1/10^6) rowEps))) /
    (712/10000 - 25488*(1+1/10^6)*((405921/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25488 (mW 12744) /
    ((1/10^5) * ((mW 12744 : ℝ)*25488*((mW 12744 : ℝ)+25488+1)))^2 +
  8*(mW 12744 : ℝ)*25488*(25488+2)*(25488+3) /
    ((1/1000)*((mW 12744 : ℝ)*25488*(25488+2)))^2 +
  covarianceVarianceBound 25488 (mW 12744) /
    ((1/1000)*covarianceMeanBound 25488 (mW 12744))^2 +
  normVarianceBound 25488 (mW 12744) / (3*inputVarianceMean 25488 (mW 12744))^2

end BstLean.Part268.WorldRow12744
namespace BstLean.Part268.WorldRow12745
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12745 = 233716535178328 := by
  have hu : mW 12745 ≤ 233716535178328 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12745 ≤ 233716535178327 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12745)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25490 ^ 2)
    ((5000000000000000000/800791967400038296486003))
    ((25000000000000000000/4003802757367511992755347)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25490) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25490 : ℝ)^2 / (mW 12745 : ℝ)) * (1 + 1/10^6)^2 *
    √(((507361/250000000000))/2) * ((1-firstRatio 25490) * √(1-firstRatio 25490) *
      sixthConstant (e1CovarianceRatio 25490 (mW 12745) (1/10^6) rowEps))) /
    (712/10000 - 25490*(1+1/10^6)*((507361/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25490 (mW 12745) /
    ((1/10^5) * ((mW 12745 : ℝ)*25490*((mW 12745 : ℝ)+25490+1)))^2 +
  8*(mW 12745 : ℝ)*25490*(25490+2)*(25490+3) /
    ((1/1000)*((mW 12745 : ℝ)*25490*(25490+2)))^2 +
  covarianceVarianceBound 25490 (mW 12745) /
    ((1/1000)*covarianceMeanBound 25490 (mW 12745))^2 +
  normVarianceBound 25490 (mW 12745) / (3*inputVarianceMean 25490 (mW 12745))^2

end BstLean.Part268.WorldRow12745
namespace BstLean.Part268.WorldRow12746
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12746 = 233780724123372 := by
  have hu : mW 12746 ≤ 233780724123372 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12746 ≤ 233780724123371 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12746)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25492 ^ 2)
    ((12500000000000000000/2002136998132775230876931))
    ((25000000000000000000/4004116916632870972079193)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25492) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25492 : ℝ)^2 / (mW 12746 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2029283/1000000000000))/2) * ((1-firstRatio 25492) * √(1-firstRatio 25492) *
      sixthConstant (e1CovarianceRatio 25492 (mW 12746) (1/10^6) rowEps))) /
    (712/10000 - 25492*(1+1/10^6)*((2029283/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25492 (mW 12746) /
    ((1/10^5) * ((mW 12746 : ℝ)*25492*((mW 12746 : ℝ)+25492+1)))^2 +
  8*(mW 12746 : ℝ)*25492*(25492+2)*(25492+3) /
    ((1/1000)*((mW 12746 : ℝ)*25492*(25492+2)))^2 +
  covarianceVarianceBound 25492 (mW 12746) /
    ((1/1000)*covarianceMeanBound 25492 (mW 12746))^2 +
  normVarianceBound 25492 (mW 12746) / (3*inputVarianceMean 25492 (mW 12746))^2

end BstLean.Part268.WorldRow12746
namespace BstLean.Part268.WorldRow12747
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12747 = 233844925659668 := by
  have hu : mW 12747 ≤ 233844925659668 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12747 ≤ 233844925659667 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12747)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25494 ^ 2)
    ((25000000000000000000/4004588155530909441077709))
    ((25000000000000000000/4004431075898229951403039)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25494) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25494 : ℝ)^2 / (mW 12747 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2029123/1000000000000))/2) * ((1-firstRatio 25494) * √(1-firstRatio 25494) *
      sixthConstant (e1CovarianceRatio 25494 (mW 12747) (1/10^6) rowEps))) /
    (712/10000 - 25494*(1+1/10^6)*((2029123/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25494 (mW 12747) /
    ((1/10^5) * ((mW 12747 : ℝ)*25494*((mW 12747 : ℝ)+25494+1)))^2 +
  8*(mW 12747 : ℝ)*25494*(25494+2)*(25494+3) /
    ((1/1000)*((mW 12747 : ℝ)*25494*(25494+2)))^2 +
  covarianceVarianceBound 25494 (mW 12747) /
    ((1/1000)*covarianceMeanBound 25494 (mW 12747))^2 +
  normVarianceBound 25494 (mW 12747) / (3*inputVarianceMean 25494 (mW 12747))^2

end BstLean.Part268.WorldRow12747
namespace BstLean.Part268.WorldRow12748
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12748 = 233909139788699 := by
  have hu : mW 12748 ≤ 233909139788699 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12748 ≤ 233909139788698 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12748)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25496 ^ 2)
    ((6250000000000000000/1001225578699067105100389))
    ((5000000000000000000/800949047032717786145377)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25496) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25496 : ℝ)^2 / (mW 12748 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1014481/500000000000))/2) * ((1-firstRatio 25496) * √(1-firstRatio 25496) *
      sixthConstant (e1CovarianceRatio 25496 (mW 12748) (1/10^6) rowEps))) /
    (712/10000 - 25496*(1+1/10^6)*((1014481/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25496 (mW 12748) /
    ((1/10^5) * ((mW 12748 : ℝ)*25496*((mW 12748 : ℝ)+25496+1)))^2 +
  8*(mW 12748 : ℝ)*25496*(25496+2)*(25496+3) /
    ((1/1000)*((mW 12748 : ℝ)*25496*(25496+2)))^2 +
  covarianceVarianceBound 25496 (mW 12748) /
    ((1/1000)*covarianceMeanBound 25496 (mW 12748))^2 +
  normVarianceBound 25496 (mW 12748) / (3*inputVarianceMean 25496 (mW 12748))^2

end BstLean.Part268.WorldRow12748
namespace BstLean.Part268.WorldRow12749
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12749 = 233973366511945 := by
  have hu : mW 12749 ≤ 233973366511945 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12749 ≤ 233973366511944 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12749)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25498 ^ 2)
    ((25000000000000000000/4005216474061627399725403))
    ((25000000000000000000/4005059394428947910050731)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25498) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25498 : ℝ)^2 / (mW 12749 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2028801/1000000000000))/2) * ((1-firstRatio 25498) * √(1-firstRatio 25498) *
      sixthConstant (e1CovarianceRatio 25498 (mW 12749) (1/10^6) rowEps))) /
    (712/10000 - 25498*(1+1/10^6)*((2028801/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25498 (mW 12749) /
    ((1/10^5) * ((mW 12749 : ℝ)*25498*((mW 12749 : ℝ)+25498+1)))^2 +
  8*(mW 12749 : ℝ)*25498*(25498+2)*(25498+3) /
    ((1/1000)*((mW 12749 : ℝ)*25498*(25498+2)))^2 +
  covarianceVarianceBound 25498 (mW 12749) /
    ((1/1000)*covarianceMeanBound 25498 (mW 12749))^2 +
  normVarianceBound 25498 (mW 12749) / (3*inputVarianceMean 25498 (mW 12749))^2

end BstLean.Part268.WorldRow12749
