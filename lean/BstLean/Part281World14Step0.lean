import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part281Scalar14
namespace BstLean.Part281.WorldRow12209
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12209 = 201085302165054 := by
  have hu : mW 12209 ≤ 201085302165054 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12209 ≤ 201085302165053 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12209)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24418 ^ 2)
    ((25000000000000000000/3835570470767778564848023))
    ((25000000000000000000/3835413391135099075173891)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24418) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24418 : ℝ)^2 / (mW 12209 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2119519/1000000000000))/2) * ((1-firstRatio 24418) * √(1-firstRatio 24418) *
      sixthConstant (e1CovarianceRatio 24418 (mW 12209) (1/10^6) rowEps))) /
    (712/10000 - 24418*(1+1/10^6)*((2119519/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24418 (mW 12209) /
    ((1/10^5) * ((mW 12209 : ℝ)*24418*((mW 12209 : ℝ)+24418+1)))^2 +
  8*(mW 12209 : ℝ)*24418*(24418+2)*(24418+3) /
    ((1/1000)*((mW 12209 : ℝ)*24418*(24418+2)))^2 +
  covarianceVarianceBound 24418 (mW 12209) /
    ((1/1000)*covarianceMeanBound 24418 (mW 12209))^2 +
  normVarianceBound 24418 (mW 12209) / (3*inputVarianceMean 24418 (mW 12209))^2

end BstLean.Part281.WorldRow12209
namespace BstLean.Part281.WorldRow12210
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12210 = 201142953947991 := by
  have hu : mW 12210 ≤ 201142953947991 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12210 ≤ 201142953947990 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12210)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24420 ^ 2)
    ((2500000000000000000/383588463003313754417187))
    ((25000000000000000000/3835727550400458054497737)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24420) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24420 : ℝ)^2 / (mW 12210 : ℝ)) * (1 + 1/10^6)^2 *
    √(((132459/62500000000))/2) * ((1-firstRatio 24420) * √(1-firstRatio 24420) *
      sixthConstant (e1CovarianceRatio 24420 (mW 12210) (1/10^6) rowEps))) /
    (712/10000 - 24420*(1+1/10^6)*((132459/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24420 (mW 12210) /
    ((1/10^5) * ((mW 12210 : ℝ)*24420*((mW 12210 : ℝ)+24420+1)))^2 +
  8*(mW 12210 : ℝ)*24420*(24420+2)*(24420+3) /
    ((1/1000)*((mW 12210 : ℝ)*24420*(24420+2)))^2 +
  covarianceVarianceBound 24420 (mW 12210) /
    ((1/1000)*covarianceMeanBound 24420 (mW 12210))^2 +
  normVarianceBound 24420 (mW 12210) / (3*inputVarianceMean 24420 (mW 12210))^2

end BstLean.Part281.WorldRow12210
namespace BstLean.Part281.WorldRow12211
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12211 = 201200617536351 := by
  have hu : mW 12211 ≤ 201200617536351 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12211 ≤ 201200617536350 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12211)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24422 ^ 2)
    ((25000000000000000000/3836198789298496523495717))
    ((25000000000000000000/3836041709665817033821583)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24422) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24422 : ℝ)^2 / (mW 12211 : ℝ)) * (1 + 1/10^6)^2 *
    √(((4139/1953125000))/2) * ((1-firstRatio 24422) * √(1-firstRatio 24422) *
      sixthConstant (e1CovarianceRatio 24422 (mW 12211) (1/10^6) rowEps))) /
    (712/10000 - 24422*(1+1/10^6)*((4139/1953125000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24422 (mW 12211) /
    ((1/10^5) * ((mW 12211 : ℝ)*24422*((mW 12211 : ℝ)+24422+1)))^2 +
  8*(mW 12211 : ℝ)*24422*(24422+2)*(24422+3) /
    ((1/1000)*((mW 12211 : ℝ)*24422*(24422+2)))^2 +
  covarianceVarianceBound 24422 (mW 12211) /
    ((1/1000)*covarianceMeanBound 24422 (mW 12211))^2 +
  normVarianceBound 24422 (mW 12211) / (3*inputVarianceMean 24422 (mW 12211))^2

end BstLean.Part281.WorldRow12211
namespace BstLean.Part281.WorldRow12212
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12212 = 201258292931584 := by
  have hu : mW 12212 ≤ 201258292931584 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12212 ≤ 201258292931583 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12212)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24424 ^ 2)
    ((6250000000000000000/959128237140963875704891))
    ((25000000000000000000/3836355868931176013145429)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24424) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24424 : ℝ)^2 / (mW 12212 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2118993/1000000000000))/2) * ((1-firstRatio 24424) * √(1-firstRatio 24424) *
      sixthConstant (e1CovarianceRatio 24424 (mW 12212) (1/10^6) rowEps))) /
    (712/10000 - 24424*(1+1/10^6)*((2118993/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24424 (mW 12212) /
    ((1/10^5) * ((mW 12212 : ℝ)*24424*((mW 12212 : ℝ)+24424+1)))^2 +
  8*(mW 12212 : ℝ)*24424*(24424+2)*(24424+3) /
    ((1/1000)*((mW 12212 : ℝ)*24424*(24424+2)))^2 +
  covarianceVarianceBound 24424 (mW 12212) /
    ((1/1000)*covarianceMeanBound 24424 (mW 12212))^2 +
  normVarianceBound 24424 (mW 12212) / (3*inputVarianceMean 24424 (mW 12212))^2

end BstLean.Part281.WorldRow12212
namespace BstLean.Part281.WorldRow12213
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12213 = 201315980135141 := by
  have hu : mW 12213 ≤ 201315980135141 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12213 ≤ 201315980135140 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12213)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24426 ^ 2)
    ((25000000000000000000/3836827107829214482143411))
    ((1000000000000000000/153466801127861399698771)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24426) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24426 : ℝ)^2 / (mW 12213 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2118817/1000000000000))/2) * ((1-firstRatio 24426) * √(1-firstRatio 24426) *
      sixthConstant (e1CovarianceRatio 24426 (mW 12213) (1/10^6) rowEps))) /
    (712/10000 - 24426*(1+1/10^6)*((2118817/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24426 (mW 12213) /
    ((1/10^5) * ((mW 12213 : ℝ)*24426*((mW 12213 : ℝ)+24426+1)))^2 +
  8*(mW 12213 : ℝ)*24426*(24426+2)*(24426+3) /
    ((1/1000)*((mW 12213 : ℝ)*24426*(24426+2)))^2 +
  covarianceVarianceBound 24426 (mW 12213) /
    ((1/1000)*covarianceMeanBound 24426 (mW 12213))^2 +
  normVarianceBound 24426 (mW 12213) / (3*inputVarianceMean 24426 (mW 12213))^2

end BstLean.Part281.WorldRow12213
namespace BstLean.Part281.WorldRow12214
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12214 = 201373679148472 := by
  have hu : mW 12214 ≤ 201373679148472 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12214 ≤ 201373679148471 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12214)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24428 ^ 2)
    ((12500000000000000000/1918570633547286730733629))
    ((25000000000000000000/3836984187461893971793121)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24428) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24428 : ℝ)^2 / (mW 12214 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1059321/500000000000))/2) * ((1-firstRatio 24428) * √(1-firstRatio 24428) *
      sixthConstant (e1CovarianceRatio 24428 (mW 12214) (1/10^6) rowEps))) /
    (712/10000 - 24428*(1+1/10^6)*((1059321/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24428 (mW 12214) /
    ((1/10^5) * ((mW 12214 : ℝ)*24428*((mW 12214 : ℝ)+24428+1)))^2 +
  8*(mW 12214 : ℝ)*24428*(24428+2)*(24428+3) /
    ((1/1000)*((mW 12214 : ℝ)*24428*(24428+2)))^2 +
  covarianceVarianceBound 24428 (mW 12214) /
    ((1/1000)*covarianceMeanBound 24428 (mW 12214))^2 +
  normVarianceBound 24428 (mW 12214) / (3*inputVarianceMean 24428 (mW 12214))^2

end BstLean.Part281.WorldRow12214
namespace BstLean.Part281.WorldRow12215
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12215 = 201431389973027 := by
  have hu : mW 12215 ≤ 201431389973027 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12215 ≤ 201431389973026 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12215)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24430 ^ 2)
    ((5000000000000000000/767491085271986488158221))
    ((25000000000000000000/3837298346727252951116967)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24430) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24430 : ℝ)^2 / (mW 12215 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2118467/1000000000000))/2) * ((1-firstRatio 24430) * √(1-firstRatio 24430) *
      sixthConstant (e1CovarianceRatio 24430 (mW 12215) (1/10^6) rowEps))) /
    (712/10000 - 24430*(1+1/10^6)*((2118467/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24430 (mW 12215) /
    ((1/10^5) * ((mW 12215 : ℝ)*24430*((mW 12215 : ℝ)+24430+1)))^2 +
  8*(mW 12215 : ℝ)*24430*(24430+2)*(24430+3) /
    ((1/1000)*((mW 12215 : ℝ)*24430*(24430+2)))^2 +
  covarianceVarianceBound 24430 (mW 12215) /
    ((1/1000)*covarianceMeanBound 24430 (mW 12215))^2 +
  normVarianceBound 24430 (mW 12215) / (3*inputVarianceMean 24430 (mW 12215))^2

end BstLean.Part281.WorldRow12215
namespace BstLean.Part281.WorldRow12216
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12216 = 201489112610258 := by
  have hu : mW 12216 ≤ 201489112610258 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12216 ≤ 201489112610257 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12216)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24432 ^ 2)
    ((3125000000000000000/479721198203161427514369))
    ((25000000000000000000/3837612505992611930440813)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24432) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24432 : ℝ)^2 / (mW 12216 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2118291/1000000000000))/2) * ((1-firstRatio 24432) * √(1-firstRatio 24432) *
      sixthConstant (e1CovarianceRatio 24432 (mW 12216) (1/10^6) rowEps))) /
    (712/10000 - 24432*(1+1/10^6)*((2118291/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24432 (mW 12216) /
    ((1/10^5) * ((mW 12216 : ℝ)*24432*((mW 12216 : ℝ)+24432+1)))^2 +
  8*(mW 12216 : ℝ)*24432*(24432+2)*(24432+3) /
    ((1/1000)*((mW 12216 : ℝ)*24432*(24432+2)))^2 +
  covarianceVarianceBound 24432 (mW 12216) /
    ((1/1000)*covarianceMeanBound 24432 (mW 12216))^2 +
  normVarianceBound 24432 (mW 12216) / (3*inputVarianceMean 24432 (mW 12216))^2

end BstLean.Part281.WorldRow12216
namespace BstLean.Part281.WorldRow12217
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12217 = 201546847061614 := by
  have hu : mW 12217 ≤ 201546847061614 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12217 ≤ 201546847061613 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12217)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24434 ^ 2)
    ((25000000000000000000/3838083744890650399438799))
    ((25000000000000000000/3837926665257970909764659)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24434) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24434 : ℝ)^2 / (mW 12217 : ℝ)) * (1 + 1/10^6)^2 *
    √(((529529/250000000000))/2) * ((1-firstRatio 24434) * √(1-firstRatio 24434) *
      sixthConstant (e1CovarianceRatio 24434 (mW 12217) (1/10^6) rowEps))) /
    (712/10000 - 24434*(1+1/10^6)*((529529/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24434 (mW 12217) /
    ((1/10^5) * ((mW 12217 : ℝ)*24434*((mW 12217 : ℝ)+24434+1)))^2 +
  8*(mW 12217 : ℝ)*24434*(24434+2)*(24434+3) /
    ((1/1000)*((mW 12217 : ℝ)*24434*(24434+2)))^2 +
  covarianceVarianceBound 24434 (mW 12217) /
    ((1/1000)*covarianceMeanBound 24434 (mW 12217))^2 +
  normVarianceBound 24434 (mW 12217) / (3*inputVarianceMean 24434 (mW 12217))^2

end BstLean.Part281.WorldRow12217
namespace BstLean.Part281.WorldRow12218
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12218 = 201604593328547 := by
  have hu : mW 12218 ≤ 201604593328547 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12218 ≤ 201604593328546 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12218)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24436 ^ 2)
    ((12500000000000000000/1919198952078004689381323))
    ((5000000000000000000/767648164904665977817701)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24436) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24436 : ℝ)^2 / (mW 12218 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2117941/1000000000000))/2) * ((1-firstRatio 24436) * √(1-firstRatio 24436) *
      sixthConstant (e1CovarianceRatio 24436 (mW 12218) (1/10^6) rowEps))) /
    (712/10000 - 24436*(1+1/10^6)*((2117941/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24436 (mW 12218) /
    ((1/10^5) * ((mW 12218 : ℝ)*24436*((mW 12218 : ℝ)+24436+1)))^2 +
  8*(mW 12218 : ℝ)*24436*(24436+2)*(24436+3) /
    ((1/1000)*((mW 12218 : ℝ)*24436*(24436+2)))^2 +
  covarianceVarianceBound 24436 (mW 12218) /
    ((1/1000)*covarianceMeanBound 24436 (mW 12218))^2 +
  normVarianceBound 24436 (mW 12218) / (3*inputVarianceMean 24436 (mW 12218))^2

end BstLean.Part281.WorldRow12218
namespace BstLean.Part281.WorldRow12219
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12219 = 201662351412507 := by
  have hu : mW 12219 ≤ 201662351412507 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12219 ≤ 201662351412506 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12219)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24438 ^ 2)
    ((25000000000000000000/3838712063421368358086493))
    ((25000000000000000000/3838554983788688868412351)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24438) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24438 : ℝ)^2 / (mW 12219 : ℝ)) * (1 + 1/10^6)^2 *
    √(((423553/200000000000))/2) * ((1-firstRatio 24438) * √(1-firstRatio 24438) *
      sixthConstant (e1CovarianceRatio 24438 (mW 12219) (1/10^6) rowEps))) /
    (712/10000 - 24438*(1+1/10^6)*((423553/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24438 (mW 12219) /
    ((1/10^5) * ((mW 12219 : ℝ)*24438*((mW 12219 : ℝ)+24438+1)))^2 +
  8*(mW 12219 : ℝ)*24438*(24438+2)*(24438+3) /
    ((1/1000)*((mW 12219 : ℝ)*24438*(24438+2)))^2 +
  covarianceVarianceBound 24438 (mW 12219) /
    ((1/1000)*covarianceMeanBound 24438 (mW 12219))^2 +
  normVarianceBound 24438 (mW 12219) / (3*inputVarianceMean 24438 (mW 12219))^2

end BstLean.Part281.WorldRow12219
namespace BstLean.Part281.WorldRow12220
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12220 = 201720121314945 := by
  have hu : mW 12220 ≤ 201720121314945 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12220 ≤ 201720121314944 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12220)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24440 ^ 2)
    ((1250000000000000000/191951311134336366870517))
    ((25000000000000000000/3838869143054047847736197)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24440) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24440 : ℝ)^2 / (mW 12220 : ℝ)) * (1 + 1/10^6)^2 *
    √(((211759/100000000000))/2) * ((1-firstRatio 24440) * √(1-firstRatio 24440) *
      sixthConstant (e1CovarianceRatio 24440 (mW 12220) (1/10^6) rowEps))) /
    (712/10000 - 24440*(1+1/10^6)*((211759/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24440 (mW 12220) /
    ((1/10^5) * ((mW 12220 : ℝ)*24440*((mW 12220 : ℝ)+24440+1)))^2 +
  8*(mW 12220 : ℝ)*24440*(24440+2)*(24440+3) /
    ((1/1000)*((mW 12220 : ℝ)*24440*(24440+2)))^2 +
  covarianceVarianceBound 24440 (mW 12220) /
    ((1/1000)*covarianceMeanBound 24440 (mW 12220))^2 +
  normVarianceBound 24440 (mW 12220) / (3*inputVarianceMean 24440 (mW 12220))^2

end BstLean.Part281.WorldRow12220
namespace BstLean.Part281.WorldRow12221
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12221 = 201777903037312 := by
  have hu : mW 12221 ≤ 201777903037312 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12221 ≤ 201777903037311 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12221)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24442 ^ 2)
    ((25000000000000000000/3839340381952086316734187))
    ((25000000000000000000/3839183302319406827060043)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24442) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24442 : ℝ)^2 / (mW 12221 : ℝ)) * (1 + 1/10^6)^2 *
    √(((423483/200000000000))/2) * ((1-firstRatio 24442) * √(1-firstRatio 24442) *
      sixthConstant (e1CovarianceRatio 24442 (mW 12221) (1/10^6) rowEps))) /
    (712/10000 - 24442*(1+1/10^6)*((423483/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24442 (mW 12221) /
    ((1/10^5) * ((mW 12221 : ℝ)*24442*((mW 12221 : ℝ)+24442+1)))^2 +
  8*(mW 12221 : ℝ)*24442*(24442+2)*(24442+3) /
    ((1/1000)*((mW 12221 : ℝ)*24442*(24442+2)))^2 +
  covarianceVarianceBound 24442 (mW 12221) /
    ((1/1000)*covarianceMeanBound 24442 (mW 12221))^2 +
  normVarianceBound 24442 (mW 12221) / (3*inputVarianceMean 24442 (mW 12221))^2

end BstLean.Part281.WorldRow12221
namespace BstLean.Part281.WorldRow12222
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12222 = 201835696581059 := by
  have hu : mW 12222 ≤ 201835696581059 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12222 ≤ 201835696581058 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12222)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24444 ^ 2)
    ((12500000000000000000/1919827270608722648029017))
    ((25000000000000000000/3839497461584765806383889)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24444) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24444 : ℝ)^2 / (mW 12222 : ℝ)) * (1 + 1/10^6)^2 *
    √(((52931/25000000000))/2) * ((1-firstRatio 24444) * √(1-firstRatio 24444) *
      sixthConstant (e1CovarianceRatio 24444 (mW 12222) (1/10^6) rowEps))) /
    (712/10000 - 24444*(1+1/10^6)*((52931/25000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24444 (mW 12222) /
    ((1/10^5) * ((mW 12222 : ℝ)*24444*((mW 12222 : ℝ)+24444+1)))^2 +
  8*(mW 12222 : ℝ)*24444*(24444+2)*(24444+3) /
    ((1/1000)*((mW 12222 : ℝ)*24444*(24444+2)))^2 +
  covarianceVarianceBound 24444 (mW 12222) /
    ((1/1000)*covarianceMeanBound 24444 (mW 12222))^2 +
  normVarianceBound 24444 (mW 12222) / (3*inputVarianceMean 24444 (mW 12222))^2

end BstLean.Part281.WorldRow12222
namespace BstLean.Part281.WorldRow12223
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12223 = 201893501947636 := by
  have hu : mW 12223 ≤ 201893501947636 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12223 ≤ 201893501947635 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12223)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24446 ^ 2)
    ((25000000000000000000/3839968700482804275381881))
    ((5000000000000000000/767962324170024957141547)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24446) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24446 : ℝ)^2 / (mW 12223 : ℝ)) * (1 + 1/10^6)^2 *
    √(((423413/200000000000))/2) * ((1-firstRatio 24446) * √(1-firstRatio 24446) *
      sixthConstant (e1CovarianceRatio 24446 (mW 12223) (1/10^6) rowEps))) /
    (712/10000 - 24446*(1+1/10^6)*((423413/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24446 (mW 12223) /
    ((1/10^5) * ((mW 12223 : ℝ)*24446*((mW 12223 : ℝ)+24446+1)))^2 +
  8*(mW 12223 : ℝ)*24446*(24446+2)*(24446+3) /
    ((1/1000)*((mW 12223 : ℝ)*24446*(24446+2)))^2 +
  covarianceVarianceBound 24446 (mW 12223) /
    ((1/1000)*covarianceMeanBound 24446 (mW 12223))^2 +
  normVarianceBound 24446 (mW 12223) / (3*inputVarianceMean 24446 (mW 12223))^2

end BstLean.Part281.WorldRow12223
