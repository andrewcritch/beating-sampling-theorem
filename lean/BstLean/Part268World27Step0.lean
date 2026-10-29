import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar27
namespace BstLean.Part268.WorldRow13025
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13025 = 252186632169498 := by
  have hu : mW 13025 ≤ 252186632169498 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13025 ≤ 252186632169497 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13025)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26050 ^ 2)
    ((1000000000000000000/163676977252028227724287))
    ((25000000000000000000/4091767351668026203432227)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26050) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26050 : ℝ)^2 / (mW 13025 : ℝ)) * (1 + 1/10^6)^2 *
    √(((62043/31250000000))/2) * ((1-firstRatio 26050) * √(1-firstRatio 26050) *
      sixthConstant (e1CovarianceRatio 26050 (mW 13025) (1/10^6) rowEps))) /
    (712/10000 - 26050*(1+1/10^6)*((62043/31250000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26050 (mW 13025) /
    ((1/10^5) * ((mW 13025 : ℝ)*26050*((mW 13025 : ℝ)+26050+1)))^2 +
  8*(mW 13025 : ℝ)*26050*(26050+2)*(26050+3) /
    ((1/1000)*((mW 13025 : ℝ)*26050*(26050+2)))^2 +
  covarianceVarianceBound 26050 (mW 13025) /
    ((1/1000)*covarianceMeanBound 26050 (mW 13025))^2 +
  normVarianceBound 26050 (mW 13025) / (3*inputVarianceMean 26050 (mW 13025))^2

end BstLean.Part268.WorldRow13025
namespace BstLean.Part268.WorldRow13026
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13026 = 252254404754792 := by
  have hu : mW 13026 ≤ 252254404754792 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13026 ≤ 252254404754791 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13026)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26052 ^ 2)
    ((12500000000000000000/2046119295283032336215511))
    ((25000000000000000000/4092081510933385182756073)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26052) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26052 : ℝ)^2 / (mW 13026 : ℝ)) * (1 + 1/10^6)^2 *
    √(((992611/500000000000))/2) * ((1-firstRatio 26052) * √(1-firstRatio 26052) *
      sixthConstant (e1CovarianceRatio 26052 (mW 13026) (1/10^6) rowEps))) /
    (712/10000 - 26052*(1+1/10^6)*((992611/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26052 (mW 13026) /
    ((1/10^5) * ((mW 13026 : ℝ)*26052*((mW 13026 : ℝ)+26052+1)))^2 +
  8*(mW 13026 : ℝ)*26052*(26052+2)*(26052+3) /
    ((1/1000)*((mW 13026 : ℝ)*26052*(26052+2)))^2 +
  covarianceVarianceBound 26052 (mW 13026) /
    ((1/1000)*covarianceMeanBound 26052 (mW 13026))^2 +
  normVarianceBound 26052 (mW 13026) / (3*inputVarianceMean 26052 (mW 13026))^2

end BstLean.Part268.WorldRow13026
namespace BstLean.Part268.WorldRow13027
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13027 = 252322190348509 := by
  have hu : mW 13027 ≤ 252322190348509 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13027 ≤ 252322190348508 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13027)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26054 ^ 2)
    ((25000000000000000000/4092552749831423651754869))
    ((25000000000000000000/4092395670198744162079919)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26054) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26054 : ℝ)^2 / (mW 13027 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1985069/1000000000000))/2) * ((1-firstRatio 26054) * √(1-firstRatio 26054) *
      sixthConstant (e1CovarianceRatio 26054 (mW 13027) (1/10^6) rowEps))) /
    (712/10000 - 26054*(1+1/10^6)*((1985069/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26054 (mW 13027) /
    ((1/10^5) * ((mW 13027 : ℝ)*26054*((mW 13027 : ℝ)+26054+1)))^2 +
  8*(mW 13027 : ℝ)*26054*(26054+2)*(26054+3) /
    ((1/1000)*((mW 13027 : ℝ)*26054*(26054+2)))^2 +
  covarianceVarianceBound 26054 (mW 13027) /
    ((1/1000)*covarianceMeanBound 26054 (mW 13027))^2 +
  normVarianceBound 26054 (mW 13027) / (3*inputVarianceMean 26054 (mW 13027))^2

end BstLean.Part268.WorldRow13027
namespace BstLean.Part268.WorldRow13028
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13028 = 252389988952147 := by
  have hu : mW 13028 ≤ 252389988952147 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13028 ≤ 252389988952146 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13028)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26056 ^ 2)
    ((6250000000000000000/1023216727274195657769679))
    ((5000000000000000000/818541965892820628280753)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26056) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26056 : ℝ)^2 / (mW 13028 : ℝ)) * (1 + 1/10^6)^2 *
    √(((396983/200000000000))/2) * ((1-firstRatio 26056) * √(1-firstRatio 26056) *
      sixthConstant (e1CovarianceRatio 26056 (mW 13028) (1/10^6) rowEps))) /
    (712/10000 - 26056*(1+1/10^6)*((396983/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26056 (mW 13028) /
    ((1/10^5) * ((mW 13028 : ℝ)*26056*((mW 13028 : ℝ)+26056+1)))^2 +
  8*(mW 13028 : ℝ)*26056*(26056+2)*(26056+3) /
    ((1/1000)*((mW 13028 : ℝ)*26056*(26056+2)))^2 +
  covarianceVarianceBound 26056 (mW 13028) /
    ((1/1000)*covarianceMeanBound 26056 (mW 13028))^2 +
  normVarianceBound 26056 (mW 13028) / (3*inputVarianceMean 26056 (mW 13028))^2

end BstLean.Part268.WorldRow13028
namespace BstLean.Part268.WorldRow13029
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13029 = 252457800567205 := by
  have hu : mW 13029 ≤ 252457800567205 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13029 ≤ 252457800567204 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13029)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26058 ^ 2)
    ((25000000000000000000/4093181068362141610402563))
    ((25000000000000000000/4093023988729462120727611)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26058) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26058 : ℝ)^2 / (mW 13029 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1984761/1000000000000))/2) * ((1-firstRatio 26058) * √(1-firstRatio 26058) *
      sixthConstant (e1CovarianceRatio 26058 (mW 13029) (1/10^6) rowEps))) /
    (712/10000 - 26058*(1+1/10^6)*((1984761/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26058 (mW 13029) /
    ((1/10^5) * ((mW 13029 : ℝ)*26058*((mW 13029 : ℝ)+26058+1)))^2 +
  8*(mW 13029 : ℝ)*26058*(26058+2)*(26058+3) /
    ((1/1000)*((mW 13029 : ℝ)*26058*(26058+2)))^2 +
  covarianceVarianceBound 26058 (mW 13029) /
    ((1/1000)*covarianceMeanBound 26058 (mW 13029))^2 +
  normVarianceBound 26058 (mW 13029) / (3*inputVarianceMean 26058 (mW 13029))^2

end BstLean.Part268.WorldRow13029
namespace BstLean.Part268.WorldRow13030
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13030 = 252525625195180 := by
  have hu : mW 13030 ≤ 252525625195180 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13030 ≤ 252525625195179 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13030)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26060 ^ 2)
    ((2500000000000000000/409349522762750058972641))
    ((25000000000000000000/4093338147994821100051457)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26060) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26060 : ℝ)^2 / (mW 13030 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1984607/1000000000000))/2) * ((1-firstRatio 26060) * √(1-firstRatio 26060) *
      sixthConstant (e1CovarianceRatio 26060 (mW 13030) (1/10^6) rowEps))) /
    (712/10000 - 26060*(1+1/10^6)*((1984607/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26060 (mW 13030) /
    ((1/10^5) * ((mW 13030 : ℝ)*26060*((mW 13030 : ℝ)+26060+1)))^2 +
  8*(mW 13030 : ℝ)*26060*(26060+2)*(26060+3) /
    ((1/1000)*((mW 13030 : ℝ)*26060*(26060+2)))^2 +
  covarianceVarianceBound 26060 (mW 13030) /
    ((1/1000)*covarianceMeanBound 26060 (mW 13030))^2 +
  normVarianceBound 26060 (mW 13030) / (3*inputVarianceMean 26060 (mW 13030))^2

end BstLean.Part268.WorldRow13030
namespace BstLean.Part268.WorldRow13031
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13031 = 252593462837571 := by
  have hu : mW 13031 ≤ 252593462837571 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13031 ≤ 252593462837570 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13031)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26062 ^ 2)
    ((25000000000000000000/4093809386892859569050257))
    ((25000000000000000000/4093652307260180079375303)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26062) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26062 : ℝ)^2 / (mW 13031 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1984453/1000000000000))/2) * ((1-firstRatio 26062) * √(1-firstRatio 26062) *
      sixthConstant (e1CovarianceRatio 26062 (mW 13031) (1/10^6) rowEps))) /
    (712/10000 - 26062*(1+1/10^6)*((1984453/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26062 (mW 13031) /
    ((1/10^5) * ((mW 13031 : ℝ)*26062*((mW 13031 : ℝ)+26062+1)))^2 +
  8*(mW 13031 : ℝ)*26062*(26062+2)*(26062+3) /
    ((1/1000)*((mW 13031 : ℝ)*26062*(26062+2)))^2 +
  covarianceVarianceBound 26062 (mW 13031) /
    ((1/1000)*covarianceMeanBound 26062 (mW 13031))^2 +
  normVarianceBound 26062 (mW 13031) / (3*inputVarianceMean 26062 (mW 13031))^2

end BstLean.Part268.WorldRow13031
namespace BstLean.Part268.WorldRow13032
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13032 = 252661313495876 := by
  have hu : mW 13032 ≤ 252661313495876 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13032 ≤ 252661313495875 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13032)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26064 ^ 2)
    ((3125000000000000000/511765443269777318546763))
    ((25000000000000000000/4093966466525539058699149)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26064) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26064 : ℝ)^2 / (mW 13032 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1984299/1000000000000))/2) * ((1-firstRatio 26064) * √(1-firstRatio 26064) *
      sixthConstant (e1CovarianceRatio 26064 (mW 13032) (1/10^6) rowEps))) /
    (712/10000 - 26064*(1+1/10^6)*((1984299/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26064 (mW 13032) /
    ((1/10^5) * ((mW 13032 : ℝ)*26064*((mW 13032 : ℝ)+26064+1)))^2 +
  8*(mW 13032 : ℝ)*26064*(26064+2)*(26064+3) /
    ((1/1000)*((mW 13032 : ℝ)*26064*(26064+2)))^2 +
  covarianceVarianceBound 26064 (mW 13032) /
    ((1/1000)*covarianceMeanBound 26064 (mW 13032))^2 +
  normVarianceBound 26064 (mW 13032) / (3*inputVarianceMean 26064 (mW 13032))^2

end BstLean.Part268.WorldRow13032
namespace BstLean.Part268.WorldRow13033
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13033 = 252729177171593 := by
  have hu : mW 13033 ≤ 252729177171593 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13033 ≤ 252729177171592 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13033)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26066 ^ 2)
    ((25000000000000000000/4094437705423577527697951))
    ((5000000000000000000/818856125158179607604599)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26066) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26066 : ℝ)^2 / (mW 13033 : ℝ)) * (1 + 1/10^6)^2 *
    √(((992073/500000000000))/2) * ((1-firstRatio 26066) * √(1-firstRatio 26066) *
      sixthConstant (e1CovarianceRatio 26066 (mW 13033) (1/10^6) rowEps))) /
    (712/10000 - 26066*(1+1/10^6)*((992073/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26066 (mW 13033) /
    ((1/10^5) * ((mW 13033 : ℝ)*26066*((mW 13033 : ℝ)+26066+1)))^2 +
  8*(mW 13033 : ℝ)*26066*(26066+2)*(26066+3) /
    ((1/1000)*((mW 13033 : ℝ)*26066*(26066+2)))^2 +
  covarianceVarianceBound 26066 (mW 13033) /
    ((1/1000)*covarianceMeanBound 26066 (mW 13033))^2 +
  normVarianceBound 26066 (mW 13033) / (3*inputVarianceMean 26066 (mW 13033))^2

end BstLean.Part268.WorldRow13033
namespace BstLean.Part268.WorldRow13034
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13034 = 252797053866221 := by
  have hu : mW 13034 ≤ 252797053866221 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13034 ≤ 252797053866220 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13034)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26068 ^ 2)
    ((12500000000000000000/2047375932344468253510899))
    ((25000000000000000000/4094594785056257017346841)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26068) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26068 : ℝ)^2 / (mW 13034 : ℝ)) * (1 + 1/10^6)^2 *
    √(((247999/125000000000))/2) * ((1-firstRatio 26068) * √(1-firstRatio 26068) *
      sixthConstant (e1CovarianceRatio 26068 (mW 13034) (1/10^6) rowEps))) /
    (712/10000 - 26068*(1+1/10^6)*((247999/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26068 (mW 13034) /
    ((1/10^5) * ((mW 13034 : ℝ)*26068*((mW 13034 : ℝ)+26068+1)))^2 +
  8*(mW 13034 : ℝ)*26068*(26068+2)*(26068+3) /
    ((1/1000)*((mW 13034 : ℝ)*26068*(26068+2)))^2 +
  covarianceVarianceBound 26068 (mW 13034) /
    ((1/1000)*covarianceMeanBound 26068 (mW 13034))^2 +
  normVarianceBound 26068 (mW 13034) / (3*inputVarianceMean 26068 (mW 13034))^2

end BstLean.Part268.WorldRow13034
namespace BstLean.Part268.WorldRow13035
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13035 = 252864943581258 := by
  have hu : mW 13035 ≤ 252864943581258 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13035 ≤ 252864943581257 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13035)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26070 ^ 2)
    ((5000000000000000000/819013204790859097269129))
    ((25000000000000000000/4094908944321615996670687)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26070) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26070 : ℝ)^2 / (mW 13035 : ℝ)) * (1 + 1/10^6)^2 *
    √(((991919/500000000000))/2) * ((1-firstRatio 26070) * √(1-firstRatio 26070) *
      sixthConstant (e1CovarianceRatio 26070 (mW 13035) (1/10^6) rowEps))) /
    (712/10000 - 26070*(1+1/10^6)*((991919/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26070 (mW 13035) /
    ((1/10^5) * ((mW 13035 : ℝ)*26070*((mW 13035 : ℝ)+26070+1)))^2 +
  8*(mW 13035 : ℝ)*26070*(26070+2)*(26070+3) /
    ((1/1000)*((mW 13035 : ℝ)*26070*(26070+2)))^2 +
  covarianceVarianceBound 26070 (mW 13035) /
    ((1/1000)*covarianceMeanBound 26070 (mW 13035))^2 +
  normVarianceBound 26070 (mW 13035) / (3*inputVarianceMean 26070 (mW 13035))^2

end BstLean.Part268.WorldRow13035
namespace BstLean.Part268.WorldRow13036
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13036 = 252932846318203 := by
  have hu : mW 13036 ≤ 252932846318203 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13036 ≤ 252932846318202 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13036)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26072 ^ 2)
    ((6250000000000000000/1023845045804913616417373))
    ((25000000000000000000/4095223103586974975994533)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26072) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26072 : ℝ)^2 / (mW 13036 : ℝ)) * (1 + 1/10^6)^2 *
    √(((495921/250000000000))/2) * ((1-firstRatio 26072) * √(1-firstRatio 26072) *
      sixthConstant (e1CovarianceRatio 26072 (mW 13036) (1/10^6) rowEps))) /
    (712/10000 - 26072*(1+1/10^6)*((495921/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26072 (mW 13036) /
    ((1/10^5) * ((mW 13036 : ℝ)*26072*((mW 13036 : ℝ)+26072+1)))^2 +
  8*(mW 13036 : ℝ)*26072*(26072+2)*(26072+3) /
    ((1/1000)*((mW 13036 : ℝ)*26072*(26072+2)))^2 +
  covarianceVarianceBound 26072 (mW 13036) /
    ((1/1000)*covarianceMeanBound 26072 (mW 13036))^2 +
  normVarianceBound 26072 (mW 13036) / (3*inputVarianceMean 26072 (mW 13036))^2

end BstLean.Part268.WorldRow13036
namespace BstLean.Part268.WorldRow13037
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13037 = 253000762078554 := by
  have hu : mW 13037 ≤ 253000762078554 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13037 ≤ 253000762078553 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13037)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26074 ^ 2)
    ((25000000000000000000/4095694342485013444993339))
    ((25000000000000000000/4095537262852333955318379)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26074) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26074 : ℝ)^2 / (mW 13037 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1983531/1000000000000))/2) * ((1-firstRatio 26074) * √(1-firstRatio 26074) *
      sixthConstant (e1CovarianceRatio 26074 (mW 13037) (1/10^6) rowEps))) /
    (712/10000 - 26074*(1+1/10^6)*((1983531/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26074 (mW 13037) /
    ((1/10^5) * ((mW 13037 : ℝ)*26074*((mW 13037 : ℝ)+26074+1)))^2 +
  8*(mW 13037 : ℝ)*26074*(26074+2)*(26074+3) /
    ((1/1000)*((mW 13037 : ℝ)*26074*(26074+2)))^2 +
  covarianceVarianceBound 26074 (mW 13037) /
    ((1/1000)*covarianceMeanBound 26074 (mW 13037))^2 +
  normVarianceBound 26074 (mW 13037) / (3*inputVarianceMean 26074 (mW 13037))^2

end BstLean.Part268.WorldRow13037
namespace BstLean.Part268.WorldRow13038
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13038 = 253068690863809 := by
  have hu : mW 13038 ≤ 253068690863809 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13038 ≤ 253068690863808 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13038)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26076 ^ 2)
    ((12500000000000000000/2048004250875186212158593))
    ((1000000000000000000/163834056884707717385689)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26076) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26076 : ℝ)^2 / (mW 13038 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1983377/1000000000000))/2) * ((1-firstRatio 26076) * √(1-firstRatio 26076) *
      sixthConstant (e1CovarianceRatio 26076 (mW 13038) (1/10^6) rowEps))) /
    (712/10000 - 26076*(1+1/10^6)*((1983377/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26076 (mW 13038) /
    ((1/10^5) * ((mW 13038 : ℝ)*26076*((mW 13038 : ℝ)+26076+1)))^2 +
  8*(mW 13038 : ℝ)*26076*(26076+2)*(26076+3) /
    ((1/1000)*((mW 13038 : ℝ)*26076*(26076+2)))^2 +
  covarianceVarianceBound 26076 (mW 13038) /
    ((1/1000)*covarianceMeanBound 26076 (mW 13038))^2 +
  normVarianceBound 26076 (mW 13038) / (3*inputVarianceMean 26076 (mW 13038))^2

end BstLean.Part268.WorldRow13038
namespace BstLean.Part268.WorldRow13039
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13039 = 253136632675467 := by
  have hu : mW 13039 ≤ 253136632675467 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13039 ≤ 253136632675466 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13039)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26078 ^ 2)
    ((25000000000000000000/4096322661015731403641033))
    ((25000000000000000000/4096165581383051913966071)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26078) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26078 : ℝ)^2 / (mW 13039 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1983223/1000000000000))/2) * ((1-firstRatio 26078) * √(1-firstRatio 26078) *
      sixthConstant (e1CovarianceRatio 26078 (mW 13039) (1/10^6) rowEps))) /
    (712/10000 - 26078*(1+1/10^6)*((1983223/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26078 (mW 13039) /
    ((1/10^5) * ((mW 13039 : ℝ)*26078*((mW 13039 : ℝ)+26078+1)))^2 +
  8*(mW 13039 : ℝ)*26078*(26078+2)*(26078+3) /
    ((1/1000)*((mW 13039 : ℝ)*26078*(26078+2)))^2 +
  covarianceVarianceBound 26078 (mW 13039) /
    ((1/1000)*covarianceMeanBound 26078 (mW 13039))^2 +
  normVarianceBound 26078 (mW 13039) / (3*inputVarianceMean 26078 (mW 13039))^2

end BstLean.Part268.WorldRow13039
namespace BstLean.Part268.WorldRow13040
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13040 = 253204587515028 := by
  have hu : mW 13040 ≤ 253204587515028 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13040 ≤ 253204587515027 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13040)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26080 ^ 2)
    ((312500000000000000/51207960253513629787061))
    ((25000000000000000000/4096479740648410893289917)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26080) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26080 : ℝ)^2 / (mW 13040 : ℝ)) * (1 + 1/10^6)^2 *
    √(((198307/100000000000))/2) * ((1-firstRatio 26080) * √(1-firstRatio 26080) *
      sixthConstant (e1CovarianceRatio 26080 (mW 13040) (1/10^6) rowEps))) /
    (712/10000 - 26080*(1+1/10^6)*((198307/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26080 (mW 13040) /
    ((1/10^5) * ((mW 13040 : ℝ)*26080*((mW 13040 : ℝ)+26080+1)))^2 +
  8*(mW 13040 : ℝ)*26080*(26080+2)*(26080+3) /
    ((1/1000)*((mW 13040 : ℝ)*26080*(26080+2)))^2 +
  covarianceVarianceBound 26080 (mW 13040) /
    ((1/1000)*covarianceMeanBound 26080 (mW 13040))^2 +
  normVarianceBound 26080 (mW 13040) / (3*inputVarianceMean 26080 (mW 13040))^2

end BstLean.Part268.WorldRow13040
namespace BstLean.Part268.WorldRow13041
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13041 = 253272555383989 := by
  have hu : mW 13041 ≤ 253272555383989 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13041 ≤ 253272555383988 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13041)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26082 ^ 2)
    ((25000000000000000000/4096950979546449362288727))
    ((25000000000000000000/4096793899913769872613763)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26082) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26082 : ℝ)^2 / (mW 13041 : ℝ)) * (1 + 1/10^6)^2 *
    √(((495729/250000000000))/2) * ((1-firstRatio 26082) * √(1-firstRatio 26082) *
      sixthConstant (e1CovarianceRatio 26082 (mW 13041) (1/10^6) rowEps))) /
    (712/10000 - 26082*(1+1/10^6)*((495729/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26082 (mW 13041) /
    ((1/10^5) * ((mW 13041 : ℝ)*26082*((mW 13041 : ℝ)+26082+1)))^2 +
  8*(mW 13041 : ℝ)*26082*(26082+2)*(26082+3) /
    ((1/1000)*((mW 13041 : ℝ)*26082*(26082+2)))^2 +
  covarianceVarianceBound 26082 (mW 13041) /
    ((1/1000)*covarianceMeanBound 26082 (mW 13041))^2 +
  normVarianceBound 26082 (mW 13041) / (3*inputVarianceMean 26082 (mW 13041))^2

end BstLean.Part268.WorldRow13041
namespace BstLean.Part268.WorldRow13042
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13042 = 253340536283849 := by
  have hu : mW 13042 ≤ 253340536283849 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13042 ≤ 253340536283848 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13042)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26084 ^ 2)
    ((12500000000000000000/2048632569405904170806287))
    ((25000000000000000000/4097108059179128851937609)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26084) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26084 : ℝ)^2 / (mW 13042 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1982763/1000000000000))/2) * ((1-firstRatio 26084) * √(1-firstRatio 26084) *
      sixthConstant (e1CovarianceRatio 26084 (mW 13042) (1/10^6) rowEps))) /
    (712/10000 - 26084*(1+1/10^6)*((1982763/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26084 (mW 13042) /
    ((1/10^5) * ((mW 13042 : ℝ)*26084*((mW 13042 : ℝ)+26084+1)))^2 +
  8*(mW 13042 : ℝ)*26084*(26084+2)*(26084+3) /
    ((1/1000)*((mW 13042 : ℝ)*26084*(26084+2)))^2 +
  covarianceVarianceBound 26084 (mW 13042) /
    ((1/1000)*covarianceMeanBound 26084 (mW 13042))^2 +
  normVarianceBound 26084 (mW 13042) / (3*inputVarianceMean 26084 (mW 13042))^2

end BstLean.Part268.WorldRow13042
namespace BstLean.Part268.WorldRow13043
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13043 = 253408530216108 := by
  have hu : mW 13043 ≤ 253408530216108 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13043 ≤ 253408530216107 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13043)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26086 ^ 2)
    ((25000000000000000000/4097579298077167320936421))
    ((5000000000000000000/819484443688897566252291)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26086) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26086 : ℝ)^2 / (mW 13043 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1982609/1000000000000))/2) * ((1-firstRatio 26086) * √(1-firstRatio 26086) *
      sixthConstant (e1CovarianceRatio 26086 (mW 13043) (1/10^6) rowEps))) /
    (712/10000 - 26086*(1+1/10^6)*((1982609/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26086 (mW 13043) /
    ((1/10^5) * ((mW 13043 : ℝ)*26086*((mW 13043 : ℝ)+26086+1)))^2 +
  8*(mW 13043 : ℝ)*26086*(26086+2)*(26086+3) /
    ((1/1000)*((mW 13043 : ℝ)*26086*(26086+2)))^2 +
  covarianceVarianceBound 26086 (mW 13043) /
    ((1/1000)*covarianceMeanBound 26086 (mW 13043))^2 +
  normVarianceBound 26086 (mW 13043) / (3*inputVarianceMean 26086 (mW 13043))^2

end BstLean.Part268.WorldRow13043
namespace BstLean.Part268.WorldRow13044
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13044 = 253476537182264 := by
  have hu : mW 13044 ≤ 253476537182264 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13044 ≤ 253476537182263 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13044)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26088 ^ 2)
    ((6250000000000000000/1024473364335631575065067))
    ((25000000000000000000/4097736377709846810585301)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26088) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26088 : ℝ)^2 / (mW 13044 : ℝ)) * (1 + 1/10^6)^2 *
    √(((247807/125000000000))/2) * ((1-firstRatio 26088) * √(1-firstRatio 26088) *
      sixthConstant (e1CovarianceRatio 26088 (mW 13044) (1/10^6) rowEps))) /
    (712/10000 - 26088*(1+1/10^6)*((247807/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26088 (mW 13044) /
    ((1/10^5) * ((mW 13044 : ℝ)*26088*((mW 13044 : ℝ)+26088+1)))^2 +
  8*(mW 13044 : ℝ)*26088*(26088+2)*(26088+3) /
    ((1/1000)*((mW 13044 : ℝ)*26088*(26088+2)))^2 +
  covarianceVarianceBound 26088 (mW 13044) /
    ((1/1000)*covarianceMeanBound 26088 (mW 13044))^2 +
  normVarianceBound 26088 (mW 13044) / (3*inputVarianceMean 26088 (mW 13044))^2

end BstLean.Part268.WorldRow13044
namespace BstLean.Part268.WorldRow13045
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13045 = 253544557183817 := by
  have hu : mW 13045 ≤ 253544557183817 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13045 ≤ 253544557183816 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13045)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26090 ^ 2)
    ((5000000000000000000/819641523321577055916823))
    ((25000000000000000000/4098050536975205789909147)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26090) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26090 : ℝ)^2 / (mW 13045 : ℝ)) * (1 + 1/10^6)^2 *
    √(((991151/500000000000))/2) * ((1-firstRatio 26090) * √(1-firstRatio 26090) *
      sixthConstant (e1CovarianceRatio 26090 (mW 13045) (1/10^6) rowEps))) /
    (712/10000 - 26090*(1+1/10^6)*((991151/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26090 (mW 13045) /
    ((1/10^5) * ((mW 13045 : ℝ)*26090*((mW 13045 : ℝ)+26090+1)))^2 +
  8*(mW 13045 : ℝ)*26090*(26090+2)*(26090+3) /
    ((1/1000)*((mW 13045 : ℝ)*26090*(26090+2)))^2 +
  covarianceVarianceBound 26090 (mW 13045) /
    ((1/1000)*covarianceMeanBound 26090 (mW 13045))^2 +
  normVarianceBound 26090 (mW 13045) / (3*inputVarianceMean 26090 (mW 13045))^2

end BstLean.Part268.WorldRow13045
namespace BstLean.Part268.WorldRow13046
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13046 = 253612590222265 := by
  have hu : mW 13046 ≤ 253612590222265 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13046 ≤ 253612590222264 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13046)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26092 ^ 2)
    ((12500000000000000000/2049260887936622129453981))
    ((25000000000000000000/4098364696240564769232993)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26092) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26092 : ℝ)^2 / (mW 13046 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1982149/1000000000000))/2) * ((1-firstRatio 26092) * √(1-firstRatio 26092) *
      sixthConstant (e1CovarianceRatio 26092 (mW 13046) (1/10^6) rowEps))) /
    (712/10000 - 26092*(1+1/10^6)*((1982149/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26092 (mW 13046) /
    ((1/10^5) * ((mW 13046 : ℝ)*26092*((mW 13046 : ℝ)+26092+1)))^2 +
  8*(mW 13046 : ℝ)*26092*(26092+2)*(26092+3) /
    ((1/1000)*((mW 13046 : ℝ)*26092*(26092+2)))^2 +
  covarianceVarianceBound 26092 (mW 13046) /
    ((1/1000)*covarianceMeanBound 26092 (mW 13046))^2 +
  normVarianceBound 26092 (mW 13046) / (3*inputVarianceMean 26092 (mW 13046))^2

end BstLean.Part268.WorldRow13046
namespace BstLean.Part268.WorldRow13047
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13047 = 253680636299107 := by
  have hu : mW 13047 ≤ 253680636299107 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13047 ≤ 253680636299106 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13047)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26094 ^ 2)
    ((25000000000000000000/4098835935138603238231809))
    ((25000000000000000000/4098678855505923748556839)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26094) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26094 : ℝ)^2 / (mW 13047 : ℝ)) * (1 + 1/10^6)^2 *
    √(((396399/200000000000))/2) * ((1-firstRatio 26094) * √(1-firstRatio 26094) *
      sixthConstant (e1CovarianceRatio 26094 (mW 13047) (1/10^6) rowEps))) /
    (712/10000 - 26094*(1+1/10^6)*((396399/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26094 (mW 13047) /
    ((1/10^5) * ((mW 13047 : ℝ)*26094*((mW 13047 : ℝ)+26094+1)))^2 +
  8*(mW 13047 : ℝ)*26094*(26094+2)*(26094+3) /
    ((1/1000)*((mW 13047 : ℝ)*26094*(26094+2)))^2 +
  covarianceVarianceBound 26094 (mW 13047) /
    ((1/1000)*covarianceMeanBound 26094 (mW 13047))^2 +
  normVarianceBound 26094 (mW 13047) / (3*inputVarianceMean 26094 (mW 13047))^2

end BstLean.Part268.WorldRow13047
namespace BstLean.Part268.WorldRow13048
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13048 = 253748695415843 := by
  have hu : mW 13048 ≤ 253748695415843 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13048 ≤ 253748695415842 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13048)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26096 ^ 2)
    ((3125000000000000000/512393761800495277194457))
    ((5000000000000000000/819798602954256545576137)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26096) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26096 : ℝ)^2 / (mW 13048 : ℝ)) * (1 + 1/10^6)^2 *
    √(((990921/500000000000))/2) * ((1-firstRatio 26096) * √(1-firstRatio 26096) *
      sixthConstant (e1CovarianceRatio 26096 (mW 13048) (1/10^6) rowEps))) /
    (712/10000 - 26096*(1+1/10^6)*((990921/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26096 (mW 13048) /
    ((1/10^5) * ((mW 13048 : ℝ)*26096*((mW 13048 : ℝ)+26096+1)))^2 +
  8*(mW 13048 : ℝ)*26096*(26096+2)*(26096+3) /
    ((1/1000)*((mW 13048 : ℝ)*26096*(26096+2)))^2 +
  covarianceVarianceBound 26096 (mW 13048) /
    ((1/1000)*covarianceMeanBound 26096 (mW 13048))^2 +
  normVarianceBound 26096 (mW 13048) / (3*inputVarianceMean 26096 (mW 13048))^2

end BstLean.Part268.WorldRow13048
namespace BstLean.Part268.WorldRow13049
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13049 = 253816767573972 := by
  have hu : mW 13049 ≤ 253816767573972 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13049 ≤ 253816767573971 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13049)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26098 ^ 2)
    ((25000000000000000000/4099464253669321196879503))
    ((25000000000000000000/4099307174036641707204531)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26098) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26098 : ℝ)^2 / (mW 13049 : ℝ)) * (1 + 1/10^6)^2 *
    √(((247711/125000000000))/2) * ((1-firstRatio 26098) * √(1-firstRatio 26098) *
      sixthConstant (e1CovarianceRatio 26098 (mW 13049) (1/10^6) rowEps))) /
    (712/10000 - 26098*(1+1/10^6)*((247711/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26098 (mW 13049) /
    ((1/10^5) * ((mW 13049 : ℝ)*26098*((mW 13049 : ℝ)+26098+1)))^2 +
  8*(mW 13049 : ℝ)*26098*(26098+2)*(26098+3) /
    ((1/1000)*((mW 13049 : ℝ)*26098*(26098+2)))^2 +
  covarianceVarianceBound 26098 (mW 13049) /
    ((1/1000)*covarianceMeanBound 26098 (mW 13049))^2 +
  normVarianceBound 26098 (mW 13049) / (3*inputVarianceMean 26098 (mW 13049))^2

end BstLean.Part268.WorldRow13049
