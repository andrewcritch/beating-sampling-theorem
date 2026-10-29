import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar30
namespace BstLean.Part268.WorldRow13100
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13100 = 257305775664056 := by
  have hu : mW 13100 ≤ 257305775664056 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13100 ≤ 257305775664055 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13100)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26200 ^ 2)
    ((250000000000000000/41154863762026291423957))
    ((25000000000000000000/4115329296569949652720677)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26200) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26200 : ℝ)^2 / (mW 13100 : ℝ)) * (1 + 1/10^6)^2 *
    √(((246737/125000000000))/2) * ((1-firstRatio 26200) * √(1-firstRatio 26200) *
      sixthConstant (e1CovarianceRatio 26200 (mW 13100) (1/10^6) rowEps))) /
    (712/10000 - 26200*(1+1/10^6)*((246737/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26200 (mW 13100) /
    ((1/10^5) * ((mW 13100 : ℝ)*26200*((mW 13100 : ℝ)+26200+1)))^2 +
  8*(mW 13100 : ℝ)*26200*(26200+2)*(26200+3) /
    ((1/1000)*((mW 13100 : ℝ)*26200*(26200+2)))^2 +
  covarianceVarianceBound 26200 (mW 13100) /
    ((1/1000)*covarianceMeanBound 26200 (mW 13100))^2 +
  normVarianceBound 26200 (mW 13100) / (3*inputVarianceMean 26200 (mW 13100))^2

end BstLean.Part268.WorldRow13100
namespace BstLean.Part268.WorldRow13101
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13101 = 257374528041947 := by
  have hu : mW 13101 ≤ 257374528041947 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13101 ≤ 257374528041946 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13101)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26202 ^ 2)
    ((25000000000000000000/4115800535467988121719547))
    ((25000000000000000000/4115643455835308632044523)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26202) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26202 : ℝ)^2 / (mW 13101 : ℝ)) * (1 + 1/10^6)^2 *
    √(((123359/62500000000))/2) * ((1-firstRatio 26202) * √(1-firstRatio 26202) *
      sixthConstant (e1CovarianceRatio 26202 (mW 13101) (1/10^6) rowEps))) /
    (712/10000 - 26202*(1+1/10^6)*((123359/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26202 (mW 13101) /
    ((1/10^5) * ((mW 13101 : ℝ)*26202*((mW 13101 : ℝ)+26202+1)))^2 +
  8*(mW 13101 : ℝ)*26202*(26202+2)*(26202+3) /
    ((1/1000)*((mW 13101 : ℝ)*26202*(26202+2)))^2 +
  covarianceVarianceBound 26202 (mW 13101) /
    ((1/1000)*covarianceMeanBound 26202 (mW 13101))^2 +
  normVarianceBound 26202 (mW 13101) / (3*inputVarianceMean 26202 (mW 13101))^2

end BstLean.Part268.WorldRow13101
namespace BstLean.Part268.WorldRow13102
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13102 = 257443293540772 := by
  have hu : mW 13102 ≤ 257443293540772 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13102 ≤ 257443293540771 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13102)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26204 ^ 2)
    ((12500000000000000000/2058057347366673550521697))
    ((25000000000000000000/4115957615100667611368369)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26204) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26204 : ℝ)^2 / (mW 13102 : ℝ)) * (1 + 1/10^6)^2 *
    √(((246699/125000000000))/2) * ((1-firstRatio 26204) * √(1-firstRatio 26204) *
      sixthConstant (e1CovarianceRatio 26204 (mW 13102) (1/10^6) rowEps))) /
    (712/10000 - 26204*(1+1/10^6)*((246699/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26204 (mW 13102) /
    ((1/10^5) * ((mW 13102 : ℝ)*26204*((mW 13102 : ℝ)+26204+1)))^2 +
  8*(mW 13102 : ℝ)*26204*(26204+2)*(26204+3) /
    ((1/1000)*((mW 13102 : ℝ)*26204*(26204+2)))^2 +
  covarianceVarianceBound 26204 (mW 13102) /
    ((1/1000)*covarianceMeanBound 26204 (mW 13102))^2 +
  normVarianceBound 26204 (mW 13102) / (3*inputVarianceMean 26204 (mW 13102))^2

end BstLean.Part268.WorldRow13102
namespace BstLean.Part268.WorldRow13103
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13103 = 257512072162031 := by
  have hu : mW 13103 ≤ 257512072162031 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13103 ≤ 257512072162030 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13103)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26206 ^ 2)
    ((25000000000000000000/4116428853998706080367241))
    ((5000000000000000000/823254354873205318138443)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26206) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26206 : ℝ)^2 / (mW 13103 : ℝ)) * (1 + 1/10^6)^2 *
    √(((6167/3125000000))/2) * ((1-firstRatio 26206) * √(1-firstRatio 26206) *
      sixthConstant (e1CovarianceRatio 26206 (mW 13103) (1/10^6) rowEps))) /
    (712/10000 - 26206*(1+1/10^6)*((6167/3125000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26206 (mW 13103) /
    ((1/10^5) * ((mW 13103 : ℝ)*26206*((mW 13103 : ℝ)+26206+1)))^2 +
  8*(mW 13103 : ℝ)*26206*(26206+2)*(26206+3) /
    ((1/1000)*((mW 13103 : ℝ)*26206*(26206+2)))^2 +
  covarianceVarianceBound 26206 (mW 13103) /
    ((1/1000)*covarianceMeanBound 26206 (mW 13103))^2 +
  normVarianceBound 26206 (mW 13103) / (3*inputVarianceMean 26206 (mW 13103))^2

end BstLean.Part268.WorldRow13103
namespace BstLean.Part268.WorldRow13104
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13104 = 257580863907229 := by
  have hu : mW 13104 ≤ 257580863907229 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13104 ≤ 257580863907228 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13104)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26208 ^ 2)
    ((1562500000000000000/257296438329004066230693))
    ((25000000000000000000/4116585933631385570016061)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26208) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26208 : ℝ)^2 / (mW 13104 : ℝ)) * (1 + 1/10^6)^2 *
    √(((246661/125000000000))/2) * ((1-firstRatio 26208) * √(1-firstRatio 26208) *
      sixthConstant (e1CovarianceRatio 26208 (mW 13104) (1/10^6) rowEps))) /
    (712/10000 - 26208*(1+1/10^6)*((246661/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26208 (mW 13104) /
    ((1/10^5) * ((mW 13104 : ℝ)*26208*((mW 13104 : ℝ)+26208+1)))^2 +
  8*(mW 13104 : ℝ)*26208*(26208+2)*(26208+3) /
    ((1/1000)*((mW 13104 : ℝ)*26208*(26208+2)))^2 +
  covarianceVarianceBound 26208 (mW 13104) /
    ((1/1000)*covarianceMeanBound 26208 (mW 13104))^2 +
  normVarianceBound 26208 (mW 13104) / (3*inputVarianceMean 26208 (mW 13104))^2

end BstLean.Part268.WorldRow13104
namespace BstLean.Part268.WorldRow13105
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13105 = 257649668777867 := by
  have hu : mW 13105 ≤ 257649668777867 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13105 ≤ 257649668777866 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13105)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26210 ^ 2)
    ((5000000000000000000/823411434505884807802987))
    ((25000000000000000000/4116900092896744549339907)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26210) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26210 : ℝ)^2 / (mW 13105 : ℝ)) * (1 + 1/10^6)^2 *
    √(((123321/62500000000))/2) * ((1-firstRatio 26210) * √(1-firstRatio 26210) *
      sixthConstant (e1CovarianceRatio 26210 (mW 13105) (1/10^6) rowEps))) /
    (712/10000 - 26210*(1+1/10^6)*((123321/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26210 (mW 13105) /
    ((1/10^5) * ((mW 13105 : ℝ)*26210*((mW 13105 : ℝ)+26210+1)))^2 +
  8*(mW 13105 : ℝ)*26210*(26210+2)*(26210+3) /
    ((1/1000)*((mW 13105 : ℝ)*26210*(26210+2)))^2 +
  covarianceVarianceBound 26210 (mW 13105) /
    ((1/1000)*covarianceMeanBound 26210 (mW 13105))^2 +
  normVarianceBound 26210 (mW 13105) / (3*inputVarianceMean 26210 (mW 13105))^2

end BstLean.Part268.WorldRow13105
namespace BstLean.Part268.WorldRow13106
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13106 = 257718486775448 := by
  have hu : mW 13106 ≤ 257718486775448 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13106 ≤ 257718486775447 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13106)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26212 ^ 2)
    ((12500000000000000000/2058685665897391509169391))
    ((25000000000000000000/4117214252162103528663753)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26212) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26212 : ℝ)^2 / (mW 13106 : ℝ)) * (1 + 1/10^6)^2 *
    √(((246623/125000000000))/2) * ((1-firstRatio 26212) * √(1-firstRatio 26212) *
      sixthConstant (e1CovarianceRatio 26212 (mW 13106) (1/10^6) rowEps))) /
    (712/10000 - 26212*(1+1/10^6)*((246623/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26212 (mW 13106) /
    ((1/10^5) * ((mW 13106 : ℝ)*26212*((mW 13106 : ℝ)+26212+1)))^2 +
  8*(mW 13106 : ℝ)*26212*(26212+2)*(26212+3) /
    ((1/1000)*((mW 13106 : ℝ)*26212*(26212+2)))^2 +
  covarianceVarianceBound 26212 (mW 13106) /
    ((1/1000)*covarianceMeanBound 26212 (mW 13106))^2 +
  normVarianceBound 26212 (mW 13106) / (3*inputVarianceMean 26212 (mW 13106))^2

end BstLean.Part268.WorldRow13106
namespace BstLean.Part268.WorldRow13107
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13107 = 257787317901474 := by
  have hu : mW 13107 ≤ 257787317901474 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13107 ≤ 257787317901473 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13107)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26214 ^ 2)
    ((25000000000000000000/4117685491060141997662629))
    ((25000000000000000000/4117528411427462507987599)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26214) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26214 : ℝ)^2 / (mW 13107 : ℝ)) * (1 + 1/10^6)^2 *
    √(((61651/31250000000))/2) * ((1-firstRatio 26214) * √(1-firstRatio 26214) *
      sixthConstant (e1CovarianceRatio 26214 (mW 13107) (1/10^6) rowEps))) /
    (712/10000 - 26214*(1+1/10^6)*((61651/31250000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26214 (mW 13107) /
    ((1/10^5) * ((mW 13107 : ℝ)*26214*((mW 13107 : ℝ)+26214+1)))^2 +
  8*(mW 13107 : ℝ)*26214*(26214+2)*(26214+3) /
    ((1/1000)*((mW 13107 : ℝ)*26214*(26214+2)))^2 +
  covarianceVarianceBound 26214 (mW 13107) /
    ((1/1000)*covarianceMeanBound 26214 (mW 13107))^2 +
  normVarianceBound 26214 (mW 13107) / (3*inputVarianceMean 26214 (mW 13107))^2

end BstLean.Part268.WorldRow13107
namespace BstLean.Part268.WorldRow13108
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13108 = 257856162157448 := by
  have hu : mW 13108 ≤ 257856162157448 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13108 ≤ 257856162157447 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13108)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26216 ^ 2)
    ((6250000000000000000/1029499912581375244246619))
    ((5000000000000000000/823568514138564297462289)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26216) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26216 : ℝ)^2 / (mW 13108 : ℝ)) * (1 + 1/10^6)^2 *
    √(((49317/25000000000))/2) * ((1-firstRatio 26216) * √(1-firstRatio 26216) *
      sixthConstant (e1CovarianceRatio 26216 (mW 13108) (1/10^6) rowEps))) /
    (712/10000 - 26216*(1+1/10^6)*((49317/25000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26216 (mW 13108) /
    ((1/10^5) * ((mW 13108 : ℝ)*26216*((mW 13108 : ℝ)+26216+1)))^2 +
  8*(mW 13108 : ℝ)*26216*(26216+2)*(26216+3) /
    ((1/1000)*((mW 13108 : ℝ)*26216*(26216+2)))^2 +
  covarianceVarianceBound 26216 (mW 13108) /
    ((1/1000)*covarianceMeanBound 26216 (mW 13108))^2 +
  normVarianceBound 26216 (mW 13108) / (3*inputVarianceMean 26216 (mW 13108))^2

end BstLean.Part268.WorldRow13108
namespace BstLean.Part268.WorldRow13109
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13109 = 257925019544873 := by
  have hu : mW 13109 ≤ 257925019544873 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13109 ≤ 257925019544872 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13109)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26218 ^ 2)
    ((25000000000000000000/4118313809590859956310323))
    ((25000000000000000000/4118156729958180466635291)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26218) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26218 : ℝ)^2 / (mW 13109 : ℝ)) * (1 + 1/10^6)^2 *
    √(((123283/62500000000))/2) * ((1-firstRatio 26218) * √(1-firstRatio 26218) *
      sixthConstant (e1CovarianceRatio 26218 (mW 13109) (1/10^6) rowEps))) /
    (712/10000 - 26218*(1+1/10^6)*((123283/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26218 (mW 13109) /
    ((1/10^5) * ((mW 13109 : ℝ)*26218*((mW 13109 : ℝ)+26218+1)))^2 +
  8*(mW 13109 : ℝ)*26218*(26218+2)*(26218+3) /
    ((1/1000)*((mW 13109 : ℝ)*26218*(26218+2)))^2 +
  covarianceVarianceBound 26218 (mW 13109) /
    ((1/1000)*covarianceMeanBound 26218 (mW 13109))^2 +
  normVarianceBound 26218 (mW 13109) / (3*inputVarianceMean 26218 (mW 13109))^2

end BstLean.Part268.WorldRow13109
namespace BstLean.Part268.WorldRow13110
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13110 = 257993890065251 := by
  have hu : mW 13110 ≤ 257993890065251 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13110 ≤ 257993890065250 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13110)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26220 ^ 2)
    ((2500000000000000000/411862796885621893563417))
    ((25000000000000000000/4118470889223539445959137)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26220) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26220 : ℝ)^2 / (mW 13110 : ℝ)) * (1 + 1/10^6)^2 *
    √(((246547/125000000000))/2) * ((1-firstRatio 26220) * √(1-firstRatio 26220) *
      sixthConstant (e1CovarianceRatio 26220 (mW 13110) (1/10^6) rowEps))) /
    (712/10000 - 26220*(1+1/10^6)*((246547/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26220 (mW 13110) /
    ((1/10^5) * ((mW 13110 : ℝ)*26220*((mW 13110 : ℝ)+26220+1)))^2 +
  8*(mW 13110 : ℝ)*26220*(26220+2)*(26220+3) /
    ((1/1000)*((mW 13110 : ℝ)*26220*(26220+2)))^2 +
  covarianceVarianceBound 26220 (mW 13110) /
    ((1/1000)*covarianceMeanBound 26220 (mW 13110))^2 +
  normVarianceBound 26220 (mW 13110) / (3*inputVarianceMean 26220 (mW 13110))^2

end BstLean.Part268.WorldRow13110
namespace BstLean.Part268.WorldRow13111
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13111 = 258062773720084 := by
  have hu : mW 13111 ≤ 258062773720084 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13111 ≤ 258062773720083 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13111)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26222 ^ 2)
    ((25000000000000000000/4118942128121577914958017))
    ((25000000000000000000/4118785048488898425282983)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26222) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26222 : ℝ)^2 / (mW 13111 : ℝ)) * (1 + 1/10^6)^2 *
    √(((963/488281250))/2) * ((1-firstRatio 26222) * √(1-firstRatio 26222) *
      sixthConstant (e1CovarianceRatio 26222 (mW 13111) (1/10^6) rowEps))) /
    (712/10000 - 26222*(1+1/10^6)*((963/488281250)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26222 (mW 13111) /
    ((1/10^5) * ((mW 13111 : ℝ)*26222*((mW 13111 : ℝ)+26222+1)))^2 +
  8*(mW 13111 : ℝ)*26222*(26222+2)*(26222+3) /
    ((1/1000)*((mW 13111 : ℝ)*26222*(26222+2)))^2 +
  covarianceVarianceBound 26222 (mW 13111) /
    ((1/1000)*covarianceMeanBound 26222 (mW 13111))^2 +
  normVarianceBound 26222 (mW 13111) / (3*inputVarianceMean 26222 (mW 13111))^2

end BstLean.Part268.WorldRow13111
namespace BstLean.Part268.WorldRow13112
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13112 = 258131670510877 := by
  have hu : mW 13112 ≤ 258131670510877 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13112 ≤ 258131670510876 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13112)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26224 ^ 2)
    ((3125000000000000000/514907035923367111785233))
    ((25000000000000000000/4119099207754257404606829)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26224) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26224 : ℝ)^2 / (mW 13112 : ℝ)) * (1 + 1/10^6)^2 *
    √(((246509/125000000000))/2) * ((1-firstRatio 26224) * √(1-firstRatio 26224) *
      sixthConstant (e1CovarianceRatio 26224 (mW 13112) (1/10^6) rowEps))) /
    (712/10000 - 26224*(1+1/10^6)*((246509/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26224 (mW 13112) /
    ((1/10^5) * ((mW 13112 : ℝ)*26224*((mW 13112 : ℝ)+26224+1)))^2 +
  8*(mW 13112 : ℝ)*26224*(26224+2)*(26224+3) /
    ((1/1000)*((mW 13112 : ℝ)*26224*(26224+2)))^2 +
  covarianceVarianceBound 26224 (mW 13112) /
    ((1/1000)*covarianceMeanBound 26224 (mW 13112))^2 +
  normVarianceBound 26224 (mW 13112) / (3*inputVarianceMean 26224 (mW 13112))^2

end BstLean.Part268.WorldRow13112
namespace BstLean.Part268.WorldRow13113
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13113 = 258200580439131 := by
  have hu : mW 13113 ≤ 258200580439131 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13113 ≤ 258200580439130 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13113)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26226 ^ 2)
    ((25000000000000000000/4119570446652295873605711))
    ((1000000000000000000/164776534680784655357227)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26226) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26226 : ℝ)^2 / (mW 13113 : ℝ)) * (1 + 1/10^6)^2 *
    √(((24649/12500000000))/2) * ((1-firstRatio 26226) * √(1-firstRatio 26226) *
      sixthConstant (e1CovarianceRatio 26226 (mW 13113) (1/10^6) rowEps))) /
    (712/10000 - 26226*(1+1/10^6)*((24649/12500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26226 (mW 13113) /
    ((1/10^5) * ((mW 13113 : ℝ)*26226*((mW 13113 : ℝ)+26226+1)))^2 +
  8*(mW 13113 : ℝ)*26226*(26226+2)*(26226+3) /
    ((1/1000)*((mW 13113 : ℝ)*26226*(26226+2)))^2 +
  covarianceVarianceBound 26226 (mW 13113) /
    ((1/1000)*covarianceMeanBound 26226 (mW 13113))^2 +
  normVarianceBound 26226 (mW 13113) / (3*inputVarianceMean 26226 (mW 13113))^2

end BstLean.Part268.WorldRow13113
namespace BstLean.Part268.WorldRow13114
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13114 = 258269503506351 := by
  have hu : mW 13114 ≤ 258269503506351 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13114 ≤ 258269503506350 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13114)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26228 ^ 2)
    ((12500000000000000000/2059942302958827426464779))
    ((25000000000000000000/4119727526284975363254521)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26228) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26228 : ℝ)^2 / (mW 13114 : ℝ)) * (1 + 1/10^6)^2 *
    √(((246471/125000000000))/2) * ((1-firstRatio 26228) * √(1-firstRatio 26228) *
      sixthConstant (e1CovarianceRatio 26228 (mW 13114) (1/10^6) rowEps))) /
    (712/10000 - 26228*(1+1/10^6)*((246471/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26228 (mW 13114) /
    ((1/10^5) * ((mW 13114 : ℝ)*26228*((mW 13114 : ℝ)+26228+1)))^2 +
  8*(mW 13114 : ℝ)*26228*(26228+2)*(26228+3) /
    ((1/1000)*((mW 13114 : ℝ)*26228*(26228+2)))^2 +
  covarianceVarianceBound 26228 (mW 13114) /
    ((1/1000)*covarianceMeanBound 26228 (mW 13114))^2 +
  normVarianceBound 26228 (mW 13114) / (3*inputVarianceMean 26228 (mW 13114))^2

end BstLean.Part268.WorldRow13114
namespace BstLean.Part268.WorldRow13115
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13115 = 258338439714037 := by
  have hu : mW 13115 ≤ 258338439714037 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13115 ≤ 258338439714036 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13115)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26230 ^ 2)
    ((5000000000000000000/824039753036602766450681))
    ((25000000000000000000/4120041685550334342578367)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26230) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26230 : ℝ)^2 / (mW 13115 : ℝ)) * (1 + 1/10^6)^2 *
    √(((61613/31250000000))/2) * ((1-firstRatio 26230) * √(1-firstRatio 26230) *
      sixthConstant (e1CovarianceRatio 26230 (mW 13115) (1/10^6) rowEps))) /
    (712/10000 - 26230*(1+1/10^6)*((61613/31250000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26230 (mW 13115) /
    ((1/10^5) * ((mW 13115 : ℝ)*26230*((mW 13115 : ℝ)+26230+1)))^2 +
  8*(mW 13115 : ℝ)*26230*(26230+2)*(26230+3) /
    ((1/1000)*((mW 13115 : ℝ)*26230*(26230+2)))^2 +
  covarianceVarianceBound 26230 (mW 13115) /
    ((1/1000)*covarianceMeanBound 26230 (mW 13115))^2 +
  normVarianceBound 26230 (mW 13115) / (3*inputVarianceMean 26230 (mW 13115))^2

end BstLean.Part268.WorldRow13115
namespace BstLean.Part268.WorldRow13116
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13116 = 258407389063695 := by
  have hu : mW 13116 ≤ 258407389063695 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13116 ≤ 258407389063694 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13116)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26232 ^ 2)
    ((6250000000000000000/1030128231112093202894313))
    ((25000000000000000000/4120355844815693321902213)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26232) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26232 : ℝ)^2 / (mW 13116 : ℝ)) * (1 + 1/10^6)^2 *
    √(((394293/200000000000))/2) * ((1-firstRatio 26232) * √(1-firstRatio 26232) *
      sixthConstant (e1CovarianceRatio 26232 (mW 13116) (1/10^6) rowEps))) /
    (712/10000 - 26232*(1+1/10^6)*((394293/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26232 (mW 13116) /
    ((1/10^5) * ((mW 13116 : ℝ)*26232*((mW 13116 : ℝ)+26232+1)))^2 +
  8*(mW 13116 : ℝ)*26232*(26232+2)*(26232+3) /
    ((1/1000)*((mW 13116 : ℝ)*26232*(26232+2)))^2 +
  covarianceVarianceBound 26232 (mW 13116) /
    ((1/1000)*covarianceMeanBound 26232 (mW 13116))^2 +
  normVarianceBound 26232 (mW 13116) / (3*inputVarianceMean 26232 (mW 13116))^2

end BstLean.Part268.WorldRow13116
namespace BstLean.Part268.WorldRow13117
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13117 = 258476351556826 := by
  have hu : mW 13117 ≤ 258476351556826 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13117 ≤ 258476351556825 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13117)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26234 ^ 2)
    ((25000000000000000000/4120827083713731790901099))
    ((25000000000000000000/4120670004081052301226059)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26234) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26234 : ℝ)^2 / (mW 13117 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1971313/1000000000000))/2) * ((1-firstRatio 26234) * √(1-firstRatio 26234) *
      sixthConstant (e1CovarianceRatio 26234 (mW 13117) (1/10^6) rowEps))) /
    (712/10000 - 26234*(1+1/10^6)*((1971313/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26234 (mW 13117) /
    ((1/10^5) * ((mW 13117 : ℝ)*26234*((mW 13117 : ℝ)+26234+1)))^2 +
  8*(mW 13117 : ℝ)*26234*(26234+2)*(26234+3) /
    ((1/1000)*((mW 13117 : ℝ)*26234*(26234+2)))^2 +
  covarianceVarianceBound 26234 (mW 13117) /
    ((1/1000)*covarianceMeanBound 26234 (mW 13117))^2 +
  normVarianceBound 26234 (mW 13117) / (3*inputVarianceMean 26234 (mW 13117))^2

end BstLean.Part268.WorldRow13117
namespace BstLean.Part268.WorldRow13118
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13118 = 258545327194934 := by
  have hu : mW 13118 ≤ 258545327194934 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13118 ≤ 258545327194933 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13118)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26236 ^ 2)
    ((12500000000000000000/2060570621489545385112473))
    ((5000000000000000000/824196832669282256109981)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26236) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26236 : ℝ)^2 / (mW 13118 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1971161/1000000000000))/2) * ((1-firstRatio 26236) * √(1-firstRatio 26236) *
      sixthConstant (e1CovarianceRatio 26236 (mW 13118) (1/10^6) rowEps))) /
    (712/10000 - 26236*(1+1/10^6)*((1971161/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26236 (mW 13118) /
    ((1/10^5) * ((mW 13118 : ℝ)*26236*((mW 13118 : ℝ)+26236+1)))^2 +
  8*(mW 13118 : ℝ)*26236*(26236+2)*(26236+3) /
    ((1/1000)*((mW 13118 : ℝ)*26236*(26236+2)))^2 +
  covarianceVarianceBound 26236 (mW 13118) /
    ((1/1000)*covarianceMeanBound 26236 (mW 13118))^2 +
  normVarianceBound 26236 (mW 13118) / (3*inputVarianceMean 26236 (mW 13118))^2

end BstLean.Part268.WorldRow13118
namespace BstLean.Part268.WorldRow13119
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13119 = 258614315979523 := by
  have hu : mW 13119 ≤ 258614315979523 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13119 ≤ 258614315979522 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13119)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26238 ^ 2)
    ((25000000000000000000/4121455402244449749548793))
    ((25000000000000000000/4121298322611770259873751)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26238) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26238 : ℝ)^2 / (mW 13119 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1971009/1000000000000))/2) * ((1-firstRatio 26238) * √(1-firstRatio 26238) *
      sixthConstant (e1CovarianceRatio 26238 (mW 13119) (1/10^6) rowEps))) /
    (712/10000 - 26238*(1+1/10^6)*((1971009/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26238 (mW 13119) /
    ((1/10^5) * ((mW 13119 : ℝ)*26238*((mW 13119 : ℝ)+26238+1)))^2 +
  8*(mW 13119 : ℝ)*26238*(26238+2)*(26238+3) /
    ((1/1000)*((mW 13119 : ℝ)*26238*(26238+2)))^2 +
  covarianceVarianceBound 26238 (mW 13119) /
    ((1/1000)*covarianceMeanBound 26238 (mW 13119))^2 +
  normVarianceBound 26238 (mW 13119) / (3*inputVarianceMean 26238 (mW 13119))^2

end BstLean.Part268.WorldRow13119
namespace BstLean.Part268.WorldRow13120
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13120 = 258683317912095 := by
  have hu : mW 13120 ≤ 258683317912095 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13120 ≤ 258683317912094 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13120)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26240 ^ 2)
    ((78125000000000000/12880529879718152277727))
    ((25000000000000000000/4121612481877129239197597)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26240) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26240 : ℝ)^2 / (mW 13120 : ℝ)) * (1 + 1/10^6)^2 *
    √(((985429/500000000000))/2) * ((1-firstRatio 26240) * √(1-firstRatio 26240) *
      sixthConstant (e1CovarianceRatio 26240 (mW 13120) (1/10^6) rowEps))) /
    (712/10000 - 26240*(1+1/10^6)*((985429/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26240 (mW 13120) /
    ((1/10^5) * ((mW 13120 : ℝ)*26240*((mW 13120 : ℝ)+26240+1)))^2 +
  8*(mW 13120 : ℝ)*26240*(26240+2)*(26240+3) /
    ((1/1000)*((mW 13120 : ℝ)*26240*(26240+2)))^2 +
  covarianceVarianceBound 26240 (mW 13120) /
    ((1/1000)*covarianceMeanBound 26240 (mW 13120))^2 +
  normVarianceBound 26240 (mW 13120) / (3*inputVarianceMean 26240 (mW 13120))^2

end BstLean.Part268.WorldRow13120
namespace BstLean.Part268.WorldRow13121
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13121 = 258752332994154 := by
  have hu : mW 13121 ≤ 258752332994154 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13121 ≤ 258752332994153 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13121)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26242 ^ 2)
    ((25000000000000000000/4122083720775167708196487))
    ((25000000000000000000/4121926641142488218521443)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26242) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26242 : ℝ)^2 / (mW 13121 : ℝ)) * (1 + 1/10^6)^2 *
    √(((985353/500000000000))/2) * ((1-firstRatio 26242) * √(1-firstRatio 26242) *
      sixthConstant (e1CovarianceRatio 26242 (mW 13121) (1/10^6) rowEps))) /
    (712/10000 - 26242*(1+1/10^6)*((985353/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26242 (mW 13121) /
    ((1/10^5) * ((mW 13121 : ℝ)*26242*((mW 13121 : ℝ)+26242+1)))^2 +
  8*(mW 13121 : ℝ)*26242*(26242+2)*(26242+3) /
    ((1/1000)*((mW 13121 : ℝ)*26242*(26242+2)))^2 +
  covarianceVarianceBound 26242 (mW 13121) /
    ((1/1000)*covarianceMeanBound 26242 (mW 13121))^2 +
  normVarianceBound 26242 (mW 13121) / (3*inputVarianceMean 26242 (mW 13121))^2

end BstLean.Part268.WorldRow13121
namespace BstLean.Part268.WorldRow13122
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13122 = 258821361227203 := by
  have hu : mW 13122 ≤ 258821361227203 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13122 ≤ 258821361227202 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13122)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26244 ^ 2)
    ((12500000000000000000/2061198940020263343760167))
    ((25000000000000000000/4122240800407847197845289)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26244) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26244 : ℝ)^2 / (mW 13122 : ℝ)) * (1 + 1/10^6)^2 *
    √(((985277/500000000000))/2) * ((1-firstRatio 26244) * √(1-firstRatio 26244) *
      sixthConstant (e1CovarianceRatio 26244 (mW 13122) (1/10^6) rowEps))) /
    (712/10000 - 26244*(1+1/10^6)*((985277/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26244 (mW 13122) /
    ((1/10^5) * ((mW 13122 : ℝ)*26244*((mW 13122 : ℝ)+26244+1)))^2 +
  8*(mW 13122 : ℝ)*26244*(26244+2)*(26244+3) /
    ((1/1000)*((mW 13122 : ℝ)*26244*(26244+2)))^2 +
  covarianceVarianceBound 26244 (mW 13122) /
    ((1/1000)*covarianceMeanBound 26244 (mW 13122))^2 +
  normVarianceBound 26244 (mW 13122) / (3*inputVarianceMean 26244 (mW 13122))^2

end BstLean.Part268.WorldRow13122
namespace BstLean.Part268.WorldRow13123
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13123 = 258890402612746 := by
  have hu : mW 13123 ≤ 258890402612746 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13123 ≤ 258890402612745 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13123)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26246 ^ 2)
    ((25000000000000000000/4122712039305885666844181))
    ((5000000000000000000/824510991934641235433827)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26246) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26246 : ℝ)^2 / (mW 13123 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1970403/1000000000000))/2) * ((1-firstRatio 26246) * √(1-firstRatio 26246) *
      sixthConstant (e1CovarianceRatio 26246 (mW 13123) (1/10^6) rowEps))) /
    (712/10000 - 26246*(1+1/10^6)*((1970403/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26246 (mW 13123) /
    ((1/10^5) * ((mW 13123 : ℝ)*26246*((mW 13123 : ℝ)+26246+1)))^2 +
  8*(mW 13123 : ℝ)*26246*(26246+2)*(26246+3) /
    ((1/1000)*((mW 13123 : ℝ)*26246*(26246+2)))^2 +
  covarianceVarianceBound 26246 (mW 13123) /
    ((1/1000)*covarianceMeanBound 26246 (mW 13123))^2 +
  normVarianceBound 26246 (mW 13123) / (3*inputVarianceMean 26246 (mW 13123))^2

end BstLean.Part268.WorldRow13123
namespace BstLean.Part268.WorldRow13124
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13124 = 258959457152286 := by
  have hu : mW 13124 ≤ 258959457152286 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13124 ≤ 258959457152285 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13124)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26248 ^ 2)
    ((6250000000000000000/1030756549642811161542007))
    ((25000000000000000000/4122869118938565156492981)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26248) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26248 : ℝ)^2 / (mW 13124 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1970251/1000000000000))/2) * ((1-firstRatio 26248) * √(1-firstRatio 26248) *
      sixthConstant (e1CovarianceRatio 26248 (mW 13124) (1/10^6) rowEps))) /
    (712/10000 - 26248*(1+1/10^6)*((1970251/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26248 (mW 13124) /
    ((1/10^5) * ((mW 13124 : ℝ)*26248*((mW 13124 : ℝ)+26248+1)))^2 +
  8*(mW 13124 : ℝ)*26248*(26248+2)*(26248+3) /
    ((1/1000)*((mW 13124 : ℝ)*26248*(26248+2)))^2 +
  covarianceVarianceBound 26248 (mW 13124) /
    ((1/1000)*covarianceMeanBound 26248 (mW 13124))^2 +
  normVarianceBound 26248 (mW 13124) / (3*inputVarianceMean 26248 (mW 13124))^2

end BstLean.Part268.WorldRow13124
