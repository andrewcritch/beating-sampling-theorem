import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar12
namespace BstLean.Part268.WorldRow12650
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12650 = 227675783240323 := by
  have hu : mW 12650 ≤ 227675783240323 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12650 ≤ 227675783240322 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12650)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25300 ^ 2)
    ((500000000000000000/79482294135821768933291))
    ((25000000000000000000/3973957627158408956989977)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25300) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25300 : ℝ)^2 / (mW 12650 : ℝ)) * (1 + 1/10^6)^2 *
    √(((408969/200000000000))/2) * ((1-firstRatio 25300) * √(1-firstRatio 25300) *
      sixthConstant (e1CovarianceRatio 25300 (mW 12650) (1/10^6) rowEps))) /
    (712/10000 - 25300*(1+1/10^6)*((408969/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25300 (mW 12650) /
    ((1/10^5) * ((mW 12650 : ℝ)*25300*((mW 12650 : ℝ)+25300+1)))^2 +
  8*(mW 12650 : ℝ)*25300*(25300+2)*(25300+3) /
    ((1/1000)*((mW 12650 : ℝ)*25300*(25300+2)))^2 +
  covarianceVarianceBound 25300 (mW 12650) /
    ((1/1000)*covarianceMeanBound 25300 (mW 12650))^2 +
  normVarianceBound 25300 (mW 12650) / (3*inputVarianceMean 25300 (mW 12650))^2

end BstLean.Part268.WorldRow12650
namespace BstLean.Part268.WorldRow12651
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12651 = 227738782764914 := by
  have hu : mW 12651 ≤ 227738782764914 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12651 ≤ 227738782764913 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12651)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25302 ^ 2)
    ((25000000000000000000/3974428866056447425988397))
    ((25000000000000000000/3974271786423767936313823)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25302) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25302 : ℝ)^2 / (mW 12651 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1022341/500000000000))/2) * ((1-firstRatio 25302) * √(1-firstRatio 25302) *
      sixthConstant (e1CovarianceRatio 25302 (mW 12651) (1/10^6) rowEps))) /
    (712/10000 - 25302*(1+1/10^6)*((1022341/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25302 (mW 12651) /
    ((1/10^5) * ((mW 12651 : ℝ)*25302*((mW 12651 : ℝ)+25302+1)))^2 +
  8*(mW 12651 : ℝ)*25302*(25302+2)*(25302+3) /
    ((1/1000)*((mW 12651 : ℝ)*25302*(25302+2)))^2 +
  covarianceVarianceBound 25302 (mW 12651) /
    ((1/1000)*covarianceMeanBound 25302 (mW 12651))^2 +
  normVarianceBound 25302 (mW 12651) / (3*inputVarianceMean 25302 (mW 12651))^2

end BstLean.Part268.WorldRow12651
namespace BstLean.Part268.WorldRow12652
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12652 = 227801794740250 := by
  have hu : mW 12652 ≤ 227801794740250 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12652 ≤ 227801794740249 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12652)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25304 ^ 2)
    ((6250000000000000000/993685756330451601328061))
    ((25000000000000000000/3974585945689126915637669)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25304) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25304 : ℝ)^2 / (mW 12652 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1022259/500000000000))/2) * ((1-firstRatio 25304) * √(1-firstRatio 25304) *
      sixthConstant (e1CovarianceRatio 25304 (mW 12652) (1/10^6) rowEps))) /
    (712/10000 - 25304*(1+1/10^6)*((1022259/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25304 (mW 12652) /
    ((1/10^5) * ((mW 12652 : ℝ)*25304*((mW 12652 : ℝ)+25304+1)))^2 +
  8*(mW 12652 : ℝ)*25304*(25304+2)*(25304+3) /
    ((1/1000)*((mW 12652 : ℝ)*25304*(25304+2)))^2 +
  covarianceVarianceBound 25304 (mW 12652) /
    ((1/1000)*covarianceMeanBound 25304 (mW 12652))^2 +
  normVarianceBound 25304 (mW 12652) / (3*inputVarianceMean 25304 (mW 12652))^2

end BstLean.Part268.WorldRow12652
namespace BstLean.Part268.WorldRow12653
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12653 = 227864819167807 := by
  have hu : mW 12653 ≤ 227864819167807 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12653 ≤ 227864819167806 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12653)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25306 ^ 2)
    ((25000000000000000000/3975057184587165384636091))
    ((5000000000000000000/794980020990897178992303)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25306) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25306 : ℝ)^2 / (mW 12653 : ℝ)) * (1 + 1/10^6)^2 *
    √(((408871/200000000000))/2) * ((1-firstRatio 25306) * √(1-firstRatio 25306) *
      sixthConstant (e1CovarianceRatio 25306 (mW 12653) (1/10^6) rowEps))) /
    (712/10000 - 25306*(1+1/10^6)*((408871/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25306 (mW 12653) /
    ((1/10^5) * ((mW 12653 : ℝ)*25306*((mW 12653 : ℝ)+25306+1)))^2 +
  8*(mW 12653 : ℝ)*25306*(25306+2)*(25306+3) /
    ((1/1000)*((mW 12653 : ℝ)*25306*(25306+2)))^2 +
  covarianceVarianceBound 25306 (mW 12653) /
    ((1/1000)*covarianceMeanBound 25306 (mW 12653))^2 +
  normVarianceBound 25306 (mW 12653) / (3*inputVarianceMean 25306 (mW 12653))^2

end BstLean.Part268.WorldRow12653
namespace BstLean.Part268.WorldRow12654
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12654 = 227927856049062 := by
  have hu : mW 12654 ≤ 227927856049062 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12654 ≤ 227927856049061 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12654)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25308 ^ 2)
    ((12500000000000000000/1987685671926262181979969))
    ((25000000000000000000/3975214264219844874285361)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25308) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25308 : ℝ)^2 / (mW 12654 : ℝ)) * (1 + 1/10^6)^2 *
    √(((63881/31250000000))/2) * ((1-firstRatio 25308) * √(1-firstRatio 25308) *
      sixthConstant (e1CovarianceRatio 25308 (mW 12654) (1/10^6) rowEps))) /
    (712/10000 - 25308*(1+1/10^6)*((63881/31250000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25308 (mW 12654) /
    ((1/10^5) * ((mW 12654 : ℝ)*25308*((mW 12654 : ℝ)+25308+1)))^2 +
  8*(mW 12654 : ℝ)*25308*(25308+2)*(25308+3) /
    ((1/1000)*((mW 12654 : ℝ)*25308*(25308+2)))^2 +
  covarianceVarianceBound 25308 (mW 12654) /
    ((1/1000)*covarianceMeanBound 25308 (mW 12654))^2 +
  normVarianceBound 25308 (mW 12654) / (3*inputVarianceMean 25308 (mW 12654))^2

end BstLean.Part268.WorldRow12654
namespace BstLean.Part268.WorldRow12655
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12655 = 227990905385491 := by
  have hu : mW 12655 ≤ 227990905385491 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12655 ≤ 227990905385490 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12655)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25310 ^ 2)
    ((5000000000000000000/795137100623576668656757))
    ((25000000000000000000/3975528423485203853609207)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25310) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25310 : ℝ)^2 / (mW 12655 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2044029/1000000000000))/2) * ((1-firstRatio 25310) * √(1-firstRatio 25310) *
      sixthConstant (e1CovarianceRatio 25310 (mW 12655) (1/10^6) rowEps))) /
    (712/10000 - 25310*(1+1/10^6)*((2044029/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25310 (mW 12655) /
    ((1/10^5) * ((mW 12655 : ℝ)*25310*((mW 12655 : ℝ)+25310+1)))^2 +
  8*(mW 12655 : ℝ)*25310*(25310+2)*(25310+3) /
    ((1/1000)*((mW 12655 : ℝ)*25310*(25310+2)))^2 +
  covarianceVarianceBound 25310 (mW 12655) /
    ((1/1000)*covarianceMeanBound 25310 (mW 12655))^2 +
  normVarianceBound 25310 (mW 12655) / (3*inputVarianceMean 25310 (mW 12655))^2

end BstLean.Part268.WorldRow12655
namespace BstLean.Part268.WorldRow12656
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12656 = 228053967178570 := by
  have hu : mW 12656 ≤ 228053967178570 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12656 ≤ 228053967178569 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12656)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25312 ^ 2)
    ((1562500000000000000/248499978898952645162977))
    ((25000000000000000000/3975842582750562832933053)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25312) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25312 : ℝ)^2 / (mW 12656 : ℝ)) * (1 + 1/10^6)^2 *
    √(((408773/200000000000))/2) * ((1-firstRatio 25312) * √(1-firstRatio 25312) *
      sixthConstant (e1CovarianceRatio 25312 (mW 12656) (1/10^6) rowEps))) /
    (712/10000 - 25312*(1+1/10^6)*((408773/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25312 (mW 12656) /
    ((1/10^5) * ((mW 12656 : ℝ)*25312*((mW 12656 : ℝ)+25312+1)))^2 +
  8*(mW 12656 : ℝ)*25312*(25312+2)*(25312+3) /
    ((1/1000)*((mW 12656 : ℝ)*25312*(25312+2)))^2 +
  covarianceVarianceBound 25312 (mW 12656) /
    ((1/1000)*covarianceMeanBound 25312 (mW 12656))^2 +
  normVarianceBound 25312 (mW 12656) / (3*inputVarianceMean 25312 (mW 12656))^2

end BstLean.Part268.WorldRow12656
namespace BstLean.Part268.WorldRow12657
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12657 = 228117041429777 := by
  have hu : mW 12657 ≤ 228117041429777 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12657 ≤ 228117041429776 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12657)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25314 ^ 2)
    ((25000000000000000000/3976313821648601301931479))
    ((25000000000000000000/3976156742015921812256899)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25314) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25314 : ℝ)^2 / (mW 12657 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1021851/500000000000))/2) * ((1-firstRatio 25314) * √(1-firstRatio 25314) *
      sixthConstant (e1CovarianceRatio 25314 (mW 12657) (1/10^6) rowEps))) /
    (712/10000 - 25314*(1+1/10^6)*((1021851/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25314 (mW 12657) /
    ((1/10^5) * ((mW 12657 : ℝ)*25314*((mW 12657 : ℝ)+25314+1)))^2 +
  8*(mW 12657 : ℝ)*25314*(25314+2)*(25314+3) /
    ((1/1000)*((mW 12657 : ℝ)*25314*(25314+2)))^2 +
  covarianceVarianceBound 25314 (mW 12657) /
    ((1/1000)*covarianceMeanBound 25314 (mW 12657))^2 +
  normVarianceBound 25314 (mW 12657) / (3*inputVarianceMean 25314 (mW 12657))^2

end BstLean.Part268.WorldRow12657
namespace BstLean.Part268.WorldRow12658
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12658 = 228180128140586 := by
  have hu : mW 12658 ≤ 228180128140586 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12658 ≤ 228180128140585 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12658)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25316 ^ 2)
    ((12500000000000000000/1988313990456980140627663))
    ((5000000000000000000/795294180256256158316149)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25316) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25316 : ℝ)^2 / (mW 12658 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2043539/1000000000000))/2) * ((1-firstRatio 25316) * √(1-firstRatio 25316) *
      sixthConstant (e1CovarianceRatio 25316 (mW 12658) (1/10^6) rowEps))) /
    (712/10000 - 25316*(1+1/10^6)*((2043539/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25316 (mW 12658) /
    ((1/10^5) * ((mW 12658 : ℝ)*25316*((mW 12658 : ℝ)+25316+1)))^2 +
  8*(mW 12658 : ℝ)*25316*(25316+2)*(25316+3) /
    ((1/1000)*((mW 12658 : ℝ)*25316*(25316+2)))^2 +
  covarianceVarianceBound 25316 (mW 12658) /
    ((1/1000)*covarianceMeanBound 25316 (mW 12658))^2 +
  normVarianceBound 25316 (mW 12658) / (3*inputVarianceMean 25316 (mW 12658))^2

end BstLean.Part268.WorldRow12658
namespace BstLean.Part268.WorldRow12659
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12659 = 228243227312476 := by
  have hu : mW 12659 ≤ 228243227312476 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12659 ≤ 228243227312475 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12659)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25318 ^ 2)
    ((25000000000000000000/3976942140179319260579173))
    ((25000000000000000000/3976785060546639770904591)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25318) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25318 : ℝ)^2 / (mW 12659 : ℝ)) * (1 + 1/10^6)^2 *
    √(((127711/62500000000))/2) * ((1-firstRatio 25318) * √(1-firstRatio 25318) *
      sixthConstant (e1CovarianceRatio 25318 (mW 12659) (1/10^6) rowEps))) /
    (712/10000 - 25318*(1+1/10^6)*((127711/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25318 (mW 12659) /
    ((1/10^5) * ((mW 12659 : ℝ)*25318*((mW 12659 : ℝ)+25318+1)))^2 +
  8*(mW 12659 : ℝ)*25318*(25318+2)*(25318+3) /
    ((1/1000)*((mW 12659 : ℝ)*25318*(25318+2)))^2 +
  covarianceVarianceBound 25318 (mW 12659) /
    ((1/1000)*covarianceMeanBound 25318 (mW 12659))^2 +
  normVarianceBound 25318 (mW 12659) / (3*inputVarianceMean 25318 (mW 12659))^2

end BstLean.Part268.WorldRow12659
namespace BstLean.Part268.WorldRow12660
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12660 = 228306338946923 := by
  have hu : mW 12660 ≤ 228306338946923 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12660 ≤ 228306338946922 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12660)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25320 ^ 2)
    ((1250000000000000000/198862814972233911995151))
    ((25000000000000000000/3977099219811998750228437)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25320) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25320 : ℝ)^2 / (mW 12660 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2043213/1000000000000))/2) * ((1-firstRatio 25320) * √(1-firstRatio 25320) *
      sixthConstant (e1CovarianceRatio 25320 (mW 12660) (1/10^6) rowEps))) /
    (712/10000 - 25320*(1+1/10^6)*((2043213/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25320 (mW 12660) /
    ((1/10^5) * ((mW 12660 : ℝ)*25320*((mW 12660 : ℝ)+25320+1)))^2 +
  8*(mW 12660 : ℝ)*25320*(25320+2)*(25320+3) /
    ((1/1000)*((mW 12660 : ℝ)*25320*(25320+2)))^2 +
  covarianceVarianceBound 25320 (mW 12660) /
    ((1/1000)*covarianceMeanBound 25320 (mW 12660))^2 +
  normVarianceBound 25320 (mW 12660) / (3*inputVarianceMean 25320 (mW 12660))^2

end BstLean.Part268.WorldRow12660
namespace BstLean.Part268.WorldRow12661
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12661 = 228369463045404 := by
  have hu : mW 12661 ≤ 228369463045404 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12661 ≤ 228369463045403 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12661)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25322 ^ 2)
    ((25000000000000000000/3977570458710037219226867))
    ((25000000000000000000/3977413379077357729552283)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25322) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25322 : ℝ)^2 / (mW 12661 : ℝ)) * (1 + 1/10^6)^2 *
    √(((40861/20000000000))/2) * ((1-firstRatio 25322) * √(1-firstRatio 25322) *
      sixthConstant (e1CovarianceRatio 25322 (mW 12661) (1/10^6) rowEps))) /
    (712/10000 - 25322*(1+1/10^6)*((40861/20000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25322 (mW 12661) /
    ((1/10^5) * ((mW 12661 : ℝ)*25322*((mW 12661 : ℝ)+25322+1)))^2 +
  8*(mW 12661 : ℝ)*25322*(25322+2)*(25322+3) /
    ((1/1000)*((mW 12661 : ℝ)*25322*(25322+2)))^2 +
  covarianceVarianceBound 25322 (mW 12661) /
    ((1/1000)*covarianceMeanBound 25322 (mW 12661))^2 +
  normVarianceBound 25322 (mW 12661) / (3*inputVarianceMean 25322 (mW 12661))^2

end BstLean.Part268.WorldRow12661
namespace BstLean.Part268.WorldRow12662
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12662 = 228432599609395 := by
  have hu : mW 12662 ≤ 228432599609395 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12662 ≤ 228432599609394 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12662)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25324 ^ 2)
    ((12500000000000000000/1988942308987698099275357))
    ((25000000000000000000/3977727538342716708876129)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25324) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25324 : ℝ)^2 / (mW 12662 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2042887/1000000000000))/2) * ((1-firstRatio 25324) * √(1-firstRatio 25324) *
      sixthConstant (e1CovarianceRatio 25324 (mW 12662) (1/10^6) rowEps))) /
    (712/10000 - 25324*(1+1/10^6)*((2042887/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25324 (mW 12662) /
    ((1/10^5) * ((mW 12662 : ℝ)*25324*((mW 12662 : ℝ)+25324+1)))^2 +
  8*(mW 12662 : ℝ)*25324*(25324+2)*(25324+3) /
    ((1/1000)*((mW 12662 : ℝ)*25324*(25324+2)))^2 +
  covarianceVarianceBound 25324 (mW 12662) /
    ((1/1000)*covarianceMeanBound 25324 (mW 12662))^2 +
  normVarianceBound 25324 (mW 12662) / (3*inputVarianceMean 25324 (mW 12662))^2

end BstLean.Part268.WorldRow12662
namespace BstLean.Part268.WorldRow12663
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12663 = 228495748640373 := by
  have hu : mW 12663 ≤ 228495748640373 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12663 ≤ 228495748640372 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12663)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25326 ^ 2)
    ((25000000000000000000/3978198777240755177874561))
    ((1000000000000000000/159121667904323027527999)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25326) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25326 : ℝ)^2 / (mW 12663 : ℝ)) * (1 + 1/10^6)^2 *
    √(((510681/250000000000))/2) * ((1-firstRatio 25326) * √(1-firstRatio 25326) *
      sixthConstant (e1CovarianceRatio 25326 (mW 12663) (1/10^6) rowEps))) /
    (712/10000 - 25326*(1+1/10^6)*((510681/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25326 (mW 12663) /
    ((1/10^5) * ((mW 12663 : ℝ)*25326*((mW 12663 : ℝ)+25326+1)))^2 +
  8*(mW 12663 : ℝ)*25326*(25326+2)*(25326+3) /
    ((1/1000)*((mW 12663 : ℝ)*25326*(25326+2)))^2 +
  covarianceVarianceBound 25326 (mW 12663) /
    ((1/1000)*covarianceMeanBound 25326 (mW 12663))^2 +
  normVarianceBound 25326 (mW 12663) / (3*inputVarianceMean 25326 (mW 12663))^2

end BstLean.Part268.WorldRow12663
namespace BstLean.Part268.WorldRow12664
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12664 = 228558910139815 := by
  have hu : mW 12664 ≤ 228558910139815 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12664 ≤ 228558910139814 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12664)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25328 ^ 2)
    ((3125000000000000000/497314117063264269649801))
    ((25000000000000000000/3978355856873434667523821)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25328) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25328 : ℝ)^2 / (mW 12664 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2042561/1000000000000))/2) * ((1-firstRatio 25328) * √(1-firstRatio 25328) *
      sixthConstant (e1CovarianceRatio 25328 (mW 12664) (1/10^6) rowEps))) /
    (712/10000 - 25328*(1+1/10^6)*((2042561/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25328 (mW 12664) /
    ((1/10^5) * ((mW 12664 : ℝ)*25328*((mW 12664 : ℝ)+25328+1)))^2 +
  8*(mW 12664 : ℝ)*25328*(25328+2)*(25328+3) /
    ((1/1000)*((mW 12664 : ℝ)*25328*(25328+2)))^2 +
  covarianceVarianceBound 25328 (mW 12664) /
    ((1/1000)*covarianceMeanBound 25328 (mW 12664))^2 +
  normVarianceBound 25328 (mW 12664) / (3*inputVarianceMean 25328 (mW 12664))^2

end BstLean.Part268.WorldRow12664
namespace BstLean.Part268.WorldRow12665
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12665 = 228622084109199 := by
  have hu : mW 12665 ≤ 228622084109199 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12665 ≤ 228622084109198 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12665)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25330 ^ 2)
    ((5000000000000000000/795765419154294627304451))
    ((25000000000000000000/3978670016138793646847667)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25330) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25330 : ℝ)^2 / (mW 12665 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1021199/500000000000))/2) * ((1-firstRatio 25330) * √(1-firstRatio 25330) *
      sixthConstant (e1CovarianceRatio 25330 (mW 12665) (1/10^6) rowEps))) /
    (712/10000 - 25330*(1+1/10^6)*((1021199/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25330 (mW 12665) /
    ((1/10^5) * ((mW 12665 : ℝ)*25330*((mW 12665 : ℝ)+25330+1)))^2 +
  8*(mW 12665 : ℝ)*25330*(25330+2)*(25330+3) /
    ((1/1000)*((mW 12665 : ℝ)*25330*(25330+2)))^2 +
  covarianceVarianceBound 25330 (mW 12665) /
    ((1/1000)*covarianceMeanBound 25330 (mW 12665))^2 +
  normVarianceBound 25330 (mW 12665) / (3*inputVarianceMean 25330 (mW 12665))^2

end BstLean.Part268.WorldRow12665
namespace BstLean.Part268.WorldRow12666
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12666 = 228685270550001 := by
  have hu : mW 12666 ≤ 228685270550001 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12666 ≤ 228685270550000 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12666)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25332 ^ 2)
    ((12500000000000000000/1989570627518416057923051))
    ((25000000000000000000/3978984175404152626171513)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25332) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25332 : ℝ)^2 / (mW 12666 : ℝ)) * (1 + 1/10^6)^2 *
    √(((408447/200000000000))/2) * ((1-firstRatio 25332) * √(1-firstRatio 25332) *
      sixthConstant (e1CovarianceRatio 25332 (mW 12666) (1/10^6) rowEps))) /
    (712/10000 - 25332*(1+1/10^6)*((408447/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25332 (mW 12666) /
    ((1/10^5) * ((mW 12666 : ℝ)*25332*((mW 12666 : ℝ)+25332+1)))^2 +
  8*(mW 12666 : ℝ)*25332*(25332+2)*(25332+3) /
    ((1/1000)*((mW 12666 : ℝ)*25332*(25332+2)))^2 +
  covarianceVarianceBound 25332 (mW 12666) /
    ((1/1000)*covarianceMeanBound 25332 (mW 12666))^2 +
  normVarianceBound 25332 (mW 12666) / (3*inputVarianceMean 25332 (mW 12666))^2

end BstLean.Part268.WorldRow12666
namespace BstLean.Part268.WorldRow12667
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12667 = 228748469463698 := by
  have hu : mW 12667 ≤ 228748469463698 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12667 ≤ 228748469463697 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12667)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25334 ^ 2)
    ((25000000000000000000/3979455414302191095169949))
    ((25000000000000000000/3979298334669511605495359)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25334) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25334 : ℝ)^2 / (mW 12667 : ℝ)) * (1 + 1/10^6)^2 *
    √(((255259/125000000000))/2) * ((1-firstRatio 25334) * √(1-firstRatio 25334) *
      sixthConstant (e1CovarianceRatio 25334 (mW 12667) (1/10^6) rowEps))) /
    (712/10000 - 25334*(1+1/10^6)*((255259/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25334 (mW 12667) /
    ((1/10^5) * ((mW 12667 : ℝ)*25334*((mW 12667 : ℝ)+25334+1)))^2 +
  8*(mW 12667 : ℝ)*25334*(25334+2)*(25334+3) /
    ((1/1000)*((mW 12667 : ℝ)*25334*(25334+2)))^2 +
  covarianceVarianceBound 25334 (mW 12667) /
    ((1/1000)*covarianceMeanBound 25334 (mW 12667))^2 +
  normVarianceBound 25334 (mW 12667) / (3*inputVarianceMean 25334 (mW 12667))^2

end BstLean.Part268.WorldRow12667
namespace BstLean.Part268.WorldRow12668
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12668 = 228811680851768 := by
  have hu : mW 12668 ≤ 228811680851768 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12668 ≤ 228811680851767 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12668)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25336 ^ 2)
    ((6250000000000000000/994942393391887518623449))
    ((5000000000000000000/795922498786974116963841)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25336) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25336 : ℝ)^2 / (mW 12668 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2041909/1000000000000))/2) * ((1-firstRatio 25336) * √(1-firstRatio 25336) *
      sixthConstant (e1CovarianceRatio 25336 (mW 12668) (1/10^6) rowEps))) /
    (712/10000 - 25336*(1+1/10^6)*((2041909/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25336 (mW 12668) /
    ((1/10^5) * ((mW 12668 : ℝ)*25336*((mW 12668 : ℝ)+25336+1)))^2 +
  8*(mW 12668 : ℝ)*25336*(25336+2)*(25336+3) /
    ((1/1000)*((mW 12668 : ℝ)*25336*(25336+2)))^2 +
  covarianceVarianceBound 25336 (mW 12668) /
    ((1/1000)*covarianceMeanBound 25336 (mW 12668))^2 +
  normVarianceBound 25336 (mW 12668) / (3*inputVarianceMean 25336 (mW 12668))^2

end BstLean.Part268.WorldRow12668
namespace BstLean.Part268.WorldRow12669
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12669 = 228874904715687 := by
  have hu : mW 12669 ≤ 228874904715687 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12669 ≤ 228874904715686 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12669)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25338 ^ 2)
    ((25000000000000000000/3980083732832909053817643))
    ((25000000000000000000/3979926653200229564143051)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25338) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25338 : ℝ)^2 / (mW 12669 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1020873/500000000000))/2) * ((1-firstRatio 25338) * √(1-firstRatio 25338) *
      sixthConstant (e1CovarianceRatio 25338 (mW 12669) (1/10^6) rowEps))) /
    (712/10000 - 25338*(1+1/10^6)*((1020873/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25338 (mW 12669) /
    ((1/10^5) * ((mW 12669 : ℝ)*25338*((mW 12669 : ℝ)+25338+1)))^2 +
  8*(mW 12669 : ℝ)*25338*(25338+2)*(25338+3) /
    ((1/1000)*((mW 12669 : ℝ)*25338*(25338+2)))^2 +
  covarianceVarianceBound 25338 (mW 12669) /
    ((1/1000)*covarianceMeanBound 25338 (mW 12669))^2 +
  normVarianceBound 25338 (mW 12669) / (3*inputVarianceMean 25338 (mW 12669))^2

end BstLean.Part268.WorldRow12669
namespace BstLean.Part268.WorldRow12670
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12670 = 228938141056934 := by
  have hu : mW 12670 ≤ 228938141056934 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12670 ≤ 228938141056933 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12670)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25340 ^ 2)
    ((2500000000000000000/398039789209826803314149))
    ((25000000000000000000/3980240812465588543466897)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25340) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25340 : ℝ)^2 / (mW 12670 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2041583/1000000000000))/2) * ((1-firstRatio 25340) * √(1-firstRatio 25340) *
      sixthConstant (e1CovarianceRatio 25340 (mW 12670) (1/10^6) rowEps))) /
    (712/10000 - 25340*(1+1/10^6)*((2041583/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25340 (mW 12670) /
    ((1/10^5) * ((mW 12670 : ℝ)*25340*((mW 12670 : ℝ)+25340+1)))^2 +
  8*(mW 12670 : ℝ)*25340*(25340+2)*(25340+3) /
    ((1/1000)*((mW 12670 : ℝ)*25340*(25340+2)))^2 +
  covarianceVarianceBound 25340 (mW 12670) /
    ((1/1000)*covarianceMeanBound 25340 (mW 12670))^2 +
  normVarianceBound 25340 (mW 12670) / (3*inputVarianceMean 25340 (mW 12670))^2

end BstLean.Part268.WorldRow12670
namespace BstLean.Part268.WorldRow12671
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12671 = 229001389876985 := by
  have hu : mW 12671 ≤ 229001389876985 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12671 ≤ 229001389876984 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12671)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25342 ^ 2)
    ((25000000000000000000/3980712051363627012465337))
    ((25000000000000000000/3980554971730947522790743)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25342) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25342 : ℝ)^2 / (mW 12671 : ℝ)) * (1 + 1/10^6)^2 *
    √(((102071/50000000000))/2) * ((1-firstRatio 25342) * √(1-firstRatio 25342) *
      sixthConstant (e1CovarianceRatio 25342 (mW 12671) (1/10^6) rowEps))) /
    (712/10000 - 25342*(1+1/10^6)*((102071/50000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25342 (mW 12671) /
    ((1/10^5) * ((mW 12671 : ℝ)*25342*((mW 12671 : ℝ)+25342+1)))^2 +
  8*(mW 12671 : ℝ)*25342*(25342+2)*(25342+3) /
    ((1/1000)*((mW 12671 : ℝ)*25342*(25342+2)))^2 +
  covarianceVarianceBound 25342 (mW 12671) /
    ((1/1000)*covarianceMeanBound 25342 (mW 12671))^2 +
  normVarianceBound 25342 (mW 12671) / (3*inputVarianceMean 25342 (mW 12671))^2

end BstLean.Part268.WorldRow12671
namespace BstLean.Part268.WorldRow12672
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12672 = 229064651177317 := by
  have hu : mW 12672 ≤ 229064651177317 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12672 ≤ 229064651177316 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12672)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25344 ^ 2)
    ((195312500000000000/31101767270538953060853))
    ((25000000000000000000/3980869130996306502114589)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25344) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25344 : ℝ)^2 / (mW 12672 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1020629/500000000000))/2) * ((1-firstRatio 25344) * √(1-firstRatio 25344) *
      sixthConstant (e1CovarianceRatio 25344 (mW 12672) (1/10^6) rowEps))) /
    (712/10000 - 25344*(1+1/10^6)*((1020629/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25344 (mW 12672) /
    ((1/10^5) * ((mW 12672 : ℝ)*25344*((mW 12672 : ℝ)+25344+1)))^2 +
  8*(mW 12672 : ℝ)*25344*(25344+2)*(25344+3) /
    ((1/1000)*((mW 12672 : ℝ)*25344*(25344+2)))^2 +
  covarianceVarianceBound 25344 (mW 12672) /
    ((1/1000)*covarianceMeanBound 25344 (mW 12672))^2 +
  normVarianceBound 25344 (mW 12672) / (3*inputVarianceMean 25344 (mW 12672))^2

end BstLean.Part268.WorldRow12672
namespace BstLean.Part268.WorldRow12673
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12673 = 229127924959409 := by
  have hu : mW 12673 ≤ 229127924959409 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12673 ≤ 229127924959408 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12673)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25346 ^ 2)
    ((25000000000000000000/3981340369894344971113031))
    ((5000000000000000000/796236658052333096287687)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25346) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25346 : ℝ)^2 / (mW 12673 : ℝ)) * (1 + 1/10^6)^2 *
    √(((408219/200000000000))/2) * ((1-firstRatio 25346) * √(1-firstRatio 25346) *
      sixthConstant (e1CovarianceRatio 25346 (mW 12673) (1/10^6) rowEps))) /
    (712/10000 - 25346*(1+1/10^6)*((408219/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25346 (mW 12673) /
    ((1/10^5) * ((mW 12673 : ℝ)*25346*((mW 12673 : ℝ)+25346+1)))^2 +
  8*(mW 12673 : ℝ)*25346*(25346+2)*(25346+3) /
    ((1/1000)*((mW 12673 : ℝ)*25346*(25346+2)))^2 +
  covarianceVarianceBound 25346 (mW 12673) /
    ((1/1000)*covarianceMeanBound 25346 (mW 12673))^2 +
  normVarianceBound 25346 (mW 12673) / (3*inputVarianceMean 25346 (mW 12673))^2

end BstLean.Part268.WorldRow12673
namespace BstLean.Part268.WorldRow12674
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12674 = 229191211224738 := by
  have hu : mW 12674 ≤ 229191211224738 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12674 ≤ 229191211224737 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12674)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25348 ^ 2)
    ((12500000000000000000/1990827264579851975218439))
    ((25000000000000000000/3981497449527024460762281)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25348) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25348 : ℝ)^2 / (mW 12674 : ℝ)) * (1 + 1/10^6)^2 *
    √(((510233/250000000000))/2) * ((1-firstRatio 25348) * √(1-firstRatio 25348) *
      sixthConstant (e1CovarianceRatio 25348 (mW 12674) (1/10^6) rowEps))) /
    (712/10000 - 25348*(1+1/10^6)*((510233/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25348 (mW 12674) /
    ((1/10^5) * ((mW 12674 : ℝ)*25348*((mW 12674 : ℝ)+25348+1)))^2 +
  8*(mW 12674 : ℝ)*25348*(25348+2)*(25348+3) /
    ((1/1000)*((mW 12674 : ℝ)*25348*(25348+2)))^2 +
  covarianceVarianceBound 25348 (mW 12674) /
    ((1/1000)*covarianceMeanBound 25348 (mW 12674))^2 +
  normVarianceBound 25348 (mW 12674) / (3*inputVarianceMean 25348 (mW 12674))^2

end BstLean.Part268.WorldRow12674
