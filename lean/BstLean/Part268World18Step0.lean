import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar18
namespace BstLean.Part268.WorldRow12800
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12800 = 237265664060629 := by
  have hu : mW 12800 ≤ 237265664060629 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12800 ≤ 237265664060628 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12800)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25600 ^ 2)
    ((1953125000000000/314159265358979323847))
    ((25000000000000000000/4021081516962255855566877)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25600) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25600 : ℝ)^2 / (mW 12800 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1010317/500000000000))/2) * ((1-firstRatio 25600) * √(1-firstRatio 25600) *
      sixthConstant (e1CovarianceRatio 25600 (mW 12800) (1/10^6) rowEps))) /
    (712/10000 - 25600*(1+1/10^6)*((1010317/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25600 (mW 12800) /
    ((1/10^5) * ((mW 12800 : ℝ)*25600*((mW 12800 : ℝ)+25600+1)))^2 +
  8*(mW 12800 : ℝ)*25600*(25600+2)*(25600+3) /
    ((1/1000)*((mW 12800 : ℝ)*25600*(25600+2)))^2 +
  covarianceVarianceBound 25600 (mW 12800) /
    ((1/1000)*covarianceMeanBound 25600 (mW 12800))^2 +
  normVarianceBound 25600 (mW 12800) / (3*inputVarianceMean 25600 (mW 12800))^2

end BstLean.Part268.WorldRow12800
namespace BstLean.Part268.WorldRow12801
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12801 = 237330547726570 := by
  have hu : mW 12801 ≤ 237330547726570 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12801 ≤ 237330547726569 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12801)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25602 ^ 2)
    ((25000000000000000000/4021552755860294324565447))
    ((25000000000000000000/4021395676227614834890723)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25602) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25602 : ℝ)^2 / (mW 12801 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1010237/500000000000))/2) * ((1-firstRatio 25602) * √(1-firstRatio 25602) *
      sixthConstant (e1CovarianceRatio 25602 (mW 12801) (1/10^6) rowEps))) /
    (712/10000 - 25602*(1+1/10^6)*((1010237/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25602 (mW 12801) /
    ((1/10^5) * ((mW 12801 : ℝ)*25602*((mW 12801 : ℝ)+25602+1)))^2 +
  8*(mW 12801 : ℝ)*25602*(25602+2)*(25602+3) /
    ((1/1000)*((mW 12801 : ℝ)*25602*(25602+2)))^2 +
  covarianceVarianceBound 25602 (mW 12801) /
    ((1/1000)*covarianceMeanBound 25602 (mW 12801))^2 +
  normVarianceBound 25602 (mW 12801) / (3*inputVarianceMean 25602 (mW 12801))^2

end BstLean.Part268.WorldRow12801
namespace BstLean.Part268.WorldRow12802
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12802 = 237395444065350 := by
  have hu : mW 12802 ≤ 237395444065350 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12802 ≤ 237395444065349 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12802)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25604 ^ 2)
    ((12500000000000000000/2010933457562826651944647))
    ((25000000000000000000/4021709835492973814214569)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25604) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25604 : ℝ)^2 / (mW 12802 : ℝ)) * (1 + 1/10^6)^2 *
    √(((404063/200000000000))/2) * ((1-firstRatio 25604) * √(1-firstRatio 25604) *
      sixthConstant (e1CovarianceRatio 25604 (mW 12802) (1/10^6) rowEps))) /
    (712/10000 - 25604*(1+1/10^6)*((404063/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25604 (mW 12802) /
    ((1/10^5) * ((mW 12802 : ℝ)*25604*((mW 12802 : ℝ)+25604+1)))^2 +
  8*(mW 12802 : ℝ)*25604*(25604+2)*(25604+3) /
    ((1/1000)*((mW 12802 : ℝ)*25604*(25604+2)))^2 +
  covarianceVarianceBound 25604 (mW 12802) /
    ((1/1000)*covarianceMeanBound 25604 (mW 12802))^2 +
  normVarianceBound 25604 (mW 12802) / (3*inputVarianceMean 25604 (mW 12802))^2

end BstLean.Part268.WorldRow12802
namespace BstLean.Part268.WorldRow12803
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12803 = 237460353078452 := by
  have hu : mW 12803 ≤ 237460353078452 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12803 ≤ 237460353078451 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12803)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25606 ^ 2)
    ((25000000000000000000/4022181074391012283213141))
    ((5000000000000000000/804404798951666558707683)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25606) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25606 : ℝ)^2 / (mW 12803 : ℝ)) * (1 + 1/10^6)^2 *
    √(((505039/250000000000))/2) * ((1-firstRatio 25606) * √(1-firstRatio 25606) *
      sixthConstant (e1CovarianceRatio 25606 (mW 12803) (1/10^6) rowEps))) /
    (712/10000 - 25606*(1+1/10^6)*((505039/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25606 (mW 12803) /
    ((1/10^5) * ((mW 12803 : ℝ)*25606*((mW 12803 : ℝ)+25606+1)))^2 +
  8*(mW 12803 : ℝ)*25606*(25606+2)*(25606+3) /
    ((1/1000)*((mW 12803 : ℝ)*25606*(25606+2)))^2 +
  covarianceVarianceBound 25606 (mW 12803) /
    ((1/1000)*covarianceMeanBound 25606 (mW 12803))^2 +
  normVarianceBound 25606 (mW 12803) / (3*inputVarianceMean 25606 (mW 12803))^2

end BstLean.Part268.WorldRow12803
namespace BstLean.Part268.WorldRow12804
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12804 = 237525274767364 := by
  have hu : mW 12804 ≤ 237525274767364 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12804 ≤ 237525274767363 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12804)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25608 ^ 2)
    ((6250000000000000000/1005623808414092815634247))
    ((25000000000000000000/4022338154023691772862261)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25608) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25608 : ℝ)^2 / (mW 12804 : ℝ)) * (1 + 1/10^6)^2 *
    √(((504999/250000000000))/2) * ((1-firstRatio 25608) * √(1-firstRatio 25608) *
      sixthConstant (e1CovarianceRatio 25608 (mW 12804) (1/10^6) rowEps))) /
    (712/10000 - 25608*(1+1/10^6)*((504999/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25608 (mW 12804) /
    ((1/10^5) * ((mW 12804 : ℝ)*25608*((mW 12804 : ℝ)+25608+1)))^2 +
  8*(mW 12804 : ℝ)*25608*(25608+2)*(25608+3) /
    ((1/1000)*((mW 12804 : ℝ)*25608*(25608+2)))^2 +
  covarianceVarianceBound 25608 (mW 12804) /
    ((1/1000)*covarianceMeanBound 25608 (mW 12804))^2 +
  normVarianceBound 25608 (mW 12804) / (3*inputVarianceMean 25608 (mW 12804))^2

end BstLean.Part268.WorldRow12804
namespace BstLean.Part268.WorldRow12805
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12805 = 237590209133569 := by
  have hu : mW 12805 ≤ 237590209133569 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12805 ≤ 237590209133568 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12805)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25610 ^ 2)
    ((5000000000000000000/804561878584346048372167))
    ((25000000000000000000/4022652313289050752186107)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25610) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25610 : ℝ)^2 / (mW 12805 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2019837/1000000000000))/2) * ((1-firstRatio 25610) * √(1-firstRatio 25610) *
      sixthConstant (e1CovarianceRatio 25610 (mW 12805) (1/10^6) rowEps))) /
    (712/10000 - 25610*(1+1/10^6)*((2019837/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25610 (mW 12805) /
    ((1/10^5) * ((mW 12805 : ℝ)*25610*((mW 12805 : ℝ)+25610+1)))^2 +
  8*(mW 12805 : ℝ)*25610*(25610+2)*(25610+3) /
    ((1/1000)*((mW 12805 : ℝ)*25610*(25610+2)))^2 +
  covarianceVarianceBound 25610 (mW 12805) /
    ((1/1000)*covarianceMeanBound 25610 (mW 12805))^2 +
  normVarianceBound 25610 (mW 12805) / (3*inputVarianceMean 25610 (mW 12805))^2

end BstLean.Part268.WorldRow12805
namespace BstLean.Part268.WorldRow12806
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12806 = 237655156178553 := by
  have hu : mW 12806 ≤ 237655156178553 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12806 ≤ 237655156178552 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12806)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25612 ^ 2)
    ((12500000000000000000/2011561776093544610592341))
    ((25000000000000000000/4022966472554409731509953)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25612) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25612 : ℝ)^2 / (mW 12806 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2019677/1000000000000))/2) * ((1-firstRatio 25612) * √(1-firstRatio 25612) *
      sixthConstant (e1CovarianceRatio 25612 (mW 12806) (1/10^6) rowEps))) /
    (712/10000 - 25612*(1+1/10^6)*((2019677/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25612 (mW 12806) /
    ((1/10^5) * ((mW 12806 : ℝ)*25612*((mW 12806 : ℝ)+25612+1)))^2 +
  8*(mW 12806 : ℝ)*25612*(25612+2)*(25612+3) /
    ((1/1000)*((mW 12806 : ℝ)*25612*(25612+2)))^2 +
  covarianceVarianceBound 25612 (mW 12806) /
    ((1/1000)*covarianceMeanBound 25612 (mW 12806))^2 +
  normVarianceBound 25612 (mW 12806) / (3*inputVarianceMean 25612 (mW 12806))^2

end BstLean.Part268.WorldRow12806
namespace BstLean.Part268.WorldRow12807
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12807 = 237720115903801 := by
  have hu : mW 12807 ≤ 237720115903801 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12807 ≤ 237720115903800 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12807)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25614 ^ 2)
    ((25000000000000000000/4023437711452448200508529))
    ((25000000000000000000/4023280631819768710833799)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25614) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25614 : ℝ)^2 / (mW 12807 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1009759/500000000000))/2) * ((1-firstRatio 25614) * √(1-firstRatio 25614) *
      sixthConstant (e1CovarianceRatio 25614 (mW 12807) (1/10^6) rowEps))) /
    (712/10000 - 25614*(1+1/10^6)*((1009759/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25614 (mW 12807) /
    ((1/10^5) * ((mW 12807 : ℝ)*25614*((mW 12807 : ℝ)+25614+1)))^2 +
  8*(mW 12807 : ℝ)*25614*(25614+2)*(25614+3) /
    ((1/1000)*((mW 12807 : ℝ)*25614*(25614+2)))^2 +
  covarianceVarianceBound 25614 (mW 12807) /
    ((1/1000)*covarianceMeanBound 25614 (mW 12807))^2 +
  normVarianceBound 25614 (mW 12807) / (3*inputVarianceMean 25614 (mW 12807))^2

end BstLean.Part268.WorldRow12807
namespace BstLean.Part268.WorldRow12808
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12808 = 237785088310798 := by
  have hu : mW 12808 ≤ 237785088310798 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12808 ≤ 237785088310797 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12808)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25616 ^ 2)
    ((3125000000000000000/502968983839725897479047))
    ((5000000000000000000/804718958217025538031529)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25616) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25616 : ℝ)^2 / (mW 12808 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2019359/1000000000000))/2) * ((1-firstRatio 25616) * √(1-firstRatio 25616) *
      sixthConstant (e1CovarianceRatio 25616 (mW 12808) (1/10^6) rowEps))) /
    (712/10000 - 25616*(1+1/10^6)*((2019359/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25616 (mW 12808) /
    ((1/10^5) * ((mW 12808 : ℝ)*25616*((mW 12808 : ℝ)+25616+1)))^2 +
  8*(mW 12808 : ℝ)*25616*(25616+2)*(25616+3) /
    ((1/1000)*((mW 12808 : ℝ)*25616*(25616+2)))^2 +
  covarianceVarianceBound 25616 (mW 12808) /
    ((1/1000)*covarianceMeanBound 25616 (mW 12808))^2 +
  normVarianceBound 25616 (mW 12808) / (3*inputVarianceMean 25616 (mW 12808))^2

end BstLean.Part268.WorldRow12808
namespace BstLean.Part268.WorldRow12809
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12809 = 237850073401030 := by
  have hu : mW 12809 ≤ 237850073401030 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12809 ≤ 237850073401029 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12809)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25618 ^ 2)
    ((25000000000000000000/4024066029983166159156223))
    ((25000000000000000000/4023908950350486669481491)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25618) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25618 : ℝ)^2 / (mW 12809 : ℝ)) * (1 + 1/10^6)^2 *
    √(((631/312500000))/2) * ((1-firstRatio 25618) * √(1-firstRatio 25618) *
      sixthConstant (e1CovarianceRatio 25618 (mW 12809) (1/10^6) rowEps))) /
    (712/10000 - 25618*(1+1/10^6)*((631/312500000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25618 (mW 12809) /
    ((1/10^5) * ((mW 12809 : ℝ)*25618*((mW 12809 : ℝ)+25618+1)))^2 +
  8*(mW 12809 : ℝ)*25618*(25618+2)*(25618+3) /
    ((1/1000)*((mW 12809 : ℝ)*25618*(25618+2)))^2 +
  covarianceVarianceBound 25618 (mW 12809) /
    ((1/1000)*covarianceMeanBound 25618 (mW 12809))^2 +
  normVarianceBound 25618 (mW 12809) / (3*inputVarianceMean 25618 (mW 12809))^2

end BstLean.Part268.WorldRow12809
namespace BstLean.Part268.WorldRow12810
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12810 = 237915071175983 := by
  have hu : mW 12810 ≤ 237915071175983 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12810 ≤ 237915071175982 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12810)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25620 ^ 2)
    ((2500000000000000000/402438018924852513848007))
    ((25000000000000000000/4024223109615845648805337)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25620) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25620 : ℝ)^2 / (mW 12810 : ℝ)) * (1 + 1/10^6)^2 *
    √(((12619/6250000000))/2) * ((1-firstRatio 25620) * √(1-firstRatio 25620) *
      sixthConstant (e1CovarianceRatio 25620 (mW 12810) (1/10^6) rowEps))) /
    (712/10000 - 25620*(1+1/10^6)*((12619/6250000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25620 (mW 12810) /
    ((1/10^5) * ((mW 12810 : ℝ)*25620*((mW 12810 : ℝ)+25620+1)))^2 +
  8*(mW 12810 : ℝ)*25620*(25620+2)*(25620+3) /
    ((1/1000)*((mW 12810 : ℝ)*25620*(25620+2)))^2 +
  covarianceVarianceBound 25620 (mW 12810) /
    ((1/1000)*covarianceMeanBound 25620 (mW 12810))^2 +
  normVarianceBound 25620 (mW 12810) / (3*inputVarianceMean 25620 (mW 12810))^2

end BstLean.Part268.WorldRow12810
namespace BstLean.Part268.WorldRow12811
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12811 = 237980081637141 := by
  have hu : mW 12811 ≤ 237980081637141 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12811 ≤ 237980081637140 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12811)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25622 ^ 2)
    ((25000000000000000000/4024694348513884117803917))
    ((25000000000000000000/4024537268881204628129183)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25622) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25622 : ℝ)^2 / (mW 12811 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2018881/1000000000000))/2) * ((1-firstRatio 25622) * √(1-firstRatio 25622) *
      sixthConstant (e1CovarianceRatio 25622 (mW 12811) (1/10^6) rowEps))) /
    (712/10000 - 25622*(1+1/10^6)*((2018881/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25622 (mW 12811) /
    ((1/10^5) * ((mW 12811 : ℝ)*25622*((mW 12811 : ℝ)+25622+1)))^2 +
  8*(mW 12811 : ℝ)*25622*(25622+2)*(25622+3) /
    ((1/1000)*((mW 12811 : ℝ)*25622*(25622+2)))^2 +
  covarianceVarianceBound 25622 (mW 12811) /
    ((1/1000)*covarianceMeanBound 25622 (mW 12811))^2 +
  normVarianceBound 25622 (mW 12811) / (3*inputVarianceMean 25622 (mW 12811))^2

end BstLean.Part268.WorldRow12811
namespace BstLean.Part268.WorldRow12812
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12812 = 238045104785990 := by
  have hu : mW 12812 ≤ 238045104785990 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12812 ≤ 238045104785989 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12812)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25624 ^ 2)
    ((6250000000000000000/1006252126944810774281941))
    ((25000000000000000000/4024851428146563607453029)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25624) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25624 : ℝ)^2 / (mW 12812 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1009361/500000000000))/2) * ((1-firstRatio 25624) * √(1-firstRatio 25624) *
      sixthConstant (e1CovarianceRatio 25624 (mW 12812) (1/10^6) rowEps))) /
    (712/10000 - 25624*(1+1/10^6)*((1009361/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25624 (mW 12812) /
    ((1/10^5) * ((mW 12812 : ℝ)*25624*((mW 12812 : ℝ)+25624+1)))^2 +
  8*(mW 12812 : ℝ)*25624*(25624+2)*(25624+3) /
    ((1/1000)*((mW 12812 : ℝ)*25624*(25624+2)))^2 +
  covarianceVarianceBound 25624 (mW 12812) /
    ((1/1000)*covarianceMeanBound 25624 (mW 12812))^2 +
  normVarianceBound 25624 (mW 12812) / (3*inputVarianceMean 25624 (mW 12812))^2

end BstLean.Part268.WorldRow12812
namespace BstLean.Part268.WorldRow12813
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12813 = 238110140624016 := by
  have hu : mW 12813 ≤ 238110140624016 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12813 ≤ 238110140624015 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12813)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25626 ^ 2)
    ((25000000000000000000/4025322667044602076451611))
    ((40000000000000000/6440264939859076138843)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25626) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25626 : ℝ)^2 / (mW 12813 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2018563/1000000000000))/2) * ((1-firstRatio 25626) * √(1-firstRatio 25626) *
      sixthConstant (e1CovarianceRatio 25626 (mW 12813) (1/10^6) rowEps))) /
    (712/10000 - 25626*(1+1/10^6)*((2018563/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25626 (mW 12813) /
    ((1/10^5) * ((mW 12813 : ℝ)*25626*((mW 12813 : ℝ)+25626+1)))^2 +
  8*(mW 12813 : ℝ)*25626*(25626+2)*(25626+3) /
    ((1/1000)*((mW 12813 : ℝ)*25626*(25626+2)))^2 +
  covarianceVarianceBound 25626 (mW 12813) /
    ((1/1000)*covarianceMeanBound 25626 (mW 12813))^2 +
  normVarianceBound 25626 (mW 12813) / (3*inputVarianceMean 25626 (mW 12813))^2

end BstLean.Part268.WorldRow12813
namespace BstLean.Part268.WorldRow12814
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12814 = 238175189152705 := by
  have hu : mW 12814 ≤ 238175189152705 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12814 ≤ 238175189152704 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12814)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25628 ^ 2)
    ((12500000000000000000/2012818413154980527887729))
    ((25000000000000000000/4025479746677281566100721)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25628) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25628 : ℝ)^2 / (mW 12814 : ℝ)) * (1 + 1/10^6)^2 *
    √(((504601/250000000000))/2) * ((1-firstRatio 25628) * √(1-firstRatio 25628) *
      sixthConstant (e1CovarianceRatio 25628 (mW 12814) (1/10^6) rowEps))) /
    (712/10000 - 25628*(1+1/10^6)*((504601/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25628 (mW 12814) /
    ((1/10^5) * ((mW 12814 : ℝ)*25628*((mW 12814 : ℝ)+25628+1)))^2 +
  8*(mW 12814 : ℝ)*25628*(25628+2)*(25628+3) /
    ((1/1000)*((mW 12814 : ℝ)*25628*(25628+2)))^2 +
  covarianceVarianceBound 25628 (mW 12814) /
    ((1/1000)*covarianceMeanBound 25628 (mW 12814))^2 +
  normVarianceBound 25628 (mW 12814) / (3*inputVarianceMean 25628 (mW 12814))^2

end BstLean.Part268.WorldRow12814
namespace BstLean.Part268.WorldRow12815
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12815 = 238240250373541 := by
  have hu : mW 12815 ≤ 238240250373541 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12815 ≤ 238240250373540 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12815)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25630 ^ 2)
    ((5000000000000000000/805190197115064007019861))
    ((25000000000000000000/4025793905942640545424567)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25630) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25630 : ℝ)^2 / (mW 12815 : ℝ)) * (1 + 1/10^6)^2 *
    √(((504561/250000000000))/2) * ((1-firstRatio 25630) * √(1-firstRatio 25630) *
      sixthConstant (e1CovarianceRatio 25630 (mW 12815) (1/10^6) rowEps))) /
    (712/10000 - 25630*(1+1/10^6)*((504561/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25630 (mW 12815) /
    ((1/10^5) * ((mW 12815 : ℝ)*25630*((mW 12815 : ℝ)+25630+1)))^2 +
  8*(mW 12815 : ℝ)*25630*(25630+2)*(25630+3) /
    ((1/1000)*((mW 12815 : ℝ)*25630*(25630+2)))^2 +
  covarianceVarianceBound 25630 (mW 12815) /
    ((1/1000)*covarianceMeanBound 25630 (mW 12815))^2 +
  normVarianceBound 25630 (mW 12815) / (3*inputVarianceMean 25630 (mW 12815))^2

end BstLean.Part268.WorldRow12815
namespace BstLean.Part268.WorldRow12816
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12816 = 238305324288012 := by
  have hu : mW 12816 ≤ 238305324288012 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12816 ≤ 238305324288011 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12816)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25632 ^ 2)
    ((1562500000000000000/251641571552542438401447))
    ((25000000000000000000/4026108065207999524748413)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25632) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25632 : ℝ)^2 / (mW 12816 : ℝ)) * (1 + 1/10^6)^2 *
    √(((403617/200000000000))/2) * ((1-firstRatio 25632) * √(1-firstRatio 25632) *
      sixthConstant (e1CovarianceRatio 25632 (mW 12816) (1/10^6) rowEps))) /
    (712/10000 - 25632*(1+1/10^6)*((403617/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25632 (mW 12816) /
    ((1/10^5) * ((mW 12816 : ℝ)*25632*((mW 12816 : ℝ)+25632+1)))^2 +
  8*(mW 12816 : ℝ)*25632*(25632+2)*(25632+3) /
    ((1/1000)*((mW 12816 : ℝ)*25632*(25632+2)))^2 +
  covarianceVarianceBound 25632 (mW 12816) /
    ((1/1000)*covarianceMeanBound 25632 (mW 12816))^2 +
  normVarianceBound 25632 (mW 12816) / (3*inputVarianceMean 25632 (mW 12816))^2

end BstLean.Part268.WorldRow12816
namespace BstLean.Part268.WorldRow12817
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12817 = 238370410897602 := by
  have hu : mW 12817 ≤ 238370410897602 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12817 ≤ 238370410897601 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12817)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25634 ^ 2)
    ((25000000000000000000/4026579304106037993746999))
    ((25000000000000000000/4026422224473358504072259)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25634) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25634 : ℝ)^2 / (mW 12817 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1008963/500000000000))/2) * ((1-firstRatio 25634) * √(1-firstRatio 25634) *
      sixthConstant (e1CovarianceRatio 25634 (mW 12817) (1/10^6) rowEps))) /
    (712/10000 - 25634*(1+1/10^6)*((1008963/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25634 (mW 12817) /
    ((1/10^5) * ((mW 12817 : ℝ)*25634*((mW 12817 : ℝ)+25634+1)))^2 +
  8*(mW 12817 : ℝ)*25634*(25634+2)*(25634+3) /
    ((1/1000)*((mW 12817 : ℝ)*25634*(25634+2)))^2 +
  covarianceVarianceBound 25634 (mW 12817) /
    ((1/1000)*covarianceMeanBound 25634 (mW 12817))^2 +
  normVarianceBound 25634 (mW 12817) / (3*inputVarianceMean 25634 (mW 12817))^2

end BstLean.Part268.WorldRow12817
namespace BstLean.Part268.WorldRow12818
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12818 = 238435510203798 := by
  have hu : mW 12818 ≤ 238435510203798 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12818 ≤ 238435510203797 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12818)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25636 ^ 2)
    ((12500000000000000000/2013446731685698486535423))
    ((5000000000000000000/805347276747743496679221)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25636) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25636 : ℝ)^2 / (mW 12818 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2017767/1000000000000))/2) * ((1-firstRatio 25636) * √(1-firstRatio 25636) *
      sixthConstant (e1CovarianceRatio 25636 (mW 12818) (1/10^6) rowEps))) /
    (712/10000 - 25636*(1+1/10^6)*((2017767/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25636 (mW 12818) /
    ((1/10^5) * ((mW 12818 : ℝ)*25636*((mW 12818 : ℝ)+25636+1)))^2 +
  8*(mW 12818 : ℝ)*25636*(25636+2)*(25636+3) /
    ((1/1000)*((mW 12818 : ℝ)*25636*(25636+2)))^2 +
  covarianceVarianceBound 25636 (mW 12818) /
    ((1/1000)*covarianceMeanBound 25636 (mW 12818))^2 +
  normVarianceBound 25636 (mW 12818) / (3*inputVarianceMean 25636 (mW 12818))^2

end BstLean.Part268.WorldRow12818
namespace BstLean.Part268.WorldRow12819
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12819 = 238500622208085 := by
  have hu : mW 12819 ≤ 238500622208085 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12819 ≤ 238500622208084 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12819)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25638 ^ 2)
    ((25000000000000000000/4027207622636755952394693))
    ((25000000000000000000/4027050543004076462719951)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25638) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25638 : ℝ)^2 / (mW 12819 : ℝ)) * (1 + 1/10^6)^2 *
    √(((252201/125000000000))/2) * ((1-firstRatio 25638) * √(1-firstRatio 25638) *
      sixthConstant (e1CovarianceRatio 25638 (mW 12819) (1/10^6) rowEps))) /
    (712/10000 - 25638*(1+1/10^6)*((252201/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25638 (mW 12819) /
    ((1/10^5) * ((mW 12819 : ℝ)*25638*((mW 12819 : ℝ)+25638+1)))^2 +
  8*(mW 12819 : ℝ)*25638*(25638+2)*(25638+3) /
    ((1/1000)*((mW 12819 : ℝ)*25638*(25638+2)))^2 +
  covarianceVarianceBound 25638 (mW 12819) /
    ((1/1000)*covarianceMeanBound 25638 (mW 12819))^2 +
  normVarianceBound 25638 (mW 12819) / (3*inputVarianceMean 25638 (mW 12819))^2

end BstLean.Part268.WorldRow12819
namespace BstLean.Part268.WorldRow12820
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12820 = 238565746911950 := by
  have hu : mW 12820 ≤ 238565746911950 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12820 ≤ 238565746911949 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12820)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25640 ^ 2)
    ((1250000000000000000/201376089095105746585927))
    ((25000000000000000000/4027364702269435442043797)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25640) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25640 : ℝ)^2 / (mW 12820 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2017449/1000000000000))/2) * ((1-firstRatio 25640) * √(1-firstRatio 25640) *
      sixthConstant (e1CovarianceRatio 25640 (mW 12820) (1/10^6) rowEps))) /
    (712/10000 - 25640*(1+1/10^6)*((2017449/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25640 (mW 12820) /
    ((1/10^5) * ((mW 12820 : ℝ)*25640*((mW 12820 : ℝ)+25640+1)))^2 +
  8*(mW 12820 : ℝ)*25640*(25640+2)*(25640+3) /
    ((1/1000)*((mW 12820 : ℝ)*25640*(25640+2)))^2 +
  covarianceVarianceBound 25640 (mW 12820) /
    ((1/1000)*covarianceMeanBound 25640 (mW 12820))^2 +
  normVarianceBound 25640 (mW 12820) / (3*inputVarianceMean 25640 (mW 12820))^2

end BstLean.Part268.WorldRow12820
namespace BstLean.Part268.WorldRow12821
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12821 = 238630884316879 := by
  have hu : mW 12821 ≤ 238630884316879 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12821 ≤ 238630884316878 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12821)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25642 ^ 2)
    ((25000000000000000000/4027835941167473911042387))
    ((25000000000000000000/4027678861534794421367643)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25642) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25642 : ℝ)^2 / (mW 12821 : ℝ)) * (1 + 1/10^6)^2 *
    √(((201729/100000000000))/2) * ((1-firstRatio 25642) * √(1-firstRatio 25642) *
      sixthConstant (e1CovarianceRatio 25642 (mW 12821) (1/10^6) rowEps))) /
    (712/10000 - 25642*(1+1/10^6)*((201729/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25642 (mW 12821) /
    ((1/10^5) * ((mW 12821 : ℝ)*25642*((mW 12821 : ℝ)+25642+1)))^2 +
  8*(mW 12821 : ℝ)*25642*(25642+2)*(25642+3) /
    ((1/1000)*((mW 12821 : ℝ)*25642*(25642+2)))^2 +
  covarianceVarianceBound 25642 (mW 12821) /
    ((1/1000)*covarianceMeanBound 25642 (mW 12821))^2 +
  normVarianceBound 25642 (mW 12821) / (3*inputVarianceMean 25642 (mW 12821))^2

end BstLean.Part268.WorldRow12821
namespace BstLean.Part268.WorldRow12822
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12822 = 238696034424357 := by
  have hu : mW 12822 ≤ 238696034424357 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12822 ≤ 238696034424356 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12822)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25644 ^ 2)
    ((12500000000000000000/2014075050216416445183117))
    ((25000000000000000000/4027993020800153400691489)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25644) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25644 : ℝ)^2 / (mW 12822 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2017131/1000000000000))/2) * ((1-firstRatio 25644) * √(1-firstRatio 25644) *
      sixthConstant (e1CovarianceRatio 25644 (mW 12822) (1/10^6) rowEps))) /
    (712/10000 - 25644*(1+1/10^6)*((2017131/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25644 (mW 12822) /
    ((1/10^5) * ((mW 12822 : ℝ)*25644*((mW 12822 : ℝ)+25644+1)))^2 +
  8*(mW 12822 : ℝ)*25644*(25644+2)*(25644+3) /
    ((1/1000)*((mW 12822 : ℝ)*25644*(25644+2)))^2 +
  covarianceVarianceBound 25644 (mW 12822) /
    ((1/1000)*covarianceMeanBound 25644 (mW 12822))^2 +
  normVarianceBound 25644 (mW 12822) / (3*inputVarianceMean 25644 (mW 12822))^2

end BstLean.Part268.WorldRow12822
namespace BstLean.Part268.WorldRow12823
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12823 = 238761197235872 := by
  have hu : mW 12823 ≤ 238761197235872 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12823 ≤ 238761197235871 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12823)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25646 ^ 2)
    ((25000000000000000000/4028464259698191869690081))
    ((5000000000000000000/805661436013102476003067)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25646) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25646 : ℝ)^2 / (mW 12823 : ℝ)) * (1 + 1/10^6)^2 *
    √(((504243/250000000000))/2) * ((1-firstRatio 25646) * √(1-firstRatio 25646) *
      sixthConstant (e1CovarianceRatio 25646 (mW 12823) (1/10^6) rowEps))) /
    (712/10000 - 25646*(1+1/10^6)*((504243/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25646 (mW 12823) /
    ((1/10^5) * ((mW 12823 : ℝ)*25646*((mW 12823 : ℝ)+25646+1)))^2 +
  8*(mW 12823 : ℝ)*25646*(25646+2)*(25646+3) /
    ((1/1000)*((mW 12823 : ℝ)*25646*(25646+2)))^2 +
  covarianceVarianceBound 25646 (mW 12823) /
    ((1/1000)*covarianceMeanBound 25646 (mW 12823))^2 +
  normVarianceBound 25646 (mW 12823) / (3*inputVarianceMean 25646 (mW 12823))^2

end BstLean.Part268.WorldRow12823
namespace BstLean.Part268.WorldRow12824
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12824 = 238826372752908 := by
  have hu : mW 12824 ≤ 238826372752908 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12824 ≤ 238826372752907 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12824)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25648 ^ 2)
    ((3125000000000000000/503597302370443856126741))
    ((25000000000000000000/4028621339330871359339181)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25648) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25648 : ℝ)^2 / (mW 12824 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2016813/1000000000000))/2) * ((1-firstRatio 25648) * √(1-firstRatio 25648) *
      sixthConstant (e1CovarianceRatio 25648 (mW 12824) (1/10^6) rowEps))) /
    (712/10000 - 25648*(1+1/10^6)*((2016813/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25648 (mW 12824) /
    ((1/10^5) * ((mW 12824 : ℝ)*25648*((mW 12824 : ℝ)+25648+1)))^2 +
  8*(mW 12824 : ℝ)*25648*(25648+2)*(25648+3) /
    ((1/1000)*((mW 12824 : ℝ)*25648*(25648+2)))^2 +
  covarianceVarianceBound 25648 (mW 12824) /
    ((1/1000)*covarianceMeanBound 25648 (mW 12824))^2 +
  normVarianceBound 25648 (mW 12824) / (3*inputVarianceMean 25648 (mW 12824))^2

end BstLean.Part268.WorldRow12824
