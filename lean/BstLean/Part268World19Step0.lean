import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar19
namespace BstLean.Part268.WorldRow12825
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12825 = 238891560976953 := by
  have hu : mW 12825 ≤ 238891560976953 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12825 ≤ 238891560976952 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12825)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25650 ^ 2)
    ((1000000000000000000/161163703129156393133511))
    ((25000000000000000000/4028935498596230338663027)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25650) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25650 : ℝ)^2 / (mW 12825 : ℝ)) * (1 + 1/10^6)^2 *
    √(((403331/200000000000))/2) * ((1-firstRatio 25650) * √(1-firstRatio 25650) *
      sixthConstant (e1CovarianceRatio 25650 (mW 12825) (1/10^6) rowEps))) /
    (712/10000 - 25650*(1+1/10^6)*((403331/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25650 (mW 12825) /
    ((1/10^5) * ((mW 12825 : ℝ)*25650*((mW 12825 : ℝ)+25650+1)))^2 +
  8*(mW 12825 : ℝ)*25650*(25650+2)*(25650+3) /
    ((1/1000)*((mW 12825 : ℝ)*25650*(25650+2)))^2 +
  covarianceVarianceBound 25650 (mW 12825) /
    ((1/1000)*covarianceMeanBound 25650 (mW 12825))^2 +
  normVarianceBound 25650 (mW 12825) / (3*inputVarianceMean 25650 (mW 12825))^2

end BstLean.Part268.WorldRow12825
namespace BstLean.Part268.WorldRow12826
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12826 = 238956761909492 := by
  have hu : mW 12826 ≤ 238956761909492 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12826 ≤ 238956761909491 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12826)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25652 ^ 2)
    ((12500000000000000000/2014703368747134403830811))
    ((25000000000000000000/4029249657861589317986873)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25652) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25652 : ℝ)^2 / (mW 12826 : ℝ)) * (1 + 1/10^6)^2 *
    √(((126031/62500000000))/2) * ((1-firstRatio 25652) * √(1-firstRatio 25652) *
      sixthConstant (e1CovarianceRatio 25652 (mW 12826) (1/10^6) rowEps))) /
    (712/10000 - 25652*(1+1/10^6)*((126031/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25652 (mW 12826) /
    ((1/10^5) * ((mW 12826 : ℝ)*25652*((mW 12826 : ℝ)+25652+1)))^2 +
  8*(mW 12826 : ℝ)*25652*(25652+2)*(25652+3) /
    ((1/1000)*((mW 12826 : ℝ)*25652*(25652+2)))^2 +
  covarianceVarianceBound 25652 (mW 12826) /
    ((1/1000)*covarianceMeanBound 25652 (mW 12826))^2 +
  normVarianceBound 25652 (mW 12826) / (3*inputVarianceMean 25652 (mW 12826))^2

end BstLean.Part268.WorldRow12826
namespace BstLean.Part268.WorldRow12827
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12827 = 239021975552013 := by
  have hu : mW 12827 ≤ 239021975552013 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12827 ≤ 239021975552012 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12827)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25654 ^ 2)
    ((25000000000000000000/4029720896759627786985469))
    ((25000000000000000000/4029563817126948297310719)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25654) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25654 : ℝ)^2 / (mW 12827 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2016337/1000000000000))/2) * ((1-firstRatio 25654) * √(1-firstRatio 25654) *
      sixthConstant (e1CovarianceRatio 25654 (mW 12827) (1/10^6) rowEps))) /
    (712/10000 - 25654*(1+1/10^6)*((2016337/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25654 (mW 12827) /
    ((1/10^5) * ((mW 12827 : ℝ)*25654*((mW 12827 : ℝ)+25654+1)))^2 +
  8*(mW 12827 : ℝ)*25654*(25654+2)*(25654+3) /
    ((1/1000)*((mW 12827 : ℝ)*25654*(25654+2)))^2 +
  covarianceVarianceBound 25654 (mW 12827) /
    ((1/1000)*covarianceMeanBound 25654 (mW 12827))^2 +
  normVarianceBound 25654 (mW 12827) / (3*inputVarianceMean 25654 (mW 12827))^2

end BstLean.Part268.WorldRow12827
namespace BstLean.Part268.WorldRow12828
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12828 = 239087201906001 := by
  have hu : mW 12828 ≤ 239087201906001 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12828 ≤ 239087201906000 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12828)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25656 ^ 2)
    ((6250000000000000000/1007508764006246691577329))
    ((5000000000000000000/805975595278461455326913)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25656) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25656 : ℝ)^2 / (mW 12828 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1008089/500000000000))/2) * ((1-firstRatio 25656) * √(1-firstRatio 25656) *
      sixthConstant (e1CovarianceRatio 25656 (mW 12828) (1/10^6) rowEps))) /
    (712/10000 - 25656*(1+1/10^6)*((1008089/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25656 (mW 12828) /
    ((1/10^5) * ((mW 12828 : ℝ)*25656*((mW 12828 : ℝ)+25656+1)))^2 +
  8*(mW 12828 : ℝ)*25656*(25656+2)*(25656+3) /
    ((1/1000)*((mW 12828 : ℝ)*25656*(25656+2)))^2 +
  covarianceVarianceBound 25656 (mW 12828) /
    ((1/1000)*covarianceMeanBound 25656 (mW 12828))^2 +
  normVarianceBound 25656 (mW 12828) / (3*inputVarianceMean 25656 (mW 12828))^2

end BstLean.Part268.WorldRow12828
namespace BstLean.Part268.WorldRow12829
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12829 = 239152440972943 := by
  have hu : mW 12829 ≤ 239152440972943 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12829 ≤ 239152440972942 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12829)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25658 ^ 2)
    ((25000000000000000000/4030349215290345745633163))
    ((25000000000000000000/4030192135657666255958411)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25658) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25658 : ℝ)^2 / (mW 12829 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2016019/1000000000000))/2) * ((1-firstRatio 25658) * √(1-firstRatio 25658) *
      sixthConstant (e1CovarianceRatio 25658 (mW 12829) (1/10^6) rowEps))) /
    (712/10000 - 25658*(1+1/10^6)*((2016019/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25658 (mW 12829) /
    ((1/10^5) * ((mW 12829 : ℝ)*25658*((mW 12829 : ℝ)+25658+1)))^2 +
  8*(mW 12829 : ℝ)*25658*(25658+2)*(25658+3) /
    ((1/1000)*((mW 12829 : ℝ)*25658*(25658+2)))^2 +
  covarianceVarianceBound 25658 (mW 12829) /
    ((1/1000)*covarianceMeanBound 25658 (mW 12829))^2 +
  normVarianceBound 25658 (mW 12829) / (3*inputVarianceMean 25658 (mW 12829))^2

end BstLean.Part268.WorldRow12829
namespace BstLean.Part268.WorldRow12830
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12830 = 239217692754327 := by
  have hu : mW 12830 ≤ 239217692754327 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12830 ≤ 239217692754326 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12830)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25660 ^ 2)
    ((2500000000000000000/403066337455570472495701))
    ((25000000000000000000/4030506294923025235282257)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25660) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25660 : ℝ)^2 / (mW 12830 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2015861/1000000000000))/2) * ((1-firstRatio 25660) * √(1-firstRatio 25660) *
      sixthConstant (e1CovarianceRatio 25660 (mW 12830) (1/10^6) rowEps))) /
    (712/10000 - 25660*(1+1/10^6)*((2015861/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25660 (mW 12830) /
    ((1/10^5) * ((mW 12830 : ℝ)*25660*((mW 12830 : ℝ)+25660+1)))^2 +
  8*(mW 12830 : ℝ)*25660*(25660+2)*(25660+3) /
    ((1/1000)*((mW 12830 : ℝ)*25660*(25660+2)))^2 +
  covarianceVarianceBound 25660 (mW 12830) /
    ((1/1000)*covarianceMeanBound 25660 (mW 12830))^2 +
  normVarianceBound 25660 (mW 12830) / (3*inputVarianceMean 25660 (mW 12830))^2

end BstLean.Part268.WorldRow12830
namespace BstLean.Part268.WorldRow12831
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12831 = 239282957251637 := by
  have hu : mW 12831 ≤ 239282957251637 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12831 ≤ 239282957251636 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12831)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25662 ^ 2)
    ((25000000000000000000/4030977533821063704280857))
    ((25000000000000000000/4030820454188384214606103)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25662) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25662 : ℝ)^2 / (mW 12831 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1007851/500000000000))/2) * ((1-firstRatio 25662) * √(1-firstRatio 25662) *
      sixthConstant (e1CovarianceRatio 25662 (mW 12831) (1/10^6) rowEps))) /
    (712/10000 - 25662*(1+1/10^6)*((1007851/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25662 (mW 12831) /
    ((1/10^5) * ((mW 12831 : ℝ)*25662*((mW 12831 : ℝ)+25662+1)))^2 +
  8*(mW 12831 : ℝ)*25662*(25662+2)*(25662+3) /
    ((1/1000)*((mW 12831 : ℝ)*25662*(25662+2)))^2 +
  covarianceVarianceBound 25662 (mW 12831) /
    ((1/1000)*covarianceMeanBound 25662 (mW 12831))^2 +
  normVarianceBound 25662 (mW 12831) / (3*inputVarianceMean 25662 (mW 12831))^2

end BstLean.Part268.WorldRow12831
namespace BstLean.Part268.WorldRow12832
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12832 = 239348234466361 := by
  have hu : mW 12832 ≤ 239348234466361 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12832 ≤ 239348234466360 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12832)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25664 ^ 2)
    ((781250000000000000/125977865408950708862647))
    ((25000000000000000000/4031134613453743193929949)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25664) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25664 : ℝ)^2 / (mW 12832 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2015543/1000000000000))/2) * ((1-firstRatio 25664) * √(1-firstRatio 25664) *
      sixthConstant (e1CovarianceRatio 25664 (mW 12832) (1/10^6) rowEps))) /
    (712/10000 - 25664*(1+1/10^6)*((2015543/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25664 (mW 12832) /
    ((1/10^5) * ((mW 12832 : ℝ)*25664*((mW 12832 : ℝ)+25664+1)))^2 +
  8*(mW 12832 : ℝ)*25664*(25664+2)*(25664+3) /
    ((1/1000)*((mW 12832 : ℝ)*25664*(25664+2)))^2 +
  covarianceVarianceBound 25664 (mW 12832) /
    ((1/1000)*covarianceMeanBound 25664 (mW 12832))^2 +
  normVarianceBound 25664 (mW 12832) / (3*inputVarianceMean 25664 (mW 12832))^2

end BstLean.Part268.WorldRow12832
namespace BstLean.Part268.WorldRow12833
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12833 = 239413524399987 := by
  have hu : mW 12833 ≤ 239413524399987 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12833 ≤ 239413524399986 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12833)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25666 ^ 2)
    ((25000000000000000000/4031605852351781662928551))
    ((5000000000000000000/806289754543820434650759)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25666) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25666 : ℝ)^2 / (mW 12833 : ℝ)) * (1 + 1/10^6)^2 *
    √(((251923/125000000000))/2) * ((1-firstRatio 25666) * √(1-firstRatio 25666) *
      sixthConstant (e1CovarianceRatio 25666 (mW 12833) (1/10^6) rowEps))) /
    (712/10000 - 25666*(1+1/10^6)*((251923/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25666 (mW 12833) /
    ((1/10^5) * ((mW 12833 : ℝ)*25666*((mW 12833 : ℝ)+25666+1)))^2 +
  8*(mW 12833 : ℝ)*25666*(25666+2)*(25666+3) /
    ((1/1000)*((mW 12833 : ℝ)*25666*(25666+2)))^2 +
  covarianceVarianceBound 25666 (mW 12833) /
    ((1/1000)*covarianceMeanBound 25666 (mW 12833))^2 +
  normVarianceBound 25666 (mW 12833) / (3*inputVarianceMean 25666 (mW 12833))^2

end BstLean.Part268.WorldRow12833
namespace BstLean.Part268.WorldRow12834
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12834 = 239478827054000 := by
  have hu : mW 12834 ≤ 239478827054000 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12834 ≤ 239478827053999 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12834)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25668 ^ 2)
    ((12500000000000000000/2015960005808570321126199))
    ((25000000000000000000/4031762931984461152577641)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25668) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25668 : ℝ)^2 / (mW 12834 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1007613/500000000000))/2) * ((1-firstRatio 25668) * √(1-firstRatio 25668) *
      sixthConstant (e1CovarianceRatio 25668 (mW 12834) (1/10^6) rowEps))) /
    (712/10000 - 25668*(1+1/10^6)*((1007613/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25668 (mW 12834) /
    ((1/10^5) * ((mW 12834 : ℝ)*25668*((mW 12834 : ℝ)+25668+1)))^2 +
  8*(mW 12834 : ℝ)*25668*(25668+2)*(25668+3) /
    ((1/1000)*((mW 12834 : ℝ)*25668*(25668+2)))^2 +
  covarianceVarianceBound 25668 (mW 12834) /
    ((1/1000)*covarianceMeanBound 25668 (mW 12834))^2 +
  normVarianceBound 25668 (mW 12834) / (3*inputVarianceMean 25668 (mW 12834))^2

end BstLean.Part268.WorldRow12834
namespace BstLean.Part268.WorldRow12835
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12835 = 239544142429887 := by
  have hu : mW 12835 ≤ 239544142429887 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12835 ≤ 239544142429886 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12835)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25670 ^ 2)
    ((5000000000000000000/806446834176499924315249))
    ((25000000000000000000/4032077091249820131901487)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25670) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25670 : ℝ)^2 / (mW 12835 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2015067/1000000000000))/2) * ((1-firstRatio 25670) * √(1-firstRatio 25670) *
      sixthConstant (e1CovarianceRatio 25670 (mW 12835) (1/10^6) rowEps))) /
    (712/10000 - 25670*(1+1/10^6)*((2015067/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25670 (mW 12835) /
    ((1/10^5) * ((mW 12835 : ℝ)*25670*((mW 12835 : ℝ)+25670+1)))^2 +
  8*(mW 12835 : ℝ)*25670*(25670+2)*(25670+3) /
    ((1/1000)*((mW 12835 : ℝ)*25670*(25670+2)))^2 +
  covarianceVarianceBound 25670 (mW 12835) /
    ((1/1000)*covarianceMeanBound 25670 (mW 12835))^2 +
  normVarianceBound 25670 (mW 12835) / (3*inputVarianceMean 25670 (mW 12835))^2

end BstLean.Part268.WorldRow12835
namespace BstLean.Part268.WorldRow12836
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12836 = 239609470529136 := by
  have hu : mW 12836 ≤ 239609470529136 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12836 ≤ 239609470529135 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12836)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25672 ^ 2)
    ((6250000000000000000/1008137082536964650225023))
    ((25000000000000000000/4032391250515179111225333)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25672) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25672 : ℝ)^2 / (mW 12836 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2014909/1000000000000))/2) * ((1-firstRatio 25672) * √(1-firstRatio 25672) *
      sixthConstant (e1CovarianceRatio 25672 (mW 12836) (1/10^6) rowEps))) /
    (712/10000 - 25672*(1+1/10^6)*((2014909/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25672 (mW 12836) /
    ((1/10^5) * ((mW 12836 : ℝ)*25672*((mW 12836 : ℝ)+25672+1)))^2 +
  8*(mW 12836 : ℝ)*25672*(25672+2)*(25672+3) /
    ((1/1000)*((mW 12836 : ℝ)*25672*(25672+2)))^2 +
  covarianceVarianceBound 25672 (mW 12836) /
    ((1/1000)*covarianceMeanBound 25672 (mW 12836))^2 +
  normVarianceBound 25672 (mW 12836) / (3*inputVarianceMean 25672 (mW 12836))^2

end BstLean.Part268.WorldRow12836
namespace BstLean.Part268.WorldRow12837
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12837 = 239674811353233 := by
  have hu : mW 12837 ≤ 239674811353233 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12837 ≤ 239674811353232 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12837)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25674 ^ 2)
    ((25000000000000000000/4032862489413217580223939))
    ((25000000000000000000/4032705409780538090549179)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25674) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25674 : ℝ)^2 / (mW 12837 : ℝ)) * (1 + 1/10^6)^2 *
    √(((8059/4000000000))/2) * ((1-firstRatio 25674) * √(1-firstRatio 25674) *
      sixthConstant (e1CovarianceRatio 25674 (mW 12837) (1/10^6) rowEps))) /
    (712/10000 - 25674*(1+1/10^6)*((8059/4000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25674 (mW 12837) /
    ((1/10^5) * ((mW 12837 : ℝ)*25674*((mW 12837 : ℝ)+25674+1)))^2 +
  8*(mW 12837 : ℝ)*25674*(25674+2)*(25674+3) /
    ((1/1000)*((mW 12837 : ℝ)*25674*(25674+2)))^2 +
  covarianceVarianceBound 25674 (mW 12837) /
    ((1/1000)*covarianceMeanBound 25674 (mW 12837))^2 +
  normVarianceBound 25674 (mW 12837) / (3*inputVarianceMean 25674 (mW 12837))^2

end BstLean.Part268.WorldRow12837
namespace BstLean.Part268.WorldRow12838
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12838 = 239740164903665 := by
  have hu : mW 12838 ≤ 239740164903665 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12838 ≤ 239740164903664 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12838)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25676 ^ 2)
    ((12500000000000000000/2016588324339288279773893))
    ((1000000000000000000/161320782761835882794921)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25676) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25676 : ℝ)^2 / (mW 12838 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2014591/1000000000000))/2) * ((1-firstRatio 25676) * √(1-firstRatio 25676) *
      sixthConstant (e1CovarianceRatio 25676 (mW 12838) (1/10^6) rowEps))) /
    (712/10000 - 25676*(1+1/10^6)*((2014591/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25676 (mW 12838) /
    ((1/10^5) * ((mW 12838 : ℝ)*25676*((mW 12838 : ℝ)+25676+1)))^2 +
  8*(mW 12838 : ℝ)*25676*(25676+2)*(25676+3) /
    ((1/1000)*((mW 12838 : ℝ)*25676*(25676+2)))^2 +
  covarianceVarianceBound 25676 (mW 12838) /
    ((1/1000)*covarianceMeanBound 25676 (mW 12838))^2 +
  normVarianceBound 25676 (mW 12838) / (3*inputVarianceMean 25676 (mW 12838))^2

end BstLean.Part268.WorldRow12838
namespace BstLean.Part268.WorldRow12839
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12839 = 239805531181920 := by
  have hu : mW 12839 ≤ 239805531181920 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12839 ≤ 239805531181919 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12839)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25678 ^ 2)
    ((25000000000000000000/4033490807943935538871633))
    ((25000000000000000000/4033333728311256049196871)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25678) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25678 : ℝ)^2 / (mW 12839 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2014433/1000000000000))/2) * ((1-firstRatio 25678) * √(1-firstRatio 25678) *
      sixthConstant (e1CovarianceRatio 25678 (mW 12839) (1/10^6) rowEps))) /
    (712/10000 - 25678*(1+1/10^6)*((2014433/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25678 (mW 12839) /
    ((1/10^5) * ((mW 12839 : ℝ)*25678*((mW 12839 : ℝ)+25678+1)))^2 +
  8*(mW 12839 : ℝ)*25678*(25678+2)*(25678+3) /
    ((1/1000)*((mW 12839 : ℝ)*25678*(25678+2)))^2 +
  covarianceVarianceBound 25678 (mW 12839) /
    ((1/1000)*covarianceMeanBound 25678 (mW 12839))^2 +
  normVarianceBound 25678 (mW 12839) / (3*inputVarianceMean 25678 (mW 12839))^2

end BstLean.Part268.WorldRow12839
namespace BstLean.Part268.WorldRow12840
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12840 = 239870910189485 := by
  have hu : mW 12840 ≤ 239870910189485 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12840 ≤ 239870910189484 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12840)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25680 ^ 2)
    ((625000000000000000/100845124180232362954887))
    ((25000000000000000000/4033647887576615028520717)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25680) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25680 : ℝ)^2 / (mW 12840 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1007137/500000000000))/2) * ((1-firstRatio 25680) * √(1-firstRatio 25680) *
      sixthConstant (e1CovarianceRatio 25680 (mW 12840) (1/10^6) rowEps))) /
    (712/10000 - 25680*(1+1/10^6)*((1007137/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25680 (mW 12840) /
    ((1/10^5) * ((mW 12840 : ℝ)*25680*((mW 12840 : ℝ)+25680+1)))^2 +
  8*(mW 12840 : ℝ)*25680*(25680+2)*(25680+3) /
    ((1/1000)*((mW 12840 : ℝ)*25680*(25680+2)))^2 +
  covarianceVarianceBound 25680 (mW 12840) /
    ((1/1000)*covarianceMeanBound 25680 (mW 12840))^2 +
  normVarianceBound 25680 (mW 12840) / (3*inputVarianceMean 25680 (mW 12840))^2

end BstLean.Part268.WorldRow12840
namespace BstLean.Part268.WorldRow12841
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12841 = 239936301927846 := by
  have hu : mW 12841 ≤ 239936301927846 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12841 ≤ 239936301927845 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12841)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25682 ^ 2)
    ((25000000000000000000/4034119126474653497519327))
    ((25000000000000000000/4033962046841974007844563)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25682) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25682 : ℝ)^2 / (mW 12841 : ℝ)) * (1 + 1/10^6)^2 *
    √(((503529/250000000000))/2) * ((1-firstRatio 25682) * √(1-firstRatio 25682) *
      sixthConstant (e1CovarianceRatio 25682 (mW 12841) (1/10^6) rowEps))) /
    (712/10000 - 25682*(1+1/10^6)*((503529/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25682 (mW 12841) /
    ((1/10^5) * ((mW 12841 : ℝ)*25682*((mW 12841 : ℝ)+25682+1)))^2 +
  8*(mW 12841 : ℝ)*25682*(25682+2)*(25682+3) /
    ((1/1000)*((mW 12841 : ℝ)*25682*(25682+2)))^2 +
  covarianceVarianceBound 25682 (mW 12841) /
    ((1/1000)*covarianceMeanBound 25682 (mW 12841))^2 +
  normVarianceBound 25682 (mW 12841) / (3*inputVarianceMean 25682 (mW 12841))^2

end BstLean.Part268.WorldRow12841
namespace BstLean.Part268.WorldRow12842
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12842 = 240001706398492 := by
  have hu : mW 12842 ≤ 240001706398492 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12842 ≤ 240001706398491 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12842)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25684 ^ 2)
    ((12500000000000000000/2017216642870006238421587))
    ((25000000000000000000/4034276206107332987168409)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25684) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25684 : ℝ)^2 / (mW 12842 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1006979/500000000000))/2) * ((1-firstRatio 25684) * √(1-firstRatio 25684) *
      sixthConstant (e1CovarianceRatio 25684 (mW 12842) (1/10^6) rowEps))) /
    (712/10000 - 25684*(1+1/10^6)*((1006979/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25684 (mW 12842) /
    ((1/10^5) * ((mW 12842 : ℝ)*25684*((mW 12842 : ℝ)+25684+1)))^2 +
  8*(mW 12842 : ℝ)*25684*(25684+2)*(25684+3) /
    ((1/1000)*((mW 12842 : ℝ)*25684*(25684+2)))^2 +
  covarianceVarianceBound 25684 (mW 12842) /
    ((1/1000)*covarianceMeanBound 25684 (mW 12842))^2 +
  normVarianceBound 25684 (mW 12842) / (3*inputVarianceMean 25684 (mW 12842))^2

end BstLean.Part268.WorldRow12842
namespace BstLean.Part268.WorldRow12843
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12843 = 240067123602909 := by
  have hu : mW 12843 ≤ 240067123602909 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12843 ≤ 240067123602908 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12843)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25686 ^ 2)
    ((25000000000000000000/4034747445005371456167021))
    ((5000000000000000000/806918073074538393298451)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25686) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25686 : ℝ)^2 / (mW 12843 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2013799/1000000000000))/2) * ((1-firstRatio 25686) * √(1-firstRatio 25686) *
      sixthConstant (e1CovarianceRatio 25686 (mW 12843) (1/10^6) rowEps))) /
    (712/10000 - 25686*(1+1/10^6)*((2013799/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25686 (mW 12843) /
    ((1/10^5) * ((mW 12843 : ℝ)*25686*((mW 12843 : ℝ)+25686+1)))^2 +
  8*(mW 12843 : ℝ)*25686*(25686+2)*(25686+3) /
    ((1/1000)*((mW 12843 : ℝ)*25686*(25686+2)))^2 +
  covarianceVarianceBound 25686 (mW 12843) /
    ((1/1000)*covarianceMeanBound 25686 (mW 12843))^2 +
  normVarianceBound 25686 (mW 12843) / (3*inputVarianceMean 25686 (mW 12843))^2

end BstLean.Part268.WorldRow12843
namespace BstLean.Part268.WorldRow12844
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12844 = 240132553542585 := by
  have hu : mW 12844 ≤ 240132553542585 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12844 ≤ 240132553542584 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12844)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25688 ^ 2)
    ((6250000000000000000/1008765401067682608872717))
    ((25000000000000000000/4034904524638050945816101)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25688) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25688 : ℝ)^2 / (mW 12844 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2013641/1000000000000))/2) * ((1-firstRatio 25688) * √(1-firstRatio 25688) *
      sixthConstant (e1CovarianceRatio 25688 (mW 12844) (1/10^6) rowEps))) /
    (712/10000 - 25688*(1+1/10^6)*((2013641/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25688 (mW 12844) /
    ((1/10^5) * ((mW 12844 : ℝ)*25688*((mW 12844 : ℝ)+25688+1)))^2 +
  8*(mW 12844 : ℝ)*25688*(25688+2)*(25688+3) /
    ((1/1000)*((mW 12844 : ℝ)*25688*(25688+2)))^2 +
  covarianceVarianceBound 25688 (mW 12844) /
    ((1/1000)*covarianceMeanBound 25688 (mW 12844))^2 +
  normVarianceBound 25688 (mW 12844) / (3*inputVarianceMean 25688 (mW 12844))^2

end BstLean.Part268.WorldRow12844
namespace BstLean.Part268.WorldRow12845
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12845 = 240197996219007 := by
  have hu : mW 12845 ≤ 240197996219007 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12845 ≤ 240197996219006 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12845)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25690 ^ 2)
    ((5000000000000000000/807075152707217882962943))
    ((25000000000000000000/4035218683903409925139947)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25690) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25690 : ℝ)^2 / (mW 12845 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1006741/500000000000))/2) * ((1-firstRatio 25690) * √(1-firstRatio 25690) *
      sixthConstant (e1CovarianceRatio 25690 (mW 12845) (1/10^6) rowEps))) /
    (712/10000 - 25690*(1+1/10^6)*((1006741/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25690 (mW 12845) /
    ((1/10^5) * ((mW 12845 : ℝ)*25690*((mW 12845 : ℝ)+25690+1)))^2 +
  8*(mW 12845 : ℝ)*25690*(25690+2)*(25690+3) /
    ((1/1000)*((mW 12845 : ℝ)*25690*(25690+2)))^2 +
  covarianceVarianceBound 25690 (mW 12845) /
    ((1/1000)*covarianceMeanBound 25690 (mW 12845))^2 +
  normVarianceBound 25690 (mW 12845) / (3*inputVarianceMean 25690 (mW 12845))^2

end BstLean.Part268.WorldRow12845
namespace BstLean.Part268.WorldRow12846
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12846 = 240263451633663 := by
  have hu : mW 12846 ≤ 240263451633663 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12846 ≤ 240263451633662 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12846)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25692 ^ 2)
    ((12500000000000000000/2017844961400724197069281))
    ((25000000000000000000/4035532843168768904463793)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25692) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25692 : ℝ)^2 / (mW 12846 : ℝ)) * (1 + 1/10^6)^2 *
    √(((503331/250000000000))/2) * ((1-firstRatio 25692) * √(1-firstRatio 25692) *
      sixthConstant (e1CovarianceRatio 25692 (mW 12846) (1/10^6) rowEps))) /
    (712/10000 - 25692*(1+1/10^6)*((503331/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25692 (mW 12846) /
    ((1/10^5) * ((mW 12846 : ℝ)*25692*((mW 12846 : ℝ)+25692+1)))^2 +
  8*(mW 12846 : ℝ)*25692*(25692+2)*(25692+3) /
    ((1/1000)*((mW 12846 : ℝ)*25692*(25692+2)))^2 +
  covarianceVarianceBound 25692 (mW 12846) /
    ((1/1000)*covarianceMeanBound 25692 (mW 12846))^2 +
  normVarianceBound 25692 (mW 12846) / (3*inputVarianceMean 25692 (mW 12846))^2

end BstLean.Part268.WorldRow12846
namespace BstLean.Part268.WorldRow12847
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12847 = 240328919788041 := by
  have hu : mW 12847 ≤ 240328919788041 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12847 ≤ 240328919788040 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12847)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25694 ^ 2)
    ((25000000000000000000/4036004082066807373462409))
    ((25000000000000000000/4035847002434127883787639)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25694) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25694 : ℝ)^2 / (mW 12847 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1006583/500000000000))/2) * ((1-firstRatio 25694) * √(1-firstRatio 25694) *
      sixthConstant (e1CovarianceRatio 25694 (mW 12847) (1/10^6) rowEps))) /
    (712/10000 - 25694*(1+1/10^6)*((1006583/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25694 (mW 12847) /
    ((1/10^5) * ((mW 12847 : ℝ)*25694*((mW 12847 : ℝ)+25694+1)))^2 +
  8*(mW 12847 : ℝ)*25694*(25694+2)*(25694+3) /
    ((1/1000)*((mW 12847 : ℝ)*25694*(25694+2)))^2 +
  covarianceVarianceBound 25694 (mW 12847) /
    ((1/1000)*covarianceMeanBound 25694 (mW 12847))^2 +
  normVarianceBound 25694 (mW 12847) / (3*inputVarianceMean 25694 (mW 12847))^2

end BstLean.Part268.WorldRow12847
namespace BstLean.Part268.WorldRow12848
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12848 = 240394400683627 := by
  have hu : mW 12848 ≤ 240394400683627 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12848 ≤ 240394400683626 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12848)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25696 ^ 2)
    ((1562500000000000000/252269890083260397049141))
    ((5000000000000000000/807232232339897372622297)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25696) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25696 : ℝ)^2 / (mW 12848 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2013007/1000000000000))/2) * ((1-firstRatio 25696) * √(1-firstRatio 25696) *
      sixthConstant (e1CovarianceRatio 25696 (mW 12848) (1/10^6) rowEps))) /
    (712/10000 - 25696*(1+1/10^6)*((2013007/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25696 (mW 12848) /
    ((1/10^5) * ((mW 12848 : ℝ)*25696*((mW 12848 : ℝ)+25696+1)))^2 +
  8*(mW 12848 : ℝ)*25696*(25696+2)*(25696+3) /
    ((1/1000)*((mW 12848 : ℝ)*25696*(25696+2)))^2 +
  covarianceVarianceBound 25696 (mW 12848) /
    ((1/1000)*covarianceMeanBound 25696 (mW 12848))^2 +
  normVarianceBound 25696 (mW 12848) / (3*inputVarianceMean 25696 (mW 12848))^2

end BstLean.Part268.WorldRow12848
namespace BstLean.Part268.WorldRow12849
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12849 = 240459894321911 := by
  have hu : mW 12849 ≤ 240459894321911 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12849 ≤ 240459894321910 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12849)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25698 ^ 2)
    ((25000000000000000000/4036632400597525332110103))
    ((25000000000000000000/4036475320964845842435331)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25698) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25698 : ℝ)^2 / (mW 12849 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2012849/1000000000000))/2) * ((1-firstRatio 25698) * √(1-firstRatio 25698) *
      sixthConstant (e1CovarianceRatio 25698 (mW 12849) (1/10^6) rowEps))) /
    (712/10000 - 25698*(1+1/10^6)*((2012849/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25698 (mW 12849) /
    ((1/10^5) * ((mW 12849 : ℝ)*25698*((mW 12849 : ℝ)+25698+1)))^2 +
  8*(mW 12849 : ℝ)*25698*(25698+2)*(25698+3) /
    ((1/1000)*((mW 12849 : ℝ)*25698*(25698+2)))^2 +
  covarianceVarianceBound 25698 (mW 12849) /
    ((1/1000)*covarianceMeanBound 25698 (mW 12849))^2 +
  normVarianceBound 25698 (mW 12849) / (3*inputVarianceMean 25698 (mW 12849))^2

end BstLean.Part268.WorldRow12849
