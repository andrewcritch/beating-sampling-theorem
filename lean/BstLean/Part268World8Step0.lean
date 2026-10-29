import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar8
namespace BstLean.Part268.WorldRow12550
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12550 = 221438453823164 := by
  have hu : mW 12550 ≤ 221438453823164 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12550 ≤ 221438453823163 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12550)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25100 ^ 2)
    ((500000000000000000/78853975605103810285597))
    ((25000000000000000000/3942541700622511024605377)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25100) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25100 : ℝ)^2 / (mW 12550 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2013/976562500))/2) * ((1-firstRatio 25100) * √(1-firstRatio 25100) *
      sixthConstant (e1CovarianceRatio 25100 (mW 12550) (1/10^6) rowEps))) /
    (712/10000 - 25100*(1+1/10^6)*((2013/976562500)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25100 (mW 12550) /
    ((1/10^5) * ((mW 12550 : ℝ)*25100*((mW 12550 : ℝ)+25100+1)))^2 +
  8*(mW 12550 : ℝ)*25100*(25100+2)*(25100+3) /
    ((1/1000)*((mW 12550 : ℝ)*25100*(25100+2)))^2 +
  covarianceVarianceBound 25100 (mW 12550) /
    ((1/1000)*covarianceMeanBound 25100 (mW 12550))^2 +
  normVarianceBound 25100 (mW 12550) / (3*inputVarianceMean 25100 (mW 12550))^2

end BstLean.Part268.WorldRow12550
namespace BstLean.Part268.WorldRow12551
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12551 = 221500215718473 := by
  have hu : mW 12551 ≤ 221500215718473 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12551 ≤ 221500215718472 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12551)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25102 ^ 2)
    ((25000000000000000000/3943012939520549493603697))
    ((25000000000000000000/3942855859887870003929223)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25102) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25102 : ℝ)^2 / (mW 12551 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1030573/500000000000))/2) * ((1-firstRatio 25102) * √(1-firstRatio 25102) *
      sixthConstant (e1CovarianceRatio 25102 (mW 12551) (1/10^6) rowEps))) /
    (712/10000 - 25102*(1+1/10^6)*((1030573/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25102 (mW 12551) /
    ((1/10^5) * ((mW 12551 : ℝ)*25102*((mW 12551 : ℝ)+25102+1)))^2 +
  8*(mW 12551 : ℝ)*25102*(25102+2)*(25102+3) /
    ((1/1000)*((mW 12551 : ℝ)*25102*(25102+2)))^2 +
  covarianceVarianceBound 25102 (mW 12551) /
    ((1/1000)*covarianceMeanBound 25102 (mW 12551))^2 +
  normVarianceBound 25102 (mW 12551) / (3*inputVarianceMean 25102 (mW 12551))^2

end BstLean.Part268.WorldRow12551
namespace BstLean.Part268.WorldRow12552
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12552 = 221561989917194 := by
  have hu : mW 12552 ≤ 221561989917194 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12552 ≤ 221561989917193 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12552)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25104 ^ 2)
    ((3125000000000000000/492915887348238559115943))
    ((25000000000000000000/3943170019153228983253069)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25104) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25104 : ℝ)^2 / (mW 12552 : ℝ)) * (1 + 1/10^6)^2 *
    √(((103049/50000000000))/2) * ((1-firstRatio 25104) * √(1-firstRatio 25104) *
      sixthConstant (e1CovarianceRatio 25104 (mW 12552) (1/10^6) rowEps))) /
    (712/10000 - 25104*(1+1/10^6)*((103049/50000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25104 (mW 12552) /
    ((1/10^5) * ((mW 12552 : ℝ)*25104*((mW 12552 : ℝ)+25104+1)))^2 +
  8*(mW 12552 : ℝ)*25104*(25104+2)*(25104+3) /
    ((1/1000)*((mW 12552 : ℝ)*25104*(25104+2)))^2 +
  covarianceVarianceBound 25104 (mW 12552) /
    ((1/1000)*covarianceMeanBound 25104 (mW 12552))^2 +
  normVarianceBound 25104 (mW 12552) / (3*inputVarianceMean 25104 (mW 12552))^2

end BstLean.Part268.WorldRow12552
namespace BstLean.Part268.WorldRow12553
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12553 = 221623776420798 := by
  have hu : mW 12553 ≤ 221623776420798 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12553 ≤ 221623776420797 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12553)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25106 ^ 2)
    ((25000000000000000000/3943641258051267452251391))
    ((5000000000000000000/788696835683717592515383)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25106) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25106 : ℝ)^2 / (mW 12553 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1030407/500000000000))/2) * ((1-firstRatio 25106) * √(1-firstRatio 25106) *
      sixthConstant (e1CovarianceRatio 25106 (mW 12553) (1/10^6) rowEps))) /
    (712/10000 - 25106*(1+1/10^6)*((1030407/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25106 (mW 12553) /
    ((1/10^5) * ((mW 12553 : ℝ)*25106*((mW 12553 : ℝ)+25106+1)))^2 +
  8*(mW 12553 : ℝ)*25106*(25106+2)*(25106+3) /
    ((1/1000)*((mW 12553 : ℝ)*25106*(25106+2)))^2 +
  covarianceVarianceBound 25106 (mW 12553) /
    ((1/1000)*covarianceMeanBound 25106 (mW 12553))^2 +
  normVarianceBound 25106 (mW 12553) / (3*inputVarianceMean 25106 (mW 12553))^2

end BstLean.Part268.WorldRow12553
namespace BstLean.Part268.WorldRow12554
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12554 = 221685575230753 := by
  have hu : mW 12554 ≤ 221685575230753 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12554 ≤ 221685575230752 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12554)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25108 ^ 2)
    ((12500000000000000000/1971977708658313215787619))
    ((25000000000000000000/3943798337683946941900761)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25108) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25108 : ℝ)^2 / (mW 12554 : ℝ)) * (1 + 1/10^6)^2 *
    √(((257581/125000000000))/2) * ((1-firstRatio 25108) * √(1-firstRatio 25108) *
      sixthConstant (e1CovarianceRatio 25108 (mW 12554) (1/10^6) rowEps))) /
    (712/10000 - 25108*(1+1/10^6)*((257581/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25108 (mW 12554) /
    ((1/10^5) * ((mW 12554 : ℝ)*25108*((mW 12554 : ℝ)+25108+1)))^2 +
  8*(mW 12554 : ℝ)*25108*(25108+2)*(25108+3) /
    ((1/1000)*((mW 12554 : ℝ)*25108*(25108+2)))^2 +
  covarianceVarianceBound 25108 (mW 12554) /
    ((1/1000)*covarianceMeanBound 25108 (mW 12554))^2 +
  normVarianceBound 25108 (mW 12554) / (3*inputVarianceMean 25108 (mW 12554))^2

end BstLean.Part268.WorldRow12554
namespace BstLean.Part268.WorldRow12555
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12555 = 221747386348531 := by
  have hu : mW 12555 ≤ 221747386348531 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12555 ≤ 221747386348530 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12555)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25110 ^ 2)
    ((5000000000000000000/788853915316397082179817))
    ((25000000000000000000/3944112496949305921224607)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25110) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25110 : ℝ)^2 / (mW 12555 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1030241/500000000000))/2) * ((1-firstRatio 25110) * √(1-firstRatio 25110) *
      sixthConstant (e1CovarianceRatio 25110 (mW 12555) (1/10^6) rowEps))) /
    (712/10000 - 25110*(1+1/10^6)*((1030241/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25110 (mW 12555) /
    ((1/10^5) * ((mW 12555 : ℝ)*25110*((mW 12555 : ℝ)+25110+1)))^2 +
  8*(mW 12555 : ℝ)*25110*(25110+2)*(25110+3) /
    ((1/1000)*((mW 12555 : ℝ)*25110*(25110+2)))^2 +
  covarianceVarianceBound 25110 (mW 12555) /
    ((1/1000)*covarianceMeanBound 25110 (mW 12555))^2 +
  normVarianceBound 25110 (mW 12555) / (3*inputVarianceMean 25110 (mW 12555))^2

end BstLean.Part268.WorldRow12555
namespace BstLean.Part268.WorldRow12556
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12556 = 221809209775603 := by
  have hu : mW 12556 ≤ 221809209775603 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12556 ≤ 221809209775602 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12556)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25112 ^ 2)
    ((6250000000000000000/986145933961836097555733))
    ((25000000000000000000/3944426656214664900548453)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25112) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25112 : ℝ)^2 / (mW 12556 : ℝ)) * (1 + 1/10^6)^2 *
    √(((515079/250000000000))/2) * ((1-firstRatio 25112) * √(1-firstRatio 25112) *
      sixthConstant (e1CovarianceRatio 25112 (mW 12556) (1/10^6) rowEps))) /
    (712/10000 - 25112*(1+1/10^6)*((515079/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25112 (mW 12556) /
    ((1/10^5) * ((mW 12556 : ℝ)*25112*((mW 12556 : ℝ)+25112+1)))^2 +
  8*(mW 12556 : ℝ)*25112*(25112+2)*(25112+3) /
    ((1/1000)*((mW 12556 : ℝ)*25112*(25112+2)))^2 +
  covarianceVarianceBound 25112 (mW 12556) /
    ((1/1000)*covarianceMeanBound 25112 (mW 12556))^2 +
  normVarianceBound 25112 (mW 12556) / (3*inputVarianceMean 25112 (mW 12556))^2

end BstLean.Part268.WorldRow12556
namespace BstLean.Part268.WorldRow12557
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12557 = 221871045513439 := by
  have hu : mW 12557 ≤ 221871045513439 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12557 ≤ 221871045513438 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12557)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25114 ^ 2)
    ((25000000000000000000/3944897895112703369546779))
    ((25000000000000000000/3944740815480023879872299)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25114) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25114 : ℝ)^2 / (mW 12557 : ℝ)) * (1 + 1/10^6)^2 *
    √(((41203/20000000000))/2) * ((1-firstRatio 25114) * √(1-firstRatio 25114) *
      sixthConstant (e1CovarianceRatio 25114 (mW 12557) (1/10^6) rowEps))) /
    (712/10000 - 25114*(1+1/10^6)*((41203/20000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25114 (mW 12557) /
    ((1/10^5) * ((mW 12557 : ℝ)*25114*((mW 12557 : ℝ)+25114+1)))^2 +
  8*(mW 12557 : ℝ)*25114*(25114+2)*(25114+3) /
    ((1/1000)*((mW 12557 : ℝ)*25114*(25114+2)))^2 +
  covarianceVarianceBound 25114 (mW 12557) /
    ((1/1000)*covarianceMeanBound 25114 (mW 12557))^2 +
  normVarianceBound 25114 (mW 12557) / (3*inputVarianceMean 25114 (mW 12557))^2

end BstLean.Part268.WorldRow12557
namespace BstLean.Part268.WorldRow12558
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12558 = 221932893563510 := by
  have hu : mW 12558 ≤ 221932893563510 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12558 ≤ 221932893563509 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12558)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25116 ^ 2)
    ((12500000000000000000/1972606027189031174435313))
    ((5000000000000000000/789010994949076571839229)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25116) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25116 : ℝ)^2 / (mW 12558 : ℝ)) * (1 + 1/10^6)^2 *
    √(((128749/62500000000))/2) * ((1-firstRatio 25116) * √(1-firstRatio 25116) *
      sixthConstant (e1CovarianceRatio 25116 (mW 12558) (1/10^6) rowEps))) /
    (712/10000 - 25116*(1+1/10^6)*((128749/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25116 (mW 12558) /
    ((1/10^5) * ((mW 12558 : ℝ)*25116*((mW 12558 : ℝ)+25116+1)))^2 +
  8*(mW 12558 : ℝ)*25116*(25116+2)*(25116+3) /
    ((1/1000)*((mW 12558 : ℝ)*25116*(25116+2)))^2 +
  covarianceVarianceBound 25116 (mW 12558) /
    ((1/1000)*covarianceMeanBound 25116 (mW 12558))^2 +
  normVarianceBound 25116 (mW 12558) / (3*inputVarianceMean 25116 (mW 12558))^2

end BstLean.Part268.WorldRow12558
namespace BstLean.Part268.WorldRow12559
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12559 = 221994753927287 := by
  have hu : mW 12559 ≤ 221994753927287 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12559 ≤ 221994753927286 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12559)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25118 ^ 2)
    ((25000000000000000000/3945526213643421328194473))
    ((25000000000000000000/3945369134010741838519991)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25118) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25118 : ℝ)^2 / (mW 12559 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2059819/1000000000000))/2) * ((1-firstRatio 25118) * √(1-firstRatio 25118) *
      sixthConstant (e1CovarianceRatio 25118 (mW 12559) (1/10^6) rowEps))) /
    (712/10000 - 25118*(1+1/10^6)*((2059819/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25118 (mW 12559) /
    ((1/10^5) * ((mW 12559 : ℝ)*25118*((mW 12559 : ℝ)+25118+1)))^2 +
  8*(mW 12559 : ℝ)*25118*(25118+2)*(25118+3) /
    ((1/1000)*((mW 12559 : ℝ)*25118*(25118+2)))^2 +
  covarianceVarianceBound 25118 (mW 12559) /
    ((1/1000)*covarianceMeanBound 25118 (mW 12559))^2 +
  normVarianceBound 25118 (mW 12559) / (3*inputVarianceMean 25118 (mW 12559))^2

end BstLean.Part268.WorldRow12559
namespace BstLean.Part268.WorldRow12560
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12560 = 222056626606240 := by
  have hu : mW 12560 ≤ 222056626606240 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12560 ≤ 222056626606239 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12560)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25120 ^ 2)
    ((312500000000000000/49323004661359753843979))
    ((25000000000000000000/3945683293276100817843837)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25120) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25120 : ℝ)^2 / (mW 12560 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2059653/1000000000000))/2) * ((1-firstRatio 25120) * √(1-firstRatio 25120) *
      sixthConstant (e1CovarianceRatio 25120 (mW 12560) (1/10^6) rowEps))) /
    (712/10000 - 25120*(1+1/10^6)*((2059653/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25120 (mW 12560) /
    ((1/10^5) * ((mW 12560 : ℝ)*25120*((mW 12560 : ℝ)+25120+1)))^2 +
  8*(mW 12560 : ℝ)*25120*(25120+2)*(25120+3) /
    ((1/1000)*((mW 12560 : ℝ)*25120*(25120+2)))^2 +
  covarianceVarianceBound 25120 (mW 12560) /
    ((1/1000)*covarianceMeanBound 25120 (mW 12560))^2 +
  normVarianceBound 25120 (mW 12560) / (3*inputVarianceMean 25120 (mW 12560))^2

end BstLean.Part268.WorldRow12560
namespace BstLean.Part268.WorldRow12561
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12561 = 222118511601841 := by
  have hu : mW 12561 ≤ 222118511601841 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12561 ≤ 222118511601840 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12561)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25122 ^ 2)
    ((25000000000000000000/3946154532174139286842167))
    ((25000000000000000000/3945997452541459797167683)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25122) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25122 : ℝ)^2 / (mW 12561 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2059487/1000000000000))/2) * ((1-firstRatio 25122) * √(1-firstRatio 25122) *
      sixthConstant (e1CovarianceRatio 25122 (mW 12561) (1/10^6) rowEps))) /
    (712/10000 - 25122*(1+1/10^6)*((2059487/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25122 (mW 12561) /
    ((1/10^5) * ((mW 12561 : ℝ)*25122*((mW 12561 : ℝ)+25122+1)))^2 +
  8*(mW 12561 : ℝ)*25122*(25122+2)*(25122+3) /
    ((1/1000)*((mW 12561 : ℝ)*25122*(25122+2)))^2 +
  covarianceVarianceBound 25122 (mW 12561) /
    ((1/1000)*covarianceMeanBound 25122 (mW 12561))^2 +
  normVarianceBound 25122 (mW 12561) / (3*inputVarianceMean 25122 (mW 12561))^2

end BstLean.Part268.WorldRow12561
namespace BstLean.Part268.WorldRow12562
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12562 = 222180408915561 := by
  have hu : mW 12562 ≤ 222180408915561 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12562 ≤ 222180408915560 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12562)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25124 ^ 2)
    ((12500000000000000000/1973234345719749133083007))
    ((25000000000000000000/3946311611806818776491529)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25124) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25124 : ℝ)^2 / (mW 12562 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1029661/500000000000))/2) * ((1-firstRatio 25124) * √(1-firstRatio 25124) *
      sixthConstant (e1CovarianceRatio 25124 (mW 12562) (1/10^6) rowEps))) /
    (712/10000 - 25124*(1+1/10^6)*((1029661/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25124 (mW 12562) /
    ((1/10^5) * ((mW 12562 : ℝ)*25124*((mW 12562 : ℝ)+25124+1)))^2 +
  8*(mW 12562 : ℝ)*25124*(25124+2)*(25124+3) /
    ((1/1000)*((mW 12562 : ℝ)*25124*(25124+2)))^2 +
  covarianceVarianceBound 25124 (mW 12562) /
    ((1/1000)*covarianceMeanBound 25124 (mW 12562))^2 +
  normVarianceBound 25124 (mW 12562) / (3*inputVarianceMean 25124 (mW 12562))^2

end BstLean.Part268.WorldRow12562
namespace BstLean.Part268.WorldRow12563
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12563 = 222242318548870 := by
  have hu : mW 12563 ≤ 222242318548870 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12563 ≤ 222242318548869 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12563)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25126 ^ 2)
    ((25000000000000000000/3946782850704857245489861))
    ((200000000000000000/31573006168577422046523)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25126) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25126 : ℝ)^2 / (mW 12563 : ℝ)) * (1 + 1/10^6)^2 *
    √(((514789/250000000000))/2) * ((1-firstRatio 25126) * √(1-firstRatio 25126) *
      sixthConstant (e1CovarianceRatio 25126 (mW 12563) (1/10^6) rowEps))) /
    (712/10000 - 25126*(1+1/10^6)*((514789/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25126 (mW 12563) /
    ((1/10^5) * ((mW 12563 : ℝ)*25126*((mW 12563 : ℝ)+25126+1)))^2 +
  8*(mW 12563 : ℝ)*25126*(25126+2)*(25126+3) /
    ((1/1000)*((mW 12563 : ℝ)*25126*(25126+2)))^2 +
  covarianceVarianceBound 25126 (mW 12563) /
    ((1/1000)*covarianceMeanBound 25126 (mW 12563))^2 +
  normVarianceBound 25126 (mW 12563) / (3*inputVarianceMean 25126 (mW 12563))^2

end BstLean.Part268.WorldRow12563
namespace BstLean.Part268.WorldRow12564
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12564 = 222304240503239 := by
  have hu : mW 12564 ≤ 222304240503239 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12564 ≤ 222304240503238 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12564)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25128 ^ 2)
    ((6250000000000000000/986774252492554056203427))
    ((25000000000000000000/3946939930337536735139221)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25128) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25128 : ℝ)^2 / (mW 12564 : ℝ)) * (1 + 1/10^6)^2 *
    √(((205899/100000000000))/2) * ((1-firstRatio 25128) * √(1-firstRatio 25128) *
      sixthConstant (e1CovarianceRatio 25128 (mW 12564) (1/10^6) rowEps))) /
    (712/10000 - 25128*(1+1/10^6)*((205899/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25128 (mW 12564) /
    ((1/10^5) * ((mW 12564 : ℝ)*25128*((mW 12564 : ℝ)+25128+1)))^2 +
  8*(mW 12564 : ℝ)*25128*(25128+2)*(25128+3) /
    ((1/1000)*((mW 12564 : ℝ)*25128*(25128+2)))^2 +
  covarianceVarianceBound 25128 (mW 12564) /
    ((1/1000)*covarianceMeanBound 25128 (mW 12564))^2 +
  normVarianceBound 25128 (mW 12564) / (3*inputVarianceMean 25128 (mW 12564))^2

end BstLean.Part268.WorldRow12564
namespace BstLean.Part268.WorldRow12565
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12565 = 222366174780140 := by
  have hu : mW 12565 ≤ 222366174780140 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12565 ≤ 222366174780139 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12565)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25130 ^ 2)
    ((5000000000000000000/789482233847115040827511))
    ((25000000000000000000/3947254089602895714463067)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25130) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25130 : ℝ)^2 / (mW 12565 : ℝ)) * (1 + 1/10^6)^2 *
    √(((82353/40000000000))/2) * ((1-firstRatio 25130) * √(1-firstRatio 25130) *
      sixthConstant (e1CovarianceRatio 25130 (mW 12565) (1/10^6) rowEps))) /
    (712/10000 - 25130*(1+1/10^6)*((82353/40000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25130 (mW 12565) /
    ((1/10^5) * ((mW 12565 : ℝ)*25130*((mW 12565 : ℝ)+25130+1)))^2 +
  8*(mW 12565 : ℝ)*25130*(25130+2)*(25130+3) /
    ((1/1000)*((mW 12565 : ℝ)*25130*(25130+2)))^2 +
  covarianceVarianceBound 25130 (mW 12565) /
    ((1/1000)*covarianceMeanBound 25130 (mW 12565))^2 +
  normVarianceBound 25130 (mW 12565) / (3*inputVarianceMean 25130 (mW 12565))^2

end BstLean.Part268.WorldRow12565
namespace BstLean.Part268.WorldRow12566
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12566 = 222428121381044 := by
  have hu : mW 12566 ≤ 222428121381044 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12566 ≤ 222428121381043 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12566)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25132 ^ 2)
    ((12500000000000000000/1973862664250467091730701))
    ((25000000000000000000/3947568248868254693786913)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25132) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25132 : ℝ)^2 / (mW 12566 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2058659/1000000000000))/2) * ((1-firstRatio 25132) * √(1-firstRatio 25132) *
      sixthConstant (e1CovarianceRatio 25132 (mW 12566) (1/10^6) rowEps))) /
    (712/10000 - 25132*(1+1/10^6)*((2058659/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25132 (mW 12566) /
    ((1/10^5) * ((mW 12566 : ℝ)*25132*((mW 12566 : ℝ)+25132+1)))^2 +
  8*(mW 12566 : ℝ)*25132*(25132+2)*(25132+3) /
    ((1/1000)*((mW 12566 : ℝ)*25132*(25132+2)))^2 +
  covarianceVarianceBound 25132 (mW 12566) /
    ((1/1000)*covarianceMeanBound 25132 (mW 12566))^2 +
  normVarianceBound 25132 (mW 12566) / (3*inputVarianceMean 25132 (mW 12566))^2

end BstLean.Part268.WorldRow12566
namespace BstLean.Part268.WorldRow12567
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12567 = 222490080307423 := by
  have hu : mW 12567 ≤ 222490080307423 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12567 ≤ 222490080307422 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12567)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25134 ^ 2)
    ((25000000000000000000/3948039487766293162785249))
    ((25000000000000000000/3947882408133613673110759)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25134) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25134 : ℝ)^2 / (mW 12567 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1029247/500000000000))/2) * ((1-firstRatio 25134) * √(1-firstRatio 25134) *
      sixthConstant (e1CovarianceRatio 25134 (mW 12567) (1/10^6) rowEps))) /
    (712/10000 - 25134*(1+1/10^6)*((1029247/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25134 (mW 12567) /
    ((1/10^5) * ((mW 12567 : ℝ)*25134*((mW 12567 : ℝ)+25134+1)))^2 +
  8*(mW 12567 : ℝ)*25134*(25134+2)*(25134+3) /
    ((1/1000)*((mW 12567 : ℝ)*25134*(25134+2)))^2 +
  covarianceVarianceBound 25134 (mW 12567) /
    ((1/1000)*covarianceMeanBound 25134 (mW 12567))^2 +
  normVarianceBound 25134 (mW 12567) / (3*inputVarianceMean 25134 (mW 12567))^2

end BstLean.Part268.WorldRow12567
namespace BstLean.Part268.WorldRow12568
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12568 = 222552051560746 := by
  have hu : mW 12568 ≤ 222552051560746 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12568 ≤ 222552051560745 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12568)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25136 ^ 2)
    ((3125000000000000000/493544205878956517763637))
    ((5000000000000000000/789639313479794530486921)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25136) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25136 : ℝ)^2 / (mW 12568 : ℝ)) * (1 + 1/10^6)^2 *
    √(((257291/125000000000))/2) * ((1-firstRatio 25136) * √(1-firstRatio 25136) *
      sixthConstant (e1CovarianceRatio 25136 (mW 12568) (1/10^6) rowEps))) /
    (712/10000 - 25136*(1+1/10^6)*((257291/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25136 (mW 12568) /
    ((1/10^5) * ((mW 12568 : ℝ)*25136*((mW 12568 : ℝ)+25136+1)))^2 +
  8*(mW 12568 : ℝ)*25136*(25136+2)*(25136+3) /
    ((1/1000)*((mW 12568 : ℝ)*25136*(25136+2)))^2 +
  covarianceVarianceBound 25136 (mW 12568) /
    ((1/1000)*covarianceMeanBound 25136 (mW 12568))^2 +
  normVarianceBound 25136 (mW 12568) / (3*inputVarianceMean 25136 (mW 12568))^2

end BstLean.Part268.WorldRow12568
namespace BstLean.Part268.WorldRow12569
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12569 = 222614035142487 := by
  have hu : mW 12569 ≤ 222614035142487 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12569 ≤ 222614035142486 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12569)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25138 ^ 2)
    ((25000000000000000000/3948667806297011121432943))
    ((25000000000000000000/3948510726664331631758451)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25138) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25138 : ℝ)^2 / (mW 12569 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1029081/500000000000))/2) * ((1-firstRatio 25138) * √(1-firstRatio 25138) *
      sixthConstant (e1CovarianceRatio 25138 (mW 12569) (1/10^6) rowEps))) /
    (712/10000 - 25138*(1+1/10^6)*((1029081/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25138 (mW 12569) /
    ((1/10^5) * ((mW 12569 : ℝ)*25138*((mW 12569 : ℝ)+25138+1)))^2 +
  8*(mW 12569 : ℝ)*25138*(25138+2)*(25138+3) /
    ((1/1000)*((mW 12569 : ℝ)*25138*(25138+2)))^2 +
  covarianceVarianceBound 25138 (mW 12569) /
    ((1/1000)*covarianceMeanBound 25138 (mW 12569))^2 +
  normVarianceBound 25138 (mW 12569) / (3*inputVarianceMean 25138 (mW 12569))^2

end BstLean.Part268.WorldRow12569
namespace BstLean.Part268.WorldRow12570
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12570 = 222676031054116 := by
  have hu : mW 12570 ≤ 222676031054116 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12570 ≤ 222676031054115 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12570)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25140 ^ 2)
    ((2500000000000000000/394898196556237010075679))
    ((25000000000000000000/3948824885929690611082297)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25140) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25140 : ℝ)^2 / (mW 12570 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2057997/1000000000000))/2) * ((1-firstRatio 25140) * √(1-firstRatio 25140) *
      sixthConstant (e1CovarianceRatio 25140 (mW 12570) (1/10^6) rowEps))) /
    (712/10000 - 25140*(1+1/10^6)*((2057997/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25140 (mW 12570) /
    ((1/10^5) * ((mW 12570 : ℝ)*25140*((mW 12570 : ℝ)+25140+1)))^2 +
  8*(mW 12570 : ℝ)*25140*(25140+2)*(25140+3) /
    ((1/1000)*((mW 12570 : ℝ)*25140*(25140+2)))^2 +
  covarianceVarianceBound 25140 (mW 12570) /
    ((1/1000)*covarianceMeanBound 25140 (mW 12570))^2 +
  normVarianceBound 25140 (mW 12570) / (3*inputVarianceMean 25140 (mW 12570))^2

end BstLean.Part268.WorldRow12570
namespace BstLean.Part268.WorldRow12571
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12571 = 222738039297105 := by
  have hu : mW 12571 ≤ 222738039297105 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12571 ≤ 222738039297104 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12571)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25142 ^ 2)
    ((25000000000000000000/3949296124827729080080637))
    ((25000000000000000000/3949139045195049590406143)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25142) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25142 : ℝ)^2 / (mW 12571 : ℝ)) * (1 + 1/10^6)^2 *
    √(((257229/125000000000))/2) * ((1-firstRatio 25142) * √(1-firstRatio 25142) *
      sixthConstant (e1CovarianceRatio 25142 (mW 12571) (1/10^6) rowEps))) /
    (712/10000 - 25142*(1+1/10^6)*((257229/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25142 (mW 12571) /
    ((1/10^5) * ((mW 12571 : ℝ)*25142*((mW 12571 : ℝ)+25142+1)))^2 +
  8*(mW 12571 : ℝ)*25142*(25142+2)*(25142+3) /
    ((1/1000)*((mW 12571 : ℝ)*25142*(25142+2)))^2 +
  covarianceVarianceBound 25142 (mW 12571) /
    ((1/1000)*covarianceMeanBound 25142 (mW 12571))^2 +
  normVarianceBound 25142 (mW 12571) / (3*inputVarianceMean 25142 (mW 12571))^2

end BstLean.Part268.WorldRow12571
namespace BstLean.Part268.WorldRow12572
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12572 = 222800059872925 := by
  have hu : mW 12572 ≤ 222800059872925 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12572 ≤ 222800059872924 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12572)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25144 ^ 2)
    ((6250000000000000000/987402571023272014851121))
    ((25000000000000000000/3949453204460408569729989)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25144) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25144 : ℝ)^2 / (mW 12572 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1028833/500000000000))/2) * ((1-firstRatio 25144) * √(1-firstRatio 25144) *
      sixthConstant (e1CovarianceRatio 25144 (mW 12572) (1/10^6) rowEps))) /
    (712/10000 - 25144*(1+1/10^6)*((1028833/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25144 (mW 12572) /
    ((1/10^5) * ((mW 12572 : ℝ)*25144*((mW 12572 : ℝ)+25144+1)))^2 +
  8*(mW 12572 : ℝ)*25144*(25144+2)*(25144+3) /
    ((1/1000)*((mW 12572 : ℝ)*25144*(25144+2)))^2 +
  covarianceVarianceBound 25144 (mW 12572) /
    ((1/1000)*covarianceMeanBound 25144 (mW 12572))^2 +
  normVarianceBound 25144 (mW 12572) / (3*inputVarianceMean 25144 (mW 12572))^2

end BstLean.Part268.WorldRow12572
namespace BstLean.Part268.WorldRow12573
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12573 = 222862092783048 := by
  have hu : mW 12573 ≤ 222862092783048 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12573 ≤ 222862092783047 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12573)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25146 ^ 2)
    ((25000000000000000000/3949924443358447038728331))
    ((5000000000000000000/789953472745153509810767)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25146) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25146 : ℝ)^2 / (mW 12573 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2057501/1000000000000))/2) * ((1-firstRatio 25146) * √(1-firstRatio 25146) *
      sixthConstant (e1CovarianceRatio 25146 (mW 12573) (1/10^6) rowEps))) /
    (712/10000 - 25146*(1+1/10^6)*((2057501/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25146 (mW 12573) /
    ((1/10^5) * ((mW 12573 : ℝ)*25146*((mW 12573 : ℝ)+25146+1)))^2 +
  8*(mW 12573 : ℝ)*25146*(25146+2)*(25146+3) /
    ((1/1000)*((mW 12573 : ℝ)*25146*(25146+2)))^2 +
  covarianceVarianceBound 25146 (mW 12573) /
    ((1/1000)*covarianceMeanBound 25146 (mW 12573))^2 +
  normVarianceBound 25146 (mW 12573) / (3*inputVarianceMean 25146 (mW 12573))^2

end BstLean.Part268.WorldRow12573
namespace BstLean.Part268.WorldRow12574
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12574 = 222924138028946 := by
  have hu : mW 12574 ≤ 222924138028946 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12574 ≤ 222924138028945 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12574)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25148 ^ 2)
    ((12500000000000000000/1975119301311903009026089))
    ((25000000000000000000/3950081522991126528377681)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25148) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25148 : ℝ)^2 / (mW 12574 : ℝ)) * (1 + 1/10^6)^2 *
    √(((411467/200000000000))/2) * ((1-firstRatio 25148) * √(1-firstRatio 25148) *
      sixthConstant (e1CovarianceRatio 25148 (mW 12574) (1/10^6) rowEps))) /
    (712/10000 - 25148*(1+1/10^6)*((411467/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25148 (mW 12574) /
    ((1/10^5) * ((mW 12574 : ℝ)*25148*((mW 12574 : ℝ)+25148+1)))^2 +
  8*(mW 12574 : ℝ)*25148*(25148+2)*(25148+3) /
    ((1/1000)*((mW 12574 : ℝ)*25148*(25148+2)))^2 +
  covarianceVarianceBound 25148 (mW 12574) /
    ((1/1000)*covarianceMeanBound 25148 (mW 12574))^2 +
  normVarianceBound 25148 (mW 12574) / (3*inputVarianceMean 25148 (mW 12574))^2

end BstLean.Part268.WorldRow12574
