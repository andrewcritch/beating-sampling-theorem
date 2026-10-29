import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar21
namespace BstLean.Part268.WorldRow12875
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12875 = 242167206478807 := by
  have hu : mW 12875 ≤ 242167206478807 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12875 ≤ 242167206478806 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12875)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25750 ^ 2)
    ((200000000000000000/32358404331974870356241))
    ((25000000000000000000/4044643461864179304855327)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25750) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25750 : ℝ)^2 / (mW 12875 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2008743/1000000000000))/2) * ((1-firstRatio 25750) * √(1-firstRatio 25750) *
      sixthConstant (e1CovarianceRatio 25750 (mW 12875) (1/10^6) rowEps))) /
    (712/10000 - 25750*(1+1/10^6)*((2008743/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25750 (mW 12875) /
    ((1/10^5) * ((mW 12875 : ℝ)*25750*((mW 12875 : ℝ)+25750+1)))^2 +
  8*(mW 12875 : ℝ)*25750*(25750+2)*(25750+3) /
    ((1/1000)*((mW 12875 : ℝ)*25750*(25750+2)))^2 +
  covarianceVarianceBound 25750 (mW 12875) /
    ((1/1000)*covarianceMeanBound 25750 (mW 12875))^2 +
  normVarianceBound 25750 (mW 12875) / (3*inputVarianceMean 25750 (mW 12875))^2

end BstLean.Part268.WorldRow12875
namespace BstLean.Part268.WorldRow12876
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12876 = 242233044732453 := by
  have hu : mW 12876 ≤ 242233044732453 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12876 ≤ 242233044732452 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12876)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25752 ^ 2)
    ((6250000000000000000/1011278675190554443463493))
    ((25000000000000000000/4044957621129538284179173)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25752) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25752 : ℝ)^2 / (mW 12876 : ℝ)) * (1 + 1/10^6)^2 *
    √(((401717/200000000000))/2) * ((1-firstRatio 25752) * √(1-firstRatio 25752) *
      sixthConstant (e1CovarianceRatio 25752 (mW 12876) (1/10^6) rowEps))) /
    (712/10000 - 25752*(1+1/10^6)*((401717/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25752 (mW 12876) /
    ((1/10^5) * ((mW 12876 : ℝ)*25752*((mW 12876 : ℝ)+25752+1)))^2 +
  8*(mW 12876 : ℝ)*25752*(25752+2)*(25752+3) /
    ((1/1000)*((mW 12876 : ℝ)*25752*(25752+2)))^2 +
  covarianceVarianceBound 25752 (mW 12876) /
    ((1/1000)*covarianceMeanBound 25752 (mW 12876))^2 +
  normVarianceBound 25752 (mW 12876) / (3*inputVarianceMean 25752 (mW 12876))^2

end BstLean.Part268.WorldRow12876
namespace BstLean.Part268.WorldRow12877
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12877 = 242298895770475 := by
  have hu : mW 12877 ≤ 242298895770475 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12877 ≤ 242298895770474 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12877)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25754 ^ 2)
    ((25000000000000000000/4045428860027576753177819))
    ((25000000000000000000/4045271780394897263503019)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25754) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25754 : ℝ)^2 / (mW 12877 : ℝ)) * (1 + 1/10^6)^2 *
    √(((502107/250000000000))/2) * ((1-firstRatio 25754) * √(1-firstRatio 25754) *
      sixthConstant (e1CovarianceRatio 25754 (mW 12877) (1/10^6) rowEps))) /
    (712/10000 - 25754*(1+1/10^6)*((502107/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25754 (mW 12877) /
    ((1/10^5) * ((mW 12877 : ℝ)*25754*((mW 12877 : ℝ)+25754+1)))^2 +
  8*(mW 12877 : ℝ)*25754*(25754+2)*(25754+3) /
    ((1/1000)*((mW 12877 : ℝ)*25754*(25754+2)))^2 +
  covarianceVarianceBound 25754 (mW 12877) /
    ((1/1000)*covarianceMeanBound 25754 (mW 12877))^2 +
  normVarianceBound 25754 (mW 12877) / (3*inputVarianceMean 25754 (mW 12877))^2

end BstLean.Part268.WorldRow12877
namespace BstLean.Part268.WorldRow12878
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12878 = 242364759594361 := by
  have hu : mW 12878 ≤ 242364759594361 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12878 ≤ 242364759594360 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12878)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25756 ^ 2)
    ((12500000000000000000/2022871509646467866250833))
    ((5000000000000000000/809117187932051248565373)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25756) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25756 : ℝ)^2 / (mW 12878 : ℝ)) * (1 + 1/10^6)^2 *
    √(((200827/100000000000))/2) * ((1-firstRatio 25756) * √(1-firstRatio 25756) *
      sixthConstant (e1CovarianceRatio 25756 (mW 12878) (1/10^6) rowEps))) /
    (712/10000 - 25756*(1+1/10^6)*((200827/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25756 (mW 12878) /
    ((1/10^5) * ((mW 12878 : ℝ)*25756*((mW 12878 : ℝ)+25756+1)))^2 +
  8*(mW 12878 : ℝ)*25756*(25756+2)*(25756+3) /
    ((1/1000)*((mW 12878 : ℝ)*25756*(25756+2)))^2 +
  covarianceVarianceBound 25756 (mW 12878) /
    ((1/1000)*covarianceMeanBound 25756 (mW 12878))^2 +
  normVarianceBound 25756 (mW 12878) / (3*inputVarianceMean 25756 (mW 12878))^2

end BstLean.Part268.WorldRow12878
namespace BstLean.Part268.WorldRow12879
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12879 = 242430636205601 := by
  have hu : mW 12879 ≤ 242430636205601 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12879 ≤ 242430636205600 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12879)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25758 ^ 2)
    ((25000000000000000000/4046057178558294711825513))
    ((25000000000000000000/4045900098925615222150711)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25758) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25758 : ℝ)^2 / (mW 12879 : ℝ)) * (1 + 1/10^6)^2 *
    √(((125507/62500000000))/2) * ((1-firstRatio 25758) * √(1-firstRatio 25758) *
      sixthConstant (e1CovarianceRatio 25758 (mW 12879) (1/10^6) rowEps))) /
    (712/10000 - 25758*(1+1/10^6)*((125507/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25758 (mW 12879) /
    ((1/10^5) * ((mW 12879 : ℝ)*25758*((mW 12879 : ℝ)+25758+1)))^2 +
  8*(mW 12879 : ℝ)*25758*(25758+2)*(25758+3) /
    ((1/1000)*((mW 12879 : ℝ)*25758*(25758+2)))^2 +
  covarianceVarianceBound 25758 (mW 12879) /
    ((1/1000)*covarianceMeanBound 25758 (mW 12879))^2 +
  normVarianceBound 25758 (mW 12879) / (3*inputVarianceMean 25758 (mW 12879))^2

end BstLean.Part268.WorldRow12879
namespace BstLean.Part268.WorldRow12880
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12880 = 242496525605684 := by
  have hu : mW 12880 ≤ 242496525605684 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12880 ≤ 242496525605683 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12880)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25760 ^ 2)
    ((312500000000000000/50579641722795671139367))
    ((25000000000000000000/4046214258190974201474557)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25760) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25760 : ℝ)^2 / (mW 12880 : ℝ)) * (1 + 1/10^6)^2 *
    √(((401591/200000000000))/2) * ((1-firstRatio 25760) * √(1-firstRatio 25760) *
      sixthConstant (e1CovarianceRatio 25760 (mW 12880) (1/10^6) rowEps))) /
    (712/10000 - 25760*(1+1/10^6)*((401591/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25760 (mW 12880) /
    ((1/10^5) * ((mW 12880 : ℝ)*25760*((mW 12880 : ℝ)+25760+1)))^2 +
  8*(mW 12880 : ℝ)*25760*(25760+2)*(25760+3) /
    ((1/1000)*((mW 12880 : ℝ)*25760*(25760+2)))^2 +
  covarianceVarianceBound 25760 (mW 12880) /
    ((1/1000)*covarianceMeanBound 25760 (mW 12880))^2 +
  normVarianceBound 25760 (mW 12880) / (3*inputVarianceMean 25760 (mW 12880))^2

end BstLean.Part268.WorldRow12880
namespace BstLean.Part268.WorldRow12881
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12881 = 242562427796101 := by
  have hu : mW 12881 ≤ 242562427796101 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12881 ≤ 242562427796100 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12881)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25762 ^ 2)
    ((25000000000000000000/4046685497089012670473207))
    ((25000000000000000000/4046528417456333180798403)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25762) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25762 : ℝ)^2 / (mW 12881 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1003899/500000000000))/2) * ((1-firstRatio 25762) * √(1-firstRatio 25762) *
      sixthConstant (e1CovarianceRatio 25762 (mW 12881) (1/10^6) rowEps))) /
    (712/10000 - 25762*(1+1/10^6)*((1003899/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25762 (mW 12881) /
    ((1/10^5) * ((mW 12881 : ℝ)*25762*((mW 12881 : ℝ)+25762+1)))^2 +
  8*(mW 12881 : ℝ)*25762*(25762+2)*(25762+3) /
    ((1/1000)*((mW 12881 : ℝ)*25762*(25762+2)))^2 +
  covarianceVarianceBound 25762 (mW 12881) /
    ((1/1000)*covarianceMeanBound 25762 (mW 12881))^2 +
  normVarianceBound 25762 (mW 12881) / (3*inputVarianceMean 25762 (mW 12881))^2

end BstLean.Part268.WorldRow12881
namespace BstLean.Part268.WorldRow12882
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12882 = 242628342778339 := by
  have hu : mW 12882 ≤ 242628342778339 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12882 ≤ 242628342778338 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12882)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25764 ^ 2)
    ((12500000000000000000/2023499828177185824898527))
    ((25000000000000000000/4046842576721692160122249)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25764) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25764 : ℝ)^2 / (mW 12882 : ℝ)) * (1 + 1/10^6)^2 *
    √(((50191/25000000000))/2) * ((1-firstRatio 25764) * √(1-firstRatio 25764) *
      sixthConstant (e1CovarianceRatio 25764 (mW 12882) (1/10^6) rowEps))) /
    (712/10000 - 25764*(1+1/10^6)*((50191/25000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25764 (mW 12882) /
    ((1/10^5) * ((mW 12882 : ℝ)*25764*((mW 12882 : ℝ)+25764+1)))^2 +
  8*(mW 12882 : ℝ)*25764*(25764+2)*(25764+3) /
    ((1/1000)*((mW 12882 : ℝ)*25764*(25764+2)))^2 +
  covarianceVarianceBound 25764 (mW 12882) /
    ((1/1000)*covarianceMeanBound 25764 (mW 12882))^2 +
  normVarianceBound 25764 (mW 12882) / (3*inputVarianceMean 25764 (mW 12882))^2

end BstLean.Part268.WorldRow12882
namespace BstLean.Part268.WorldRow12883
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12883 = 242694270553890 := by
  have hu : mW 12883 ≤ 242694270553890 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12883 ≤ 242694270553889 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12883)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25766 ^ 2)
    ((25000000000000000000/4047313815619730629120901))
    ((5000000000000000000/809431347197410227889219)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25766) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25766 : ℝ)^2 / (mW 12883 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2007483/1000000000000))/2) * ((1-firstRatio 25766) * √(1-firstRatio 25766) *
      sixthConstant (e1CovarianceRatio 25766 (mW 12883) (1/10^6) rowEps))) /
    (712/10000 - 25766*(1+1/10^6)*((2007483/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25766 (mW 12883) /
    ((1/10^5) * ((mW 12883 : ℝ)*25766*((mW 12883 : ℝ)+25766+1)))^2 +
  8*(mW 12883 : ℝ)*25766*(25766+2)*(25766+3) /
    ((1/1000)*((mW 12883 : ℝ)*25766*(25766+2)))^2 +
  covarianceVarianceBound 25766 (mW 12883) /
    ((1/1000)*covarianceMeanBound 25766 (mW 12883))^2 +
  normVarianceBound 25766 (mW 12883) / (3*inputVarianceMean 25766 (mW 12883))^2

end BstLean.Part268.WorldRow12883
namespace BstLean.Part268.WorldRow12884
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12884 = 242760211124243 := by
  have hu : mW 12884 ≤ 242760211124243 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12884 ≤ 242760211124242 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12884)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25768 ^ 2)
    ((6250000000000000000/1011906993721272402111187))
    ((25000000000000000000/4047470895252410118769941)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25768) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25768 : ℝ)^2 / (mW 12884 : ℝ)) * (1 + 1/10^6)^2 *
    √(((80293/40000000000))/2) * ((1-firstRatio 25768) * √(1-firstRatio 25768) *
      sixthConstant (e1CovarianceRatio 25768 (mW 12884) (1/10^6) rowEps))) /
    (712/10000 - 25768*(1+1/10^6)*((80293/40000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25768 (mW 12884) /
    ((1/10^5) * ((mW 12884 : ℝ)*25768*((mW 12884 : ℝ)+25768+1)))^2 +
  8*(mW 12884 : ℝ)*25768*(25768+2)*(25768+3) /
    ((1/1000)*((mW 12884 : ℝ)*25768*(25768+2)))^2 +
  covarianceVarianceBound 25768 (mW 12884) /
    ((1/1000)*covarianceMeanBound 25768 (mW 12884))^2 +
  normVarianceBound 25768 (mW 12884) / (3*inputVarianceMean 25768 (mW 12884))^2

end BstLean.Part268.WorldRow12884
namespace BstLean.Part268.WorldRow12885
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12885 = 242826164490887 := by
  have hu : mW 12885 ≤ 242826164490887 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12885 ≤ 242826164490886 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12885)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25770 ^ 2)
    ((5000000000000000000/809588426830089717553719))
    ((25000000000000000000/4047785054517769098093787)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25770) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25770 : ℝ)^2 / (mW 12885 : ℝ)) * (1 + 1/10^6)^2 *
    √(((15681/7812500000))/2) * ((1-firstRatio 25770) * √(1-firstRatio 25770) *
      sixthConstant (e1CovarianceRatio 25770 (mW 12885) (1/10^6) rowEps))) /
    (712/10000 - 25770*(1+1/10^6)*((15681/7812500000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25770 (mW 12885) /
    ((1/10^5) * ((mW 12885 : ℝ)*25770*((mW 12885 : ℝ)+25770+1)))^2 +
  8*(mW 12885 : ℝ)*25770*(25770+2)*(25770+3) /
    ((1/1000)*((mW 12885 : ℝ)*25770*(25770+2)))^2 +
  covarianceVarianceBound 25770 (mW 12885) /
    ((1/1000)*covarianceMeanBound 25770 (mW 12885))^2 +
  normVarianceBound 25770 (mW 12885) / (3*inputVarianceMean 25770 (mW 12885))^2

end BstLean.Part268.WorldRow12885
namespace BstLean.Part268.WorldRow12886
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12886 = 242892130655313 := by
  have hu : mW 12886 ≤ 242892130655313 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12886 ≤ 242892130655312 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12886)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25772 ^ 2)
    ((12500000000000000000/2024128146707903783546221))
    ((25000000000000000000/4048099213783128077417633)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25772) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25772 : ℝ)^2 / (mW 12886 : ℝ)) * (1 + 1/10^6)^2 *
    √(((200701/100000000000))/2) * ((1-firstRatio 25772) * √(1-firstRatio 25772) *
      sixthConstant (e1CovarianceRatio 25772 (mW 12886) (1/10^6) rowEps))) /
    (712/10000 - 25772*(1+1/10^6)*((200701/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25772 (mW 12886) /
    ((1/10^5) * ((mW 12886 : ℝ)*25772*((mW 12886 : ℝ)+25772+1)))^2 +
  8*(mW 12886 : ℝ)*25772*(25772+2)*(25772+3) /
    ((1/1000)*((mW 12886 : ℝ)*25772*(25772+2)))^2 +
  covarianceVarianceBound 25772 (mW 12886) /
    ((1/1000)*covarianceMeanBound 25772 (mW 12886))^2 +
  normVarianceBound 25772 (mW 12886) / (3*inputVarianceMean 25772 (mW 12886))^2

end BstLean.Part268.WorldRow12886
namespace BstLean.Part268.WorldRow12887
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12887 = 242958109619010 := by
  have hu : mW 12887 ≤ 242958109619010 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12887 ≤ 242958109619009 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12887)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25774 ^ 2)
    ((25000000000000000000/4048570452681166546416289))
    ((25000000000000000000/4048413373048487056741479)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25774) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25774 : ℝ)^2 / (mW 12887 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2006853/1000000000000))/2) * ((1-firstRatio 25774) * √(1-firstRatio 25774) *
      sixthConstant (e1CovarianceRatio 25774 (mW 12887) (1/10^6) rowEps))) /
    (712/10000 - 25774*(1+1/10^6)*((2006853/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25774 (mW 12887) /
    ((1/10^5) * ((mW 12887 : ℝ)*25774*((mW 12887 : ℝ)+25774+1)))^2 +
  8*(mW 12887 : ℝ)*25774*(25774+2)*(25774+3) /
    ((1/1000)*((mW 12887 : ℝ)*25774*(25774+2)))^2 +
  covarianceVarianceBound 25774 (mW 12887) /
    ((1/1000)*covarianceMeanBound 25774 (mW 12887))^2 +
  normVarianceBound 25774 (mW 12887) / (3*inputVarianceMean 25774 (mW 12887))^2

end BstLean.Part268.WorldRow12887
namespace BstLean.Part268.WorldRow12888
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12888 = 243024101383468 := by
  have hu : mW 12888 ≤ 243024101383468 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12888 ≤ 243024101383467 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12888)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25776 ^ 2)
    ((3125000000000000000/506110576493315690717517))
    ((1000000000000000000/161949101292553841442613)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25776) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25776 : ℝ)^2 / (mW 12888 : ℝ)) * (1 + 1/10^6)^2 *
    √(((250837/125000000000))/2) * ((1-firstRatio 25776) * √(1-firstRatio 25776) *
      sixthConstant (e1CovarianceRatio 25776 (mW 12888) (1/10^6) rowEps))) /
    (712/10000 - 25776*(1+1/10^6)*((250837/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25776 (mW 12888) /
    ((1/10^5) * ((mW 12888 : ℝ)*25776*((mW 12888 : ℝ)+25776+1)))^2 +
  8*(mW 12888 : ℝ)*25776*(25776+2)*(25776+3) /
    ((1/1000)*((mW 12888 : ℝ)*25776*(25776+2)))^2 +
  covarianceVarianceBound 25776 (mW 12888) /
    ((1/1000)*covarianceMeanBound 25776 (mW 12888))^2 +
  normVarianceBound 25776 (mW 12888) / (3*inputVarianceMean 25776 (mW 12888))^2

end BstLean.Part268.WorldRow12888
namespace BstLean.Part268.WorldRow12889
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12889 = 243090105950177 := by
  have hu : mW 12889 ≤ 243090105950177 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12889 ≤ 243090105950176 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12889)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25778 ^ 2)
    ((25000000000000000000/4049198771211884505063983))
    ((25000000000000000000/4049041691579205015389171)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25778) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25778 : ℝ)^2 / (mW 12889 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2006539/1000000000000))/2) * ((1-firstRatio 25778) * √(1-firstRatio 25778) *
      sixthConstant (e1CovarianceRatio 25778 (mW 12889) (1/10^6) rowEps))) /
    (712/10000 - 25778*(1+1/10^6)*((2006539/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25778 (mW 12889) /
    ((1/10^5) * ((mW 12889 : ℝ)*25778*((mW 12889 : ℝ)+25778+1)))^2 +
  8*(mW 12889 : ℝ)*25778*(25778+2)*(25778+3) /
    ((1/1000)*((mW 12889 : ℝ)*25778*(25778+2)))^2 +
  covarianceVarianceBound 25778 (mW 12889) /
    ((1/1000)*covarianceMeanBound 25778 (mW 12889))^2 +
  normVarianceBound 25778 (mW 12889) / (3*inputVarianceMean 25778 (mW 12889))^2

end BstLean.Part268.WorldRow12889
namespace BstLean.Part268.WorldRow12890
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12890 = 243156123320628 := by
  have hu : mW 12890 ≤ 243156123320628 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12890 ≤ 243156123320627 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12890)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25780 ^ 2)
    ((2500000000000000000/404951293047724348438783))
    ((25000000000000000000/4049355850844563994713017)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25780) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25780 : ℝ)^2 / (mW 12890 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2006381/1000000000000))/2) * ((1-firstRatio 25780) * √(1-firstRatio 25780) *
      sixthConstant (e1CovarianceRatio 25780 (mW 12890) (1/10^6) rowEps))) /
    (712/10000 - 25780*(1+1/10^6)*((2006381/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25780 (mW 12890) /
    ((1/10^5) * ((mW 12890 : ℝ)*25780*((mW 12890 : ℝ)+25780+1)))^2 +
  8*(mW 12890 : ℝ)*25780*(25780+2)*(25780+3) /
    ((1/1000)*((mW 12890 : ℝ)*25780*(25780+2)))^2 +
  covarianceVarianceBound 25780 (mW 12890) /
    ((1/1000)*covarianceMeanBound 25780 (mW 12890))^2 +
  normVarianceBound 25780 (mW 12890) / (3*inputVarianceMean 25780 (mW 12890))^2

end BstLean.Part268.WorldRow12890
namespace BstLean.Part268.WorldRow12891
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12891 = 243222153496309 := by
  have hu : mW 12891 ≤ 243222153496309 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12891 ≤ 243222153496308 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12891)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25782 ^ 2)
    ((25000000000000000000/4049827089742602463711677))
    ((25000000000000000000/4049670010109922974036863)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25782) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25782 : ℝ)^2 / (mW 12891 : ℝ)) * (1 + 1/10^6)^2 *
    √(((125389/62500000000))/2) * ((1-firstRatio 25782) * √(1-firstRatio 25782) *
      sixthConstant (e1CovarianceRatio 25782 (mW 12891) (1/10^6) rowEps))) /
    (712/10000 - 25782*(1+1/10^6)*((125389/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25782 (mW 12891) /
    ((1/10^5) * ((mW 12891 : ℝ)*25782*((mW 12891 : ℝ)+25782+1)))^2 +
  8*(mW 12891 : ℝ)*25782*(25782+2)*(25782+3) /
    ((1/1000)*((mW 12891 : ℝ)*25782*(25782+2)))^2 +
  covarianceVarianceBound 25782 (mW 12891) /
    ((1/1000)*covarianceMeanBound 25782 (mW 12891))^2 +
  normVarianceBound 25782 (mW 12891) / (3*inputVarianceMean 25782 (mW 12891))^2

end BstLean.Part268.WorldRow12891
namespace BstLean.Part268.WorldRow12892
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12892 = 243288196478713 := by
  have hu : mW 12892 ≤ 243288196478713 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12892 ≤ 243288196478712 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12892)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25784 ^ 2)
    ((6250000000000000000/1012535312251990360758881))
    ((25000000000000000000/4049984169375281953360709)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25784) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25784 : ℝ)^2 / (mW 12892 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2006067/1000000000000))/2) * ((1-firstRatio 25784) * √(1-firstRatio 25784) *
      sixthConstant (e1CovarianceRatio 25784 (mW 12892) (1/10^6) rowEps))) /
    (712/10000 - 25784*(1+1/10^6)*((2006067/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25784 (mW 12892) /
    ((1/10^5) * ((mW 12892 : ℝ)*25784*((mW 12892 : ℝ)+25784+1)))^2 +
  8*(mW 12892 : ℝ)*25784*(25784+2)*(25784+3) /
    ((1/1000)*((mW 12892 : ℝ)*25784*(25784+2)))^2 +
  covarianceVarianceBound 25784 (mW 12892) /
    ((1/1000)*covarianceMeanBound 25784 (mW 12892))^2 +
  normVarianceBound 25784 (mW 12892) / (3*inputVarianceMean 25784 (mW 12892))^2

end BstLean.Part268.WorldRow12892
namespace BstLean.Part268.WorldRow12893
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12893 = 243354252269328 := by
  have hu : mW 12893 ≤ 243354252269328 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12893 ≤ 243354252269327 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12893)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25786 ^ 2)
    ((25000000000000000000/4050455408273320422359371))
    ((5000000000000000000/810059665728128186536911)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25786) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25786 : ℝ)^2 / (mW 12893 : ℝ)) * (1 + 1/10^6)^2 *
    √(((200591/100000000000))/2) * ((1-firstRatio 25786) * √(1-firstRatio 25786) *
      sixthConstant (e1CovarianceRatio 25786 (mW 12893) (1/10^6) rowEps))) /
    (712/10000 - 25786*(1+1/10^6)*((200591/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25786 (mW 12893) /
    ((1/10^5) * ((mW 12893 : ℝ)*25786*((mW 12893 : ℝ)+25786+1)))^2 +
  8*(mW 12893 : ℝ)*25786*(25786+2)*(25786+3) /
    ((1/1000)*((mW 12893 : ℝ)*25786*(25786+2)))^2 +
  covarianceVarianceBound 25786 (mW 12893) /
    ((1/1000)*covarianceMeanBound 25786 (mW 12893))^2 +
  normVarianceBound 25786 (mW 12893) / (3*inputVarianceMean 25786 (mW 12893))^2

end BstLean.Part268.WorldRow12893
namespace BstLean.Part268.WorldRow12894
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12894 = 243420320869645 := by
  have hu : mW 12894 ≤ 243420320869645 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12894 ≤ 243420320869644 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12894)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25788 ^ 2)
    ((12500000000000000000/2025384783769339700841609))
    ((25000000000000000000/4050612487905999912008401)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25788) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25788 : ℝ)^2 / (mW 12894 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2005753/1000000000000))/2) * ((1-firstRatio 25788) * √(1-firstRatio 25788) *
      sixthConstant (e1CovarianceRatio 25788 (mW 12894) (1/10^6) rowEps))) /
    (712/10000 - 25788*(1+1/10^6)*((2005753/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25788 (mW 12894) /
    ((1/10^5) * ((mW 12894 : ℝ)*25788*((mW 12894 : ℝ)+25788+1)))^2 +
  8*(mW 12894 : ℝ)*25788*(25788+2)*(25788+3) /
    ((1/1000)*((mW 12894 : ℝ)*25788*(25788+2)))^2 +
  covarianceVarianceBound 25788 (mW 12894) /
    ((1/1000)*covarianceMeanBound 25788 (mW 12894))^2 +
  normVarianceBound 25788 (mW 12894) / (3*inputVarianceMean 25788 (mW 12894))^2

end BstLean.Part268.WorldRow12894
namespace BstLean.Part268.WorldRow12895
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12895 = 243486402281155 := by
  have hu : mW 12895 ≤ 243486402281155 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12895 ≤ 243486402281154 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12895)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25790 ^ 2)
    ((5000000000000000000/810216745360807676201413))
    ((25000000000000000000/4050926647171358891332247)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25790) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25790 : ℝ)^2 / (mW 12895 : ℝ)) * (1 + 1/10^6)^2 *
    √(((401119/200000000000))/2) * ((1-firstRatio 25790) * √(1-firstRatio 25790) *
      sixthConstant (e1CovarianceRatio 25790 (mW 12895) (1/10^6) rowEps))) /
    (712/10000 - 25790*(1+1/10^6)*((401119/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25790 (mW 12895) /
    ((1/10^5) * ((mW 12895 : ℝ)*25790*((mW 12895 : ℝ)+25790+1)))^2 +
  8*(mW 12895 : ℝ)*25790*(25790+2)*(25790+3) /
    ((1/1000)*((mW 12895 : ℝ)*25790*(25790+2)))^2 +
  covarianceVarianceBound 25790 (mW 12895) /
    ((1/1000)*covarianceMeanBound 25790 (mW 12895))^2 +
  normVarianceBound 25790 (mW 12895) / (3*inputVarianceMean 25790 (mW 12895))^2

end BstLean.Part268.WorldRow12895
namespace BstLean.Part268.WorldRow12896
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12896 = 243552496505347 := by
  have hu : mW 12896 ≤ 243552496505347 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12896 ≤ 243552496505346 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12896)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25792 ^ 2)
    ((781250000000000000/126606183939668667510341))
    ((25000000000000000000/4051240806436717870656093)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25792) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25792 : ℝ)^2 / (mW 12896 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1002719/500000000000))/2) * ((1-firstRatio 25792) * √(1-firstRatio 25792) *
      sixthConstant (e1CovarianceRatio 25792 (mW 12896) (1/10^6) rowEps))) /
    (712/10000 - 25792*(1+1/10^6)*((1002719/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25792 (mW 12896) /
    ((1/10^5) * ((mW 12896 : ℝ)*25792*((mW 12896 : ℝ)+25792+1)))^2 +
  8*(mW 12896 : ℝ)*25792*(25792+2)*(25792+3) /
    ((1/1000)*((mW 12896 : ℝ)*25792*(25792+2)))^2 +
  covarianceVarianceBound 25792 (mW 12896) /
    ((1/1000)*covarianceMeanBound 25792 (mW 12896))^2 +
  normVarianceBound 25792 (mW 12896) / (3*inputVarianceMean 25792 (mW 12896))^2

end BstLean.Part268.WorldRow12896
namespace BstLean.Part268.WorldRow12897
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12897 = 243618603543712 := by
  have hu : mW 12897 ≤ 243618603543712 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12897 ≤ 243618603543711 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12897)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25794 ^ 2)
    ((25000000000000000000/4051712045334756339654759))
    ((25000000000000000000/4051554965702076849979939)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25794) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25794 : ℝ)^2 / (mW 12897 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2005281/1000000000000))/2) * ((1-firstRatio 25794) * √(1-firstRatio 25794) *
      sixthConstant (e1CovarianceRatio 25794 (mW 12897) (1/10^6) rowEps))) /
    (712/10000 - 25794*(1+1/10^6)*((2005281/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25794 (mW 12897) /
    ((1/10^5) * ((mW 12897 : ℝ)*25794*((mW 12897 : ℝ)+25794+1)))^2 +
  8*(mW 12897 : ℝ)*25794*(25794+2)*(25794+3) /
    ((1/1000)*((mW 12897 : ℝ)*25794*(25794+2)))^2 +
  covarianceVarianceBound 25794 (mW 12897) /
    ((1/1000)*covarianceMeanBound 25794 (mW 12897))^2 +
  normVarianceBound 25794 (mW 12897) / (3*inputVarianceMean 25794 (mW 12897))^2

end BstLean.Part268.WorldRow12897
namespace BstLean.Part268.WorldRow12898
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12898 = 243684723397742 := by
  have hu : mW 12898 ≤ 243684723397742 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12898 ≤ 243684723397741 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12898)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25796 ^ 2)
    ((12500000000000000000/2026013102300057659489303))
    ((5000000000000000000/810373824993487165860757)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25796) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25796 : ℝ)^2 / (mW 12898 : ℝ)) * (1 + 1/10^6)^2 *
    √(((501281/250000000000))/2) * ((1-firstRatio 25796) * √(1-firstRatio 25796) *
      sixthConstant (e1CovarianceRatio 25796 (mW 12898) (1/10^6) rowEps))) /
    (712/10000 - 25796*(1+1/10^6)*((501281/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25796 (mW 12898) /
    ((1/10^5) * ((mW 12898 : ℝ)*25796*((mW 12898 : ℝ)+25796+1)))^2 +
  8*(mW 12898 : ℝ)*25796*(25796+2)*(25796+3) /
    ((1/1000)*((mW 12898 : ℝ)*25796*(25796+2)))^2 +
  covarianceVarianceBound 25796 (mW 12898) /
    ((1/1000)*covarianceMeanBound 25796 (mW 12898))^2 +
  normVarianceBound 25796 (mW 12898) / (3*inputVarianceMean 25796 (mW 12898))^2

end BstLean.Part268.WorldRow12898
namespace BstLean.Part268.WorldRow12899
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12899 = 243750856068925 := by
  have hu : mW 12899 ≤ 243750856068925 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12899 ≤ 243750856068924 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12899)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25798 ^ 2)
    ((25000000000000000000/4052340363865474298302453))
    ((25000000000000000000/4052183284232794808627631)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25798) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25798 : ℝ)^2 / (mW 12899 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2004967/1000000000000))/2) * ((1-firstRatio 25798) * √(1-firstRatio 25798) *
      sixthConstant (e1CovarianceRatio 25798 (mW 12899) (1/10^6) rowEps))) /
    (712/10000 - 25798*(1+1/10^6)*((2004967/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25798 (mW 12899) /
    ((1/10^5) * ((mW 12899 : ℝ)*25798*((mW 12899 : ℝ)+25798+1)))^2 +
  8*(mW 12899 : ℝ)*25798*(25798+2)*(25798+3) /
    ((1/1000)*((mW 12899 : ℝ)*25798*(25798+2)))^2 +
  covarianceVarianceBound 25798 (mW 12899) /
    ((1/1000)*covarianceMeanBound 25798 (mW 12899))^2 +
  normVarianceBound 25798 (mW 12899) / (3*inputVarianceMean 25798 (mW 12899))^2

end BstLean.Part268.WorldRow12899
