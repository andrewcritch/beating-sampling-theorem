import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar1
namespace BstLean.Part268.WorldRow12375
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12375 = 210818261010658 := by
  have hu : mW 12375 ≤ 210818261010658 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12375 ≤ 210818261010657 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12375)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24750 ^ 2)
    ((200000000000000000/31101767270538953060853))
    ((25000000000000000000/3887563829184689642932327)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24750) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24750 : ℝ)^2 / (mW 12375 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2090777/1000000000000))/2) * ((1-firstRatio 24750) * √(1-firstRatio 24750) *
      sixthConstant (e1CovarianceRatio 24750 (mW 12375) (1/10^6) rowEps))) /
    (712/10000 - 24750*(1+1/10^6)*((2090777/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24750 (mW 12375) /
    ((1/10^5) * ((mW 12375 : ℝ)*24750*((mW 12375 : ℝ)+24750+1)))^2 +
  8*(mW 12375 : ℝ)*24750*(24750+2)*(24750+3) /
    ((1/1000)*((mW 12375 : ℝ)*24750*(24750+2)))^2 +
  covarianceVarianceBound 24750 (mW 12375) /
    ((1/1000)*covarianceMeanBound 24750 (mW 12375))^2 +
  normVarianceBound 24750 (mW 12375) / (3*inputVarianceMean 24750 (mW 12375))^2

end BstLean.Part268.WorldRow12375
namespace BstLean.Part268.WorldRow12376
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12376 = 210877892400416 := by
  have hu : mW 12376 ≤ 210877892400416 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12376 ≤ 210877892400415 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12376)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24752 ^ 2)
    ((3125000000000000000/486004383510341013991309))
    ((25000000000000000000/3887877988450048622256173)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24752) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24752 : ℝ)^2 / (mW 12376 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1045303/500000000000))/2) * ((1-firstRatio 24752) * √(1-firstRatio 24752) *
      sixthConstant (e1CovarianceRatio 24752 (mW 12376) (1/10^6) rowEps))) /
    (712/10000 - 24752*(1+1/10^6)*((1045303/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24752 (mW 12376) /
    ((1/10^5) * ((mW 12376 : ℝ)*24752*((mW 12376 : ℝ)+24752+1)))^2 +
  8*(mW 12376 : ℝ)*24752*(24752+2)*(24752+3) /
    ((1/1000)*((mW 12376 : ℝ)*24752*(24752+2)))^2 +
  covarianceVarianceBound 24752 (mW 12376) /
    ((1/1000)*covarianceMeanBound 24752 (mW 12376))^2 +
  normVarianceBound 24752 (mW 12376) / (3*inputVarianceMean 24752 (mW 12376))^2

end BstLean.Part268.WorldRow12376
namespace BstLean.Part268.WorldRow12377
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12377 = 210937535837163 := by
  have hu : mW 12377 ≤ 210937535837163 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12377 ≤ 210937535837162 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12377)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24754 ^ 2)
    ((25000000000000000000/3888349227348087091254319))
    ((25000000000000000000/3888192147715407601580019)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24754) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24754 : ℝ)^2 / (mW 12377 : ℝ)) * (1 + 1/10^6)^2 *
    √(((522609/250000000000))/2) * ((1-firstRatio 24754) * √(1-firstRatio 24754) *
      sixthConstant (e1CovarianceRatio 24754 (mW 12377) (1/10^6) rowEps))) /
    (712/10000 - 24754*(1+1/10^6)*((522609/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24754 (mW 12377) /
    ((1/10^5) * ((mW 12377 : ℝ)*24754*((mW 12377 : ℝ)+24754+1)))^2 +
  8*(mW 12377 : ℝ)*24754*(24754+2)*(24754+3) /
    ((1/1000)*((mW 12377 : ℝ)*24754*(24754+2)))^2 +
  covarianceVarianceBound 24754 (mW 12377) /
    ((1/1000)*covarianceMeanBound 24754 (mW 12377))^2 +
  normVarianceBound 24754 (mW 12377) / (3*inputVarianceMean 24754 (mW 12377))^2

end BstLean.Part268.WorldRow12377
namespace BstLean.Part268.WorldRow12378
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12378 = 210997191322359 := by
  have hu : mW 12378 ≤ 210997191322359 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12378 ≤ 210997191322358 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12378)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24756 ^ 2)
    ((12500000000000000000/1944331693306723035289083))
    ((5000000000000000000/777701261396153316180773)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24756) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24756 : ℝ)^2 / (mW 12378 : ℝ)) * (1 + 1/10^6)^2 *
    √(((418053/200000000000))/2) * ((1-firstRatio 24756) * √(1-firstRatio 24756) *
      sixthConstant (e1CovarianceRatio 24756 (mW 12378) (1/10^6) rowEps))) /
    (712/10000 - 24756*(1+1/10^6)*((418053/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24756 (mW 12378) /
    ((1/10^5) * ((mW 12378 : ℝ)*24756*((mW 12378 : ℝ)+24756+1)))^2 +
  8*(mW 12378 : ℝ)*24756*(24756+2)*(24756+3) /
    ((1/1000)*((mW 12378 : ℝ)*24756*(24756+2)))^2 +
  covarianceVarianceBound 24756 (mW 12378) /
    ((1/1000)*covarianceMeanBound 24756 (mW 12378))^2 +
  normVarianceBound 24756 (mW 12378) / (3*inputVarianceMean 24756 (mW 12378))^2

end BstLean.Part268.WorldRow12378
namespace BstLean.Part268.WorldRow12379
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12379 = 211056858857463 := by
  have hu : mW 12379 ≤ 211056858857463 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12379 ≤ 211056858857462 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12379)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24758 ^ 2)
    ((25000000000000000000/3888977545878805049902013))
    ((25000000000000000000/3888820466246125560227711)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24758) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24758 : ℝ)^2 / (mW 12379 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1045047/500000000000))/2) * ((1-firstRatio 24758) * √(1-firstRatio 24758) *
      sixthConstant (e1CovarianceRatio 24758 (mW 12379) (1/10^6) rowEps))) /
    (712/10000 - 24758*(1+1/10^6)*((1045047/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24758 (mW 12379) /
    ((1/10^5) * ((mW 12379 : ℝ)*24758*((mW 12379 : ℝ)+24758+1)))^2 +
  8*(mW 12379 : ℝ)*24758*(24758+2)*(24758+3) /
    ((1/1000)*((mW 12379 : ℝ)*24758*(24758+2)))^2 +
  covarianceVarianceBound 24758 (mW 12379) /
    ((1/1000)*covarianceMeanBound 24758 (mW 12379))^2 +
  normVarianceBound 24758 (mW 12379) / (3*inputVarianceMean 24758 (mW 12379))^2

end BstLean.Part268.WorldRow12379
namespace BstLean.Part268.WorldRow12380
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12380 = 211116538443938 := by
  have hu : mW 12380 ≤ 211116538443938 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12380 ≤ 211116538443937 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12380)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24760 ^ 2)
    ((1250000000000000000/194464585257208201461293))
    ((25000000000000000000/3889134625511484539551557)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24760) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24760 : ℝ)^2 / (mW 12380 : ℝ)) * (1 + 1/10^6)^2 *
    √(((522481/250000000000))/2) * ((1-firstRatio 24760) * √(1-firstRatio 24760) *
      sixthConstant (e1CovarianceRatio 24760 (mW 12380) (1/10^6) rowEps))) /
    (712/10000 - 24760*(1+1/10^6)*((522481/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24760 (mW 12380) /
    ((1/10^5) * ((mW 12380 : ℝ)*24760*((mW 12380 : ℝ)+24760+1)))^2 +
  8*(mW 12380 : ℝ)*24760*(24760+2)*(24760+3) /
    ((1/1000)*((mW 12380 : ℝ)*24760*(24760+2)))^2 +
  covarianceVarianceBound 24760 (mW 12380) /
    ((1/1000)*covarianceMeanBound 24760 (mW 12380))^2 +
  normVarianceBound 24760 (mW 12380) / (3*inputVarianceMean 24760 (mW 12380))^2

end BstLean.Part268.WorldRow12380
namespace BstLean.Part268.WorldRow12381
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12381 = 211176230083242 := by
  have hu : mW 12381 ≤ 211176230083242 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12381 ≤ 211176230083241 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12381)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24762 ^ 2)
    ((25000000000000000000/3889605864409523008549707))
    ((25000000000000000000/3889448784776843518875403)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24762) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24762 : ℝ)^2 / (mW 12381 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2089753/1000000000000))/2) * ((1-firstRatio 24762) * √(1-firstRatio 24762) *
      sixthConstant (e1CovarianceRatio 24762 (mW 12381) (1/10^6) rowEps))) /
    (712/10000 - 24762*(1+1/10^6)*((2089753/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24762 (mW 12381) /
    ((1/10^5) * ((mW 12381 : ℝ)*24762*((mW 12381 : ℝ)+24762+1)))^2 +
  8*(mW 12381 : ℝ)*24762*(24762+2)*(24762+3) /
    ((1/1000)*((mW 12381 : ℝ)*24762*(24762+2)))^2 +
  covarianceVarianceBound 24762 (mW 12381) /
    ((1/1000)*covarianceMeanBound 24762 (mW 12381))^2 +
  normVarianceBound 24762 (mW 12381) / (3*inputVarianceMean 24762 (mW 12381))^2

end BstLean.Part268.WorldRow12381
namespace BstLean.Part268.WorldRow12382
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12382 = 211235933776836 := by
  have hu : mW 12382 ≤ 211235933776836 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12382 ≤ 211235933776835 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12382)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24764 ^ 2)
    ((12500000000000000000/1944960011837440993936777))
    ((25000000000000000000/3889762944042202498199249)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24764) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24764 : ℝ)^2 / (mW 12382 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1044791/500000000000))/2) * ((1-firstRatio 24764) * √(1-firstRatio 24764) *
      sixthConstant (e1CovarianceRatio 24764 (mW 12382) (1/10^6) rowEps))) /
    (712/10000 - 24764*(1+1/10^6)*((1044791/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24764 (mW 12382) /
    ((1/10^5) * ((mW 12382 : ℝ)*24764*((mW 12382 : ℝ)+24764+1)))^2 +
  8*(mW 12382 : ℝ)*24764*(24764+2)*(24764+3) /
    ((1/1000)*((mW 12382 : ℝ)*24764*(24764+2)))^2 +
  covarianceVarianceBound 24764 (mW 12382) /
    ((1/1000)*covarianceMeanBound 24764 (mW 12382))^2 +
  normVarianceBound 24764 (mW 12382) / (3*inputVarianceMean 24764 (mW 12382))^2

end BstLean.Part268.WorldRow12382
namespace BstLean.Part268.WorldRow12383
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12383 = 211295649526180 := by
  have hu : mW 12383 ≤ 211295649526180 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12383 ≤ 211295649526179 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12383)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24766 ^ 2)
    ((25000000000000000000/3890234182940240967197401))
    ((5000000000000000000/778015420661512295504619)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24766) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24766 : ℝ)^2 / (mW 12383 : ℝ)) * (1 + 1/10^6)^2 *
    √(((522353/250000000000))/2) * ((1-firstRatio 24766) * √(1-firstRatio 24766) *
      sixthConstant (e1CovarianceRatio 24766 (mW 12383) (1/10^6) rowEps))) /
    (712/10000 - 24766*(1+1/10^6)*((522353/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24766 (mW 12383) /
    ((1/10^5) * ((mW 12383 : ℝ)*24766*((mW 12383 : ℝ)+24766+1)))^2 +
  8*(mW 12383 : ℝ)*24766*(24766+2)*(24766+3) /
    ((1/1000)*((mW 12383 : ℝ)*24766*(24766+2)))^2 +
  covarianceVarianceBound 24766 (mW 12383) /
    ((1/1000)*covarianceMeanBound 24766 (mW 12383))^2 +
  normVarianceBound 24766 (mW 12383) / (3*inputVarianceMean 24766 (mW 12383))^2

end BstLean.Part268.WorldRow12383
namespace BstLean.Part268.WorldRow12384
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12384 = 211355377332736 := by
  have hu : mW 12384 ≤ 211355377332736 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12384 ≤ 211355377332735 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12384)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24768 ^ 2)
    ((781250000000000000/121579635693924998328789))
    ((25000000000000000000/3890391262572920456846941)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24768) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24768 : ℝ)^2 / (mW 12384 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2089241/1000000000000))/2) * ((1-firstRatio 24768) * √(1-firstRatio 24768) *
      sixthConstant (e1CovarianceRatio 24768 (mW 12384) (1/10^6) rowEps))) /
    (712/10000 - 24768*(1+1/10^6)*((2089241/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24768 (mW 12384) /
    ((1/10^5) * ((mW 12384 : ℝ)*24768*((mW 12384 : ℝ)+24768+1)))^2 +
  8*(mW 12384 : ℝ)*24768*(24768+2)*(24768+3) /
    ((1/1000)*((mW 12384 : ℝ)*24768*(24768+2)))^2 +
  covarianceVarianceBound 24768 (mW 12384) /
    ((1/1000)*covarianceMeanBound 24768 (mW 12384))^2 +
  normVarianceBound 24768 (mW 12384) / (3*inputVarianceMean 24768 (mW 12384))^2

end BstLean.Part268.WorldRow12384
namespace BstLean.Part268.WorldRow12385
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12385 = 211415117197963 := by
  have hu : mW 12385 ≤ 211415117197963 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12385 ≤ 211415117197962 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12385)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24770 ^ 2)
    ((5000000000000000000/778172500294191785169019))
    ((25000000000000000000/3890705421838279436170787)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24770) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24770 : ℝ)^2 / (mW 12385 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2089071/1000000000000))/2) * ((1-firstRatio 24770) * √(1-firstRatio 24770) *
      sixthConstant (e1CovarianceRatio 24770 (mW 12385) (1/10^6) rowEps))) /
    (712/10000 - 24770*(1+1/10^6)*((2089071/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24770 (mW 12385) /
    ((1/10^5) * ((mW 12385 : ℝ)*24770*((mW 12385 : ℝ)+24770+1)))^2 +
  8*(mW 12385 : ℝ)*24770*(24770+2)*(24770+3) /
    ((1/1000)*((mW 12385 : ℝ)*24770*(24770+2)))^2 +
  covarianceVarianceBound 24770 (mW 12385) /
    ((1/1000)*covarianceMeanBound 24770 (mW 12385))^2 +
  normVarianceBound 24770 (mW 12385) / (3*inputVarianceMean 24770 (mW 12385))^2

end BstLean.Part268.WorldRow12385
namespace BstLean.Part268.WorldRow12386
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12386 = 211474869123323 := by
  have hu : mW 12386 ≤ 211474869123323 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12386 ≤ 211474869123322 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12386)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24772 ^ 2)
    ((12500000000000000000/1945588330368158952584471))
    ((25000000000000000000/3891019581103638415494633)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24772) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24772 : ℝ)^2 / (mW 12386 : ℝ)) * (1 + 1/10^6)^2 *
    √(((20889/10000000000))/2) * ((1-firstRatio 24772) * √(1-firstRatio 24772) *
      sixthConstant (e1CovarianceRatio 24772 (mW 12386) (1/10^6) rowEps))) /
    (712/10000 - 24772*(1+1/10^6)*((20889/10000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24772 (mW 12386) /
    ((1/10^5) * ((mW 12386 : ℝ)*24772*((mW 12386 : ℝ)+24772+1)))^2 +
  8*(mW 12386 : ℝ)*24772*(24772+2)*(24772+3) /
    ((1/1000)*((mW 12386 : ℝ)*24772*(24772+2)))^2 +
  covarianceVarianceBound 24772 (mW 12386) /
    ((1/1000)*covarianceMeanBound 24772 (mW 12386))^2 +
  normVarianceBound 24772 (mW 12386) / (3*inputVarianceMean 24772 (mW 12386))^2

end BstLean.Part268.WorldRow12386
namespace BstLean.Part268.WorldRow12387
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12387 = 211534633110275 := by
  have hu : mW 12387 ≤ 211534633110275 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12387 ≤ 211534633110274 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12387)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24774 ^ 2)
    ((25000000000000000000/3891490820001676884492789))
    ((25000000000000000000/3891333740368997394818479)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24774) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24774 : ℝ)^2 / (mW 12387 : ℝ)) * (1 + 1/10^6)^2 *
    √(((208873/100000000000))/2) * ((1-firstRatio 24774) * √(1-firstRatio 24774) *
      sixthConstant (e1CovarianceRatio 24774 (mW 12387) (1/10^6) rowEps))) /
    (712/10000 - 24774*(1+1/10^6)*((208873/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24774 (mW 12387) /
    ((1/10^5) * ((mW 12387 : ℝ)*24774*((mW 12387 : ℝ)+24774+1)))^2 +
  8*(mW 12387 : ℝ)*24774*(24774+2)*(24774+3) /
    ((1/1000)*((mW 12387 : ℝ)*24774*(24774+2)))^2 +
  covarianceVarianceBound 24774 (mW 12387) /
    ((1/1000)*covarianceMeanBound 24774 (mW 12387))^2 +
  normVarianceBound 24774 (mW 12387) / (3*inputVarianceMean 24774 (mW 12387))^2

end BstLean.Part268.WorldRow12387
namespace BstLean.Part268.WorldRow12388
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12388 = 211594409160281 := by
  have hu : mW 12388 ≤ 211594409160281 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12388 ≤ 211594409160280 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12388)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24776 ^ 2)
    ((6250000000000000000/972951244816758965954159))
    ((1000000000000000000/155665915985374254965693)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24776) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24776 : ℝ)^2 / (mW 12388 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2088559/1000000000000))/2) * ((1-firstRatio 24776) * √(1-firstRatio 24776) *
      sixthConstant (e1CovarianceRatio 24776 (mW 12388) (1/10^6) rowEps))) /
    (712/10000 - 24776*(1+1/10^6)*((2088559/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24776 (mW 12388) /
    ((1/10^5) * ((mW 12388 : ℝ)*24776*((mW 12388 : ℝ)+24776+1)))^2 +
  8*(mW 12388 : ℝ)*24776*(24776+2)*(24776+3) /
    ((1/1000)*((mW 12388 : ℝ)*24776*(24776+2)))^2 +
  covarianceVarianceBound 24776 (mW 12388) /
    ((1/1000)*covarianceMeanBound 24776 (mW 12388))^2 +
  normVarianceBound 24776 (mW 12388) / (3*inputVarianceMean 24776 (mW 12388))^2

end BstLean.Part268.WorldRow12388
namespace BstLean.Part268.WorldRow12389
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12389 = 211654197274801 := by
  have hu : mW 12389 ≤ 211654197274801 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12389 ≤ 211654197274800 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12389)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24778 ^ 2)
    ((25000000000000000000/3892119138532394843140483))
    ((25000000000000000000/3891962058899715353466171)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24778) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24778 : ℝ)^2 / (mW 12389 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2088389/1000000000000))/2) * ((1-firstRatio 24778) * √(1-firstRatio 24778) *
      sixthConstant (e1CovarianceRatio 24778 (mW 12389) (1/10^6) rowEps))) /
    (712/10000 - 24778*(1+1/10^6)*((2088389/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24778 (mW 12389) /
    ((1/10^5) * ((mW 12389 : ℝ)*24778*((mW 12389 : ℝ)+24778+1)))^2 +
  8*(mW 12389 : ℝ)*24778*(24778+2)*(24778+3) /
    ((1/1000)*((mW 12389 : ℝ)*24778*(24778+2)))^2 +
  covarianceVarianceBound 24778 (mW 12389) /
    ((1/1000)*covarianceMeanBound 24778 (mW 12389))^2 +
  normVarianceBound 24778 (mW 12389) / (3*inputVarianceMean 24778 (mW 12389))^2

end BstLean.Part268.WorldRow12389
namespace BstLean.Part268.WorldRow12390
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12390 = 211713997455297 := by
  have hu : mW 12390 ≤ 211713997455297 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12390 ≤ 211713997455296 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12390)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24780 ^ 2)
    ((2500000000000000000/389243329779775382246433))
    ((25000000000000000000/3892276218165074332790017)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24780) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24780 : ℝ)^2 / (mW 12390 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2088219/1000000000000))/2) * ((1-firstRatio 24780) * √(1-firstRatio 24780) *
      sixthConstant (e1CovarianceRatio 24780 (mW 12390) (1/10^6) rowEps))) /
    (712/10000 - 24780*(1+1/10^6)*((2088219/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24780 (mW 12390) /
    ((1/10^5) * ((mW 12390 : ℝ)*24780*((mW 12390 : ℝ)+24780+1)))^2 +
  8*(mW 12390 : ℝ)*24780*(24780+2)*(24780+3) /
    ((1/1000)*((mW 12390 : ℝ)*24780*(24780+2)))^2 +
  covarianceVarianceBound 24780 (mW 12390) /
    ((1/1000)*covarianceMeanBound 24780 (mW 12390))^2 +
  normVarianceBound 24780 (mW 12390) / (3*inputVarianceMean 24780 (mW 12390))^2

end BstLean.Part268.WorldRow12390
namespace BstLean.Part268.WorldRow12391
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12391 = 211773809703229 := by
  have hu : mW 12391 ≤ 211773809703229 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12391 ≤ 211773809703228 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12391)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24782 ^ 2)
    ((25000000000000000000/3892747457063112801788177))
    ((25000000000000000000/3892590377430433312113863)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24782) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24782 : ℝ)^2 / (mW 12391 : ℝ)) * (1 + 1/10^6)^2 *
    √(((130503/62500000000))/2) * ((1-firstRatio 24782) * √(1-firstRatio 24782) *
      sixthConstant (e1CovarianceRatio 24782 (mW 12391) (1/10^6) rowEps))) /
    (712/10000 - 24782*(1+1/10^6)*((130503/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24782 (mW 12391) /
    ((1/10^5) * ((mW 12391 : ℝ)*24782*((mW 12391 : ℝ)+24782+1)))^2 +
  8*(mW 12391 : ℝ)*24782*(24782+2)*(24782+3) /
    ((1/1000)*((mW 12391 : ℝ)*24782*(24782+2)))^2 +
  covarianceVarianceBound 24782 (mW 12391) /
    ((1/1000)*covarianceMeanBound 24782 (mW 12391))^2 +
  normVarianceBound 24782 (mW 12391) / (3*inputVarianceMean 24782 (mW 12391))^2

end BstLean.Part268.WorldRow12391
namespace BstLean.Part268.WorldRow12392
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12392 = 211833634020058 := by
  have hu : mW 12392 ≤ 211833634020058 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12392 ≤ 211833634020057 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12392)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24784 ^ 2)
    ((3125000000000000000/486632702041058972639003))
    ((25000000000000000000/3892904536695792291437709)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24784) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24784 : ℝ)^2 / (mW 12392 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1043939/500000000000))/2) * ((1-firstRatio 24784) * √(1-firstRatio 24784) *
      sixthConstant (e1CovarianceRatio 24784 (mW 12392) (1/10^6) rowEps))) /
    (712/10000 - 24784*(1+1/10^6)*((1043939/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24784 (mW 12392) /
    ((1/10^5) * ((mW 12392 : ℝ)*24784*((mW 12392 : ℝ)+24784+1)))^2 +
  8*(mW 12392 : ℝ)*24784*(24784+2)*(24784+3) /
    ((1/1000)*((mW 12392 : ℝ)*24784*(24784+2)))^2 +
  covarianceVarianceBound 24784 (mW 12392) /
    ((1/1000)*covarianceMeanBound 24784 (mW 12392))^2 +
  normVarianceBound 24784 (mW 12392) / (3*inputVarianceMean 24784 (mW 12392))^2

end BstLean.Part268.WorldRow12392
namespace BstLean.Part268.WorldRow12393
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12393 = 211893470407246 := by
  have hu : mW 12393 ≤ 211893470407246 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12393 ≤ 211893470407245 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12393)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24786 ^ 2)
    ((25000000000000000000/3893375775593830760435871))
    ((5000000000000000000/778643739192230254152311)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24786) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24786 : ℝ)^2 / (mW 12393 : ℝ)) * (1 + 1/10^6)^2 *
    √(((521927/250000000000))/2) * ((1-firstRatio 24786) * √(1-firstRatio 24786) *
      sixthConstant (e1CovarianceRatio 24786 (mW 12393) (1/10^6) rowEps))) /
    (712/10000 - 24786*(1+1/10^6)*((521927/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24786 (mW 12393) /
    ((1/10^5) * ((mW 12393 : ℝ)*24786*((mW 12393 : ℝ)+24786+1)))^2 +
  8*(mW 12393 : ℝ)*24786*(24786+2)*(24786+3) /
    ((1/1000)*((mW 12393 : ℝ)*24786*(24786+2)))^2 +
  covarianceVarianceBound 24786 (mW 12393) /
    ((1/1000)*covarianceMeanBound 24786 (mW 12393))^2 +
  normVarianceBound 24786 (mW 12393) / (3*inputVarianceMean 24786 (mW 12393))^2

end BstLean.Part268.WorldRow12393
namespace BstLean.Part268.WorldRow12394
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12394 = 211953318866253 := by
  have hu : mW 12394 ≤ 211953318866253 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12394 ≤ 211953318866252 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12394)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24788 ^ 2)
    ((12500000000000000000/1946844967429594869879859))
    ((25000000000000000000/3893532855226510250085401)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24788) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24788 : ℝ)^2 / (mW 12394 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2087537/1000000000000))/2) * ((1-firstRatio 24788) * √(1-firstRatio 24788) *
      sixthConstant (e1CovarianceRatio 24788 (mW 12394) (1/10^6) rowEps))) /
    (712/10000 - 24788*(1+1/10^6)*((2087537/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24788 (mW 12394) /
    ((1/10^5) * ((mW 12394 : ℝ)*24788*((mW 12394 : ℝ)+24788+1)))^2 +
  8*(mW 12394 : ℝ)*24788*(24788+2)*(24788+3) /
    ((1/1000)*((mW 12394 : ℝ)*24788*(24788+2)))^2 +
  covarianceVarianceBound 24788 (mW 12394) /
    ((1/1000)*covarianceMeanBound 24788 (mW 12394))^2 +
  normVarianceBound 24788 (mW 12394) / (3*inputVarianceMean 24788 (mW 12394))^2

end BstLean.Part268.WorldRow12394
namespace BstLean.Part268.WorldRow12395
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12395 = 212013179398540 := by
  have hu : mW 12395 ≤ 212013179398540 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12395 ≤ 212013179398539 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12395)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24790 ^ 2)
    ((5000000000000000000/778800818824909743816713))
    ((25000000000000000000/3893847014491869229409247)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24790) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24790 : ℝ)^2 / (mW 12395 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2087367/1000000000000))/2) * ((1-firstRatio 24790) * √(1-firstRatio 24790) *
      sixthConstant (e1CovarianceRatio 24790 (mW 12395) (1/10^6) rowEps))) /
    (712/10000 - 24790*(1+1/10^6)*((2087367/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24790 (mW 12395) /
    ((1/10^5) * ((mW 12395 : ℝ)*24790*((mW 12395 : ℝ)+24790+1)))^2 +
  8*(mW 12395 : ℝ)*24790*(24790+2)*(24790+3) /
    ((1/1000)*((mW 12395 : ℝ)*24790*(24790+2)))^2 +
  covarianceVarianceBound 24790 (mW 12395) /
    ((1/1000)*covarianceMeanBound 24790 (mW 12395))^2 +
  normVarianceBound 24790 (mW 12395) / (3*inputVarianceMean 24790 (mW 12395))^2

end BstLean.Part268.WorldRow12395
namespace BstLean.Part268.WorldRow12396
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12396 = 212073052005569 := by
  have hu : mW 12396 ≤ 212073052005569 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12396 ≤ 212073052005568 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12396)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24792 ^ 2)
    ((6250000000000000000/973579563347476924601853))
    ((25000000000000000000/3894161173757228208733093)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24792) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24792 : ℝ)^2 / (mW 12396 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2087197/1000000000000))/2) * ((1-firstRatio 24792) * √(1-firstRatio 24792) *
      sixthConstant (e1CovarianceRatio 24792 (mW 12396) (1/10^6) rowEps))) /
    (712/10000 - 24792*(1+1/10^6)*((2087197/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24792 (mW 12396) /
    ((1/10^5) * ((mW 12396 : ℝ)*24792*((mW 12396 : ℝ)+24792+1)))^2 +
  8*(mW 12396 : ℝ)*24792*(24792+2)*(24792+3) /
    ((1/1000)*((mW 12396 : ℝ)*24792*(24792+2)))^2 +
  covarianceVarianceBound 24792 (mW 12396) /
    ((1/1000)*covarianceMeanBound 24792 (mW 12396))^2 +
  normVarianceBound 24792 (mW 12396) / (3*inputVarianceMean 24792 (mW 12396))^2

end BstLean.Part268.WorldRow12396
namespace BstLean.Part268.WorldRow12397
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12397 = 212132936688801 := by
  have hu : mW 12397 ≤ 212132936688801 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12397 ≤ 212132936688800 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12397)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24794 ^ 2)
    ((25000000000000000000/3894632412655266677731259))
    ((25000000000000000000/3894475333022587188056939)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24794) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24794 : ℝ)^2 / (mW 12397 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2087027/1000000000000))/2) * ((1-firstRatio 24794) * √(1-firstRatio 24794) *
      sixthConstant (e1CovarianceRatio 24794 (mW 12397) (1/10^6) rowEps))) /
    (712/10000 - 24794*(1+1/10^6)*((2087027/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24794 (mW 12397) /
    ((1/10^5) * ((mW 12397 : ℝ)*24794*((mW 12397 : ℝ)+24794+1)))^2 +
  8*(mW 12397 : ℝ)*24794*(24794+2)*(24794+3) /
    ((1/1000)*((mW 12397 : ℝ)*24794*(24794+2)))^2 +
  covarianceVarianceBound 24794 (mW 12397) /
    ((1/1000)*covarianceMeanBound 24794 (mW 12397))^2 +
  normVarianceBound 24794 (mW 12397) / (3*inputVarianceMean 24794 (mW 12397))^2

end BstLean.Part268.WorldRow12397
namespace BstLean.Part268.WorldRow12398
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12398 = 212192833449698 := by
  have hu : mW 12398 ≤ 212192833449698 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12398 ≤ 212192833449697 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12398)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24796 ^ 2)
    ((12500000000000000000/1947473285960312828527553))
    ((5000000000000000000/778957898457589233476157)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24796) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24796 : ℝ)^2 / (mW 12398 : ℝ)) * (1 + 1/10^6)^2 *
    √(((260857/125000000000))/2) * ((1-firstRatio 24796) * √(1-firstRatio 24796) *
      sixthConstant (e1CovarianceRatio 24796 (mW 12398) (1/10^6) rowEps))) /
    (712/10000 - 24796*(1+1/10^6)*((260857/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24796 (mW 12398) /
    ((1/10^5) * ((mW 12398 : ℝ)*24796*((mW 12398 : ℝ)+24796+1)))^2 +
  8*(mW 12398 : ℝ)*24796*(24796+2)*(24796+3) /
    ((1/1000)*((mW 12398 : ℝ)*24796*(24796+2)))^2 +
  covarianceVarianceBound 24796 (mW 12398) /
    ((1/1000)*covarianceMeanBound 24796 (mW 12398))^2 +
  normVarianceBound 24796 (mW 12398) / (3*inputVarianceMean 24796 (mW 12398))^2

end BstLean.Part268.WorldRow12398
namespace BstLean.Part268.WorldRow12399
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12399 = 212252742289720 := by
  have hu : mW 12399 ≤ 212252742289720 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12399 ≤ 212252742289719 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12399)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24798 ^ 2)
    ((25000000000000000000/3895260731185984636378953))
    ((25000000000000000000/3895103651553305146704631)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24798) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24798 : ℝ)^2 / (mW 12399 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1043343/500000000000))/2) * ((1-firstRatio 24798) * √(1-firstRatio 24798) *
      sixthConstant (e1CovarianceRatio 24798 (mW 12399) (1/10^6) rowEps))) /
    (712/10000 - 24798*(1+1/10^6)*((1043343/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24798 (mW 12399) /
    ((1/10^5) * ((mW 12399 : ℝ)*24798*((mW 12399 : ℝ)+24798+1)))^2 +
  8*(mW 12399 : ℝ)*24798*(24798+2)*(24798+3) /
    ((1/1000)*((mW 12399 : ℝ)*24798*(24798+2)))^2 +
  covarianceVarianceBound 24798 (mW 12399) /
    ((1/1000)*covarianceMeanBound 24798 (mW 12399))^2 +
  normVarianceBound 24798 (mW 12399) / (3*inputVarianceMean 24798 (mW 12399))^2

end BstLean.Part268.WorldRow12399
