import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar23
namespace BstLean.Part268.WorldRow12925
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12925 = 245474809225325 := by
  have hu : mW 12925 ≤ 245474809225325 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12925 ≤ 245474809225324 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12925)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25850 ^ 2)
    ((1000000000000000000/162420340190592310428899))
    ((25000000000000000000/4060351425132128271047627)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25850) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25850 : ℝ)^2 / (mW 12925 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2000893/1000000000000))/2) * ((1-firstRatio 25850) * √(1-firstRatio 25850) *
      sixthConstant (e1CovarianceRatio 25850 (mW 12925) (1/10^6) rowEps))) /
    (712/10000 - 25850*(1+1/10^6)*((2000893/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25850 (mW 12925) /
    ((1/10^5) * ((mW 12925 : ℝ)*25850*((mW 12925 : ℝ)+25850+1)))^2 +
  8*(mW 12925 : ℝ)*25850*(25850+2)*(25850+3) /
    ((1/1000)*((mW 12925 : ℝ)*25850*(25850+2)))^2 +
  covarianceVarianceBound 25850 (mW 12925) /
    ((1/1000)*covarianceMeanBound 25850 (mW 12925))^2 +
  normVarianceBound 25850 (mW 12925) / (3*inputVarianceMean 25850 (mW 12925))^2

end BstLean.Part268.WorldRow12925
namespace BstLean.Part268.WorldRow12926
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12926 = 245541288523320 := by
  have hu : mW 12926 ≤ 245541288523320 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12926 ≤ 245541288523319 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12926)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25852 ^ 2)
    ((12500000000000000000/2030411332015083370023161))
    ((25000000000000000000/4060665584397487250371473)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25852) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25852 : ℝ)^2 / (mW 12926 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2000737/1000000000000))/2) * ((1-firstRatio 25852) * √(1-firstRatio 25852) *
      sixthConstant (e1CovarianceRatio 25852 (mW 12926) (1/10^6) rowEps))) /
    (712/10000 - 25852*(1+1/10^6)*((2000737/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25852 (mW 12926) /
    ((1/10^5) * ((mW 12926 : ℝ)*25852*((mW 12926 : ℝ)+25852+1)))^2 +
  8*(mW 12926 : ℝ)*25852*(25852+2)*(25852+3) /
    ((1/1000)*((mW 12926 : ℝ)*25852*(25852+2)))^2 +
  covarianceVarianceBound 25852 (mW 12926) /
    ((1/1000)*covarianceMeanBound 25852 (mW 12926))^2 +
  normVarianceBound 25852 (mW 12926) / (3*inputVarianceMean 25852 (mW 12926))^2

end BstLean.Part268.WorldRow12926
namespace BstLean.Part268.WorldRow12927
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12927 = 245607780680229 := by
  have hu : mW 12927 ≤ 245607780680229 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12927 ≤ 245607780680228 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12927)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25854 ^ 2)
    ((25000000000000000000/4061136823295525719370169))
    ((25000000000000000000/4060979743662846229695319)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25854) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25854 : ℝ)^2 / (mW 12927 : ℝ)) * (1 + 1/10^6)^2 *
    √(((100029/50000000000))/2) * ((1-firstRatio 25854) * √(1-firstRatio 25854) *
      sixthConstant (e1CovarianceRatio 25854 (mW 12927) (1/10^6) rowEps))) /
    (712/10000 - 25854*(1+1/10^6)*((100029/50000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25854 (mW 12927) /
    ((1/10^5) * ((mW 12927 : ℝ)*25854*((mW 12927 : ℝ)+25854+1)))^2 +
  8*(mW 12927 : ℝ)*25854*(25854+2)*(25854+3) /
    ((1/1000)*((mW 12927 : ℝ)*25854*(25854+2)))^2 +
  covarianceVarianceBound 25854 (mW 12927) /
    ((1/1000)*covarianceMeanBound 25854 (mW 12927))^2 +
  normVarianceBound 25854 (mW 12927) / (3*inputVarianceMean 25854 (mW 12927))^2

end BstLean.Part268.WorldRow12927
namespace BstLean.Part268.WorldRow12928
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12928 = 245674285697544 := by
  have hu : mW 12928 ≤ 245674285697544 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12928 ≤ 245674285697543 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12928)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25856 ^ 2)
    ((195312500000000000/31730085801256911708547))
    ((5000000000000000000/812258780585641041803833)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25856) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25856 : ℝ)^2 / (mW 12928 : ℝ)) * (1 + 1/10^6)^2 *
    √(((250053/125000000000))/2) * ((1-firstRatio 25856) * √(1-firstRatio 25856) *
      sixthConstant (e1CovarianceRatio 25856 (mW 12928) (1/10^6) rowEps))) /
    (712/10000 - 25856*(1+1/10^6)*((250053/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25856 (mW 12928) /
    ((1/10^5) * ((mW 12928 : ℝ)*25856*((mW 12928 : ℝ)+25856+1)))^2 +
  8*(mW 12928 : ℝ)*25856*(25856+2)*(25856+3) /
    ((1/1000)*((mW 12928 : ℝ)*25856*(25856+2)))^2 +
  covarianceVarianceBound 25856 (mW 12928) /
    ((1/1000)*covarianceMeanBound 25856 (mW 12928))^2 +
  normVarianceBound 25856 (mW 12928) / (3*inputVarianceMean 25856 (mW 12928))^2

end BstLean.Part268.WorldRow12928
namespace BstLean.Part268.WorldRow12929
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12929 = 245740803576757 := by
  have hu : mW 12929 ≤ 245740803576757 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12929 ≤ 245740803576756 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12929)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25858 ^ 2)
    ((25000000000000000000/4061765141826243678017863))
    ((25000000000000000000/4061608062193564188343011)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25858) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25858 : ℝ)^2 / (mW 12929 : ℝ)) * (1 + 1/10^6)^2 *
    √(((500067/250000000000))/2) * ((1-firstRatio 25858) * √(1-firstRatio 25858) *
      sixthConstant (e1CovarianceRatio 25858 (mW 12929) (1/10^6) rowEps))) /
    (712/10000 - 25858*(1+1/10^6)*((500067/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25858 (mW 12929) /
    ((1/10^5) * ((mW 12929 : ℝ)*25858*((mW 12929 : ℝ)+25858+1)))^2 +
  8*(mW 12929 : ℝ)*25858*(25858+2)*(25858+3) /
    ((1/1000)*((mW 12929 : ℝ)*25858*(25858+2)))^2 +
  covarianceVarianceBound 25858 (mW 12929) /
    ((1/1000)*covarianceMeanBound 25858 (mW 12929))^2 +
  normVarianceBound 25858 (mW 12929) / (3*inputVarianceMean 25858 (mW 12929))^2

end BstLean.Part268.WorldRow12929
namespace BstLean.Part268.WorldRow12930
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12930 = 245807334319361 := by
  have hu : mW 12930 ≤ 245807334319361 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12930 ≤ 245807334319360 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12930)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25860 ^ 2)
    ((2500000000000000000/406207930109160265734171))
    ((25000000000000000000/4061922221458923167666857)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25860) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25860 : ℝ)^2 / (mW 12930 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2000111/1000000000000))/2) * ((1-firstRatio 25860) * √(1-firstRatio 25860) *
      sixthConstant (e1CovarianceRatio 25860 (mW 12930) (1/10^6) rowEps))) /
    (712/10000 - 25860*(1+1/10^6)*((2000111/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25860 (mW 12930) /
    ((1/10^5) * ((mW 12930 : ℝ)*25860*((mW 12930 : ℝ)+25860+1)))^2 +
  8*(mW 12930 : ℝ)*25860*(25860+2)*(25860+3) /
    ((1/1000)*((mW 12930 : ℝ)*25860*(25860+2)))^2 +
  covarianceVarianceBound 25860 (mW 12930) /
    ((1/1000)*covarianceMeanBound 25860 (mW 12930))^2 +
  normVarianceBound 25860 (mW 12930) / (3*inputVarianceMean 25860 (mW 12930))^2

end BstLean.Part268.WorldRow12930
namespace BstLean.Part268.WorldRow12931
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12931 = 245873877926848 := by
  have hu : mW 12931 ≤ 245873877926848 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12931 ≤ 245873877926847 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12931)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25862 ^ 2)
    ((25000000000000000000/4062393460356961636665557))
    ((25000000000000000000/4062236380724282146990703)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25862) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25862 : ℝ)^2 / (mW 12931 : ℝ)) * (1 + 1/10^6)^2 *
    √(((399991/200000000000))/2) * ((1-firstRatio 25862) * √(1-firstRatio 25862) *
      sixthConstant (e1CovarianceRatio 25862 (mW 12931) (1/10^6) rowEps))) /
    (712/10000 - 25862*(1+1/10^6)*((399991/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25862 (mW 12931) /
    ((1/10^5) * ((mW 12931 : ℝ)*25862*((mW 12931 : ℝ)+25862+1)))^2 +
  8*(mW 12931 : ℝ)*25862*(25862+2)*(25862+3) /
    ((1/1000)*((mW 12931 : ℝ)*25862*(25862+2)))^2 +
  covarianceVarianceBound 25862 (mW 12931) /
    ((1/1000)*covarianceMeanBound 25862 (mW 12931))^2 +
  normVarianceBound 25862 (mW 12931) / (3*inputVarianceMean 25862 (mW 12931))^2

end BstLean.Part268.WorldRow12931
namespace BstLean.Part268.WorldRow12932
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12932 = 245940434400710 := by
  have hu : mW 12932 ≤ 245940434400710 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12932 ≤ 245940434400709 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12932)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25864 ^ 2)
    ((6250000000000000000/1015676904905580153997351))
    ((25000000000000000000/4062550539989641126314549)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25864) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25864 : ℝ)^2 / (mW 12932 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1999799/1000000000000))/2) * ((1-firstRatio 25864) * √(1-firstRatio 25864) *
      sixthConstant (e1CovarianceRatio 25864 (mW 12932) (1/10^6) rowEps))) /
    (712/10000 - 25864*(1+1/10^6)*((1999799/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25864 (mW 12932) /
    ((1/10^5) * ((mW 12932 : ℝ)*25864*((mW 12932 : ℝ)+25864+1)))^2 +
  8*(mW 12932 : ℝ)*25864*(25864+2)*(25864+3) /
    ((1/1000)*((mW 12932 : ℝ)*25864*(25864+2)))^2 +
  covarianceVarianceBound 25864 (mW 12932) /
    ((1/1000)*covarianceMeanBound 25864 (mW 12932))^2 +
  normVarianceBound 25864 (mW 12932) / (3*inputVarianceMean 25864 (mW 12932))^2

end BstLean.Part268.WorldRow12932
namespace BstLean.Part268.WorldRow12933
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12933 = 246007003742440 := by
  have hu : mW 12933 ≤ 246007003742440 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12933 ≤ 246007003742439 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12933)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25866 ^ 2)
    ((25000000000000000000/4063021778887679595313251))
    ((5000000000000000000/812572939851000021127679)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25866) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25866 : ℝ)^2 / (mW 12933 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1999643/1000000000000))/2) * ((1-firstRatio 25866) * √(1-firstRatio 25866) *
      sixthConstant (e1CovarianceRatio 25866 (mW 12933) (1/10^6) rowEps))) /
    (712/10000 - 25866*(1+1/10^6)*((1999643/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25866 (mW 12933) /
    ((1/10^5) * ((mW 12933 : ℝ)*25866*((mW 12933 : ℝ)+25866+1)))^2 +
  8*(mW 12933 : ℝ)*25866*(25866+2)*(25866+3) /
    ((1/1000)*((mW 12933 : ℝ)*25866*(25866+2)))^2 +
  covarianceVarianceBound 25866 (mW 12933) /
    ((1/1000)*covarianceMeanBound 25866 (mW 12933))^2 +
  normVarianceBound 25866 (mW 12933) / (3*inputVarianceMean 25866 (mW 12933))^2

end BstLean.Part268.WorldRow12933
namespace BstLean.Part268.WorldRow12934
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12934 = 246073585953531 := by
  have hu : mW 12934 ≤ 246073585953531 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12934 ≤ 246073585953530 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12934)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25868 ^ 2)
    ((12500000000000000000/2031667969076519287318549))
    ((25000000000000000000/4063178858520359084962241)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25868) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25868 : ℝ)^2 / (mW 12934 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1999487/1000000000000))/2) * ((1-firstRatio 25868) * √(1-firstRatio 25868) *
      sixthConstant (e1CovarianceRatio 25868 (mW 12934) (1/10^6) rowEps))) /
    (712/10000 - 25868*(1+1/10^6)*((1999487/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25868 (mW 12934) /
    ((1/10^5) * ((mW 12934 : ℝ)*25868*((mW 12934 : ℝ)+25868+1)))^2 +
  8*(mW 12934 : ℝ)*25868*(25868+2)*(25868+3) /
    ((1/1000)*((mW 12934 : ℝ)*25868*(25868+2)))^2 +
  covarianceVarianceBound 25868 (mW 12934) /
    ((1/1000)*covarianceMeanBound 25868 (mW 12934))^2 +
  normVarianceBound 25868 (mW 12934) / (3*inputVarianceMean 25868 (mW 12934))^2

end BstLean.Part268.WorldRow12934
namespace BstLean.Part268.WorldRow12935
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12935 = 246140181035475 := by
  have hu : mW 12935 ≤ 246140181035475 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12935 ≤ 246140181035474 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12935)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25870 ^ 2)
    ((5000000000000000000/812730019483679510792189))
    ((25000000000000000000/4063493017785718064286087)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25870) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25870 : ℝ)^2 / (mW 12935 : ℝ)) * (1 + 1/10^6)^2 *
    √(((199933/100000000000))/2) * ((1-firstRatio 25870) * √(1-firstRatio 25870) *
      sixthConstant (e1CovarianceRatio 25870 (mW 12935) (1/10^6) rowEps))) /
    (712/10000 - 25870*(1+1/10^6)*((199933/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25870 (mW 12935) /
    ((1/10^5) * ((mW 12935 : ℝ)*25870*((mW 12935 : ℝ)+25870+1)))^2 +
  8*(mW 12935 : ℝ)*25870*(25870+2)*(25870+3) /
    ((1/1000)*((mW 12935 : ℝ)*25870*(25870+2)))^2 +
  covarianceVarianceBound 25870 (mW 12935) /
    ((1/1000)*covarianceMeanBound 25870 (mW 12935))^2 +
  normVarianceBound 25870 (mW 12935) / (3*inputVarianceMean 25870 (mW 12935))^2

end BstLean.Part268.WorldRow12935
namespace BstLean.Part268.WorldRow12936
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12936 = 246206788989764 := by
  have hu : mW 12936 ≤ 246206788989764 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12936 ≤ 246206788989763 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12936)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25872 ^ 2)
    ((3125000000000000000/507995532085469566660599))
    ((25000000000000000000/4063807177051077043609933)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25872) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25872 : ℝ)^2 / (mW 12936 : ℝ)) * (1 + 1/10^6)^2 *
    √(((999587/500000000000))/2) * ((1-firstRatio 25872) * √(1-firstRatio 25872) *
      sixthConstant (e1CovarianceRatio 25872 (mW 12936) (1/10^6) rowEps))) /
    (712/10000 - 25872*(1+1/10^6)*((999587/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25872 (mW 12936) /
    ((1/10^5) * ((mW 12936 : ℝ)*25872*((mW 12936 : ℝ)+25872+1)))^2 +
  8*(mW 12936 : ℝ)*25872*(25872+2)*(25872+3) /
    ((1/1000)*((mW 12936 : ℝ)*25872*(25872+2)))^2 +
  covarianceVarianceBound 25872 (mW 12936) /
    ((1/1000)*covarianceMeanBound 25872 (mW 12936))^2 +
  normVarianceBound 25872 (mW 12936) / (3*inputVarianceMean 25872 (mW 12936))^2

end BstLean.Part268.WorldRow12936
namespace BstLean.Part268.WorldRow12937
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12937 = 246273409817893 := by
  have hu : mW 12937 ≤ 246273409817893 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12937 ≤ 246273409817892 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12937)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25874 ^ 2)
    ((25000000000000000000/4064278415949115512608639))
    ((25000000000000000000/4064121336316436022933779)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25874) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25874 : ℝ)^2 / (mW 12937 : ℝ)) * (1 + 1/10^6)^2 *
    √(((999509/500000000000))/2) * ((1-firstRatio 25874) * √(1-firstRatio 25874) *
      sixthConstant (e1CovarianceRatio 25874 (mW 12937) (1/10^6) rowEps))) /
    (712/10000 - 25874*(1+1/10^6)*((999509/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25874 (mW 12937) /
    ((1/10^5) * ((mW 12937 : ℝ)*25874*((mW 12937 : ℝ)+25874+1)))^2 +
  8*(mW 12937 : ℝ)*25874*(25874+2)*(25874+3) /
    ((1/1000)*((mW 12937 : ℝ)*25874*(25874+2)))^2 +
  covarianceVarianceBound 25874 (mW 12937) /
    ((1/1000)*covarianceMeanBound 25874 (mW 12937))^2 +
  normVarianceBound 25874 (mW 12937) / (3*inputVarianceMean 25874 (mW 12937))^2

end BstLean.Part268.WorldRow12937
namespace BstLean.Part268.WorldRow12938
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12938 = 246340043521353 := by
  have hu : mW 12938 ≤ 246340043521353 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12938 ≤ 246340043521352 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12938)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25876 ^ 2)
    ((12500000000000000000/2032296287607237245966243))
    ((200000000000000000/32515483964654360018061)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25876) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25876 : ℝ)^2 / (mW 12938 : ℝ)) * (1 + 1/10^6)^2 *
    √(((999431/500000000000))/2) * ((1-firstRatio 25876) * √(1-firstRatio 25876) *
      sixthConstant (e1CovarianceRatio 25876 (mW 12938) (1/10^6) rowEps))) /
    (712/10000 - 25876*(1+1/10^6)*((999431/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25876 (mW 12938) /
    ((1/10^5) * ((mW 12938 : ℝ)*25876*((mW 12938 : ℝ)+25876+1)))^2 +
  8*(mW 12938 : ℝ)*25876*(25876+2)*(25876+3) /
    ((1/1000)*((mW 12938 : ℝ)*25876*(25876+2)))^2 +
  covarianceVarianceBound 25876 (mW 12938) /
    ((1/1000)*covarianceMeanBound 25876 (mW 12938))^2 +
  normVarianceBound 25876 (mW 12938) / (3*inputVarianceMean 25876 (mW 12938))^2

end BstLean.Part268.WorldRow12938
namespace BstLean.Part268.WorldRow12939
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12939 = 246406690101638 := by
  have hu : mW 12939 ≤ 246406690101638 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12939 ≤ 246406690101637 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12939)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25878 ^ 2)
    ((25000000000000000000/4064906734479833471256333))
    ((25000000000000000000/4064749654847153981581471)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25878) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25878 : ℝ)^2 / (mW 12939 : ℝ)) * (1 + 1/10^6)^2 *
    √(((999353/500000000000))/2) * ((1-firstRatio 25878) * √(1-firstRatio 25878) *
      sixthConstant (e1CovarianceRatio 25878 (mW 12939) (1/10^6) rowEps))) /
    (712/10000 - 25878*(1+1/10^6)*((999353/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25878 (mW 12939) /
    ((1/10^5) * ((mW 12939 : ℝ)*25878*((mW 12939 : ℝ)+25878+1)))^2 +
  8*(mW 12939 : ℝ)*25878*(25878+2)*(25878+3) /
    ((1/1000)*((mW 12939 : ℝ)*25878*(25878+2)))^2 +
  covarianceVarianceBound 25878 (mW 12939) /
    ((1/1000)*covarianceMeanBound 25878 (mW 12939))^2 +
  normVarianceBound 25878 (mW 12939) / (3*inputVarianceMean 25878 (mW 12939))^2

end BstLean.Part268.WorldRow12939
namespace BstLean.Part268.WorldRow12940
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12940 = 246473349560239 := by
  have hu : mW 12940 ≤ 246473349560239 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12940 ≤ 246473349560238 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12940)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25880 ^ 2)
    ((1250000000000000000/203261044687259622529009))
    ((25000000000000000000/4065063814112512960905317)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25880) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25880 : ℝ)^2 / (mW 12940 : ℝ)) * (1 + 1/10^6)^2 *
    √(((39971/20000000000))/2) * ((1-firstRatio 25880) * √(1-firstRatio 25880) *
      sixthConstant (e1CovarianceRatio 25880 (mW 12940) (1/10^6) rowEps))) /
    (712/10000 - 25880*(1+1/10^6)*((39971/20000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25880 (mW 12940) /
    ((1/10^5) * ((mW 12940 : ℝ)*25880*((mW 12940 : ℝ)+25880+1)))^2 +
  8*(mW 12940 : ℝ)*25880*(25880+2)*(25880+3) /
    ((1/1000)*((mW 12940 : ℝ)*25880*(25880+2)))^2 +
  covarianceVarianceBound 25880 (mW 12940) /
    ((1/1000)*covarianceMeanBound 25880 (mW 12940))^2 +
  normVarianceBound 25880 (mW 12940) / (3*inputVarianceMean 25880 (mW 12940))^2

end BstLean.Part268.WorldRow12940
namespace BstLean.Part268.WorldRow12941
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12941 = 246540021898652 := by
  have hu : mW 12941 ≤ 246540021898652 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12941 ≤ 246540021898651 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12941)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25882 ^ 2)
    ((25000000000000000000/4065535053010551429904027))
    ((25000000000000000000/4065377973377871940229163)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25882) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25882 : ℝ)^2 / (mW 12941 : ℝ)) * (1 + 1/10^6)^2 *
    √(((999197/500000000000))/2) * ((1-firstRatio 25882) * √(1-firstRatio 25882) *
      sixthConstant (e1CovarianceRatio 25882 (mW 12941) (1/10^6) rowEps))) /
    (712/10000 - 25882*(1+1/10^6)*((999197/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25882 (mW 12941) /
    ((1/10^5) * ((mW 12941 : ℝ)*25882*((mW 12941 : ℝ)+25882+1)))^2 +
  8*(mW 12941 : ℝ)*25882*(25882+2)*(25882+3) /
    ((1/1000)*((mW 12941 : ℝ)*25882*(25882+2)))^2 +
  covarianceVarianceBound 25882 (mW 12941) /
    ((1/1000)*covarianceMeanBound 25882 (mW 12941))^2 +
  normVarianceBound 25882 (mW 12941) / (3*inputVarianceMean 25882 (mW 12941))^2

end BstLean.Part268.WorldRow12941
namespace BstLean.Part268.WorldRow12942
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12942 = 246606707118367 := by
  have hu : mW 12942 ≤ 246606707118367 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12942 ≤ 246606707118366 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12942)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25884 ^ 2)
    ((12500000000000000000/2032924606137955204613937))
    ((25000000000000000000/4065692132643230919553009)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25884) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25884 : ℝ)^2 / (mW 12942 : ℝ)) * (1 + 1/10^6)^2 *
    √(((999119/500000000000))/2) * ((1-firstRatio 25884) * √(1-firstRatio 25884) *
      sixthConstant (e1CovarianceRatio 25884 (mW 12942) (1/10^6) rowEps))) /
    (712/10000 - 25884*(1+1/10^6)*((999119/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25884 (mW 12942) /
    ((1/10^5) * ((mW 12942 : ℝ)*25884*((mW 12942 : ℝ)+25884+1)))^2 +
  8*(mW 12942 : ℝ)*25884*(25884+2)*(25884+3) /
    ((1/1000)*((mW 12942 : ℝ)*25884*(25884+2)))^2 +
  covarianceVarianceBound 25884 (mW 12942) /
    ((1/1000)*covarianceMeanBound 25884 (mW 12942))^2 +
  normVarianceBound 25884 (mW 12942) / (3*inputVarianceMean 25884 (mW 12942))^2

end BstLean.Part268.WorldRow12942
namespace BstLean.Part268.WorldRow12943
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12943 = 246673405220879 := by
  have hu : mW 12943 ≤ 246673405220879 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12943 ≤ 246673405220878 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12943)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25886 ^ 2)
    ((25000000000000000000/4066163371541269388551721))
    ((5000000000000000000/813201258381717979775371)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25886) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25886 : ℝ)^2 / (mW 12943 : ℝ)) * (1 + 1/10^6)^2 *
    √(((999041/500000000000))/2) * ((1-firstRatio 25886) * √(1-firstRatio 25886) *
      sixthConstant (e1CovarianceRatio 25886 (mW 12943) (1/10^6) rowEps))) /
    (712/10000 - 25886*(1+1/10^6)*((999041/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25886 (mW 12943) /
    ((1/10^5) * ((mW 12943 : ℝ)*25886*((mW 12943 : ℝ)+25886+1)))^2 +
  8*(mW 12943 : ℝ)*25886*(25886+2)*(25886+3) /
    ((1/1000)*((mW 12943 : ℝ)*25886*(25886+2)))^2 +
  covarianceVarianceBound 25886 (mW 12943) /
    ((1/1000)*covarianceMeanBound 25886 (mW 12943))^2 +
  normVarianceBound 25886 (mW 12943) / (3*inputVarianceMean 25886 (mW 12943))^2

end BstLean.Part268.WorldRow12943
namespace BstLean.Part268.WorldRow12944
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12944 = 246740116207681 := by
  have hu : mW 12944 ≤ 246740116207681 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12944 ≤ 246740116207680 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12944)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25888 ^ 2)
    ((1562500000000000000/254154845675414272992223))
    ((25000000000000000000/4066320451173948878200701)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25888) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25888 : ℝ)^2 / (mW 12944 : ℝ)) * (1 + 1/10^6)^2 *
    √(((998963/500000000000))/2) * ((1-firstRatio 25888) * √(1-firstRatio 25888) *
      sixthConstant (e1CovarianceRatio 25888 (mW 12944) (1/10^6) rowEps))) /
    (712/10000 - 25888*(1+1/10^6)*((998963/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25888 (mW 12944) /
    ((1/10^5) * ((mW 12944 : ℝ)*25888*((mW 12944 : ℝ)+25888+1)))^2 +
  8*(mW 12944 : ℝ)*25888*(25888+2)*(25888+3) /
    ((1/1000)*((mW 12944 : ℝ)*25888*(25888+2)))^2 +
  covarianceVarianceBound 25888 (mW 12944) /
    ((1/1000)*covarianceMeanBound 25888 (mW 12944))^2 +
  normVarianceBound 25888 (mW 12944) / (3*inputVarianceMean 25888 (mW 12944))^2

end BstLean.Part268.WorldRow12944
namespace BstLean.Part268.WorldRow12945
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12945 = 246806840080266 := by
  have hu : mW 12945 ≤ 246806840080266 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12945 ≤ 246806840080265 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12945)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25890 ^ 2)
    ((5000000000000000000/813358338014397469439883))
    ((25000000000000000000/4066634610439307857524547)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25890) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25890 : ℝ)^2 / (mW 12945 : ℝ)) * (1 + 1/10^6)^2 *
    √(((199777/100000000000))/2) * ((1-firstRatio 25890) * √(1-firstRatio 25890) *
      sixthConstant (e1CovarianceRatio 25890 (mW 12945) (1/10^6) rowEps))) /
    (712/10000 - 25890*(1+1/10^6)*((199777/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25890 (mW 12945) /
    ((1/10^5) * ((mW 12945 : ℝ)*25890*((mW 12945 : ℝ)+25890+1)))^2 +
  8*(mW 12945 : ℝ)*25890*(25890+2)*(25890+3) /
    ((1/1000)*((mW 12945 : ℝ)*25890*(25890+2)))^2 +
  covarianceVarianceBound 25890 (mW 12945) /
    ((1/1000)*covarianceMeanBound 25890 (mW 12945))^2 +
  normVarianceBound 25890 (mW 12945) / (3*inputVarianceMean 25890 (mW 12945))^2

end BstLean.Part268.WorldRow12945
namespace BstLean.Part268.WorldRow12946
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12946 = 246873576840126 := by
  have hu : mW 12946 ≤ 246873576840126 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12946 ≤ 246873576840125 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12946)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25892 ^ 2)
    ((12500000000000000000/2033552924668673163261631))
    ((25000000000000000000/4066948769704666836848393)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25892) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25892 : ℝ)^2 / (mW 12946 : ℝ)) * (1 + 1/10^6)^2 *
    √(((998807/500000000000))/2) * ((1-firstRatio 25892) * √(1-firstRatio 25892) *
      sixthConstant (e1CovarianceRatio 25892 (mW 12946) (1/10^6) rowEps))) /
    (712/10000 - 25892*(1+1/10^6)*((998807/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25892 (mW 12946) /
    ((1/10^5) * ((mW 12946 : ℝ)*25892*((mW 12946 : ℝ)+25892+1)))^2 +
  8*(mW 12946 : ℝ)*25892*(25892+2)*(25892+3) /
    ((1/1000)*((mW 12946 : ℝ)*25892*(25892+2)))^2 +
  covarianceVarianceBound 25892 (mW 12946) /
    ((1/1000)*covarianceMeanBound 25892 (mW 12946))^2 +
  normVarianceBound 25892 (mW 12946) / (3*inputVarianceMean 25892 (mW 12946))^2

end BstLean.Part268.WorldRow12946
namespace BstLean.Part268.WorldRow12947
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12947 = 246940326488757 := by
  have hu : mW 12947 ≤ 246940326488757 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12947 ≤ 246940326488756 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12947)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25894 ^ 2)
    ((25000000000000000000/4067420008602705305847109))
    ((25000000000000000000/4067262928970025816172239)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25894) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25894 : ℝ)^2 / (mW 12947 : ℝ)) * (1 + 1/10^6)^2 *
    √(((998729/500000000000))/2) * ((1-firstRatio 25894) * √(1-firstRatio 25894) *
      sixthConstant (e1CovarianceRatio 25894 (mW 12947) (1/10^6) rowEps))) /
    (712/10000 - 25894*(1+1/10^6)*((998729/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25894 (mW 12947) /
    ((1/10^5) * ((mW 12947 : ℝ)*25894*((mW 12947 : ℝ)+25894+1)))^2 +
  8*(mW 12947 : ℝ)*25894*(25894+2)*(25894+3) /
    ((1/1000)*((mW 12947 : ℝ)*25894*(25894+2)))^2 +
  covarianceVarianceBound 25894 (mW 12947) /
    ((1/1000)*covarianceMeanBound 25894 (mW 12947))^2 +
  normVarianceBound 25894 (mW 12947) / (3*inputVarianceMean 25894 (mW 12947))^2

end BstLean.Part268.WorldRow12947
namespace BstLean.Part268.WorldRow12948
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12948 = 247007089027650 := by
  have hu : mW 12948 ≤ 247007089027650 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12948 ≤ 247007089027649 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12948)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25896 ^ 2)
    ((6250000000000000000/1016933541967016071292739))
    ((5000000000000000000/813515417647076959099217)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25896) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25896 : ℝ)^2 / (mW 12948 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1997303/1000000000000))/2) * ((1-firstRatio 25896) * √(1-firstRatio 25896) *
      sixthConstant (e1CovarianceRatio 25896 (mW 12948) (1/10^6) rowEps))) /
    (712/10000 - 25896*(1+1/10^6)*((1997303/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25896 (mW 12948) /
    ((1/10^5) * ((mW 12948 : ℝ)*25896*((mW 12948 : ℝ)+25896+1)))^2 +
  8*(mW 12948 : ℝ)*25896*(25896+2)*(25896+3) /
    ((1/1000)*((mW 12948 : ℝ)*25896*(25896+2)))^2 +
  covarianceVarianceBound 25896 (mW 12948) /
    ((1/1000)*covarianceMeanBound 25896 (mW 12948))^2 +
  normVarianceBound 25896 (mW 12948) / (3*inputVarianceMean 25896 (mW 12948))^2

end BstLean.Part268.WorldRow12948
namespace BstLean.Part268.WorldRow12949
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12949 = 247073864458299 := by
  have hu : mW 12949 ≤ 247073864458299 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12949 ≤ 247073864458298 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12949)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25898 ^ 2)
    ((25000000000000000000/4068048327133423264494803))
    ((25000000000000000000/4067891247500743774819931)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25898) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25898 : ℝ)^2 / (mW 12949 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1997147/1000000000000))/2) * ((1-firstRatio 25898) * √(1-firstRatio 25898) *
      sixthConstant (e1CovarianceRatio 25898 (mW 12949) (1/10^6) rowEps))) /
    (712/10000 - 25898*(1+1/10^6)*((1997147/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25898 (mW 12949) /
    ((1/10^5) * ((mW 12949 : ℝ)*25898*((mW 12949 : ℝ)+25898+1)))^2 +
  8*(mW 12949 : ℝ)*25898*(25898+2)*(25898+3) /
    ((1/1000)*((mW 12949 : ℝ)*25898*(25898+2)))^2 +
  covarianceVarianceBound 25898 (mW 12949) /
    ((1/1000)*covarianceMeanBound 25898 (mW 12949))^2 +
  normVarianceBound 25898 (mW 12949) / (3*inputVarianceMean 25898 (mW 12949))^2

end BstLean.Part268.WorldRow12949
