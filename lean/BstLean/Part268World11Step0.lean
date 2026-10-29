import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar11
namespace BstLean.Part268.WorldRow12625
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12625 = 226104837300712 := by
  have hu : mW 12625 ≤ 226104837300712 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12625 ≤ 226104837300711 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12625)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25250 ^ 2)
    ((200000000000000000/31730085801256911708547))
    ((25000000000000000000/3966103645524434473893827)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25250) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25250 : ℝ)^2 / (mW 12625 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2048937/1000000000000))/2) * ((1-firstRatio 25250) * √(1-firstRatio 25250) *
      sixthConstant (e1CovarianceRatio 25250 (mW 12625) (1/10^6) rowEps))) /
    (712/10000 - 25250*(1+1/10^6)*((2048937/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25250 (mW 12625) /
    ((1/10^5) * ((mW 12625 : ℝ)*25250*((mW 12625 : ℝ)+25250+1)))^2 +
  8*(mW 12625 : ℝ)*25250*(25250+2)*(25250+3) /
    ((1/1000)*((mW 12625 : ℝ)*25250*(25250+2)))^2 +
  covarianceVarianceBound 25250 (mW 12625) /
    ((1/1000)*covarianceMeanBound 25250 (mW 12625))^2 +
  normVarianceBound 25250 (mW 12625) / (3*inputVarianceMean 25250 (mW 12625))^2

end BstLean.Part268.WorldRow12625
namespace BstLean.Part268.WorldRow12626
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12626 = 226167526036302 := by
  have hu : mW 12626 ≤ 226167526036302 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12626 ≤ 226167526036301 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12626)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25252 ^ 2)
    ((12500000000000000000/1983287442211236471446111))
    ((25000000000000000000/3966417804789793453217673)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25252) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25252 : ℝ)^2 / (mW 12626 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2048773/1000000000000))/2) * ((1-firstRatio 25252) * √(1-firstRatio 25252) *
      sixthConstant (e1CovarianceRatio 25252 (mW 12626) (1/10^6) rowEps))) /
    (712/10000 - 25252*(1+1/10^6)*((2048773/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25252 (mW 12626) /
    ((1/10^5) * ((mW 12626 : ℝ)*25252*((mW 12626 : ℝ)+25252+1)))^2 +
  8*(mW 12626 : ℝ)*25252*(25252+2)*(25252+3) /
    ((1/1000)*((mW 12626 : ℝ)*25252*(25252+2)))^2 +
  covarianceVarianceBound 25252 (mW 12626) /
    ((1/1000)*covarianceMeanBound 25252 (mW 12626))^2 +
  normVarianceBound 25252 (mW 12626) / (3*inputVarianceMean 25252 (mW 12626))^2

end BstLean.Part268.WorldRow12626
namespace BstLean.Part268.WorldRow12627
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12627 = 226230227185748 := by
  have hu : mW 12627 ≤ 226230227185748 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12627 ≤ 226230227185747 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12627)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25254 ^ 2)
    ((25000000000000000000/3966889043687831922216069))
    ((25000000000000000000/3966731964055152432541519)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25254) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25254 : ℝ)^2 / (mW 12627 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2048609/1000000000000))/2) * ((1-firstRatio 25254) * √(1-firstRatio 25254) *
      sixthConstant (e1CovarianceRatio 25254 (mW 12627) (1/10^6) rowEps))) /
    (712/10000 - 25254*(1+1/10^6)*((2048609/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25254 (mW 12627) /
    ((1/10^5) * ((mW 12627 : ℝ)*25254*((mW 12627 : ℝ)+25254+1)))^2 +
  8*(mW 12627 : ℝ)*25254*(25254+2)*(25254+3) /
    ((1/1000)*((mW 12627 : ℝ)*25254*(25254+2)))^2 +
  covarianceVarianceBound 25254 (mW 12627) /
    ((1/1000)*covarianceMeanBound 25254 (mW 12627))^2 +
  normVarianceBound 25254 (mW 12627) / (3*inputVarianceMean 25254 (mW 12627))^2

end BstLean.Part268.WorldRow12627
namespace BstLean.Part268.WorldRow12628
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12628 = 226292940750526 := by
  have hu : mW 12628 ≤ 226292940750526 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12628 ≤ 226292940750525 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12628)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25256 ^ 2)
    ((6250000000000000000/991800800738297725384979))
    ((5000000000000000000/793409224664102282373073)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25256) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25256 : ℝ)^2 / (mW 12628 : ℝ)) * (1 + 1/10^6)^2 *
    √(((409689/200000000000))/2) * ((1-firstRatio 25256) * √(1-firstRatio 25256) *
      sixthConstant (e1CovarianceRatio 25256 (mW 12628) (1/10^6) rowEps))) /
    (712/10000 - 25256*(1+1/10^6)*((409689/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25256 (mW 12628) /
    ((1/10^5) * ((mW 12628 : ℝ)*25256*((mW 12628 : ℝ)+25256+1)))^2 +
  8*(mW 12628 : ℝ)*25256*(25256+2)*(25256+3) /
    ((1/1000)*((mW 12628 : ℝ)*25256*(25256+2)))^2 +
  covarianceVarianceBound 25256 (mW 12628) /
    ((1/1000)*covarianceMeanBound 25256 (mW 12628))^2 +
  normVarianceBound 25256 (mW 12628) / (3*inputVarianceMean 25256 (mW 12628))^2

end BstLean.Part268.WorldRow12628
namespace BstLean.Part268.WorldRow12629
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12629 = 226355666732110 := by
  have hu : mW 12629 ≤ 226355666732110 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12629 ≤ 226355666732109 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12629)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25258 ^ 2)
    ((25000000000000000000/3967517362218549880863763))
    ((25000000000000000000/3967360282585870391189211)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25258) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25258 : ℝ)^2 / (mW 12629 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2048281/1000000000000))/2) * ((1-firstRatio 25258) * √(1-firstRatio 25258) *
      sixthConstant (e1CovarianceRatio 25258 (mW 12629) (1/10^6) rowEps))) /
    (712/10000 - 25258*(1+1/10^6)*((2048281/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25258 (mW 12629) /
    ((1/10^5) * ((mW 12629 : ℝ)*25258*((mW 12629 : ℝ)+25258+1)))^2 +
  8*(mW 12629 : ℝ)*25258*(25258+2)*(25258+3) /
    ((1/1000)*((mW 12629 : ℝ)*25258*(25258+2)))^2 +
  covarianceVarianceBound 25258 (mW 12629) /
    ((1/1000)*covarianceMeanBound 25258 (mW 12629))^2 +
  normVarianceBound 25258 (mW 12629) / (3*inputVarianceMean 25258 (mW 12629))^2

end BstLean.Part268.WorldRow12629
namespace BstLean.Part268.WorldRow12630
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12630 = 226418405131976 := by
  have hu : mW 12630 ≤ 226418405131976 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12630 ≤ 226418405131975 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12630)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25260 ^ 2)
    ((2500000000000000000/396783152148390886018761))
    ((25000000000000000000/3967674441851229370513057)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25260) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25260 : ℝ)^2 / (mW 12630 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2048117/1000000000000))/2) * ((1-firstRatio 25260) * √(1-firstRatio 25260) *
      sixthConstant (e1CovarianceRatio 25260 (mW 12630) (1/10^6) rowEps))) /
    (712/10000 - 25260*(1+1/10^6)*((2048117/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25260 (mW 12630) /
    ((1/10^5) * ((mW 12630 : ℝ)*25260*((mW 12630 : ℝ)+25260+1)))^2 +
  8*(mW 12630 : ℝ)*25260*(25260+2)*(25260+3) /
    ((1/1000)*((mW 12630 : ℝ)*25260*(25260+2)))^2 +
  covarianceVarianceBound 25260 (mW 12630) /
    ((1/1000)*covarianceMeanBound 25260 (mW 12630))^2 +
  normVarianceBound 25260 (mW 12630) / (3*inputVarianceMean 25260 (mW 12630))^2

end BstLean.Part268.WorldRow12630
namespace BstLean.Part268.WorldRow12631
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12631 = 226481155951598 := by
  have hu : mW 12631 ≤ 226481155951598 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12631 ≤ 226481155951597 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12631)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25262 ^ 2)
    ((25000000000000000000/3968145680749267839511457))
    ((25000000000000000000/3967988601116588349836903)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25262) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25262 : ℝ)^2 / (mW 12631 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2047953/1000000000000))/2) * ((1-firstRatio 25262) * √(1-firstRatio 25262) *
      sixthConstant (e1CovarianceRatio 25262 (mW 12631) (1/10^6) rowEps))) /
    (712/10000 - 25262*(1+1/10^6)*((2047953/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25262 (mW 12631) /
    ((1/10^5) * ((mW 12631 : ℝ)*25262*((mW 12631 : ℝ)+25262+1)))^2 +
  8*(mW 12631 : ℝ)*25262*(25262+2)*(25262+3) /
    ((1/1000)*((mW 12631 : ℝ)*25262*(25262+2)))^2 +
  covarianceVarianceBound 25262 (mW 12631) /
    ((1/1000)*covarianceMeanBound 25262 (mW 12631))^2 +
  normVarianceBound 25262 (mW 12631) / (3*inputVarianceMean 25262 (mW 12631))^2

end BstLean.Part268.WorldRow12631
namespace BstLean.Part268.WorldRow12632
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12632 = 226543919192452 := by
  have hu : mW 12632 ≤ 226543919192452 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12632 ≤ 226543919192451 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12632)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25264 ^ 2)
    ((3125000000000000000/496057480001828352354413))
    ((25000000000000000000/3968302760381947329160749)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25264) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25264 : ℝ)^2 / (mW 12632 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2047789/1000000000000))/2) * ((1-firstRatio 25264) * √(1-firstRatio 25264) *
      sixthConstant (e1CovarianceRatio 25264 (mW 12632) (1/10^6) rowEps))) /
    (712/10000 - 25264*(1+1/10^6)*((2047789/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25264 (mW 12632) /
    ((1/10^5) * ((mW 12632 : ℝ)*25264*((mW 12632 : ℝ)+25264+1)))^2 +
  8*(mW 12632 : ℝ)*25264*(25264+2)*(25264+3) /
    ((1/1000)*((mW 12632 : ℝ)*25264*(25264+2)))^2 +
  covarianceVarianceBound 25264 (mW 12632) /
    ((1/1000)*covarianceMeanBound 25264 (mW 12632))^2 +
  normVarianceBound 25264 (mW 12632) / (3*inputVarianceMean 25264 (mW 12632))^2

end BstLean.Part268.WorldRow12632
namespace BstLean.Part268.WorldRow12633
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12633 = 226606694856012 := by
  have hu : mW 12633 ≤ 226606694856012 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12633 ≤ 226606694856011 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12633)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25266 ^ 2)
    ((25000000000000000000/3968773999279985798159151))
    ((5000000000000000000/793723383929461261696919)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25266) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25266 : ℝ)^2 / (mW 12633 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1023813/500000000000))/2) * ((1-firstRatio 25266) * √(1-firstRatio 25266) *
      sixthConstant (e1CovarianceRatio 25266 (mW 12633) (1/10^6) rowEps))) /
    (712/10000 - 25266*(1+1/10^6)*((1023813/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25266 (mW 12633) /
    ((1/10^5) * ((mW 12633 : ℝ)*25266*((mW 12633 : ℝ)+25266+1)))^2 +
  8*(mW 12633 : ℝ)*25266*(25266+2)*(25266+3) /
    ((1/1000)*((mW 12633 : ℝ)*25266*(25266+2)))^2 +
  covarianceVarianceBound 25266 (mW 12633) /
    ((1/1000)*covarianceMeanBound 25266 (mW 12633))^2 +
  normVarianceBound 25266 (mW 12633) / (3*inputVarianceMean 25266 (mW 12633))^2

end BstLean.Part268.WorldRow12633
namespace BstLean.Part268.WorldRow12634
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12634 = 226669482943754 := by
  have hu : mW 12634 ≤ 226669482943754 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12634 ≤ 226669482943753 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12634)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25268 ^ 2)
    ((12500000000000000000/1984544079272672388741499))
    ((25000000000000000000/3968931078912665287808441)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25268) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25268 : ℝ)^2 / (mW 12634 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1023731/500000000000))/2) * ((1-firstRatio 25268) * √(1-firstRatio 25268) *
      sixthConstant (e1CovarianceRatio 25268 (mW 12634) (1/10^6) rowEps))) /
    (712/10000 - 25268*(1+1/10^6)*((1023731/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25268 (mW 12634) /
    ((1/10^5) * ((mW 12634 : ℝ)*25268*((mW 12634 : ℝ)+25268+1)))^2 +
  8*(mW 12634 : ℝ)*25268*(25268+2)*(25268+3) /
    ((1/1000)*((mW 12634 : ℝ)*25268*(25268+2)))^2 +
  covarianceVarianceBound 25268 (mW 12634) /
    ((1/1000)*covarianceMeanBound 25268 (mW 12634))^2 +
  normVarianceBound 25268 (mW 12634) / (3*inputVarianceMean 25268 (mW 12634))^2

end BstLean.Part268.WorldRow12634
namespace BstLean.Part268.WorldRow12635
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12635 = 226732283457154 := by
  have hu : mW 12635 ≤ 226732283457154 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12635 ≤ 226732283457153 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12635)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25270 ^ 2)
    ((5000000000000000000/793880463562140751361369))
    ((25000000000000000000/3969245238178024267132287)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25270) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25270 : ℝ)^2 / (mW 12635 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1023649/500000000000))/2) * ((1-firstRatio 25270) * √(1-firstRatio 25270) *
      sixthConstant (e1CovarianceRatio 25270 (mW 12635) (1/10^6) rowEps))) /
    (712/10000 - 25270*(1+1/10^6)*((1023649/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25270 (mW 12635) /
    ((1/10^5) * ((mW 12635 : ℝ)*25270*((mW 12635 : ℝ)+25270+1)))^2 +
  8*(mW 12635 : ℝ)*25270*(25270+2)*(25270+3) /
    ((1/1000)*((mW 12635 : ℝ)*25270*(25270+2)))^2 +
  covarianceVarianceBound 25270 (mW 12635) /
    ((1/1000)*covarianceMeanBound 25270 (mW 12635))^2 +
  normVarianceBound 25270 (mW 12635) / (3*inputVarianceMean 25270 (mW 12635))^2

end BstLean.Part268.WorldRow12635
namespace BstLean.Part268.WorldRow12636
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12636 = 226795096397685 := by
  have hu : mW 12636 ≤ 226795096397685 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12636 ≤ 226795096397684 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12636)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25272 ^ 2)
    ((6250000000000000000/992429119269015684032673))
    ((25000000000000000000/3969559397443383246456133)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25272) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25272 : ℝ)^2 / (mW 12636 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1023567/500000000000))/2) * ((1-firstRatio 25272) * √(1-firstRatio 25272) *
      sixthConstant (e1CovarianceRatio 25272 (mW 12636) (1/10^6) rowEps))) /
    (712/10000 - 25272*(1+1/10^6)*((1023567/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25272 (mW 12636) /
    ((1/10^5) * ((mW 12636 : ℝ)*25272*((mW 12636 : ℝ)+25272+1)))^2 +
  8*(mW 12636 : ℝ)*25272*(25272+2)*(25272+3) /
    ((1/1000)*((mW 12636 : ℝ)*25272*(25272+2)))^2 +
  covarianceVarianceBound 25272 (mW 12636) /
    ((1/1000)*covarianceMeanBound 25272 (mW 12636))^2 +
  normVarianceBound 25272 (mW 12636) / (3*inputVarianceMean 25272 (mW 12636))^2

end BstLean.Part268.WorldRow12636
namespace BstLean.Part268.WorldRow12637
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12637 = 226857921766824 := by
  have hu : mW 12637 ≤ 226857921766824 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12637 ≤ 226857921766823 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12637)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25274 ^ 2)
    ((25000000000000000000/3970030636341421715454539))
    ((25000000000000000000/3969873556708742225779979)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25274) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25274 : ℝ)^2 / (mW 12637 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2046971/1000000000000))/2) * ((1-firstRatio 25274) * √(1-firstRatio 25274) *
      sixthConstant (e1CovarianceRatio 25274 (mW 12637) (1/10^6) rowEps))) /
    (712/10000 - 25274*(1+1/10^6)*((2046971/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25274 (mW 12637) /
    ((1/10^5) * ((mW 12637 : ℝ)*25274*((mW 12637 : ℝ)+25274+1)))^2 +
  8*(mW 12637 : ℝ)*25274*(25274+2)*(25274+3) /
    ((1/1000)*((mW 12637 : ℝ)*25274*(25274+2)))^2 +
  covarianceVarianceBound 25274 (mW 12637) /
    ((1/1000)*covarianceMeanBound 25274 (mW 12637))^2 +
  normVarianceBound 25274 (mW 12637) / (3*inputVarianceMean 25274 (mW 12637))^2

end BstLean.Part268.WorldRow12637
namespace BstLean.Part268.WorldRow12638
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12638 = 226920759566046 := by
  have hu : mW 12638 ≤ 226920759566046 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12638 ≤ 226920759566045 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12638)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25276 ^ 2)
    ((12500000000000000000/1985172397803390347389193))
    ((1000000000000000000/158807508638964048204153)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25276) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25276 : ℝ)^2 / (mW 12638 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2046807/1000000000000))/2) * ((1-firstRatio 25276) * √(1-firstRatio 25276) *
      sixthConstant (e1CovarianceRatio 25276 (mW 12638) (1/10^6) rowEps))) /
    (712/10000 - 25276*(1+1/10^6)*((2046807/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25276 (mW 12638) /
    ((1/10^5) * ((mW 12638 : ℝ)*25276*((mW 12638 : ℝ)+25276+1)))^2 +
  8*(mW 12638 : ℝ)*25276*(25276+2)*(25276+3) /
    ((1/1000)*((mW 12638 : ℝ)*25276*(25276+2)))^2 +
  covarianceVarianceBound 25276 (mW 12638) /
    ((1/1000)*covarianceMeanBound 25276 (mW 12638))^2 +
  normVarianceBound 25276 (mW 12638) / (3*inputVarianceMean 25276 (mW 12638))^2

end BstLean.Part268.WorldRow12638
namespace BstLean.Part268.WorldRow12639
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12639 = 226983609796827 := by
  have hu : mW 12639 ≤ 226983609796827 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12639 ≤ 226983609796826 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12639)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25278 ^ 2)
    ((25000000000000000000/3970658954872139674102233))
    ((25000000000000000000/3970501875239460184427671)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25278) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25278 : ℝ)^2 / (mW 12639 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2046643/1000000000000))/2) * ((1-firstRatio 25278) * √(1-firstRatio 25278) *
      sixthConstant (e1CovarianceRatio 25278 (mW 12639) (1/10^6) rowEps))) /
    (712/10000 - 25278*(1+1/10^6)*((2046643/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25278 (mW 12639) /
    ((1/10^5) * ((mW 12639 : ℝ)*25278*((mW 12639 : ℝ)+25278+1)))^2 +
  8*(mW 12639 : ℝ)*25278*(25278+2)*(25278+3) /
    ((1/1000)*((mW 12639 : ℝ)*25278*(25278+2)))^2 +
  covarianceVarianceBound 25278 (mW 12639) /
    ((1/1000)*covarianceMeanBound 25278 (mW 12639))^2 +
  normVarianceBound 25278 (mW 12639) / (3*inputVarianceMean 25278 (mW 12639))^2

end BstLean.Part268.WorldRow12639
namespace BstLean.Part268.WorldRow12640
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12640 = 227046472460642 := by
  have hu : mW 12640 ≤ 227046472460642 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12640 ≤ 227046472460641 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12640)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25280 ^ 2)
    ((156250000000000000/24818581963359366583913))
    ((25000000000000000000/3970816034504819163751517)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25280) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25280 : ℝ)^2 / (mW 12640 : ℝ)) * (1 + 1/10^6)^2 *
    √(((25581/12500000000))/2) * ((1-firstRatio 25280) * √(1-firstRatio 25280) *
      sixthConstant (e1CovarianceRatio 25280 (mW 12640) (1/10^6) rowEps))) /
    (712/10000 - 25280*(1+1/10^6)*((25581/12500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25280 (mW 12640) /
    ((1/10^5) * ((mW 12640 : ℝ)*25280*((mW 12640 : ℝ)+25280+1)))^2 +
  8*(mW 12640 : ℝ)*25280*(25280+2)*(25280+3) /
    ((1/1000)*((mW 12640 : ℝ)*25280*(25280+2)))^2 +
  covarianceVarianceBound 25280 (mW 12640) /
    ((1/1000)*covarianceMeanBound 25280 (mW 12640))^2 +
  normVarianceBound 25280 (mW 12640) / (3*inputVarianceMean 25280 (mW 12640))^2

end BstLean.Part268.WorldRow12640
namespace BstLean.Part268.WorldRow12641
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12641 = 227109347558967 := by
  have hu : mW 12641 ≤ 227109347558967 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12641 ≤ 227109347558966 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12641)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25282 ^ 2)
    ((25000000000000000000/3971287273402857632749927))
    ((25000000000000000000/3971130193770178143075363)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25282) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25282 : ℝ)^2 / (mW 12641 : ℝ)) * (1 + 1/10^6)^2 *
    √(((511579/250000000000))/2) * ((1-firstRatio 25282) * √(1-firstRatio 25282) *
      sixthConstant (e1CovarianceRatio 25282 (mW 12641) (1/10^6) rowEps))) /
    (712/10000 - 25282*(1+1/10^6)*((511579/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25282 (mW 12641) /
    ((1/10^5) * ((mW 12641 : ℝ)*25282*((mW 12641 : ℝ)+25282+1)))^2 +
  8*(mW 12641 : ℝ)*25282*(25282+2)*(25282+3) /
    ((1/1000)*((mW 12641 : ℝ)*25282*(25282+2)))^2 +
  covarianceVarianceBound 25282 (mW 12641) /
    ((1/1000)*covarianceMeanBound 25282 (mW 12641))^2 +
  normVarianceBound 25282 (mW 12641) / (3*inputVarianceMean 25282 (mW 12641))^2

end BstLean.Part268.WorldRow12641
namespace BstLean.Part268.WorldRow12642
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12642 = 227172235093276 := by
  have hu : mW 12642 ≤ 227172235093276 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12642 ≤ 227172235093275 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12642)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25284 ^ 2)
    ((12500000000000000000/1985800716334108306036887))
    ((25000000000000000000/3971444353035537122399209)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25284) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25284 : ℝ)^2 / (mW 12642 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2046153/1000000000000))/2) * ((1-firstRatio 25284) * √(1-firstRatio 25284) *
      sixthConstant (e1CovarianceRatio 25284 (mW 12642) (1/10^6) rowEps))) /
    (712/10000 - 25284*(1+1/10^6)*((2046153/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25284 (mW 12642) /
    ((1/10^5) * ((mW 12642 : ℝ)*25284*((mW 12642 : ℝ)+25284+1)))^2 +
  8*(mW 12642 : ℝ)*25284*(25284+2)*(25284+3) /
    ((1/1000)*((mW 12642 : ℝ)*25284*(25284+2)))^2 +
  covarianceVarianceBound 25284 (mW 12642) /
    ((1/1000)*covarianceMeanBound 25284 (mW 12642))^2 +
  normVarianceBound 25284 (mW 12642) / (3*inputVarianceMean 25284 (mW 12642))^2

end BstLean.Part268.WorldRow12642
namespace BstLean.Part268.WorldRow12643
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12643 = 227235135065047 := by
  have hu : mW 12643 ≤ 227235135065047 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12643 ≤ 227235135065046 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12643)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25286 ^ 2)
    ((25000000000000000000/3971915591933575591397621))
    ((5000000000000000000/794351702460179220344611)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25286) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25286 : ℝ)^2 / (mW 12643 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2045989/1000000000000))/2) * ((1-firstRatio 25286) * √(1-firstRatio 25286) *
      sixthConstant (e1CovarianceRatio 25286 (mW 12643) (1/10^6) rowEps))) /
    (712/10000 - 25286*(1+1/10^6)*((2045989/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25286 (mW 12643) /
    ((1/10^5) * ((mW 12643 : ℝ)*25286*((mW 12643 : ℝ)+25286+1)))^2 +
  8*(mW 12643 : ℝ)*25286*(25286+2)*(25286+3) /
    ((1/1000)*((mW 12643 : ℝ)*25286*(25286+2)))^2 +
  covarianceVarianceBound 25286 (mW 12643) /
    ((1/1000)*covarianceMeanBound 25286 (mW 12643))^2 +
  normVarianceBound 25286 (mW 12643) / (3*inputVarianceMean 25286 (mW 12643))^2

end BstLean.Part268.WorldRow12643
namespace BstLean.Part268.WorldRow12644
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12644 = 227298047475755 := by
  have hu : mW 12644 ≤ 227298047475755 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12644 ≤ 227298047475754 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12644)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25288 ^ 2)
    ((6250000000000000000/993057437799733642680367))
    ((25000000000000000000/3972072671566255081046901)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25288) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25288 : ℝ)^2 / (mW 12644 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1022913/500000000000))/2) * ((1-firstRatio 25288) * √(1-firstRatio 25288) *
      sixthConstant (e1CovarianceRatio 25288 (mW 12644) (1/10^6) rowEps))) /
    (712/10000 - 25288*(1+1/10^6)*((1022913/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25288 (mW 12644) /
    ((1/10^5) * ((mW 12644 : ℝ)*25288*((mW 12644 : ℝ)+25288+1)))^2 +
  8*(mW 12644 : ℝ)*25288*(25288+2)*(25288+3) /
    ((1/1000)*((mW 12644 : ℝ)*25288*(25288+2)))^2 +
  covarianceVarianceBound 25288 (mW 12644) /
    ((1/1000)*covarianceMeanBound 25288 (mW 12644))^2 +
  normVarianceBound 25288 (mW 12644) / (3*inputVarianceMean 25288 (mW 12644))^2

end BstLean.Part268.WorldRow12644
namespace BstLean.Part268.WorldRow12645
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12645 = 227360972326875 := by
  have hu : mW 12645 ≤ 227360972326875 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12645 ≤ 227360972326874 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12645)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25290 ^ 2)
    ((5000000000000000000/794508782092858710009063))
    ((25000000000000000000/3972386830831614060370747)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25290) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25290 : ℝ)^2 / (mW 12645 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1022831/500000000000))/2) * ((1-firstRatio 25290) * √(1-firstRatio 25290) *
      sixthConstant (e1CovarianceRatio 25290 (mW 12645) (1/10^6) rowEps))) /
    (712/10000 - 25290*(1+1/10^6)*((1022831/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25290 (mW 12645) /
    ((1/10^5) * ((mW 12645 : ℝ)*25290*((mW 12645 : ℝ)+25290+1)))^2 +
  8*(mW 12645 : ℝ)*25290*(25290+2)*(25290+3) /
    ((1/1000)*((mW 12645 : ℝ)*25290*(25290+2)))^2 +
  covarianceVarianceBound 25290 (mW 12645) /
    ((1/1000)*covarianceMeanBound 25290 (mW 12645))^2 +
  normVarianceBound 25290 (mW 12645) / (3*inputVarianceMean 25290 (mW 12645))^2

end BstLean.Part268.WorldRow12645
namespace BstLean.Part268.WorldRow12646
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12646 = 227423909619884 := by
  have hu : mW 12646 ≤ 227423909619884 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12646 ≤ 227423909619883 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12646)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25292 ^ 2)
    ((12500000000000000000/1986429034864826264684581))
    ((25000000000000000000/3972700990096973039694593)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25292) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25292 : ℝ)^2 / (mW 12646 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2045499/1000000000000))/2) * ((1-firstRatio 25292) * √(1-firstRatio 25292) *
      sixthConstant (e1CovarianceRatio 25292 (mW 12646) (1/10^6) rowEps))) /
    (712/10000 - 25292*(1+1/10^6)*((2045499/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25292 (mW 12646) /
    ((1/10^5) * ((mW 12646 : ℝ)*25292*((mW 12646 : ℝ)+25292+1)))^2 +
  8*(mW 12646 : ℝ)*25292*(25292+2)*(25292+3) /
    ((1/1000)*((mW 12646 : ℝ)*25292*(25292+2)))^2 +
  covarianceVarianceBound 25292 (mW 12646) /
    ((1/1000)*covarianceMeanBound 25292 (mW 12646))^2 +
  normVarianceBound 25292 (mW 12646) / (3*inputVarianceMean 25292 (mW 12646))^2

end BstLean.Part268.WorldRow12646
namespace BstLean.Part268.WorldRow12647
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12647 = 227486859356257 := by
  have hu : mW 12647 ≤ 227486859356257 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12647 ≤ 227486859356256 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12647)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25294 ^ 2)
    ((25000000000000000000/3973172228995011508693009))
    ((25000000000000000000/3973015149362332019018439)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25294) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25294 : ℝ)^2 / (mW 12647 : ℝ)) * (1 + 1/10^6)^2 *
    √(((409067/200000000000))/2) * ((1-firstRatio 25294) * √(1-firstRatio 25294) *
      sixthConstant (e1CovarianceRatio 25294 (mW 12647) (1/10^6) rowEps))) /
    (712/10000 - 25294*(1+1/10^6)*((409067/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25294 (mW 12647) /
    ((1/10^5) * ((mW 12647 : ℝ)*25294*((mW 12647 : ℝ)+25294+1)))^2 +
  8*(mW 12647 : ℝ)*25294*(25294+2)*(25294+3) /
    ((1/1000)*((mW 12647 : ℝ)*25294*(25294+2)))^2 +
  covarianceVarianceBound 25294 (mW 12647) /
    ((1/1000)*covarianceMeanBound 25294 (mW 12647))^2 +
  normVarianceBound 25294 (mW 12647) / (3*inputVarianceMean 25294 (mW 12647))^2

end BstLean.Part268.WorldRow12647
namespace BstLean.Part268.WorldRow12648
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12648 = 227549821537470 := by
  have hu : mW 12648 ≤ 227549821537470 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12648 ≤ 227549821537469 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12648)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25296 ^ 2)
    ((3125000000000000000/496685798532546311002107))
    ((5000000000000000000/794665861725538199668457)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25296) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25296 : ℝ)^2 / (mW 12648 : ℝ)) * (1 + 1/10^6)^2 *
    √(((511293/250000000000))/2) * ((1-firstRatio 25296) * √(1-firstRatio 25296) *
      sixthConstant (e1CovarianceRatio 25296 (mW 12648) (1/10^6) rowEps))) /
    (712/10000 - 25296*(1+1/10^6)*((511293/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25296 (mW 12648) /
    ((1/10^5) * ((mW 12648 : ℝ)*25296*((mW 12648 : ℝ)+25296+1)))^2 +
  8*(mW 12648 : ℝ)*25296*(25296+2)*(25296+3) /
    ((1/1000)*((mW 12648 : ℝ)*25296*(25296+2)))^2 +
  covarianceVarianceBound 25296 (mW 12648) /
    ((1/1000)*covarianceMeanBound 25296 (mW 12648))^2 +
  normVarianceBound 25296 (mW 12648) / (3*inputVarianceMean 25296 (mW 12648))^2

end BstLean.Part268.WorldRow12648
namespace BstLean.Part268.WorldRow12649
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12649 = 227612796165000 := by
  have hu : mW 12649 ≤ 227612796165000 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12649 ≤ 227612796164999 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12649)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25298 ^ 2)
    ((25000000000000000000/3973800547525729467340703))
    ((25000000000000000000/3973643467893049977666131)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25298) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25298 : ℝ)^2 / (mW 12649 : ℝ)) * (1 + 1/10^6)^2 *
    √(((127813/62500000000))/2) * ((1-firstRatio 25298) * √(1-firstRatio 25298) *
      sixthConstant (e1CovarianceRatio 25298 (mW 12649) (1/10^6) rowEps))) /
    (712/10000 - 25298*(1+1/10^6)*((127813/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25298 (mW 12649) /
    ((1/10^5) * ((mW 12649 : ℝ)*25298*((mW 12649 : ℝ)+25298+1)))^2 +
  8*(mW 12649 : ℝ)*25298*(25298+2)*(25298+3) /
    ((1/1000)*((mW 12649 : ℝ)*25298*(25298+2)))^2 +
  covarianceVarianceBound 25298 (mW 12649) /
    ((1/1000)*covarianceMeanBound 25298 (mW 12649))^2 +
  normVarianceBound 25298 (mW 12649) / (3*inputVarianceMean 25298 (mW 12649))^2

end BstLean.Part268.WorldRow12649
