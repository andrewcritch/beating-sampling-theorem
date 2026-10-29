import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar20
namespace BstLean.Part268.WorldRow12850
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12850 = 240525400704378 := by
  have hu : mW 12850 ≤ 240525400704378 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12850 ≤ 240525400704377 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12850)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25700 ^ 2)
    ((500000000000000000/80738931197257686228679))
    ((25000000000000000000/4036789480230204821759177)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25700) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25700 : ℝ)^2 / (mW 12850 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2012691/1000000000000))/2) * ((1-firstRatio 25700) * √(1-firstRatio 25700) *
      sixthConstant (e1CovarianceRatio 25700 (mW 12850) (1/10^6) rowEps))) /
    (712/10000 - 25700*(1+1/10^6)*((2012691/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25700 (mW 12850) /
    ((1/10^5) * ((mW 12850 : ℝ)*25700*((mW 12850 : ℝ)+25700+1)))^2 +
  8*(mW 12850 : ℝ)*25700*(25700+2)*(25700+3) /
    ((1/1000)*((mW 12850 : ℝ)*25700*(25700+2)))^2 +
  covarianceVarianceBound 25700 (mW 12850) /
    ((1/1000)*covarianceMeanBound 25700 (mW 12850))^2 +
  normVarianceBound 25700 (mW 12850) / (3*inputVarianceMean 25700 (mW 12850))^2

end BstLean.Part268.WorldRow12850
namespace BstLean.Part268.WorldRow12851
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12851 = 240590919832518 := by
  have hu : mW 12851 ≤ 240590919832518 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12851 ≤ 240590919832517 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12851)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25702 ^ 2)
    ((25000000000000000000/4037260719128243290757797))
    ((25000000000000000000/4037103639495563801083023)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25702) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25702 : ℝ)^2 / (mW 12851 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2012533/1000000000000))/2) * ((1-firstRatio 25702) * √(1-firstRatio 25702) *
      sixthConstant (e1CovarianceRatio 25702 (mW 12851) (1/10^6) rowEps))) /
    (712/10000 - 25702*(1+1/10^6)*((2012533/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25702 (mW 12851) /
    ((1/10^5) * ((mW 12851 : ℝ)*25702*((mW 12851 : ℝ)+25702+1)))^2 +
  8*(mW 12851 : ℝ)*25702*(25702+2)*(25702+3) /
    ((1/1000)*((mW 12851 : ℝ)*25702*(25702+2)))^2 +
  covarianceVarianceBound 25702 (mW 12851) /
    ((1/1000)*covarianceMeanBound 25702 (mW 12851))^2 +
  normVarianceBound 25702 (mW 12851) / (3*inputVarianceMean 25702 (mW 12851))^2

end BstLean.Part268.WorldRow12851
namespace BstLean.Part268.WorldRow12852
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12852 = 240656451707818 := by
  have hu : mW 12852 ≤ 240656451707818 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12852 ≤ 240656451707817 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12852)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25704 ^ 2)
    ((6250000000000000000/1009393719598400567520411))
    ((25000000000000000000/4037417798760922780406869)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25704) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25704 : ℝ)^2 / (mW 12852 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1006187/500000000000))/2) * ((1-firstRatio 25704) * √(1-firstRatio 25704) *
      sixthConstant (e1CovarianceRatio 25704 (mW 12852) (1/10^6) rowEps))) /
    (712/10000 - 25704*(1+1/10^6)*((1006187/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25704 (mW 12852) /
    ((1/10^5) * ((mW 12852 : ℝ)*25704*((mW 12852 : ℝ)+25704+1)))^2 +
  8*(mW 12852 : ℝ)*25704*(25704+2)*(25704+3) /
    ((1/1000)*((mW 12852 : ℝ)*25704*(25704+2)))^2 +
  covarianceVarianceBound 25704 (mW 12852) /
    ((1/1000)*covarianceMeanBound 25704 (mW 12852))^2 +
  normVarianceBound 25704 (mW 12852) / (3*inputVarianceMean 25704 (mW 12852))^2

end BstLean.Part268.WorldRow12852
namespace BstLean.Part268.WorldRow12853
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12853 = 240721996331765 := by
  have hu : mW 12853 ≤ 240721996331765 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12853 ≤ 240721996331764 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12853)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25706 ^ 2)
    ((25000000000000000000/4037889037658961249405491))
    ((5000000000000000000/807546391605256351946143)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25706) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25706 : ℝ)^2 / (mW 12853 : ℝ)) * (1 + 1/10^6)^2 *
    √(((251527/125000000000))/2) * ((1-firstRatio 25706) * √(1-firstRatio 25706) *
      sixthConstant (e1CovarianceRatio 25706 (mW 12853) (1/10^6) rowEps))) /
    (712/10000 - 25706*(1+1/10^6)*((251527/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25706 (mW 12853) /
    ((1/10^5) * ((mW 12853 : ℝ)*25706*((mW 12853 : ℝ)+25706+1)))^2 +
  8*(mW 12853 : ℝ)*25706*(25706+2)*(25706+3) /
    ((1/1000)*((mW 12853 : ℝ)*25706*(25706+2)))^2 +
  covarianceVarianceBound 25706 (mW 12853) /
    ((1/1000)*covarianceMeanBound 25706 (mW 12853))^2 +
  normVarianceBound 25706 (mW 12853) / (3*inputVarianceMean 25706 (mW 12853))^2

end BstLean.Part268.WorldRow12853
namespace BstLean.Part268.WorldRow12854
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12854 = 240787553705849 := by
  have hu : mW 12854 ≤ 240787553705849 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12854 ≤ 240787553705848 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12854)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25708 ^ 2)
    ((12500000000000000000/2019101598462160114364669))
    ((25000000000000000000/4038046117291640739054561)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25708) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25708 : ℝ)^2 / (mW 12854 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1006029/500000000000))/2) * ((1-firstRatio 25708) * √(1-firstRatio 25708) *
      sixthConstant (e1CovarianceRatio 25708 (mW 12854) (1/10^6) rowEps))) /
    (712/10000 - 25708*(1+1/10^6)*((1006029/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25708 (mW 12854) /
    ((1/10^5) * ((mW 12854 : ℝ)*25708*((mW 12854 : ℝ)+25708+1)))^2 +
  8*(mW 12854 : ℝ)*25708*(25708+2)*(25708+3) /
    ((1/1000)*((mW 12854 : ℝ)*25708*(25708+2)))^2 +
  covarianceVarianceBound 25708 (mW 12854) /
    ((1/1000)*covarianceMeanBound 25708 (mW 12854))^2 +
  normVarianceBound 25708 (mW 12854) / (3*inputVarianceMean 25708 (mW 12854))^2

end BstLean.Part268.WorldRow12854
namespace BstLean.Part268.WorldRow12855
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12855 = 240853123831557 := by
  have hu : mW 12855 ≤ 240853123831557 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12855 ≤ 240853123831556 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12855)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25710 ^ 2)
    ((5000000000000000000/807703471237935841610637))
    ((25000000000000000000/4038360276556999718378407)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25710) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25710 : ℝ)^2 / (mW 12855 : ℝ)) * (1 + 1/10^6)^2 *
    √(((20119/10000000000))/2) * ((1-firstRatio 25710) * √(1-firstRatio 25710) *
      sixthConstant (e1CovarianceRatio 25710 (mW 12855) (1/10^6) rowEps))) /
    (712/10000 - 25710*(1+1/10^6)*((20119/10000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25710 (mW 12855) /
    ((1/10^5) * ((mW 12855 : ℝ)*25710*((mW 12855 : ℝ)+25710+1)))^2 +
  8*(mW 12855 : ℝ)*25710*(25710+2)*(25710+3) /
    ((1/1000)*((mW 12855 : ℝ)*25710*(25710+2)))^2 +
  covarianceVarianceBound 25710 (mW 12855) /
    ((1/1000)*covarianceMeanBound 25710 (mW 12855))^2 +
  normVarianceBound 25710 (mW 12855) / (3*inputVarianceMean 25710 (mW 12855))^2

end BstLean.Part268.WorldRow12855
namespace BstLean.Part268.WorldRow12856
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12856 = 240918706710376 := by
  have hu : mW 12856 ≤ 240918706710376 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12856 ≤ 240918706710375 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12856)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25712 ^ 2)
    ((3125000000000000000/504853939431879773422129))
    ((25000000000000000000/4038674435822358697702253)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25712) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25712 : ℝ)^2 / (mW 12856 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1005871/500000000000))/2) * ((1-firstRatio 25712) * √(1-firstRatio 25712) *
      sixthConstant (e1CovarianceRatio 25712 (mW 12856) (1/10^6) rowEps))) /
    (712/10000 - 25712*(1+1/10^6)*((1005871/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25712 (mW 12856) /
    ((1/10^5) * ((mW 12856 : ℝ)*25712*((mW 12856 : ℝ)+25712+1)))^2 +
  8*(mW 12856 : ℝ)*25712*(25712+2)*(25712+3) /
    ((1/1000)*((mW 12856 : ℝ)*25712*(25712+2)))^2 +
  covarianceVarianceBound 25712 (mW 12856) /
    ((1/1000)*covarianceMeanBound 25712 (mW 12856))^2 +
  normVarianceBound 25712 (mW 12856) / (3*inputVarianceMean 25712 (mW 12856))^2

end BstLean.Part268.WorldRow12856
namespace BstLean.Part268.WorldRow12857
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12857 = 240984302343796 := by
  have hu : mW 12857 ≤ 240984302343796 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12857 ≤ 240984302343795 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12857)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25714 ^ 2)
    ((25000000000000000000/4039145674720397166700879))
    ((25000000000000000000/4038988595087717677026099)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25714) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25714 : ℝ)^2 / (mW 12857 : ℝ)) * (1 + 1/10^6)^2 *
    √(((31431/15625000000))/2) * ((1-firstRatio 25714) * √(1-firstRatio 25714) *
      sixthConstant (e1CovarianceRatio 25714 (mW 12857) (1/10^6) rowEps))) /
    (712/10000 - 25714*(1+1/10^6)*((31431/15625000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25714 (mW 12857) /
    ((1/10^5) * ((mW 12857 : ℝ)*25714*((mW 12857 : ℝ)+25714+1)))^2 +
  8*(mW 12857 : ℝ)*25714*(25714+2)*(25714+3) /
    ((1/1000)*((mW 12857 : ℝ)*25714*(25714+2)))^2 +
  covarianceVarianceBound 25714 (mW 12857) /
    ((1/1000)*covarianceMeanBound 25714 (mW 12857))^2 +
  normVarianceBound 25714 (mW 12857) / (3*inputVarianceMean 25714 (mW 12857))^2

end BstLean.Part268.WorldRow12857
namespace BstLean.Part268.WorldRow12858
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12858 = 241049910733304 := by
  have hu : mW 12858 ≤ 241049910733304 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12858 ≤ 241049910733303 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12858)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25716 ^ 2)
    ((12500000000000000000/2019729916992878073012363))
    ((5000000000000000000/807860550870615331269989)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25716) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25716 : ℝ)^2 / (mW 12858 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1005713/500000000000))/2) * ((1-firstRatio 25716) * √(1-firstRatio 25716) *
      sixthConstant (e1CovarianceRatio 25716 (mW 12858) (1/10^6) rowEps))) /
    (712/10000 - 25716*(1+1/10^6)*((1005713/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25716 (mW 12858) /
    ((1/10^5) * ((mW 12858 : ℝ)*25716*((mW 12858 : ℝ)+25716+1)))^2 +
  8*(mW 12858 : ℝ)*25716*(25716+2)*(25716+3) /
    ((1/1000)*((mW 12858 : ℝ)*25716*(25716+2)))^2 +
  covarianceVarianceBound 25716 (mW 12858) /
    ((1/1000)*covarianceMeanBound 25716 (mW 12858))^2 +
  normVarianceBound 25716 (mW 12858) / (3*inputVarianceMean 25716 (mW 12858))^2

end BstLean.Part268.WorldRow12858
namespace BstLean.Part268.WorldRow12859
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12859 = 241115531880389 := by
  have hu : mW 12859 ≤ 241115531880389 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12859 ≤ 241115531880388 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12859)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25718 ^ 2)
    ((25000000000000000000/4039773993251115125348573))
    ((25000000000000000000/4039616913618435635673791)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25718) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25718 : ℝ)^2 / (mW 12859 : ℝ)) * (1 + 1/10^6)^2 *
    √(((502817/250000000000))/2) * ((1-firstRatio 25718) * √(1-firstRatio 25718) *
      sixthConstant (e1CovarianceRatio 25718 (mW 12859) (1/10^6) rowEps))) /
    (712/10000 - 25718*(1+1/10^6)*((502817/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25718 (mW 12859) /
    ((1/10^5) * ((mW 12859 : ℝ)*25718*((mW 12859 : ℝ)+25718+1)))^2 +
  8*(mW 12859 : ℝ)*25718*(25718+2)*(25718+3) /
    ((1/1000)*((mW 12859 : ℝ)*25718*(25718+2)))^2 +
  covarianceVarianceBound 25718 (mW 12859) /
    ((1/1000)*covarianceMeanBound 25718 (mW 12859))^2 +
  normVarianceBound 25718 (mW 12859) / (3*inputVarianceMean 25718 (mW 12859))^2

end BstLean.Part268.WorldRow12859
namespace BstLean.Part268.WorldRow12860
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12860 = 241181165786539 := by
  have hu : mW 12860 ≤ 241181165786539 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12860 ≤ 241181165786538 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12860)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25720 ^ 2)
    ((1250000000000000000/202004407625823705233621))
    ((25000000000000000000/4039931072883794614997637)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25720) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25720 : ℝ)^2 / (mW 12860 : ℝ)) * (1 + 1/10^6)^2 *
    √(((201111/100000000000))/2) * ((1-firstRatio 25720) * √(1-firstRatio 25720) *
      sixthConstant (e1CovarianceRatio 25720 (mW 12860) (1/10^6) rowEps))) /
    (712/10000 - 25720*(1+1/10^6)*((201111/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25720 (mW 12860) /
    ((1/10^5) * ((mW 12860 : ℝ)*25720*((mW 12860 : ℝ)+25720+1)))^2 +
  8*(mW 12860 : ℝ)*25720*(25720+2)*(25720+3) /
    ((1/1000)*((mW 12860 : ℝ)*25720*(25720+2)))^2 +
  covarianceVarianceBound 25720 (mW 12860) /
    ((1/1000)*covarianceMeanBound 25720 (mW 12860))^2 +
  normVarianceBound 25720 (mW 12860) / (3*inputVarianceMean 25720 (mW 12860))^2

end BstLean.Part268.WorldRow12860
namespace BstLean.Part268.WorldRow12861
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12861 = 241246812453242 := by
  have hu : mW 12861 ≤ 241246812453242 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12861 ≤ 241246812453241 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12861)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25722 ^ 2)
    ((25000000000000000000/4040402311781833083996267))
    ((25000000000000000000/4040245232149153594321483)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25722) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25722 : ℝ)^2 / (mW 12861 : ℝ)) * (1 + 1/10^6)^2 *
    √(((251369/125000000000))/2) * ((1-firstRatio 25722) * √(1-firstRatio 25722) *
      sixthConstant (e1CovarianceRatio 25722 (mW 12861) (1/10^6) rowEps))) /
    (712/10000 - 25722*(1+1/10^6)*((251369/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25722 (mW 12861) /
    ((1/10^5) * ((mW 12861 : ℝ)*25722*((mW 12861 : ℝ)+25722+1)))^2 +
  8*(mW 12861 : ℝ)*25722*(25722+2)*(25722+3) /
    ((1/1000)*((mW 12861 : ℝ)*25722*(25722+2)))^2 +
  covarianceVarianceBound 25722 (mW 12861) /
    ((1/1000)*covarianceMeanBound 25722 (mW 12861))^2 +
  normVarianceBound 25722 (mW 12861) / (3*inputVarianceMean 25722 (mW 12861))^2

end BstLean.Part268.WorldRow12861
namespace BstLean.Part268.WorldRow12862
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12862 = 241312471881986 := by
  have hu : mW 12862 ≤ 241312471881986 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12862 ≤ 241312471881985 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12862)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25724 ^ 2)
    ((12500000000000000000/2020358235523596031660057))
    ((25000000000000000000/4040559391414512573645329)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25724) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25724 : ℝ)^2 / (mW 12862 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1005397/500000000000))/2) * ((1-firstRatio 25724) * √(1-firstRatio 25724) *
      sixthConstant (e1CovarianceRatio 25724 (mW 12862) (1/10^6) rowEps))) /
    (712/10000 - 25724*(1+1/10^6)*((1005397/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25724 (mW 12862) /
    ((1/10^5) * ((mW 12862 : ℝ)*25724*((mW 12862 : ℝ)+25724+1)))^2 +
  8*(mW 12862 : ℝ)*25724*(25724+2)*(25724+3) /
    ((1/1000)*((mW 12862 : ℝ)*25724*(25724+2)))^2 +
  covarianceVarianceBound 25724 (mW 12862) /
    ((1/1000)*covarianceMeanBound 25724 (mW 12862))^2 +
  normVarianceBound 25724 (mW 12862) / (3*inputVarianceMean 25724 (mW 12862))^2

end BstLean.Part268.WorldRow12862
namespace BstLean.Part268.WorldRow12863
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12863 = 241378144074261 := by
  have hu : mW 12863 ≤ 241378144074261 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12863 ≤ 241378144074260 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12863)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25726 ^ 2)
    ((25000000000000000000/4041030630312551042643961))
    ((1000000000000000000/161634942027194862118767)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25726) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25726 : ℝ)^2 / (mW 12863 : ℝ)) * (1 + 1/10^6)^2 *
    √(((502659/250000000000))/2) * ((1-firstRatio 25726) * √(1-firstRatio 25726) *
      sixthConstant (e1CovarianceRatio 25726 (mW 12863) (1/10^6) rowEps))) /
    (712/10000 - 25726*(1+1/10^6)*((502659/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25726 (mW 12863) /
    ((1/10^5) * ((mW 12863 : ℝ)*25726*((mW 12863 : ℝ)+25726+1)))^2 +
  8*(mW 12863 : ℝ)*25726*(25726+2)*(25726+3) /
    ((1/1000)*((mW 12863 : ℝ)*25726*(25726+2)))^2 +
  covarianceVarianceBound 25726 (mW 12863) /
    ((1/1000)*covarianceMeanBound 25726 (mW 12863))^2 +
  normVarianceBound 25726 (mW 12863) / (3*inputVarianceMean 25726 (mW 12863))^2

end BstLean.Part268.WorldRow12863
namespace BstLean.Part268.WorldRow12864
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12864 = 241443829031555 := by
  have hu : mW 12864 ≤ 241443829031555 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12864 ≤ 241443829031554 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12864)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25728 ^ 2)
    ((390625000000000000/63146012337154844093247))
    ((25000000000000000000/4041187709945230532293021)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25728) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25728 : ℝ)^2 / (mW 12864 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1005239/500000000000))/2) * ((1-firstRatio 25728) * √(1-firstRatio 25728) *
      sixthConstant (e1CovarianceRatio 25728 (mW 12864) (1/10^6) rowEps))) /
    (712/10000 - 25728*(1+1/10^6)*((1005239/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25728 (mW 12864) /
    ((1/10^5) * ((mW 12864 : ℝ)*25728*((mW 12864 : ℝ)+25728+1)))^2 +
  8*(mW 12864 : ℝ)*25728*(25728+2)*(25728+3) /
    ((1/1000)*((mW 12864 : ℝ)*25728*(25728+2)))^2 +
  covarianceVarianceBound 25728 (mW 12864) /
    ((1/1000)*covarianceMeanBound 25728 (mW 12864))^2 +
  normVarianceBound 25728 (mW 12864) / (3*inputVarianceMean 25728 (mW 12864))^2

end BstLean.Part268.WorldRow12864
namespace BstLean.Part268.WorldRow12865
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12865 = 241509526755356 := by
  have hu : mW 12865 ≤ 241509526755356 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12865 ≤ 241509526755355 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12865)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25730 ^ 2)
    ((5000000000000000000/808331789768653800258331))
    ((25000000000000000000/4041501869210589511616867)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25730) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25730 : ℝ)^2 / (mW 12865 : ℝ)) * (1 + 1/10^6)^2 *
    √(((25129/12500000000))/2) * ((1-firstRatio 25730) * √(1-firstRatio 25730) *
      sixthConstant (e1CovarianceRatio 25730 (mW 12865) (1/10^6) rowEps))) /
    (712/10000 - 25730*(1+1/10^6)*((25129/12500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25730 (mW 12865) /
    ((1/10^5) * ((mW 12865 : ℝ)*25730*((mW 12865 : ℝ)+25730+1)))^2 +
  8*(mW 12865 : ℝ)*25730*(25730+2)*(25730+3) /
    ((1/1000)*((mW 12865 : ℝ)*25730*(25730+2)))^2 +
  covarianceVarianceBound 25730 (mW 12865) /
    ((1/1000)*covarianceMeanBound 25730 (mW 12865))^2 +
  normVarianceBound 25730 (mW 12865) / (3*inputVarianceMean 25730 (mW 12865))^2

end BstLean.Part268.WorldRow12865
namespace BstLean.Part268.WorldRow12866
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12866 = 241575237247153 := by
  have hu : mW 12866 ≤ 241575237247153 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12866 ≤ 241575237247152 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12866)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25732 ^ 2)
    ((12500000000000000000/2020986554054313990307751))
    ((25000000000000000000/4041816028475948490940713)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25732) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25732 : ℝ)^2 / (mW 12866 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1005081/500000000000))/2) * ((1-firstRatio 25732) * √(1-firstRatio 25732) *
      sixthConstant (e1CovarianceRatio 25732 (mW 12866) (1/10^6) rowEps))) /
    (712/10000 - 25732*(1+1/10^6)*((1005081/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25732 (mW 12866) /
    ((1/10^5) * ((mW 12866 : ℝ)*25732*((mW 12866 : ℝ)+25732+1)))^2 +
  8*(mW 12866 : ℝ)*25732*(25732+2)*(25732+3) /
    ((1/1000)*((mW 12866 : ℝ)*25732*(25732+2)))^2 +
  covarianceVarianceBound 25732 (mW 12866) /
    ((1/1000)*covarianceMeanBound 25732 (mW 12866))^2 +
  normVarianceBound 25732 (mW 12866) / (3*inputVarianceMean 25732 (mW 12866))^2

end BstLean.Part268.WorldRow12866
namespace BstLean.Part268.WorldRow12867
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12867 = 241640960508435 := by
  have hu : mW 12867 ≤ 241640960508435 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12867 ≤ 241640960508434 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12867)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25734 ^ 2)
    ((25000000000000000000/4042287267373986959939349))
    ((25000000000000000000/4042130187741307470264559)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25734) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25734 : ℝ)^2 / (mW 12867 : ℝ)) * (1 + 1/10^6)^2 *
    √(((502501/250000000000))/2) * ((1-firstRatio 25734) * √(1-firstRatio 25734) *
      sixthConstant (e1CovarianceRatio 25734 (mW 12867) (1/10^6) rowEps))) /
    (712/10000 - 25734*(1+1/10^6)*((502501/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25734 (mW 12867) /
    ((1/10^5) * ((mW 12867 : ℝ)*25734*((mW 12867 : ℝ)+25734+1)))^2 +
  8*(mW 12867 : ℝ)*25734*(25734+2)*(25734+3) /
    ((1/1000)*((mW 12867 : ℝ)*25734*(25734+2)))^2 +
  covarianceVarianceBound 25734 (mW 12867) /
    ((1/1000)*covarianceMeanBound 25734 (mW 12867))^2 +
  normVarianceBound 25734 (mW 12867) / (3*inputVarianceMean 25734 (mW 12867))^2

end BstLean.Part268.WorldRow12867
namespace BstLean.Part268.WorldRow12868
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12868 = 241706696540691 := by
  have hu : mW 12868 ≤ 241706696540691 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12868 ≤ 241706696540690 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12868)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25736 ^ 2)
    ((6250000000000000000/1010650356659836484815799))
    ((5000000000000000000/808488869401333289917681)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25736) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25736 : ℝ)^2 / (mW 12868 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2009847/1000000000000))/2) * ((1-firstRatio 25736) * √(1-firstRatio 25736) *
      sixthConstant (e1CovarianceRatio 25736 (mW 12868) (1/10^6) rowEps))) /
    (712/10000 - 25736*(1+1/10^6)*((2009847/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25736 (mW 12868) /
    ((1/10^5) * ((mW 12868 : ℝ)*25736*((mW 12868 : ℝ)+25736+1)))^2 +
  8*(mW 12868 : ℝ)*25736*(25736+2)*(25736+3) /
    ((1/1000)*((mW 12868 : ℝ)*25736*(25736+2)))^2 +
  covarianceVarianceBound 25736 (mW 12868) /
    ((1/1000)*covarianceMeanBound 25736 (mW 12868))^2 +
  normVarianceBound 25736 (mW 12868) / (3*inputVarianceMean 25736 (mW 12868))^2

end BstLean.Part268.WorldRow12868
namespace BstLean.Part268.WorldRow12869
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12869 = 241772445345408 := by
  have hu : mW 12869 ≤ 241772445345408 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12869 ≤ 241772445345407 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12869)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25738 ^ 2)
    ((25000000000000000000/4042915585904704918587043))
    ((25000000000000000000/4042758506272025428912251)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25738) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25738 : ℝ)^2 / (mW 12869 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2009689/1000000000000))/2) * ((1-firstRatio 25738) * √(1-firstRatio 25738) *
      sixthConstant (e1CovarianceRatio 25738 (mW 12869) (1/10^6) rowEps))) /
    (712/10000 - 25738*(1+1/10^6)*((2009689/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25738 (mW 12869) /
    ((1/10^5) * ((mW 12869 : ℝ)*25738*((mW 12869 : ℝ)+25738+1)))^2 +
  8*(mW 12869 : ℝ)*25738*(25738+2)*(25738+3) /
    ((1/1000)*((mW 12869 : ℝ)*25738*(25738+2)))^2 +
  covarianceVarianceBound 25738 (mW 12869) /
    ((1/1000)*covarianceMeanBound 25738 (mW 12869))^2 +
  normVarianceBound 25738 (mW 12869) / (3*inputVarianceMean 25738 (mW 12869))^2

end BstLean.Part268.WorldRow12869
namespace BstLean.Part268.WorldRow12870
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12870 = 241838206924077 := by
  have hu : mW 12870 ≤ 241838206924077 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12870 ≤ 241838206924076 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12870)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25740 ^ 2)
    ((2500000000000000000/404322974517006389791089))
    ((25000000000000000000/4043072665537384408236097)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25740) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25740 : ℝ)^2 / (mW 12870 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2009531/1000000000000))/2) * ((1-firstRatio 25740) * √(1-firstRatio 25740) *
      sixthConstant (e1CovarianceRatio 25740 (mW 12870) (1/10^6) rowEps))) /
    (712/10000 - 25740*(1+1/10^6)*((2009531/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25740 (mW 12870) /
    ((1/10^5) * ((mW 12870 : ℝ)*25740*((mW 12870 : ℝ)+25740+1)))^2 +
  8*(mW 12870 : ℝ)*25740*(25740+2)*(25740+3) /
    ((1/1000)*((mW 12870 : ℝ)*25740*(25740+2)))^2 +
  covarianceVarianceBound 25740 (mW 12870) /
    ((1/1000)*covarianceMeanBound 25740 (mW 12870))^2 +
  normVarianceBound 25740 (mW 12870) / (3*inputVarianceMean 25740 (mW 12870))^2

end BstLean.Part268.WorldRow12870
namespace BstLean.Part268.WorldRow12871
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12871 = 241903981278187 := by
  have hu : mW 12871 ≤ 241903981278187 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12871 ≤ 241903981278186 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12871)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25742 ^ 2)
    ((25000000000000000000/4043543904435422877234737))
    ((25000000000000000000/4043386824802743387559943)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25742) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25742 : ℝ)^2 / (mW 12871 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2009373/1000000000000))/2) * ((1-firstRatio 25742) * √(1-firstRatio 25742) *
      sixthConstant (e1CovarianceRatio 25742 (mW 12871) (1/10^6) rowEps))) /
    (712/10000 - 25742*(1+1/10^6)*((2009373/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25742 (mW 12871) /
    ((1/10^5) * ((mW 12871 : ℝ)*25742*((mW 12871 : ℝ)+25742+1)))^2 +
  8*(mW 12871 : ℝ)*25742*(25742+2)*(25742+3) /
    ((1/1000)*((mW 12871 : ℝ)*25742*(25742+2)))^2 +
  covarianceVarianceBound 25742 (mW 12871) /
    ((1/1000)*covarianceMeanBound 25742 (mW 12871))^2 +
  normVarianceBound 25742 (mW 12871) / (3*inputVarianceMean 25742 (mW 12871))^2

end BstLean.Part268.WorldRow12871
namespace BstLean.Part268.WorldRow12872
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12872 = 241969768409225 := by
  have hu : mW 12872 ≤ 241969768409225 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12872 ≤ 241969768409224 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12872)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25744 ^ 2)
    ((3125000000000000000/505482257962597732069823))
    ((25000000000000000000/4043700984068102366883789)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25744) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25744 : ℝ)^2 / (mW 12872 : ℝ)) * (1 + 1/10^6)^2 *
    √(((15697/7812500000))/2) * ((1-firstRatio 25744) * √(1-firstRatio 25744) *
      sixthConstant (e1CovarianceRatio 25744 (mW 12872) (1/10^6) rowEps))) /
    (712/10000 - 25744*(1+1/10^6)*((15697/7812500000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25744 (mW 12872) /
    ((1/10^5) * ((mW 12872 : ℝ)*25744*((mW 12872 : ℝ)+25744+1)))^2 +
  8*(mW 12872 : ℝ)*25744*(25744+2)*(25744+3) /
    ((1/1000)*((mW 12872 : ℝ)*25744*(25744+2)))^2 +
  covarianceVarianceBound 25744 (mW 12872) /
    ((1/1000)*covarianceMeanBound 25744 (mW 12872))^2 +
  normVarianceBound 25744 (mW 12872) / (3*inputVarianceMean 25744 (mW 12872))^2

end BstLean.Part268.WorldRow12872
namespace BstLean.Part268.WorldRow12873
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12873 = 242035568318682 := by
  have hu : mW 12873 ≤ 242035568318682 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12873 ≤ 242035568318681 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12873)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25746 ^ 2)
    ((25000000000000000000/4044172222966140835882431))
    ((5000000000000000000/808803028666692269241527)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25746) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25746 : ℝ)^2 / (mW 12873 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1004529/500000000000))/2) * ((1-firstRatio 25746) * √(1-firstRatio 25746) *
      sixthConstant (e1CovarianceRatio 25746 (mW 12873) (1/10^6) rowEps))) /
    (712/10000 - 25746*(1+1/10^6)*((1004529/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25746 (mW 12873) /
    ((1/10^5) * ((mW 12873 : ℝ)*25746*((mW 12873 : ℝ)+25746+1)))^2 +
  8*(mW 12873 : ℝ)*25746*(25746+2)*(25746+3) /
    ((1/1000)*((mW 12873 : ℝ)*25746*(25746+2)))^2 +
  covarianceVarianceBound 25746 (mW 12873) /
    ((1/1000)*covarianceMeanBound 25746 (mW 12873))^2 +
  normVarianceBound 25746 (mW 12873) / (3*inputVarianceMean 25746 (mW 12873))^2

end BstLean.Part268.WorldRow12873
namespace BstLean.Part268.WorldRow12874
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12874 = 242101381008046 := by
  have hu : mW 12874 ≤ 242101381008046 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12874 ≤ 242101381008045 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12874)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25748 ^ 2)
    ((12500000000000000000/2022243191115749907603139))
    ((25000000000000000000/4044329302598820325531481)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25748) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25748 : ℝ)^2 / (mW 12874 : ℝ)) * (1 + 1/10^6)^2 *
    √(((20089/10000000000))/2) * ((1-firstRatio 25748) * √(1-firstRatio 25748) *
      sixthConstant (e1CovarianceRatio 25748 (mW 12874) (1/10^6) rowEps))) /
    (712/10000 - 25748*(1+1/10^6)*((20089/10000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25748 (mW 12874) /
    ((1/10^5) * ((mW 12874 : ℝ)*25748*((mW 12874 : ℝ)+25748+1)))^2 +
  8*(mW 12874 : ℝ)*25748*(25748+2)*(25748+3) /
    ((1/1000)*((mW 12874 : ℝ)*25748*(25748+2)))^2 +
  covarianceVarianceBound 25748 (mW 12874) /
    ((1/1000)*covarianceMeanBound 25748 (mW 12874))^2 +
  normVarianceBound 25748 (mW 12874) / (3*inputVarianceMean 25748 (mW 12874))^2

end BstLean.Part268.WorldRow12874
