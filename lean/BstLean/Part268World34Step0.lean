import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar34
namespace BstLean.Part268.WorldRow13200
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13200 = 264246205220656 := by
  have hu : mW 13200 ≤ 264246205220656 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13200 ≤ 264246205220655 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13200)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26400 ^ 2)
    ((62500000000000000/10367255756846317686951))
    ((25000000000000000000/4146745223105847585105277)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26400) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26400 : ℝ)^2 / (mW 13200 : ℝ)) * (1 + 1/10^6)^2 *
    √(((391759/200000000000))/2) * ((1-firstRatio 26400) * √(1-firstRatio 26400) *
      sixthConstant (e1CovarianceRatio 26400 (mW 13200) (1/10^6) rowEps))) /
    (712/10000 - 26400*(1+1/10^6)*((391759/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26400 (mW 13200) /
    ((1/10^5) * ((mW 13200 : ℝ)*26400*((mW 13200 : ℝ)+26400+1)))^2 +
  8*(mW 13200 : ℝ)*26400*(26400+2)*(26400+3) /
    ((1/1000)*((mW 13200 : ℝ)*26400*(26400+2)))^2 +
  covarianceVarianceBound 26400 (mW 13200) /
    ((1/1000)*covarianceMeanBound 26400 (mW 13200))^2 +
  normVarianceBound 26400 (mW 13200) / (3*inputVarianceMean 26400 (mW 13200))^2

end BstLean.Part268.WorldRow13200
namespace BstLean.Part268.WorldRow13201
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13201 = 264316277137565 := by
  have hu : mW 13201 ≤ 264316277137565 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13201 ≤ 264316277137564 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13201)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26402 ^ 2)
    ((25000000000000000000/4147216462003886054104247))
    ((25000000000000000000/4147059382371206564429123)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26402) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26402 : ℝ)^2 / (mW 13201 : ℝ)) * (1 + 1/10^6)^2 *
    √(((391729/200000000000))/2) * ((1-firstRatio 26402) * √(1-firstRatio 26402) *
      sixthConstant (e1CovarianceRatio 26402 (mW 13201) (1/10^6) rowEps))) /
    (712/10000 - 26402*(1+1/10^6)*((391729/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26402 (mW 13201) /
    ((1/10^5) * ((mW 13201 : ℝ)*26402*((mW 13201 : ℝ)+26402+1)))^2 +
  8*(mW 13201 : ℝ)*26402*(26402+2)*(26402+3) /
    ((1/1000)*((mW 13201 : ℝ)*26402*(26402+2)))^2 +
  covarianceVarianceBound 26402 (mW 13201) /
    ((1/1000)*covarianceMeanBound 26402 (mW 13201))^2 +
  normVarianceBound 26402 (mW 13201) / (3*inputVarianceMean 26402 (mW 13201))^2

end BstLean.Part268.WorldRow13201
namespace BstLean.Part268.WorldRow13202
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13202 = 264386362325921 := by
  have hu : mW 13202 ≤ 264386362325921 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13202 ≤ 264386362325920 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13202)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26404 ^ 2)
    ((12500000000000000000/2073765310634622516714047))
    ((25000000000000000000/4147373541636565543752969)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26404) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26404 : ℝ)^2 / (mW 13202 : ℝ)) * (1 + 1/10^6)^2 *
    √(((61203/31250000000))/2) * ((1-firstRatio 26404) * √(1-firstRatio 26404) *
      sixthConstant (e1CovarianceRatio 26404 (mW 13202) (1/10^6) rowEps))) /
    (712/10000 - 26404*(1+1/10^6)*((61203/31250000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26404 (mW 13202) /
    ((1/10^5) * ((mW 13202 : ℝ)*26404*((mW 13202 : ℝ)+26404+1)))^2 +
  8*(mW 13202 : ℝ)*26404*(26404+2)*(26404+3) /
    ((1/1000)*((mW 13202 : ℝ)*26404*(26404+2)))^2 +
  covarianceVarianceBound 26404 (mW 13202) /
    ((1/1000)*covarianceMeanBound 26404 (mW 13202))^2 +
  normVarianceBound 26404 (mW 13202) / (3*inputVarianceMean 26404 (mW 13202))^2

end BstLean.Part268.WorldRow13202
namespace BstLean.Part268.WorldRow13203
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13203 = 264456460787233 := by
  have hu : mW 13203 ≤ 264456460787233 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13203 ≤ 264456460787232 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13203)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26406 ^ 2)
    ((25000000000000000000/4147844780534604012751941))
    ((5000000000000000000/829537540180384904615363)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26406) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26406 : ℝ)^2 / (mW 13203 : ℝ)) * (1 + 1/10^6)^2 *
    √(((979173/500000000000))/2) * ((1-firstRatio 26406) * √(1-firstRatio 26406) *
      sixthConstant (e1CovarianceRatio 26406 (mW 13203) (1/10^6) rowEps))) /
    (712/10000 - 26406*(1+1/10^6)*((979173/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26406 (mW 13203) /
    ((1/10^5) * ((mW 13203 : ℝ)*26406*((mW 13203 : ℝ)+26406+1)))^2 +
  8*(mW 13203 : ℝ)*26406*(26406+2)*(26406+3) /
    ((1/1000)*((mW 13203 : ℝ)*26406*(26406+2)))^2 +
  covarianceVarianceBound 26406 (mW 13203) /
    ((1/1000)*covarianceMeanBound 26406 (mW 13203))^2 +
  normVarianceBound 26406 (mW 13203) / (3*inputVarianceMean 26406 (mW 13203))^2

end BstLean.Part268.WorldRow13203
namespace BstLean.Part268.WorldRow13204
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13204 = 264526572523008 := by
  have hu : mW 13204 ≤ 264526572523008 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13204 ≤ 264526572523007 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13204)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26408 ^ 2)
    ((6250000000000000000/1037039734949990748018947))
    ((25000000000000000000/4148001860167283502400661)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26408) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26408 : ℝ)^2 / (mW 13204 : ℝ)) * (1 + 1/10^6)^2 *
    √(((489549/250000000000))/2) * ((1-firstRatio 26408) * √(1-firstRatio 26408) *
      sixthConstant (e1CovarianceRatio 26408 (mW 13204) (1/10^6) rowEps))) /
    (712/10000 - 26408*(1+1/10^6)*((489549/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26408 (mW 13204) /
    ((1/10^5) * ((mW 13204 : ℝ)*26408*((mW 13204 : ℝ)+26408+1)))^2 +
  8*(mW 13204 : ℝ)*26408*(26408+2)*(26408+3) /
    ((1/1000)*((mW 13204 : ℝ)*26408*(26408+2)))^2 +
  covarianceVarianceBound 26408 (mW 13204) /
    ((1/1000)*covarianceMeanBound 26408 (mW 13204))^2 +
  normVarianceBound 26408 (mW 13204) / (3*inputVarianceMean 26408 (mW 13204))^2

end BstLean.Part268.WorldRow13204
namespace BstLean.Part268.WorldRow13205
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13205 = 264596697534756 := by
  have hu : mW 13205 ≤ 264596697534756 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13205 ≤ 264596697534755 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13205)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26410 ^ 2)
    ((5000000000000000000/829694619813064394279927))
    ((25000000000000000000/4148316019432642481724507)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26410) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26410 : ℝ)^2 / (mW 13205 : ℝ)) * (1 + 1/10^6)^2 *
    √(((979023/500000000000))/2) * ((1-firstRatio 26410) * √(1-firstRatio 26410) *
      sixthConstant (e1CovarianceRatio 26410 (mW 13205) (1/10^6) rowEps))) /
    (712/10000 - 26410*(1+1/10^6)*((979023/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26410 (mW 13205) /
    ((1/10^5) * ((mW 13205 : ℝ)*26410*((mW 13205 : ℝ)+26410+1)))^2 +
  8*(mW 13205 : ℝ)*26410*(26410+2)*(26410+3) /
    ((1/1000)*((mW 13205 : ℝ)*26410*(26410+2)))^2 +
  covarianceVarianceBound 26410 (mW 13205) /
    ((1/1000)*covarianceMeanBound 26410 (mW 13205))^2 +
  normVarianceBound 26410 (mW 13205) / (3*inputVarianceMean 26410 (mW 13205))^2

end BstLean.Part268.WorldRow13205
namespace BstLean.Part268.WorldRow13206
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13206 = 264666835823984 := by
  have hu : mW 13206 ≤ 264666835823984 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13206 ≤ 264666835823983 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13206)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26412 ^ 2)
    ((12500000000000000000/2074393629165340475361741))
    ((25000000000000000000/4148630178698001461048353)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26412) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26412 : ℝ)^2 / (mW 13206 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1957897/1000000000000))/2) * ((1-firstRatio 26412) * √(1-firstRatio 26412) *
      sixthConstant (e1CovarianceRatio 26412 (mW 13206) (1/10^6) rowEps))) /
    (712/10000 - 26412*(1+1/10^6)*((1957897/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26412 (mW 13206) /
    ((1/10^5) * ((mW 13206 : ℝ)*26412*((mW 13206 : ℝ)+26412+1)))^2 +
  8*(mW 13206 : ℝ)*26412*(26412+2)*(26412+3) /
    ((1/1000)*((mW 13206 : ℝ)*26412*(26412+2)))^2 +
  covarianceVarianceBound 26412 (mW 13206) /
    ((1/1000)*covarianceMeanBound 26412 (mW 13206))^2 +
  normVarianceBound 26412 (mW 13206) / (3*inputVarianceMean 26412 (mW 13206))^2

end BstLean.Part268.WorldRow13206
namespace BstLean.Part268.WorldRow13207
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13207 = 264736987392200 := by
  have hu : mW 13207 ≤ 264736987392200 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13207 ≤ 264736987392199 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13207)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26414 ^ 2)
    ((25000000000000000000/4149101417596039930047329))
    ((25000000000000000000/4148944337963360440372199)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26414) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26414 : ℝ)^2 / (mW 13207 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1957747/1000000000000))/2) * ((1-firstRatio 26414) * √(1-firstRatio 26414) *
      sixthConstant (e1CovarianceRatio 26414 (mW 13207) (1/10^6) rowEps))) /
    (712/10000 - 26414*(1+1/10^6)*((1957747/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26414 (mW 13207) /
    ((1/10^5) * ((mW 13207 : ℝ)*26414*((mW 13207 : ℝ)+26414+1)))^2 +
  8*(mW 13207 : ℝ)*26414*(26414+2)*(26414+3) /
    ((1/1000)*((mW 13207 : ℝ)*26414*(26414+2)))^2 +
  covarianceVarianceBound 26414 (mW 13207) /
    ((1/1000)*covarianceMeanBound 26414 (mW 13207))^2 +
  normVarianceBound 26414 (mW 13207) / (3*inputVarianceMean 26414 (mW 13207))^2

end BstLean.Part268.WorldRow13207
namespace BstLean.Part268.WorldRow13208
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13208 = 264807152240913 := by
  have hu : mW 13208 ≤ 264807152240913 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13208 ≤ 264807152240912 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13208)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26416 ^ 2)
    ((3125000000000000000/518676947107674863671397))
    ((5000000000000000000/829851699445743883939209)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26416) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26416 : ℝ)^2 / (mW 13208 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1957597/1000000000000))/2) * ((1-firstRatio 26416) * √(1-firstRatio 26416) *
      sixthConstant (e1CovarianceRatio 26416 (mW 13208) (1/10^6) rowEps))) /
    (712/10000 - 26416*(1+1/10^6)*((1957597/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26416 (mW 13208) /
    ((1/10^5) * ((mW 13208 : ℝ)*26416*((mW 13208 : ℝ)+26416+1)))^2 +
  8*(mW 13208 : ℝ)*26416*(26416+2)*(26416+3) /
    ((1/1000)*((mW 13208 : ℝ)*26416*(26416+2)))^2 +
  covarianceVarianceBound 26416 (mW 13208) /
    ((1/1000)*covarianceMeanBound 26416 (mW 13208))^2 +
  normVarianceBound 26416 (mW 13208) / (3*inputVarianceMean 26416 (mW 13208))^2

end BstLean.Part268.WorldRow13208
namespace BstLean.Part268.WorldRow13209
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13209 = 264877330371631 := by
  have hu : mW 13209 ≤ 264877330371631 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13209 ≤ 264877330371630 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13209)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26418 ^ 2)
    ((25000000000000000000/4149729736126757888695023))
    ((25000000000000000000/4149572656494078399019891)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26418) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26418 : ℝ)^2 / (mW 13209 : ℝ)) * (1 + 1/10^6)^2 *
    √(((244681/125000000000))/2) * ((1-firstRatio 26418) * √(1-firstRatio 26418) *
      sixthConstant (e1CovarianceRatio 26418 (mW 13209) (1/10^6) rowEps))) /
    (712/10000 - 26418*(1+1/10^6)*((244681/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26418 (mW 13209) /
    ((1/10^5) * ((mW 13209 : ℝ)*26418*((mW 13209 : ℝ)+26418+1)))^2 +
  8*(mW 13209 : ℝ)*26418*(26418+2)*(26418+3) /
    ((1/1000)*((mW 13209 : ℝ)*26418*(26418+2)))^2 +
  covarianceVarianceBound 26418 (mW 13209) /
    ((1/1000)*covarianceMeanBound 26418 (mW 13209))^2 +
  normVarianceBound 26418 (mW 13209) / (3*inputVarianceMean 26418 (mW 13209))^2

end BstLean.Part268.WorldRow13209
namespace BstLean.Part268.WorldRow13210
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13210 = 264947521785863 := by
  have hu : mW 13210 ≤ 264947521785863 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13210 ≤ 264947521785862 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13210)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26420 ^ 2)
    ((2500000000000000000/415004389539211686801887))
    ((25000000000000000000/4149886815759437378343737)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26420) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26420 : ℝ)^2 / (mW 13210 : ℝ)) * (1 + 1/10^6)^2 *
    √(((978649/500000000000))/2) * ((1-firstRatio 26420) * √(1-firstRatio 26420) *
      sixthConstant (e1CovarianceRatio 26420 (mW 13210) (1/10^6) rowEps))) /
    (712/10000 - 26420*(1+1/10^6)*((978649/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26420 (mW 13210) /
    ((1/10^5) * ((mW 13210 : ℝ)*26420*((mW 13210 : ℝ)+26420+1)))^2 +
  8*(mW 13210 : ℝ)*26420*(26420+2)*(26420+3) /
    ((1/1000)*((mW 13210 : ℝ)*26420*(26420+2)))^2 +
  covarianceVarianceBound 26420 (mW 13210) /
    ((1/1000)*covarianceMeanBound 26420 (mW 13210))^2 +
  normVarianceBound 26420 (mW 13210) / (3*inputVarianceMean 26420 (mW 13210))^2

end BstLean.Part268.WorldRow13210
namespace BstLean.Part268.WorldRow13211
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13211 = 265017726485117 := by
  have hu : mW 13211 ≤ 265017726485117 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13211 ≤ 265017726485116 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13211)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26422 ^ 2)
    ((25000000000000000000/4150358054657475847342717))
    ((25000000000000000000/4150200975024796357667583)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26422) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26422 : ℝ)^2 / (mW 13211 : ℝ)) * (1 + 1/10^6)^2 *
    √(((489287/250000000000))/2) * ((1-firstRatio 26422) * √(1-firstRatio 26422) *
      sixthConstant (e1CovarianceRatio 26422 (mW 13211) (1/10^6) rowEps))) /
    (712/10000 - 26422*(1+1/10^6)*((489287/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26422 (mW 13211) /
    ((1/10^5) * ((mW 13211 : ℝ)*26422*((mW 13211 : ℝ)+26422+1)))^2 +
  8*(mW 13211 : ℝ)*26422*(26422+2)*(26422+3) /
    ((1/1000)*((mW 13211 : ℝ)*26422*(26422+2)))^2 +
  covarianceVarianceBound 26422 (mW 13211) /
    ((1/1000)*covarianceMeanBound 26422 (mW 13211))^2 +
  normVarianceBound 26422 (mW 13211) / (3*inputVarianceMean 26422 (mW 13211))^2

end BstLean.Part268.WorldRow13211
namespace BstLean.Part268.WorldRow13212
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13212 = 265087944470901 := by
  have hu : mW 13212 ≤ 265087944470901 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13212 ≤ 265087944470900 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13212)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26424 ^ 2)
    ((6250000000000000000/1037668053480708706666641))
    ((25000000000000000000/4150515134290155336991429)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26424) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26424 : ℝ)^2 / (mW 13212 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1956999/1000000000000))/2) * ((1-firstRatio 26424) * √(1-firstRatio 26424) *
      sixthConstant (e1CovarianceRatio 26424 (mW 13212) (1/10^6) rowEps))) /
    (712/10000 - 26424*(1+1/10^6)*((1956999/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26424 (mW 13212) /
    ((1/10^5) * ((mW 13212 : ℝ)*26424*((mW 13212 : ℝ)+26424+1)))^2 +
  8*(mW 13212 : ℝ)*26424*(26424+2)*(26424+3) /
    ((1/1000)*((mW 13212 : ℝ)*26424*(26424+2)))^2 +
  covarianceVarianceBound 26424 (mW 13212) /
    ((1/1000)*covarianceMeanBound 26424 (mW 13212))^2 +
  normVarianceBound 26424 (mW 13212) / (3*inputVarianceMean 26424 (mW 13212))^2

end BstLean.Part268.WorldRow13212
namespace BstLean.Part268.WorldRow13213
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13213 = 265158175744725 := by
  have hu : mW 13213 ≤ 265158175744725 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13213 ≤ 265158175744724 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13213)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26426 ^ 2)
    ((25000000000000000000/4150986373188193805990411))
    ((1000000000000000000/166033171742220572652611)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26426) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26426 : ℝ)^2 / (mW 13213 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1956849/1000000000000))/2) * ((1-firstRatio 26426) * √(1-firstRatio 26426) *
      sixthConstant (e1CovarianceRatio 26426 (mW 13213) (1/10^6) rowEps))) /
    (712/10000 - 26426*(1+1/10^6)*((1956849/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26426 (mW 13213) /
    ((1/10^5) * ((mW 13213 : ℝ)*26426*((mW 13213 : ℝ)+26426+1)))^2 +
  8*(mW 13213 : ℝ)*26426*(26426+2)*(26426+3) /
    ((1/1000)*((mW 13213 : ℝ)*26426*(26426+2)))^2 +
  covarianceVarianceBound 26426 (mW 13213) /
    ((1/1000)*covarianceMeanBound 26426 (mW 13213))^2 +
  normVarianceBound 26426 (mW 13213) / (3*inputVarianceMean 26426 (mW 13213))^2

end BstLean.Part268.WorldRow13213
namespace BstLean.Part268.WorldRow13214
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13214 = 265228420308096 := by
  have hu : mW 13214 ≤ 265228420308096 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13214 ≤ 265228420308095 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13214)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26428 ^ 2)
    ((12500000000000000000/2075650266226776392657129))
    ((25000000000000000000/4151143452820873295639121)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26428) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26428 : ℝ)^2 / (mW 13214 : ℝ)) * (1 + 1/10^6)^2 *
    √(((19567/10000000000))/2) * ((1-firstRatio 26428) * √(1-firstRatio 26428) *
      sixthConstant (e1CovarianceRatio 26428 (mW 13214) (1/10^6) rowEps))) /
    (712/10000 - 26428*(1+1/10^6)*((19567/10000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26428 (mW 13214) /
    ((1/10^5) * ((mW 13214 : ℝ)*26428*((mW 13214 : ℝ)+26428+1)))^2 +
  8*(mW 13214 : ℝ)*26428*(26428+2)*(26428+3) /
    ((1/1000)*((mW 13214 : ℝ)*26428*(26428+2)))^2 +
  covarianceVarianceBound 26428 (mW 13214) /
    ((1/1000)*covarianceMeanBound 26428 (mW 13214))^2 +
  normVarianceBound 26428 (mW 13214) / (3*inputVarianceMean 26428 (mW 13214))^2

end BstLean.Part268.WorldRow13214
namespace BstLean.Part268.WorldRow13215
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13215 = 265298678162524 := by
  have hu : mW 13215 ≤ 265298678162524 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13215 ≤ 265298678162523 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13215)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26430 ^ 2)
    ((5000000000000000000/830322938343782352927621))
    ((25000000000000000000/4151457612086232274962967)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26430) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26430 : ℝ)^2 / (mW 13215 : ℝ)) * (1 + 1/10^6)^2 *
    √(((39131/20000000000))/2) * ((1-firstRatio 26430) * √(1-firstRatio 26430) *
      sixthConstant (e1CovarianceRatio 26430 (mW 13215) (1/10^6) rowEps))) /
    (712/10000 - 26430*(1+1/10^6)*((39131/20000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26430 (mW 13215) /
    ((1/10^5) * ((mW 13215 : ℝ)*26430*((mW 13215 : ℝ)+26430+1)))^2 +
  8*(mW 13215 : ℝ)*26430*(26430+2)*(26430+3) /
    ((1/1000)*((mW 13215 : ℝ)*26430*(26430+2)))^2 +
  covarianceVarianceBound 26430 (mW 13215) /
    ((1/1000)*covarianceMeanBound 26430 (mW 13215))^2 +
  normVarianceBound 26430 (mW 13215) / (3*inputVarianceMean 26430 (mW 13215))^2

end BstLean.Part268.WorldRow13215
namespace BstLean.Part268.WorldRow13216
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13216 = 265368949309518 := by
  have hu : mW 13216 ≤ 265368949309518 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13216 ≤ 265368949309517 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13216)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26432 ^ 2)
    ((781250000000000000/129747776593258460748811))
    ((25000000000000000000/4151771771351591254286813)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26432) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26432 : ℝ)^2 / (mW 13216 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1956401/1000000000000))/2) * ((1-firstRatio 26432) * √(1-firstRatio 26432) *
      sixthConstant (e1CovarianceRatio 26432 (mW 13216) (1/10^6) rowEps))) /
    (712/10000 - 26432*(1+1/10^6)*((1956401/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26432 (mW 13216) /
    ((1/10^5) * ((mW 13216 : ℝ)*26432*((mW 13216 : ℝ)+26432+1)))^2 +
  8*(mW 13216 : ℝ)*26432*(26432+2)*(26432+3) /
    ((1/1000)*((mW 13216 : ℝ)*26432*(26432+2)))^2 +
  covarianceVarianceBound 26432 (mW 13216) /
    ((1/1000)*covarianceMeanBound 26432 (mW 13216))^2 +
  normVarianceBound 26432 (mW 13216) / (3*inputVarianceMean 26432 (mW 13216))^2

end BstLean.Part268.WorldRow13216
namespace BstLean.Part268.WorldRow13217
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13217 = 265439233750585 := by
  have hu : mW 13217 ≤ 265439233750585 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13217 ≤ 265439233750584 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13217)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26434 ^ 2)
    ((25000000000000000000/4152243010249629723285799))
    ((25000000000000000000/4152085930616950233610659)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26434) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26434 : ℝ)^2 / (mW 13217 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1956251/1000000000000))/2) * ((1-firstRatio 26434) * √(1-firstRatio 26434) *
      sixthConstant (e1CovarianceRatio 26434 (mW 13217) (1/10^6) rowEps))) /
    (712/10000 - 26434*(1+1/10^6)*((1956251/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26434 (mW 13217) /
    ((1/10^5) * ((mW 13217 : ℝ)*26434*((mW 13217 : ℝ)+26434+1)))^2 +
  8*(mW 13217 : ℝ)*26434*(26434+2)*(26434+3) /
    ((1/1000)*((mW 13217 : ℝ)*26434*(26434+2)))^2 +
  covarianceVarianceBound 26434 (mW 13217) /
    ((1/1000)*covarianceMeanBound 26434 (mW 13217))^2 +
  normVarianceBound 26434 (mW 13217) / (3*inputVarianceMean 26434 (mW 13217))^2

end BstLean.Part268.WorldRow13217
namespace BstLean.Part268.WorldRow13218
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13218 = 265509531487236 := by
  have hu : mW 13218 ≤ 265509531487236 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13218 ≤ 265509531487235 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13218)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26436 ^ 2)
    ((12500000000000000000/2076278584757494351304823))
    ((5000000000000000000/830480017976461842586901)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26436) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26436 : ℝ)^2 / (mW 13218 : ℝ)) * (1 + 1/10^6)^2 *
    √(((978051/500000000000))/2) * ((1-firstRatio 26436) * √(1-firstRatio 26436) *
      sixthConstant (e1CovarianceRatio 26436 (mW 13218) (1/10^6) rowEps))) /
    (712/10000 - 26436*(1+1/10^6)*((978051/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26436 (mW 13218) /
    ((1/10^5) * ((mW 13218 : ℝ)*26436*((mW 13218 : ℝ)+26436+1)))^2 +
  8*(mW 13218 : ℝ)*26436*(26436+2)*(26436+3) /
    ((1/1000)*((mW 13218 : ℝ)*26436*(26436+2)))^2 +
  covarianceVarianceBound 26436 (mW 13218) /
    ((1/1000)*covarianceMeanBound 26436 (mW 13218))^2 +
  normVarianceBound 26436 (mW 13218) / (3*inputVarianceMean 26436 (mW 13218))^2

end BstLean.Part268.WorldRow13218
namespace BstLean.Part268.WorldRow13219
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13219 = 265579842520979 := by
  have hu : mW 13219 ≤ 265579842520979 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13219 ≤ 265579842520978 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13219)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26438 ^ 2)
    ((25000000000000000000/4152871328780347681933493))
    ((25000000000000000000/4152714249147668192258351)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26438) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26438 : ℝ)^2 / (mW 13219 : ℝ)) * (1 + 1/10^6)^2 *
    √(((122247/62500000000))/2) * ((1-firstRatio 26438) * √(1-firstRatio 26438) *
      sixthConstant (e1CovarianceRatio 26438 (mW 13219) (1/10^6) rowEps))) /
    (712/10000 - 26438*(1+1/10^6)*((122247/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26438 (mW 13219) /
    ((1/10^5) * ((mW 13219 : ℝ)*26438*((mW 13219 : ℝ)+26438+1)))^2 +
  8*(mW 13219 : ℝ)*26438*(26438+2)*(26438+3) /
    ((1/1000)*((mW 13219 : ℝ)*26438*(26438+2)))^2 +
  covarianceVarianceBound 26438 (mW 13219) /
    ((1/1000)*covarianceMeanBound 26438 (mW 13219))^2 +
  normVarianceBound 26438 (mW 13219) / (3*inputVarianceMean 26438 (mW 13219))^2

end BstLean.Part268.WorldRow13219
namespace BstLean.Part268.WorldRow13220
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13220 = 265650166853322 := by
  have hu : mW 13220 ≤ 265650166853322 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13220 ≤ 265650166853321 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13220)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26440 ^ 2)
    ((1250000000000000000/207659274402285333062867))
    ((25000000000000000000/4153028408413027171582197)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26440) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26440 : ℝ)^2 / (mW 13220 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1955803/1000000000000))/2) * ((1-firstRatio 26440) * √(1-firstRatio 26440) *
      sixthConstant (e1CovarianceRatio 26440 (mW 13220) (1/10^6) rowEps))) /
    (712/10000 - 26440*(1+1/10^6)*((1955803/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26440 (mW 13220) /
    ((1/10^5) * ((mW 13220 : ℝ)*26440*((mW 13220 : ℝ)+26440+1)))^2 +
  8*(mW 13220 : ℝ)*26440*(26440+2)*(26440+3) /
    ((1/1000)*((mW 13220 : ℝ)*26440*(26440+2)))^2 +
  covarianceVarianceBound 26440 (mW 13220) /
    ((1/1000)*covarianceMeanBound 26440 (mW 13220))^2 +
  normVarianceBound 26440 (mW 13220) / (3*inputVarianceMean 26440 (mW 13220))^2

end BstLean.Part268.WorldRow13220
namespace BstLean.Part268.WorldRow13221
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13221 = 265720504485776 := by
  have hu : mW 13221 ≤ 265720504485776 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13221 ≤ 265720504485775 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13221)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26442 ^ 2)
    ((25000000000000000000/4153499647311065640581187))
    ((25000000000000000000/4153342567678386150906043)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26442) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26442 : ℝ)^2 / (mW 13221 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1955653/1000000000000))/2) * ((1-firstRatio 26442) * √(1-firstRatio 26442) *
      sixthConstant (e1CovarianceRatio 26442 (mW 13221) (1/10^6) rowEps))) /
    (712/10000 - 26442*(1+1/10^6)*((1955653/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26442 (mW 13221) /
    ((1/10^5) * ((mW 13221 : ℝ)*26442*((mW 13221 : ℝ)+26442+1)))^2 +
  8*(mW 13221 : ℝ)*26442*(26442+2)*(26442+3) /
    ((1/1000)*((mW 13221 : ℝ)*26442*(26442+2)))^2 +
  covarianceVarianceBound 26442 (mW 13221) /
    ((1/1000)*covarianceMeanBound 26442 (mW 13221))^2 +
  normVarianceBound 26442 (mW 13221) / (3*inputVarianceMean 26442 (mW 13221))^2

end BstLean.Part268.WorldRow13221
namespace BstLean.Part268.WorldRow13222
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13222 = 265790855419849 := by
  have hu : mW 13222 ≤ 265790855419849 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13222 ≤ 265790855419848 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13222)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26444 ^ 2)
    ((12500000000000000000/2076906903288212309952517))
    ((25000000000000000000/4153656726943745130229889)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26444) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26444 : ℝ)^2 / (mW 13222 : ℝ)) * (1 + 1/10^6)^2 *
    √(((122219/62500000000))/2) * ((1-firstRatio 26444) * √(1-firstRatio 26444) *
      sixthConstant (e1CovarianceRatio 26444 (mW 13222) (1/10^6) rowEps))) /
    (712/10000 - 26444*(1+1/10^6)*((122219/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26444 (mW 13222) /
    ((1/10^5) * ((mW 13222 : ℝ)*26444*((mW 13222 : ℝ)+26444+1)))^2 +
  8*(mW 13222 : ℝ)*26444*(26444+2)*(26444+3) /
    ((1/1000)*((mW 13222 : ℝ)*26444*(26444+2)))^2 +
  covarianceVarianceBound 26444 (mW 13222) /
    ((1/1000)*covarianceMeanBound 26444 (mW 13222))^2 +
  normVarianceBound 26444 (mW 13222) / (3*inputVarianceMean 26444 (mW 13222))^2

end BstLean.Part268.WorldRow13222
namespace BstLean.Part268.WorldRow13223
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13223 = 265861219657051 := by
  have hu : mW 13223 ≤ 265861219657051 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13223 ≤ 265861219657050 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13223)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26446 ^ 2)
    ((25000000000000000000/4154127965841783599228881))
    ((5000000000000000000/830794177241820821910747)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26446) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26446 : ℝ)^2 / (mW 13223 : ℝ)) * (1 + 1/10^6)^2 *
    √(((391071/200000000000))/2) * ((1-firstRatio 26446) * √(1-firstRatio 26446) *
      sixthConstant (e1CovarianceRatio 26446 (mW 13223) (1/10^6) rowEps))) /
    (712/10000 - 26446*(1+1/10^6)*((391071/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26446 (mW 13223) /
    ((1/10^5) * ((mW 13223 : ℝ)*26446*((mW 13223 : ℝ)+26446+1)))^2 +
  8*(mW 13223 : ℝ)*26446*(26446+2)*(26446+3) /
    ((1/1000)*((mW 13223 : ℝ)*26446*(26446+2)))^2 +
  covarianceVarianceBound 26446 (mW 13223) /
    ((1/1000)*covarianceMeanBound 26446 (mW 13223))^2 +
  normVarianceBound 26446 (mW 13223) / (3*inputVarianceMean 26446 (mW 13223))^2

end BstLean.Part268.WorldRow13223
namespace BstLean.Part268.WorldRow13224
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13224 = 265931597198890 := by
  have hu : mW 13224 ≤ 265931597198890 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13224 ≤ 265931597198889 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13224)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26448 ^ 2)
    ((3125000000000000000/519305265638392822319091))
    ((25000000000000000000/4154285045474463088877581)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26448) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26448 : ℝ)^2 / (mW 13224 : ℝ)) * (1 + 1/10^6)^2 *
    √(((391041/200000000000))/2) * ((1-firstRatio 26448) * √(1-firstRatio 26448) *
      sixthConstant (e1CovarianceRatio 26448 (mW 13224) (1/10^6) rowEps))) /
    (712/10000 - 26448*(1+1/10^6)*((391041/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26448 (mW 13224) /
    ((1/10^5) * ((mW 13224 : ℝ)*26448*((mW 13224 : ℝ)+26448+1)))^2 +
  8*(mW 13224 : ℝ)*26448*(26448+2)*(26448+3) /
    ((1/1000)*((mW 13224 : ℝ)*26448*(26448+2)))^2 +
  covarianceVarianceBound 26448 (mW 13224) /
    ((1/1000)*covarianceMeanBound 26448 (mW 13224))^2 +
  normVarianceBound 26448 (mW 13224) / (3*inputVarianceMean 26448 (mW 13224))^2

end BstLean.Part268.WorldRow13224
