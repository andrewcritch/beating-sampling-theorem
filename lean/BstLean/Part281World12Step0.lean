import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part281Scalar12
namespace BstLean.Part281.WorldRow12159
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12159 = 198217732897554 := by
  have hu : mW 12159 ≤ 198217732897554 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12159 ≤ 198217732897553 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12159)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24318 ^ 2)
    ((25000000000000000000/3819862507499829598655673))
    ((25000000000000000000/3819705427867150108981591)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24318) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24318 : ℝ)^2 / (mW 12159 : ℝ)) * (1 + 1/10^6)^2 *
    √(((532083/250000000000))/2) * ((1-firstRatio 24318) * √(1-firstRatio 24318) *
      sixthConstant (e1CovarianceRatio 24318 (mW 12159) (1/10^6) rowEps))) /
    (712/10000 - 24318*(1+1/10^6)*((532083/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24318 (mW 12159) /
    ((1/10^5) * ((mW 12159 : ℝ)*24318*((mW 12159 : ℝ)+24318+1)))^2 +
  8*(mW 12159 : ℝ)*24318*(24318+2)*(24318+3) /
    ((1/1000)*((mW 12159 : ℝ)*24318*(24318+2)))^2 +
  covarianceVarianceBound 24318 (mW 12159) /
    ((1/1000)*covarianceMeanBound 24318 (mW 12159))^2 +
  normVarianceBound 24318 (mW 12159) / (3*inputVarianceMean 24318 (mW 12159))^2

end BstLean.Part281.WorldRow12159
namespace BstLean.Part281.WorldRow12160
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12160 = 198274796257200 := by
  have hu : mW 12160 ≤ 198274796257200 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12160 ≤ 198274796257199 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12160)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24320 ^ 2)
    ((39062500000000000/5969026041820607153093))
    ((25000000000000000000/3820019587132509088305437)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24320) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24320 : ℝ)^2 / (mW 12160 : ℝ)) * (1 + 1/10^6)^2 *
    √(((425631/200000000000))/2) * ((1-firstRatio 24320) * √(1-firstRatio 24320) *
      sixthConstant (e1CovarianceRatio 24320 (mW 12160) (1/10^6) rowEps))) /
    (712/10000 - 24320*(1+1/10^6)*((425631/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24320 (mW 12160) /
    ((1/10^5) * ((mW 12160 : ℝ)*24320*((mW 12160 : ℝ)+24320+1)))^2 +
  8*(mW 12160 : ℝ)*24320*(24320+2)*(24320+3) /
    ((1/1000)*((mW 12160 : ℝ)*24320*(24320+2)))^2 +
  covarianceVarianceBound 24320 (mW 12160) /
    ((1/1000)*covarianceMeanBound 24320 (mW 12160))^2 +
  normVarianceBound 24320 (mW 12160) / (3*inputVarianceMean 24320 (mW 12160))^2

end BstLean.Part281.WorldRow12160
namespace BstLean.Part281.WorldRow12161
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12161 = 198331871349829 := by
  have hu : mW 12161 ≤ 198331871349829 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12161 ≤ 198331871349828 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12161)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24322 ^ 2)
    ((25000000000000000000/3820490826030547557303367))
    ((25000000000000000000/3820333746397868067629283)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24322) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24322 : ℝ)^2 / (mW 12161 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2127979/1000000000000))/2) * ((1-firstRatio 24322) * √(1-firstRatio 24322) *
      sixthConstant (e1CovarianceRatio 24322 (mW 12161) (1/10^6) rowEps))) /
    (712/10000 - 24322*(1+1/10^6)*((2127979/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24322 (mW 12161) /
    ((1/10^5) * ((mW 12161 : ℝ)*24322*((mW 12161 : ℝ)+24322+1)))^2 +
  8*(mW 12161 : ℝ)*24322*(24322+2)*(24322+3) /
    ((1/1000)*((mW 12161 : ℝ)*24322*(24322+2)))^2 +
  covarianceVarianceBound 24322 (mW 12161) /
    ((1/1000)*covarianceMeanBound 24322 (mW 12161))^2 +
  normVarianceBound 24322 (mW 12161) / (3*inputVarianceMean 24322 (mW 12161))^2

end BstLean.Part281.WorldRow12161
namespace BstLean.Part281.WorldRow12162
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12162 = 198388958176888 := by
  have hu : mW 12162 ≤ 198388958176888 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12162 ≤ 198388958176887 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12162)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24324 ^ 2)
    ((12500000000000000000/1910402492647953268313607))
    ((25000000000000000000/3820647905663227046953129)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24324) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24324 : ℝ)^2 / (mW 12162 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1063901/500000000000))/2) * ((1-firstRatio 24324) * √(1-firstRatio 24324) *
      sixthConstant (e1CovarianceRatio 24324 (mW 12162) (1/10^6) rowEps))) /
    (712/10000 - 24324*(1+1/10^6)*((1063901/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24324 (mW 12162) /
    ((1/10^5) * ((mW 12162 : ℝ)*24324*((mW 12162 : ℝ)+24324+1)))^2 +
  8*(mW 12162 : ℝ)*24324*(24324+2)*(24324+3) /
    ((1/1000)*((mW 12162 : ℝ)*24324*(24324+2)))^2 +
  covarianceVarianceBound 24324 (mW 12162) /
    ((1/1000)*covarianceMeanBound 24324 (mW 12162))^2 +
  normVarianceBound 24324 (mW 12162) / (3*inputVarianceMean 24324 (mW 12162))^2

end BstLean.Part281.WorldRow12162
namespace BstLean.Part281.WorldRow12163
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12163 = 198446056739823 := by
  have hu : mW 12163 ≤ 198446056739823 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12163 ≤ 198446056739822 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12163)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24326 ^ 2)
    ((25000000000000000000/3821119144561265515951061))
    ((1000000000000000000/152838482597143441051079)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24326) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24326 : ℝ)^2 / (mW 12163 : ℝ)) * (1 + 1/10^6)^2 *
    √(((17021/8000000000))/2) * ((1-firstRatio 24326) * √(1-firstRatio 24326) *
      sixthConstant (e1CovarianceRatio 24326 (mW 12163) (1/10^6) rowEps))) /
    (712/10000 - 24326*(1+1/10^6)*((17021/8000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24326 (mW 12163) /
    ((1/10^5) * ((mW 12163 : ℝ)*24326*((mW 12163 : ℝ)+24326+1)))^2 +
  8*(mW 12163 : ℝ)*24326*(24326+2)*(24326+3) /
    ((1/1000)*((mW 12163 : ℝ)*24326*(24326+2)))^2 +
  covarianceVarianceBound 24326 (mW 12163) /
    ((1/1000)*covarianceMeanBound 24326 (mW 12163))^2 +
  normVarianceBound 24326 (mW 12163) / (3*inputVarianceMean 24326 (mW 12163))^2

end BstLean.Part281.WorldRow12163
namespace BstLean.Part281.WorldRow12164
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12164 = 198503167040083 := by
  have hu : mW 12164 ≤ 198503167040083 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12164 ≤ 198503167040082 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12164)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24328 ^ 2)
    ((6250000000000000000/955358325956656123818727))
    ((25000000000000000000/3821276224193945005600821)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24328) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24328 : ℝ)^2 / (mW 12164 : ℝ)) * (1 + 1/10^6)^2 *
    √(((265931/125000000000))/2) * ((1-firstRatio 24328) * √(1-firstRatio 24328) *
      sixthConstant (e1CovarianceRatio 24328 (mW 12164) (1/10^6) rowEps))) /
    (712/10000 - 24328*(1+1/10^6)*((265931/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24328 (mW 12164) /
    ((1/10^5) * ((mW 12164 : ℝ)*24328*((mW 12164 : ℝ)+24328+1)))^2 +
  8*(mW 12164 : ℝ)*24328*(24328+2)*(24328+3) /
    ((1/1000)*((mW 12164 : ℝ)*24328*(24328+2)))^2 +
  covarianceVarianceBound 24328 (mW 12164) /
    ((1/1000)*covarianceMeanBound 24328 (mW 12164))^2 +
  normVarianceBound 24328 (mW 12164) / (3*inputVarianceMean 24328 (mW 12164))^2

end BstLean.Part281.WorldRow12164
namespace BstLean.Part281.WorldRow12165
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12165 = 198560289079115 := by
  have hu : mW 12165 ≤ 198560289079115 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12165 ≤ 198560289079114 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12165)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24330 ^ 2)
    ((5000000000000000000/764349492618396694919751))
    ((25000000000000000000/3821590383459303984924667)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24330) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24330 : ℝ)^2 / (mW 12165 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2127271/1000000000000))/2) * ((1-firstRatio 24330) * √(1-firstRatio 24330) *
      sixthConstant (e1CovarianceRatio 24330 (mW 12165) (1/10^6) rowEps))) /
    (712/10000 - 24330*(1+1/10^6)*((2127271/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24330 (mW 12165) /
    ((1/10^5) * ((mW 12165 : ℝ)*24330*((mW 12165 : ℝ)+24330+1)))^2 +
  8*(mW 12165 : ℝ)*24330*(24330+2)*(24330+3) /
    ((1/1000)*((mW 12165 : ℝ)*24330*(24330+2)))^2 +
  covarianceVarianceBound 24330 (mW 12165) /
    ((1/1000)*covarianceMeanBound 24330 (mW 12165))^2 +
  normVarianceBound 24330 (mW 12165) / (3*inputVarianceMean 24330 (mW 12165))^2

end BstLean.Part281.WorldRow12165
namespace BstLean.Part281.WorldRow12166
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12166 = 198617422858367 := by
  have hu : mW 12166 ≤ 198617422858367 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12166 ≤ 198617422858366 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12166)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24332 ^ 2)
    ((12500000000000000000/1911030811178671226961301))
    ((25000000000000000000/3821904542724662964248513)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24332) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24332 : ℝ)^2 / (mW 12166 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1063547/500000000000))/2) * ((1-firstRatio 24332) * √(1-firstRatio 24332) *
      sixthConstant (e1CovarianceRatio 24332 (mW 12166) (1/10^6) rowEps))) /
    (712/10000 - 24332*(1+1/10^6)*((1063547/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24332 (mW 12166) /
    ((1/10^5) * ((mW 12166 : ℝ)*24332*((mW 12166 : ℝ)+24332+1)))^2 +
  8*(mW 12166 : ℝ)*24332*(24332+2)*(24332+3) /
    ((1/1000)*((mW 12166 : ℝ)*24332*(24332+2)))^2 +
  covarianceVarianceBound 24332 (mW 12166) /
    ((1/1000)*covarianceMeanBound 24332 (mW 12166))^2 +
  normVarianceBound 24332 (mW 12166) / (3*inputVarianceMean 24332 (mW 12166))^2

end BstLean.Part281.WorldRow12166
namespace BstLean.Part281.WorldRow12167
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12167 = 198674568379286 := by
  have hu : mW 12167 ≤ 198674568379286 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12167 ≤ 198674568379285 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12167)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24334 ^ 2)
    ((25000000000000000000/3822375781622701433246449))
    ((25000000000000000000/3822218701990021943572359)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24334) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24334 : ℝ)^2 / (mW 12167 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2126917/1000000000000))/2) * ((1-firstRatio 24334) * √(1-firstRatio 24334) *
      sixthConstant (e1CovarianceRatio 24334 (mW 12167) (1/10^6) rowEps))) /
    (712/10000 - 24334*(1+1/10^6)*((2126917/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24334 (mW 12167) /
    ((1/10^5) * ((mW 12167 : ℝ)*24334*((mW 12167 : ℝ)+24334+1)))^2 +
  8*(mW 12167 : ℝ)*24334*(24334+2)*(24334+3) /
    ((1/1000)*((mW 12167 : ℝ)*24334*(24334+2)))^2 +
  covarianceVarianceBound 24334 (mW 12167) /
    ((1/1000)*covarianceMeanBound 24334 (mW 12167))^2 +
  normVarianceBound 24334 (mW 12167) / (3*inputVarianceMean 24334 (mW 12167))^2

end BstLean.Part281.WorldRow12167
namespace BstLean.Part281.WorldRow12168
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12168 = 198731725643320 := by
  have hu : mW 12168 ≤ 198731725643320 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12168 ≤ 198731725643319 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12168)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24336 ^ 2)
    ((3125000000000000000/477836242611007551571287))
    ((5000000000000000000/764506572251076184579241)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24336) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24336 : ℝ)^2 / (mW 12168 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2126741/1000000000000))/2) * ((1-firstRatio 24336) * √(1-firstRatio 24336) *
      sixthConstant (e1CovarianceRatio 24336 (mW 12168) (1/10^6) rowEps))) /
    (712/10000 - 24336*(1+1/10^6)*((2126741/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24336 (mW 12168) /
    ((1/10^5) * ((mW 12168 : ℝ)*24336*((mW 12168 : ℝ)+24336+1)))^2 +
  8*(mW 12168 : ℝ)*24336*(24336+2)*(24336+3) /
    ((1/1000)*((mW 12168 : ℝ)*24336*(24336+2)))^2 +
  covarianceVarianceBound 24336 (mW 12168) /
    ((1/1000)*covarianceMeanBound 24336 (mW 12168))^2 +
  normVarianceBound 24336 (mW 12168) / (3*inputVarianceMean 24336 (mW 12168))^2

end BstLean.Part281.WorldRow12168
namespace BstLean.Part281.WorldRow12169
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12169 = 198788894651917 := by
  have hu : mW 12169 ≤ 198788894651917 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12169 ≤ 198788894651916 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12169)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24338 ^ 2)
    ((25000000000000000000/3823004100153419391894143))
    ((25000000000000000000/3822847020520739902220051)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24338) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24338 : ℝ)^2 / (mW 12169 : ℝ)) * (1 + 1/10^6)^2 *
    √(((531641/250000000000))/2) * ((1-firstRatio 24338) * √(1-firstRatio 24338) *
      sixthConstant (e1CovarianceRatio 24338 (mW 12169) (1/10^6) rowEps))) /
    (712/10000 - 24338*(1+1/10^6)*((531641/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24338 (mW 12169) /
    ((1/10^5) * ((mW 12169 : ℝ)*24338*((mW 12169 : ℝ)+24338+1)))^2 +
  8*(mW 12169 : ℝ)*24338*(24338+2)*(24338+3) /
    ((1/1000)*((mW 12169 : ℝ)*24338*(24338+2)))^2 +
  covarianceVarianceBound 24338 (mW 12169) /
    ((1/1000)*covarianceMeanBound 24338 (mW 12169))^2 +
  normVarianceBound 24338 (mW 12169) / (3*inputVarianceMean 24338 (mW 12169))^2

end BstLean.Part281.WorldRow12169
namespace BstLean.Part281.WorldRow12170
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12170 = 198846075406525 := by
  have hu : mW 12170 ≤ 198846075406525 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12170 ≤ 198846075406524 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12170)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24340 ^ 2)
    ((2500000000000000000/382331825941877837121799))
    ((25000000000000000000/3823161179786098881543897)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24340) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24340 : ℝ)^2 / (mW 12170 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2126387/1000000000000))/2) * ((1-firstRatio 24340) * √(1-firstRatio 24340) *
      sixthConstant (e1CovarianceRatio 24340 (mW 12170) (1/10^6) rowEps))) /
    (712/10000 - 24340*(1+1/10^6)*((2126387/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24340 (mW 12170) /
    ((1/10^5) * ((mW 12170 : ℝ)*24340*((mW 12170 : ℝ)+24340+1)))^2 +
  8*(mW 12170 : ℝ)*24340*(24340+2)*(24340+3) /
    ((1/1000)*((mW 12170 : ℝ)*24340*(24340+2)))^2 +
  covarianceVarianceBound 24340 (mW 12170) /
    ((1/1000)*covarianceMeanBound 24340 (mW 12170))^2 +
  normVarianceBound 24340 (mW 12170) / (3*inputVarianceMean 24340 (mW 12170))^2

end BstLean.Part281.WorldRow12170
namespace BstLean.Part281.WorldRow12171
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12171 = 198903267908591 := by
  have hu : mW 12171 ≤ 198903267908591 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12171 ≤ 198903267908590 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12171)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24342 ^ 2)
    ((25000000000000000000/3823632418684137350541837))
    ((25000000000000000000/3823475339051457860867743)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24342) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24342 : ℝ)^2 / (mW 12171 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2126211/1000000000000))/2) * ((1-firstRatio 24342) * √(1-firstRatio 24342) *
      sixthConstant (e1CovarianceRatio 24342 (mW 12171) (1/10^6) rowEps))) /
    (712/10000 - 24342*(1+1/10^6)*((2126211/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24342 (mW 12171) /
    ((1/10^5) * ((mW 12171 : ℝ)*24342*((mW 12171 : ℝ)+24342+1)))^2 +
  8*(mW 12171 : ℝ)*24342*(24342+2)*(24342+3) /
    ((1/1000)*((mW 12171 : ℝ)*24342*(24342+2)))^2 +
  covarianceVarianceBound 24342 (mW 12171) /
    ((1/1000)*covarianceMeanBound 24342 (mW 12171))^2 +
  normVarianceBound 24342 (mW 12171) / (3*inputVarianceMean 24342 (mW 12171))^2

end BstLean.Part281.WorldRow12171
namespace BstLean.Part281.WorldRow12172
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12172 = 198960472159564 := by
  have hu : mW 12172 ≤ 198960472159564 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12172 ≤ 198960472159563 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12172)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24344 ^ 2)
    ((6250000000000000000/955986644487374082466421))
    ((25000000000000000000/3823789498316816840191589)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24344) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24344 : ℝ)^2 / (mW 12172 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1063017/500000000000))/2) * ((1-firstRatio 24344) * √(1-firstRatio 24344) *
      sixthConstant (e1CovarianceRatio 24344 (mW 12172) (1/10^6) rowEps))) /
    (712/10000 - 24344*(1+1/10^6)*((1063017/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24344 (mW 12172) /
    ((1/10^5) * ((mW 12172 : ℝ)*24344*((mW 12172 : ℝ)+24344+1)))^2 +
  8*(mW 12172 : ℝ)*24344*(24344+2)*(24344+3) /
    ((1/1000)*((mW 12172 : ℝ)*24344*(24344+2)))^2 +
  covarianceVarianceBound 24344 (mW 12172) /
    ((1/1000)*covarianceMeanBound 24344 (mW 12172))^2 +
  normVarianceBound 24344 (mW 12172) / (3*inputVarianceMean 24344 (mW 12172))^2

end BstLean.Part281.WorldRow12172
namespace BstLean.Part281.WorldRow12173
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12173 = 199017688160891 := by
  have hu : mW 12173 ≤ 199017688160891 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12173 ≤ 199017688160890 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12173)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24346 ^ 2)
    ((25000000000000000000/3824260737214855309189531))
    ((5000000000000000000/764820731516435163903087)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24346) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24346 : ℝ)^2 / (mW 12173 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2125857/1000000000000))/2) * ((1-firstRatio 24346) * √(1-firstRatio 24346) *
      sixthConstant (e1CovarianceRatio 24346 (mW 12173) (1/10^6) rowEps))) /
    (712/10000 - 24346*(1+1/10^6)*((2125857/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24346 (mW 12173) /
    ((1/10^5) * ((mW 12173 : ℝ)*24346*((mW 12173 : ℝ)+24346+1)))^2 +
  8*(mW 12173 : ℝ)*24346*(24346+2)*(24346+3) /
    ((1/1000)*((mW 12173 : ℝ)*24346*(24346+2)))^2 +
  covarianceVarianceBound 24346 (mW 12173) /
    ((1/1000)*covarianceMeanBound 24346 (mW 12173))^2 +
  normVarianceBound 24346 (mW 12173) / (3*inputVarianceMean 24346 (mW 12173))^2

end BstLean.Part281.WorldRow12173
namespace BstLean.Part281.WorldRow12174
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12174 = 199074915914020 := by
  have hu : mW 12174 ≤ 199074915914020 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12174 ≤ 199074915914019 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12174)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24348 ^ 2)
    ((12500000000000000000/1912287448240107144256689))
    ((25000000000000000000/3824417816847534798839281)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24348) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24348 : ℝ)^2 / (mW 12174 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2125681/1000000000000))/2) * ((1-firstRatio 24348) * √(1-firstRatio 24348) *
      sixthConstant (e1CovarianceRatio 24348 (mW 12174) (1/10^6) rowEps))) /
    (712/10000 - 24348*(1+1/10^6)*((2125681/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24348 (mW 12174) /
    ((1/10^5) * ((mW 12174 : ℝ)*24348*((mW 12174 : ℝ)+24348+1)))^2 +
  8*(mW 12174 : ℝ)*24348*(24348+2)*(24348+3) /
    ((1/1000)*((mW 12174 : ℝ)*24348*(24348+2)))^2 +
  covarianceVarianceBound 24348 (mW 12174) /
    ((1/1000)*covarianceMeanBound 24348 (mW 12174))^2 +
  normVarianceBound 24348 (mW 12174) / (3*inputVarianceMean 24348 (mW 12174))^2

end BstLean.Part281.WorldRow12174
namespace BstLean.Part281.WorldRow12175
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12175 = 199132155420401 := by
  have hu : mW 12175 ≤ 199132155420401 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12175 ≤ 199132155420400 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12175)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24350 ^ 2)
    ((1000000000000000000/152995562229822930713489))
    ((25000000000000000000/3824731976112893778163127)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24350) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24350 : ℝ)^2 / (mW 12175 : ℝ)) * (1 + 1/10^6)^2 *
    √(((33211/15625000000))/2) * ((1-firstRatio 24350) * √(1-firstRatio 24350) *
      sixthConstant (e1CovarianceRatio 24350 (mW 12175) (1/10^6) rowEps))) /
    (712/10000 - 24350*(1+1/10^6)*((33211/15625000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24350 (mW 12175) /
    ((1/10^5) * ((mW 12175 : ℝ)*24350*((mW 12175 : ℝ)+24350+1)))^2 +
  8*(mW 12175 : ℝ)*24350*(24350+2)*(24350+3) /
    ((1/1000)*((mW 12175 : ℝ)*24350*(24350+2)))^2 +
  covarianceVarianceBound 24350 (mW 12175) /
    ((1/1000)*covarianceMeanBound 24350 (mW 12175))^2 +
  normVarianceBound 24350 (mW 12175) / (3*inputVarianceMean 24350 (mW 12175))^2

end BstLean.Part281.WorldRow12175
namespace BstLean.Part281.WorldRow12176
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12176 = 199189406681480 := by
  have hu : mW 12176 ≤ 199189406681480 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12176 ≤ 199189406681479 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12176)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24352 ^ 2)
    ((1562500000000000000/239075200938183265447567))
    ((25000000000000000000/3825046135378252757486973)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24352) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24352 : ℝ)^2 / (mW 12176 : ℝ)) * (1 + 1/10^6)^2 *
    √(((132833/62500000000))/2) * ((1-firstRatio 24352) * √(1-firstRatio 24352) *
      sixthConstant (e1CovarianceRatio 24352 (mW 12176) (1/10^6) rowEps))) /
    (712/10000 - 24352*(1+1/10^6)*((132833/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24352 (mW 12176) /
    ((1/10^5) * ((mW 12176 : ℝ)*24352*((mW 12176 : ℝ)+24352+1)))^2 +
  8*(mW 12176 : ℝ)*24352*(24352+2)*(24352+3) /
    ((1/1000)*((mW 12176 : ℝ)*24352*(24352+2)))^2 +
  covarianceVarianceBound 24352 (mW 12176) /
    ((1/1000)*covarianceMeanBound 24352 (mW 12176))^2 +
  normVarianceBound 24352 (mW 12176) / (3*inputVarianceMean 24352 (mW 12176))^2

end BstLean.Part281.WorldRow12176
namespace BstLean.Part281.WorldRow12177
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12177 = 199246669698706 := by
  have hu : mW 12177 ≤ 199246669698706 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12177 ≤ 199246669698705 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12177)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24354 ^ 2)
    ((25000000000000000000/3825517374276291226484919))
    ((25000000000000000000/3825360294643611736810819)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24354) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24354 : ℝ)^2 / (mW 12177 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2125151/1000000000000))/2) * ((1-firstRatio 24354) * √(1-firstRatio 24354) *
      sixthConstant (e1CovarianceRatio 24354 (mW 12177) (1/10^6) rowEps))) /
    (712/10000 - 24354*(1+1/10^6)*((2125151/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24354 (mW 12177) /
    ((1/10^5) * ((mW 12177 : ℝ)*24354*((mW 12177 : ℝ)+24354+1)))^2 +
  8*(mW 12177 : ℝ)*24354*(24354+2)*(24354+3) /
    ((1/1000)*((mW 12177 : ℝ)*24354*(24354+2)))^2 +
  covarianceVarianceBound 24354 (mW 12177) /
    ((1/1000)*covarianceMeanBound 24354 (mW 12177))^2 +
  normVarianceBound 24354 (mW 12177) / (3*inputVarianceMean 24354 (mW 12177))^2

end BstLean.Part281.WorldRow12177
namespace BstLean.Part281.WorldRow12178
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12178 = 199303944473528 := by
  have hu : mW 12178 ≤ 199303944473528 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12178 ≤ 199303944473527 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12178)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24356 ^ 2)
    ((12500000000000000000/1912915766770825102904383))
    ((5000000000000000000/765134890781794143226933)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24356) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24356 : ℝ)^2 / (mW 12178 : ℝ)) * (1 + 1/10^6)^2 *
    √(((84999/40000000000))/2) * ((1-firstRatio 24356) * √(1-firstRatio 24356) *
      sixthConstant (e1CovarianceRatio 24356 (mW 12178) (1/10^6) rowEps))) /
    (712/10000 - 24356*(1+1/10^6)*((84999/40000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24356 (mW 12178) /
    ((1/10^5) * ((mW 12178 : ℝ)*24356*((mW 12178 : ℝ)+24356+1)))^2 +
  8*(mW 12178 : ℝ)*24356*(24356+2)*(24356+3) /
    ((1/1000)*((mW 12178 : ℝ)*24356*(24356+2)))^2 +
  covarianceVarianceBound 24356 (mW 12178) /
    ((1/1000)*covarianceMeanBound 24356 (mW 12178))^2 +
  normVarianceBound 24356 (mW 12178) / (3*inputVarianceMean 24356 (mW 12178))^2

end BstLean.Part281.WorldRow12178
namespace BstLean.Part281.WorldRow12179
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12179 = 199361231007394 := by
  have hu : mW 12179 ≤ 199361231007394 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12179 ≤ 199361231007393 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12179)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24358 ^ 2)
    ((25000000000000000000/3826145692807009185132613))
    ((25000000000000000000/3825988613174329695458511)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24358) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24358 : ℝ)^2 / (mW 12179 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1062399/500000000000))/2) * ((1-firstRatio 24358) * √(1-firstRatio 24358) *
      sixthConstant (e1CovarianceRatio 24358 (mW 12179) (1/10^6) rowEps))) /
    (712/10000 - 24358*(1+1/10^6)*((1062399/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24358 (mW 12179) /
    ((1/10^5) * ((mW 12179 : ℝ)*24358*((mW 12179 : ℝ)+24358+1)))^2 +
  8*(mW 12179 : ℝ)*24358*(24358+2)*(24358+3) /
    ((1/1000)*((mW 12179 : ℝ)*24358*(24358+2)))^2 +
  covarianceVarianceBound 24358 (mW 12179) /
    ((1/1000)*covarianceMeanBound 24358 (mW 12179))^2 +
  normVarianceBound 24358 (mW 12179) / (3*inputVarianceMean 24358 (mW 12179))^2

end BstLean.Part281.WorldRow12179
namespace BstLean.Part281.WorldRow12180
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12180 = 199418529301751 := by
  have hu : mW 12180 ≤ 199418529301751 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12180 ≤ 199418529301750 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12180)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24360 ^ 2)
    ((1250000000000000000/191322992603618408222823))
    ((25000000000000000000/3826302772439688674782357)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24360) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24360 : ℝ)^2 / (mW 12180 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1062311/500000000000))/2) * ((1-firstRatio 24360) * √(1-firstRatio 24360) *
      sixthConstant (e1CovarianceRatio 24360 (mW 12180) (1/10^6) rowEps))) /
    (712/10000 - 24360*(1+1/10^6)*((1062311/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24360 (mW 12180) /
    ((1/10^5) * ((mW 12180 : ℝ)*24360*((mW 12180 : ℝ)+24360+1)))^2 +
  8*(mW 12180 : ℝ)*24360*(24360+2)*(24360+3) /
    ((1/1000)*((mW 12180 : ℝ)*24360*(24360+2)))^2 +
  covarianceVarianceBound 24360 (mW 12180) /
    ((1/1000)*covarianceMeanBound 24360 (mW 12180))^2 +
  normVarianceBound 24360 (mW 12180) / (3*inputVarianceMean 24360 (mW 12180))^2

end BstLean.Part281.WorldRow12180
namespace BstLean.Part281.WorldRow12181
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12181 = 199475839358050 := by
  have hu : mW 12181 ≤ 199475839358050 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12181 ≤ 199475839358049 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12181)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24362 ^ 2)
    ((25000000000000000000/3826774011337727143780307))
    ((25000000000000000000/3826616931705047654106203)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24362) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24362 : ℝ)^2 / (mW 12181 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1062223/500000000000))/2) * ((1-firstRatio 24362) * √(1-firstRatio 24362) *
      sixthConstant (e1CovarianceRatio 24362 (mW 12181) (1/10^6) rowEps))) /
    (712/10000 - 24362*(1+1/10^6)*((1062223/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24362 (mW 12181) /
    ((1/10^5) * ((mW 12181 : ℝ)*24362*((mW 12181 : ℝ)+24362+1)))^2 +
  8*(mW 12181 : ℝ)*24362*(24362+2)*(24362+3) /
    ((1/1000)*((mW 12181 : ℝ)*24362*(24362+2)))^2 +
  covarianceVarianceBound 24362 (mW 12181) /
    ((1/1000)*covarianceMeanBound 24362 (mW 12181))^2 +
  normVarianceBound 24362 (mW 12181) / (3*inputVarianceMean 24362 (mW 12181))^2

end BstLean.Part281.WorldRow12181
namespace BstLean.Part281.WorldRow12182
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12182 = 199533161177738 := by
  have hu : mW 12182 ≤ 199533161177738 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12182 ≤ 199533161177737 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12182)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24364 ^ 2)
    ((12500000000000000000/1913544085301543061552077))
    ((25000000000000000000/3826931090970406633430049)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24364) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24364 : ℝ)^2 / (mW 12182 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2124269/1000000000000))/2) * ((1-firstRatio 24364) * √(1-firstRatio 24364) *
      sixthConstant (e1CovarianceRatio 24364 (mW 12182) (1/10^6) rowEps))) /
    (712/10000 - 24364*(1+1/10^6)*((2124269/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24364 (mW 12182) /
    ((1/10^5) * ((mW 12182 : ℝ)*24364*((mW 12182 : ℝ)+24364+1)))^2 +
  8*(mW 12182 : ℝ)*24364*(24364+2)*(24364+3) /
    ((1/1000)*((mW 12182 : ℝ)*24364*(24364+2)))^2 +
  covarianceVarianceBound 24364 (mW 12182) /
    ((1/1000)*covarianceMeanBound 24364 (mW 12182))^2 +
  normVarianceBound 24364 (mW 12182) / (3*inputVarianceMean 24364 (mW 12182))^2

end BstLean.Part281.WorldRow12182
namespace BstLean.Part281.WorldRow12183
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12183 = 199590494762263 := by
  have hu : mW 12183 ≤ 199590494762263 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12183 ≤ 199590494762262 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12183)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24366 ^ 2)
    ((25000000000000000000/3827402329868445102428001))
    ((5000000000000000000/765449050047153122550779)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24366) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24366 : ℝ)^2 / (mW 12183 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2124093/1000000000000))/2) * ((1-firstRatio 24366) * √(1-firstRatio 24366) *
      sixthConstant (e1CovarianceRatio 24366 (mW 12183) (1/10^6) rowEps))) /
    (712/10000 - 24366*(1+1/10^6)*((2124093/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24366 (mW 12183) /
    ((1/10^5) * ((mW 12183 : ℝ)*24366*((mW 12183 : ℝ)+24366+1)))^2 +
  8*(mW 12183 : ℝ)*24366*(24366+2)*(24366+3) /
    ((1/1000)*((mW 12183 : ℝ)*24366*(24366+2)))^2 +
  covarianceVarianceBound 24366 (mW 12183) /
    ((1/1000)*covarianceMeanBound 24366 (mW 12183))^2 +
  normVarianceBound 24366 (mW 12183) / (3*inputVarianceMean 24366 (mW 12183))^2

end BstLean.Part281.WorldRow12183
