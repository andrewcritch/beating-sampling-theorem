import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar31
namespace BstLean.Part268.WorldRow13125
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13125 = 259028524847327 := by
  have hu : mW 13125 ≤ 259028524847327 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13125 ≤ 259028524847326 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13125)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26250 ^ 2)
    ((40000000000000000/6597344572538565800787))
    ((25000000000000000000/4123183278203924135816827)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26250) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26250 : ℝ)^2 / (mW 13125 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1970099/1000000000000))/2) * ((1-firstRatio 26250) * √(1-firstRatio 26250) *
      sixthConstant (e1CovarianceRatio 26250 (mW 13125) (1/10^6) rowEps))) /
    (712/10000 - 26250*(1+1/10^6)*((1970099/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26250 (mW 13125) /
    ((1/10^5) * ((mW 13125 : ℝ)*26250*((mW 13125 : ℝ)+26250+1)))^2 +
  8*(mW 13125 : ℝ)*26250*(26250+2)*(26250+3) /
    ((1/1000)*((mW 13125 : ℝ)*26250*(26250+2)))^2 +
  covarianceVarianceBound 26250 (mW 13125) /
    ((1/1000)*covarianceMeanBound 26250 (mW 13125))^2 +
  normVarianceBound 26250 (mW 13125) / (3*inputVarianceMean 26250 (mW 13125))^2

end BstLean.Part268.WorldRow13125
namespace BstLean.Part268.WorldRow13126
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13126 = 259097605699373 := by
  have hu : mW 13126 ≤ 259097605699373 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13126 ≤ 259097605699372 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13126)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26252 ^ 2)
    ((12500000000000000000/2061827258550981302407861))
    ((25000000000000000000/4123497437469283115140673)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26252) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26252 : ℝ)^2 / (mW 13126 : ℝ)) * (1 + 1/10^6)^2 *
    √(((492487/250000000000))/2) * ((1-firstRatio 26252) * √(1-firstRatio 26252) *
      sixthConstant (e1CovarianceRatio 26252 (mW 13126) (1/10^6) rowEps))) /
    (712/10000 - 26252*(1+1/10^6)*((492487/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26252 (mW 13126) /
    ((1/10^5) * ((mW 13126 : ℝ)*26252*((mW 13126 : ℝ)+26252+1)))^2 +
  8*(mW 13126 : ℝ)*26252*(26252+2)*(26252+3) /
    ((1/1000)*((mW 13126 : ℝ)*26252*(26252+2)))^2 +
  covarianceVarianceBound 26252 (mW 13126) /
    ((1/1000)*covarianceMeanBound 26252 (mW 13126))^2 +
  normVarianceBound 26252 (mW 13126) / (3*inputVarianceMean 26252 (mW 13126))^2

end BstLean.Part268.WorldRow13126
namespace BstLean.Part268.WorldRow13127
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13127 = 259166699709926 := by
  have hu : mW 13127 ≤ 259166699709926 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13127 ≤ 259166699709925 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13127)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26254 ^ 2)
    ((25000000000000000000/4123968676367321584139569))
    ((25000000000000000000/4123811596734642094464519)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26254) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26254 : ℝ)^2 / (mW 13127 : ℝ)) * (1 + 1/10^6)^2 *
    √(((492449/250000000000))/2) * ((1-firstRatio 26254) * √(1-firstRatio 26254) *
      sixthConstant (e1CovarianceRatio 26254 (mW 13127) (1/10^6) rowEps))) /
    (712/10000 - 26254*(1+1/10^6)*((492449/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26254 (mW 13127) /
    ((1/10^5) * ((mW 13127 : ℝ)*26254*((mW 13127 : ℝ)+26254+1)))^2 +
  8*(mW 13127 : ℝ)*26254*(26254+2)*(26254+3) /
    ((1/1000)*((mW 13127 : ℝ)*26254*(26254+2)))^2 +
  covarianceVarianceBound 26254 (mW 13127) /
    ((1/1000)*covarianceMeanBound 26254 (mW 13127))^2 +
  normVarianceBound 26254 (mW 13127) / (3*inputVarianceMean 26254 (mW 13127))^2

end BstLean.Part268.WorldRow13127
namespace BstLean.Part268.WorldRow13128
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13128 = 259235806880492 := by
  have hu : mW 13128 ≤ 259235806880492 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13128 ≤ 259235806880491 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13128)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26256 ^ 2)
    ((3125000000000000000/515535354454085070432927))
    ((5000000000000000000/824825151200000214757673)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26256) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26256 : ℝ)^2 / (mW 13128 : ℝ)) * (1 + 1/10^6)^2 *
    √(((393929/200000000000))/2) * ((1-firstRatio 26256) * √(1-firstRatio 26256) *
      sixthConstant (e1CovarianceRatio 26256 (mW 13128) (1/10^6) rowEps))) /
    (712/10000 - 26256*(1+1/10^6)*((393929/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26256 (mW 13128) /
    ((1/10^5) * ((mW 13128 : ℝ)*26256*((mW 13128 : ℝ)+26256+1)))^2 +
  8*(mW 13128 : ℝ)*26256*(26256+2)*(26256+3) /
    ((1/1000)*((mW 13128 : ℝ)*26256*(26256+2)))^2 +
  covarianceVarianceBound 26256 (mW 13128) /
    ((1/1000)*covarianceMeanBound 26256 (mW 13128))^2 +
  normVarianceBound 26256 (mW 13128) / (3*inputVarianceMean 26256 (mW 13128))^2

end BstLean.Part268.WorldRow13128
namespace BstLean.Part268.WorldRow13129
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13129 = 259304927212573 := by
  have hu : mW 13129 ≤ 259304927212573 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13129 ≤ 259304927212572 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13129)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26258 ^ 2)
    ((25000000000000000000/4124596994898039542787263))
    ((25000000000000000000/4124439915265360053112211)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26258) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26258 : ℝ)^2 / (mW 13129 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1969493/1000000000000))/2) * ((1-firstRatio 26258) * √(1-firstRatio 26258) *
      sixthConstant (e1CovarianceRatio 26258 (mW 13129) (1/10^6) rowEps))) /
    (712/10000 - 26258*(1+1/10^6)*((1969493/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26258 (mW 13129) /
    ((1/10^5) * ((mW 13129 : ℝ)*26258*((mW 13129 : ℝ)+26258+1)))^2 +
  8*(mW 13129 : ℝ)*26258*(26258+2)*(26258+3) /
    ((1/1000)*((mW 13129 : ℝ)*26258*(26258+2)))^2 +
  covarianceVarianceBound 26258 (mW 13129) /
    ((1/1000)*covarianceMeanBound 26258 (mW 13129))^2 +
  normVarianceBound 26258 (mW 13129) / (3*inputVarianceMean 26258 (mW 13129))^2

end BstLean.Part268.WorldRow13129
namespace BstLean.Part268.WorldRow13130
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13130 = 259374060707674 := by
  have hu : mW 13130 ≤ 259374060707674 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13130 ≤ 259374060707673 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13130)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26260 ^ 2)
    ((2500000000000000000/412491115416339852211111))
    ((25000000000000000000/4124754074530719032436057)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26260) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26260 : ℝ)^2 / (mW 13130 : ℝ)) * (1 + 1/10^6)^2 *
    √(((984671/500000000000))/2) * ((1-firstRatio 26260) * √(1-firstRatio 26260) *
      sixthConstant (e1CovarianceRatio 26260 (mW 13130) (1/10^6) rowEps))) /
    (712/10000 - 26260*(1+1/10^6)*((984671/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26260 (mW 13130) /
    ((1/10^5) * ((mW 13130 : ℝ)*26260*((mW 13130 : ℝ)+26260+1)))^2 +
  8*(mW 13130 : ℝ)*26260*(26260+2)*(26260+3) /
    ((1/1000)*((mW 13130 : ℝ)*26260*(26260+2)))^2 +
  covarianceVarianceBound 26260 (mW 13130) /
    ((1/1000)*covarianceMeanBound 26260 (mW 13130))^2 +
  normVarianceBound 26260 (mW 13130) / (3*inputVarianceMean 26260 (mW 13130))^2

end BstLean.Part268.WorldRow13130
namespace BstLean.Part268.WorldRow13131
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13131 = 259443207367298 := by
  have hu : mW 13131 ≤ 259443207367298 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13131 ≤ 259443207367297 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13131)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26262 ^ 2)
    ((25000000000000000000/4125225313428757501434957))
    ((25000000000000000000/4125068233796078011759903)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26262) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26262 : ℝ)^2 / (mW 13131 : ℝ)) * (1 + 1/10^6)^2 *
    √(((196919/100000000000))/2) * ((1-firstRatio 26262) * √(1-firstRatio 26262) *
      sixthConstant (e1CovarianceRatio 26262 (mW 13131) (1/10^6) rowEps))) /
    (712/10000 - 26262*(1+1/10^6)*((196919/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26262 (mW 13131) /
    ((1/10^5) * ((mW 13131 : ℝ)*26262*((mW 13131 : ℝ)+26262+1)))^2 +
  8*(mW 13131 : ℝ)*26262*(26262+2)*(26262+3) /
    ((1/1000)*((mW 13131 : ℝ)*26262*(26262+2)))^2 +
  covarianceVarianceBound 26262 (mW 13131) /
    ((1/1000)*covarianceMeanBound 26262 (mW 13131))^2 +
  normVarianceBound 26262 (mW 13131) / (3*inputVarianceMean 26262 (mW 13131))^2

end BstLean.Part268.WorldRow13131
namespace BstLean.Part268.WorldRow13132
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13132 = 259512367192949 := by
  have hu : mW 13132 ≤ 259512367192949 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13132 ≤ 259512367192948 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13132)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26264 ^ 2)
    ((6250000000000000000/1031384868173529120189701))
    ((25000000000000000000/4125382393061436991083749)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26264) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26264 : ℝ)^2 / (mW 13132 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1969039/1000000000000))/2) * ((1-firstRatio 26264) * √(1-firstRatio 26264) *
      sixthConstant (e1CovarianceRatio 26264 (mW 13132) (1/10^6) rowEps))) /
    (712/10000 - 26264*(1+1/10^6)*((1969039/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26264 (mW 13132) /
    ((1/10^5) * ((mW 13132 : ℝ)*26264*((mW 13132 : ℝ)+26264+1)))^2 +
  8*(mW 13132 : ℝ)*26264*(26264+2)*(26264+3) /
    ((1/1000)*((mW 13132 : ℝ)*26264*(26264+2)))^2 +
  covarianceVarianceBound 26264 (mW 13132) /
    ((1/1000)*covarianceMeanBound 26264 (mW 13132))^2 +
  normVarianceBound 26264 (mW 13132) / (3*inputVarianceMean 26264 (mW 13132))^2

end BstLean.Part268.WorldRow13132
namespace BstLean.Part268.WorldRow13133
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13133 = 259581540186132 := by
  have hu : mW 13133 ≤ 259581540186132 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13133 ≤ 259581540186131 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13133)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26266 ^ 2)
    ((25000000000000000000/4125853631959475460082651))
    ((5000000000000000000/825139310465359194081519)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26266) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26266 : ℝ)^2 / (mW 13133 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1968887/1000000000000))/2) * ((1-firstRatio 26266) * √(1-firstRatio 26266) *
      sixthConstant (e1CovarianceRatio 26266 (mW 13133) (1/10^6) rowEps))) /
    (712/10000 - 26266*(1+1/10^6)*((1968887/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26266 (mW 13133) /
    ((1/10^5) * ((mW 13133 : ℝ)*26266*((mW 13133 : ℝ)+26266+1)))^2 +
  8*(mW 13133 : ℝ)*26266*(26266+2)*(26266+3) /
    ((1/1000)*((mW 13133 : ℝ)*26266*(26266+2)))^2 +
  covarianceVarianceBound 26266 (mW 13133) /
    ((1/1000)*covarianceMeanBound 26266 (mW 13133))^2 +
  normVarianceBound 26266 (mW 13133) / (3*inputVarianceMean 26266 (mW 13133))^2

end BstLean.Part268.WorldRow13133
namespace BstLean.Part268.WorldRow13134
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13134 = 259650726348351 := by
  have hu : mW 13134 ≤ 259650726348351 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13134 ≤ 259650726348350 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13134)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26268 ^ 2)
    ((12500000000000000000/2063083895612417219703249))
    ((25000000000000000000/4126010711592154949731441)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26268) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26268 : ℝ)^2 / (mW 13134 : ℝ)) * (1 + 1/10^6)^2 *
    √(((61523/31250000000))/2) * ((1-firstRatio 26268) * √(1-firstRatio 26268) *
      sixthConstant (e1CovarianceRatio 26268 (mW 13134) (1/10^6) rowEps))) /
    (712/10000 - 26268*(1+1/10^6)*((61523/31250000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26268 (mW 13134) /
    ((1/10^5) * ((mW 13134 : ℝ)*26268*((mW 13134 : ℝ)+26268+1)))^2 +
  8*(mW 13134 : ℝ)*26268*(26268+2)*(26268+3) /
    ((1/1000)*((mW 13134 : ℝ)*26268*(26268+2)))^2 +
  covarianceVarianceBound 26268 (mW 13134) /
    ((1/1000)*covarianceMeanBound 26268 (mW 13134))^2 +
  normVarianceBound 26268 (mW 13134) / (3*inputVarianceMean 26268 (mW 13134))^2

end BstLean.Part268.WorldRow13134
namespace BstLean.Part268.WorldRow13135
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13135 = 259719925681109 := by
  have hu : mW 13135 ≤ 259719925681109 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13135 ≤ 259719925681108 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13135)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26270 ^ 2)
    ((5000000000000000000/825296390098038683746069))
    ((25000000000000000000/4126324870857513929055287)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26270) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26270 : ℝ)^2 / (mW 13135 : ℝ)) * (1 + 1/10^6)^2 *
    √(((393717/200000000000))/2) * ((1-firstRatio 26270) * √(1-firstRatio 26270) *
      sixthConstant (e1CovarianceRatio 26270 (mW 13135) (1/10^6) rowEps))) /
    (712/10000 - 26270*(1+1/10^6)*((393717/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26270 (mW 13135) /
    ((1/10^5) * ((mW 13135 : ℝ)*26270*((mW 13135 : ℝ)+26270+1)))^2 +
  8*(mW 13135 : ℝ)*26270*(26270+2)*(26270+3) /
    ((1/1000)*((mW 13135 : ℝ)*26270*(26270+2)))^2 +
  covarianceVarianceBound 26270 (mW 13135) /
    ((1/1000)*covarianceMeanBound 26270 (mW 13135))^2 +
  normVarianceBound 26270 (mW 13135) / (3*inputVarianceMean 26270 (mW 13135))^2

end BstLean.Part268.WorldRow13135
namespace BstLean.Part268.WorldRow13136
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13136 = 259789138185911 := by
  have hu : mW 13136 ≤ 259789138185911 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13136 ≤ 259789138185910 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13136)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26272 ^ 2)
    ((1562500000000000000/257924756859722024878387))
    ((25000000000000000000/4126639030122872908379133)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26272) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26272 : ℝ)^2 / (mW 13136 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1968433/1000000000000))/2) * ((1-firstRatio 26272) * √(1-firstRatio 26272) *
      sixthConstant (e1CovarianceRatio 26272 (mW 13136) (1/10^6) rowEps))) /
    (712/10000 - 26272*(1+1/10^6)*((1968433/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26272 (mW 13136) /
    ((1/10^5) * ((mW 13136 : ℝ)*26272*((mW 13136 : ℝ)+26272+1)))^2 +
  8*(mW 13136 : ℝ)*26272*(26272+2)*(26272+3) /
    ((1/1000)*((mW 13136 : ℝ)*26272*(26272+2)))^2 +
  covarianceVarianceBound 26272 (mW 13136) /
    ((1/1000)*covarianceMeanBound 26272 (mW 13136))^2 +
  normVarianceBound 26272 (mW 13136) / (3*inputVarianceMean 26272 (mW 13136))^2

end BstLean.Part268.WorldRow13136
namespace BstLean.Part268.WorldRow13137
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13137 = 259858363864261 := by
  have hu : mW 13137 ≤ 259858363864261 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13137 ≤ 259858363864260 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13137)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26274 ^ 2)
    ((25000000000000000000/4127110269020911377378039))
    ((25000000000000000000/4126953189388231887702979)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26274) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26274 : ℝ)^2 / (mW 13137 : ℝ)) * (1 + 1/10^6)^2 *
    √(((984141/500000000000))/2) * ((1-firstRatio 26274) * √(1-firstRatio 26274) *
      sixthConstant (e1CovarianceRatio 26274 (mW 13137) (1/10^6) rowEps))) /
    (712/10000 - 26274*(1+1/10^6)*((984141/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26274 (mW 13137) /
    ((1/10^5) * ((mW 13137 : ℝ)*26274*((mW 13137 : ℝ)+26274+1)))^2 +
  8*(mW 13137 : ℝ)*26274*(26274+2)*(26274+3) /
    ((1/1000)*((mW 13137 : ℝ)*26274*(26274+2)))^2 +
  covarianceVarianceBound 26274 (mW 13137) /
    ((1/1000)*covarianceMeanBound 26274 (mW 13137))^2 +
  normVarianceBound 26274 (mW 13137) / (3*inputVarianceMean 26274 (mW 13137))^2

end BstLean.Part268.WorldRow13137
namespace BstLean.Part268.WorldRow13138
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13138 = 259927602717664 := by
  have hu : mW 13138 ≤ 259927602717664 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13138 ≤ 259927602717663 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13138)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26276 ^ 2)
    ((12500000000000000000/2063712214143135178350943))
    ((1000000000000000000/165090693946143634681073)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26276) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26276 : ℝ)^2 / (mW 13138 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1968131/1000000000000))/2) * ((1-firstRatio 26276) * √(1-firstRatio 26276) *
      sixthConstant (e1CovarianceRatio 26276 (mW 13138) (1/10^6) rowEps))) /
    (712/10000 - 26276*(1+1/10^6)*((1968131/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26276 (mW 13138) /
    ((1/10^5) * ((mW 13138 : ℝ)*26276*((mW 13138 : ℝ)+26276+1)))^2 +
  8*(mW 13138 : ℝ)*26276*(26276+2)*(26276+3) /
    ((1/1000)*((mW 13138 : ℝ)*26276*(26276+2)))^2 +
  covarianceVarianceBound 26276 (mW 13138) /
    ((1/1000)*covarianceMeanBound 26276 (mW 13138))^2 +
  normVarianceBound 26276 (mW 13138) / (3*inputVarianceMean 26276 (mW 13138))^2

end BstLean.Part268.WorldRow13138
namespace BstLean.Part268.WorldRow13139
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13139 = 259996854747623 := by
  have hu : mW 13139 ≤ 259996854747623 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13139 ≤ 259996854747622 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13139)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26278 ^ 2)
    ((25000000000000000000/4127738587551629336025733))
    ((25000000000000000000/4127581507918949846350671)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26278) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26278 : ℝ)^2 / (mW 13139 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1967979/1000000000000))/2) * ((1-firstRatio 26278) * √(1-firstRatio 26278) *
      sixthConstant (e1CovarianceRatio 26278 (mW 13139) (1/10^6) rowEps))) /
    (712/10000 - 26278*(1+1/10^6)*((1967979/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26278 (mW 13139) /
    ((1/10^5) * ((mW 13139 : ℝ)*26278*((mW 13139 : ℝ)+26278+1)))^2 +
  8*(mW 13139 : ℝ)*26278*(26278+2)*(26278+3) /
    ((1/1000)*((mW 13139 : ℝ)*26278*(26278+2)))^2 +
  covarianceVarianceBound 26278 (mW 13139) /
    ((1/1000)*covarianceMeanBound 26278 (mW 13139))^2 +
  normVarianceBound 26278 (mW 13139) / (3*inputVarianceMean 26278 (mW 13139))^2

end BstLean.Part268.WorldRow13139
namespace BstLean.Part268.WorldRow13140
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13140 = 260066119955644 := by
  have hu : mW 13140 ≤ 260066119955644 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13140 ≤ 260066119955643 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13140)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26280 ^ 2)
    ((1250000000000000000/206402637340849415767479))
    ((25000000000000000000/4127895667184308825674517)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26280) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26280 : ℝ)^2 / (mW 13140 : ℝ)) * (1 + 1/10^6)^2 *
    √(((491957/250000000000))/2) * ((1-firstRatio 26280) * √(1-firstRatio 26280) *
      sixthConstant (e1CovarianceRatio 26280 (mW 13140) (1/10^6) rowEps))) /
    (712/10000 - 26280*(1+1/10^6)*((491957/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26280 (mW 13140) /
    ((1/10^5) * ((mW 13140 : ℝ)*26280*((mW 13140 : ℝ)+26280+1)))^2 +
  8*(mW 13140 : ℝ)*26280*(26280+2)*(26280+3) /
    ((1/1000)*((mW 13140 : ℝ)*26280*(26280+2)))^2 +
  covarianceVarianceBound 26280 (mW 13140) /
    ((1/1000)*covarianceMeanBound 26280 (mW 13140))^2 +
  normVarianceBound 26280 (mW 13140) / (3*inputVarianceMean 26280 (mW 13140))^2

end BstLean.Part268.WorldRow13140
namespace BstLean.Part268.WorldRow13141
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13141 = 260135398343231 := by
  have hu : mW 13141 ≤ 260135398343231 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13141 ≤ 260135398343230 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13141)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26282 ^ 2)
    ((25000000000000000000/4128366906082347294673427))
    ((25000000000000000000/4128209826449667804998363)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26282) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26282 : ℝ)^2 / (mW 13141 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1967677/1000000000000))/2) * ((1-firstRatio 26282) * √(1-firstRatio 26282) *
      sixthConstant (e1CovarianceRatio 26282 (mW 13141) (1/10^6) rowEps))) /
    (712/10000 - 26282*(1+1/10^6)*((1967677/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26282 (mW 13141) /
    ((1/10^5) * ((mW 13141 : ℝ)*26282*((mW 13141 : ℝ)+26282+1)))^2 +
  8*(mW 13141 : ℝ)*26282*(26282+2)*(26282+3) /
    ((1/1000)*((mW 13141 : ℝ)*26282*(26282+2)))^2 +
  covarianceVarianceBound 26282 (mW 13141) /
    ((1/1000)*covarianceMeanBound 26282 (mW 13141))^2 +
  normVarianceBound 26282 (mW 13141) / (3*inputVarianceMean 26282 (mW 13141))^2

end BstLean.Part268.WorldRow13141
namespace BstLean.Part268.WorldRow13142
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13142 = 260204689911887 := by
  have hu : mW 13142 ≤ 260204689911887 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13142 ≤ 260204689911886 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13142)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26284 ^ 2)
    ((12500000000000000000/2064340532673853136998637))
    ((25000000000000000000/4128523985715026784322209)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26284) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26284 : ℝ)^2 / (mW 13142 : ℝ)) * (1 + 1/10^6)^2 *
    √(((983763/500000000000))/2) * ((1-firstRatio 26284) * √(1-firstRatio 26284) *
      sixthConstant (e1CovarianceRatio 26284 (mW 13142) (1/10^6) rowEps))) /
    (712/10000 - 26284*(1+1/10^6)*((983763/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26284 (mW 13142) /
    ((1/10^5) * ((mW 13142 : ℝ)*26284*((mW 13142 : ℝ)+26284+1)))^2 +
  8*(mW 13142 : ℝ)*26284*(26284+2)*(26284+3) /
    ((1/1000)*((mW 13142 : ℝ)*26284*(26284+2)))^2 +
  covarianceVarianceBound 26284 (mW 13142) /
    ((1/1000)*covarianceMeanBound 26284 (mW 13142))^2 +
  normVarianceBound 26284 (mW 13142) / (3*inputVarianceMean 26284 (mW 13142))^2

end BstLean.Part268.WorldRow13142
namespace BstLean.Part268.WorldRow13143
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13143 = 260273994663119 := by
  have hu : mW 13143 ≤ 260273994663119 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13143 ≤ 260273994663118 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13143)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26286 ^ 2)
    ((25000000000000000000/4128995224613065253321121))
    ((5000000000000000000/825767628996077152729211)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26286) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26286 : ℝ)^2 / (mW 13143 : ℝ)) * (1 + 1/10^6)^2 *
    √(((983687/500000000000))/2) * ((1-firstRatio 26286) * √(1-firstRatio 26286) *
      sixthConstant (e1CovarianceRatio 26286 (mW 13143) (1/10^6) rowEps))) /
    (712/10000 - 26286*(1+1/10^6)*((983687/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26286 (mW 13143) /
    ((1/10^5) * ((mW 13143 : ℝ)*26286*((mW 13143 : ℝ)+26286+1)))^2 +
  8*(mW 13143 : ℝ)*26286*(26286+2)*(26286+3) /
    ((1/1000)*((mW 13143 : ℝ)*26286*(26286+2)))^2 +
  covarianceVarianceBound 26286 (mW 13143) /
    ((1/1000)*covarianceMeanBound 26286 (mW 13143))^2 +
  normVarianceBound 26286 (mW 13143) / (3*inputVarianceMean 26286 (mW 13143))^2

end BstLean.Part268.WorldRow13143
namespace BstLean.Part268.WorldRow13144
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13144 = 260343312598430 := by
  have hu : mW 13144 ≤ 260343312598430 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13144 ≤ 260343312598429 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13144)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26288 ^ 2)
    ((3125000000000000000/516163672984803029080621))
    ((25000000000000000000/4129152304245744742969901)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26288) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26288 : ℝ)^2 / (mW 13144 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1967223/1000000000000))/2) * ((1-firstRatio 26288) * √(1-firstRatio 26288) *
      sixthConstant (e1CovarianceRatio 26288 (mW 13144) (1/10^6) rowEps))) /
    (712/10000 - 26288*(1+1/10^6)*((1967223/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26288 (mW 13144) /
    ((1/10^5) * ((mW 13144 : ℝ)*26288*((mW 13144 : ℝ)+26288+1)))^2 +
  8*(mW 13144 : ℝ)*26288*(26288+2)*(26288+3) /
    ((1/1000)*((mW 13144 : ℝ)*26288*(26288+2)))^2 +
  covarianceVarianceBound 26288 (mW 13144) /
    ((1/1000)*covarianceMeanBound 26288 (mW 13144))^2 +
  normVarianceBound 26288 (mW 13144) / (3*inputVarianceMean 26288 (mW 13144))^2

end BstLean.Part268.WorldRow13144
namespace BstLean.Part268.WorldRow13145
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13145 = 260412643719326 := by
  have hu : mW 13145 ≤ 260412643719326 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13145 ≤ 260412643719325 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13145)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26290 ^ 2)
    ((5000000000000000000/825924708628756642393763))
    ((25000000000000000000/4129466463511103722293747)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26290) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26290 : ℝ)^2 / (mW 13145 : ℝ)) * (1 + 1/10^6)^2 *
    √(((61471/31250000000))/2) * ((1-firstRatio 26290) * √(1-firstRatio 26290) *
      sixthConstant (e1CovarianceRatio 26290 (mW 13145) (1/10^6) rowEps))) /
    (712/10000 - 26290*(1+1/10^6)*((61471/31250000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26290 (mW 13145) /
    ((1/10^5) * ((mW 13145 : ℝ)*26290*((mW 13145 : ℝ)+26290+1)))^2 +
  8*(mW 13145 : ℝ)*26290*(26290+2)*(26290+3) /
    ((1/1000)*((mW 13145 : ℝ)*26290*(26290+2)))^2 +
  covarianceVarianceBound 26290 (mW 13145) /
    ((1/1000)*covarianceMeanBound 26290 (mW 13145))^2 +
  normVarianceBound 26290 (mW 13145) / (3*inputVarianceMean 26290 (mW 13145))^2

end BstLean.Part268.WorldRow13145
namespace BstLean.Part268.WorldRow13146
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13146 = 260481988027310 := by
  have hu : mW 13146 ≤ 260481988027310 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13146 ≤ 260481988027309 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13146)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26292 ^ 2)
    ((12500000000000000000/2064968851204571095646331))
    ((25000000000000000000/4129780622776462701617593)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26292) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26292 : ℝ)^2 / (mW 13146 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1966921/1000000000000))/2) * ((1-firstRatio 26292) * √(1-firstRatio 26292) *
      sixthConstant (e1CovarianceRatio 26292 (mW 13146) (1/10^6) rowEps))) /
    (712/10000 - 26292*(1+1/10^6)*((1966921/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26292 (mW 13146) /
    ((1/10^5) * ((mW 13146 : ℝ)*26292*((mW 13146 : ℝ)+26292+1)))^2 +
  8*(mW 13146 : ℝ)*26292*(26292+2)*(26292+3) /
    ((1/1000)*((mW 13146 : ℝ)*26292*(26292+2)))^2 +
  covarianceVarianceBound 26292 (mW 13146) /
    ((1/1000)*covarianceMeanBound 26292 (mW 13146))^2 +
  normVarianceBound 26292 (mW 13146) / (3*inputVarianceMean 26292 (mW 13146))^2

end BstLean.Part268.WorldRow13146
namespace BstLean.Part268.WorldRow13147
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13147 = 260551345523889 := by
  have hu : mW 13147 ≤ 260551345523889 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13147 ≤ 260551345523888 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13147)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26294 ^ 2)
    ((25000000000000000000/4130251861674501170616509))
    ((25000000000000000000/4130094782041821680941439)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26294) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26294 : ℝ)^2 / (mW 13147 : ℝ)) * (1 + 1/10^6)^2 *
    √(((196677/100000000000))/2) * ((1-firstRatio 26294) * √(1-firstRatio 26294) *
      sixthConstant (e1CovarianceRatio 26294 (mW 13147) (1/10^6) rowEps))) /
    (712/10000 - 26294*(1+1/10^6)*((196677/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26294 (mW 13147) /
    ((1/10^5) * ((mW 13147 : ℝ)*26294*((mW 13147 : ℝ)+26294+1)))^2 +
  8*(mW 13147 : ℝ)*26294*(26294+2)*(26294+3) /
    ((1/1000)*((mW 13147 : ℝ)*26294*(26294+2)))^2 +
  covarianceVarianceBound 26294 (mW 13147) /
    ((1/1000)*covarianceMeanBound 26294 (mW 13147))^2 +
  normVarianceBound 26294 (mW 13147) / (3*inputVarianceMean 26294 (mW 13147))^2

end BstLean.Part268.WorldRow13147
namespace BstLean.Part268.WorldRow13148
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13148 = 260620716210566 := by
  have hu : mW 13148 ≤ 260620716210566 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13148 ≤ 260620716210565 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13148)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26296 ^ 2)
    ((6250000000000000000/1032641505234965037485089))
    ((5000000000000000000/826081788261436132053057)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26296) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26296 : ℝ)^2 / (mW 13148 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1966619/1000000000000))/2) * ((1-firstRatio 26296) * √(1-firstRatio 26296) *
      sixthConstant (e1CovarianceRatio 26296 (mW 13148) (1/10^6) rowEps))) /
    (712/10000 - 26296*(1+1/10^6)*((1966619/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26296 (mW 13148) /
    ((1/10^5) * ((mW 13148 : ℝ)*26296*((mW 13148 : ℝ)+26296+1)))^2 +
  8*(mW 13148 : ℝ)*26296*(26296+2)*(26296+3) /
    ((1/1000)*((mW 13148 : ℝ)*26296*(26296+2)))^2 +
  covarianceVarianceBound 26296 (mW 13148) /
    ((1/1000)*covarianceMeanBound 26296 (mW 13148))^2 +
  normVarianceBound 26296 (mW 13148) / (3*inputVarianceMean 26296 (mW 13148))^2

end BstLean.Part268.WorldRow13148
namespace BstLean.Part268.WorldRow13149
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13149 = 260690100088847 := by
  have hu : mW 13149 ≤ 260690100088847 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13149 ≤ 260690100088846 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13149)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26298 ^ 2)
    ((25000000000000000000/4130880180205219129264203))
    ((25000000000000000000/4130723100572539639589131)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26298) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26298 : ℝ)^2 / (mW 13149 : ℝ)) * (1 + 1/10^6)^2 *
    √(((491617/250000000000))/2) * ((1-firstRatio 26298) * √(1-firstRatio 26298) *
      sixthConstant (e1CovarianceRatio 26298 (mW 13149) (1/10^6) rowEps))) /
    (712/10000 - 26298*(1+1/10^6)*((491617/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26298 (mW 13149) /
    ((1/10^5) * ((mW 13149 : ℝ)*26298*((mW 13149 : ℝ)+26298+1)))^2 +
  8*(mW 13149 : ℝ)*26298*(26298+2)*(26298+3) /
    ((1/1000)*((mW 13149 : ℝ)*26298*(26298+2)))^2 +
  covarianceVarianceBound 26298 (mW 13149) /
    ((1/1000)*covarianceMeanBound 26298 (mW 13149))^2 +
  normVarianceBound 26298 (mW 13149) / (3*inputVarianceMean 26298 (mW 13149))^2

end BstLean.Part268.WorldRow13149
