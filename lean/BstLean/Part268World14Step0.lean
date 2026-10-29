import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar14
namespace BstLean.Part268.WorldRow12700
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12700 = 230841040581069 := by
  have hu : mW 12700 ≤ 230841040581069 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12700 ≤ 230841040581068 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12700)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25400 ^ 2)
    ((250000000000000000/39898226700590374128569))
    ((25000000000000000000/3989665590426357923182277)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25400) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25400 : ℝ)^2 / (mW 12700 : ℝ)) * (1 + 1/10^6)^2 *
    √(((203671/100000000000))/2) * ((1-firstRatio 25400) * √(1-firstRatio 25400) *
      sixthConstant (e1CovarianceRatio 25400 (mW 12700) (1/10^6) rowEps))) /
    (712/10000 - 25400*(1+1/10^6)*((203671/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25400 (mW 12700) /
    ((1/10^5) * ((mW 12700 : ℝ)*25400*((mW 12700 : ℝ)+25400+1)))^2 +
  8*(mW 12700 : ℝ)*25400*(25400+2)*(25400+3) /
    ((1/1000)*((mW 12700 : ℝ)*25400*(25400+2)))^2 +
  covarianceVarianceBound 25400 (mW 12700) /
    ((1/1000)*covarianceMeanBound 25400 (mW 12700))^2 +
  normVarianceBound 25400 (mW 12700) / (3*inputVarianceMean 25400 (mW 12700))^2

end BstLean.Part268.WorldRow12700
namespace BstLean.Part268.WorldRow12701
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12701 = 230904664452500 := by
  have hu : mW 12701 ≤ 230904664452500 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12701 ≤ 230904664452499 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12701)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25402 ^ 2)
    ((25000000000000000000/3990136829324396392180747))
    ((25000000000000000000/3989979749691716902506123)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25402) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25402 : ℝ)^2 / (mW 12701 : ℝ)) * (1 + 1/10^6)^2 *
    √(((509137/250000000000))/2) * ((1-firstRatio 25402) * √(1-firstRatio 25402) *
      sixthConstant (e1CovarianceRatio 25402 (mW 12701) (1/10^6) rowEps))) /
    (712/10000 - 25402*(1+1/10^6)*((509137/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25402 (mW 12701) /
    ((1/10^5) * ((mW 12701 : ℝ)*25402*((mW 12701 : ℝ)+25402+1)))^2 +
  8*(mW 12701 : ℝ)*25402*(25402+2)*(25402+3) /
    ((1/1000)*((mW 12701 : ℝ)*25402*(25402+2)))^2 +
  covarianceVarianceBound 25402 (mW 12701) /
    ((1/1000)*covarianceMeanBound 25402 (mW 12701))^2 +
  normVarianceBound 25402 (mW 12701) / (3*inputVarianceMean 25402 (mW 12701))^2

end BstLean.Part268.WorldRow12701
namespace BstLean.Part268.WorldRow12702
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12702 = 230968300848562 := by
  have hu : mW 12702 ≤ 230968300848562 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12702 ≤ 230968300848561 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12702)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25404 ^ 2)
    ((12500000000000000000/1995225494294877685752297))
    ((25000000000000000000/3990293908957075881829969)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25404) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25404 : ℝ)^2 / (mW 12702 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1018193/500000000000))/2) * ((1-firstRatio 25404) * √(1-firstRatio 25404) *
      sixthConstant (e1CovarianceRatio 25404 (mW 12702) (1/10^6) rowEps))) /
    (712/10000 - 25404*(1+1/10^6)*((1018193/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25404 (mW 12702) /
    ((1/10^5) * ((mW 12702 : ℝ)*25404*((mW 12702 : ℝ)+25404+1)))^2 +
  8*(mW 12702 : ℝ)*25404*(25404+2)*(25404+3) /
    ((1/1000)*((mW 12702 : ℝ)*25404*(25404+2)))^2 +
  covarianceVarianceBound 25404 (mW 12702) /
    ((1/1000)*covarianceMeanBound 25404 (mW 12702))^2 +
  normVarianceBound 25404 (mW 12702) / (3*inputVarianceMean 25404 (mW 12702))^2

end BstLean.Part268.WorldRow12702
namespace BstLean.Part268.WorldRow12703
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12703 = 231031949770733 := by
  have hu : mW 12703 ≤ 231031949770733 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12703 ≤ 231031949770732 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12703)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25406 ^ 2)
    ((25000000000000000000/3990765147855114350828441))
    ((5000000000000000000/798121613644486972230763)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25406) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25406 : ℝ)^2 / (mW 12703 : ℝ)) * (1 + 1/10^6)^2 *
    √(((3977/1953125000))/2) * ((1-firstRatio 25406) * √(1-firstRatio 25406) *
      sixthConstant (e1CovarianceRatio 25406 (mW 12703) (1/10^6) rowEps))) /
    (712/10000 - 25406*(1+1/10^6)*((3977/1953125000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25406 (mW 12703) /
    ((1/10^5) * ((mW 12703 : ℝ)*25406*((mW 12703 : ℝ)+25406+1)))^2 +
  8*(mW 12703 : ℝ)*25406*(25406+2)*(25406+3) /
    ((1/1000)*((mW 12703 : ℝ)*25406*(25406+2)))^2 +
  covarianceVarianceBound 25406 (mW 12703) /
    ((1/1000)*covarianceMeanBound 25406 (mW 12703))^2 +
  normVarianceBound 25406 (mW 12703) / (3*inputVarianceMean 25406 (mW 12703))^2

end BstLean.Part268.WorldRow12703
namespace BstLean.Part268.WorldRow12704
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12704 = 231095611220494 := by
  have hu : mW 12704 ≤ 231095611220494 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12704 ≤ 231095611220493 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12704)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25408 ^ 2)
    ((781250000000000000/124721228347514791567259))
    ((25000000000000000000/3990922227487793840477661)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25408) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25408 : ℝ)^2 / (mW 12704 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1018031/500000000000))/2) * ((1-firstRatio 25408) * √(1-firstRatio 25408) *
      sixthConstant (e1CovarianceRatio 25408 (mW 12704) (1/10^6) rowEps))) /
    (712/10000 - 25408*(1+1/10^6)*((1018031/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25408 (mW 12704) /
    ((1/10^5) * ((mW 12704 : ℝ)*25408*((mW 12704 : ℝ)+25408+1)))^2 +
  8*(mW 12704 : ℝ)*25408*(25408+2)*(25408+3) /
    ((1/1000)*((mW 12704 : ℝ)*25408*(25408+2)))^2 +
  covarianceVarianceBound 25408 (mW 12704) /
    ((1/1000)*covarianceMeanBound 25408 (mW 12704))^2 +
  normVarianceBound 25408 (mW 12704) / (3*inputVarianceMean 25408 (mW 12704))^2

end BstLean.Part268.WorldRow12704
namespace BstLean.Part268.WorldRow12705
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12705 = 231159285199323 := by
  have hu : mW 12705 ≤ 231159285199323 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12705 ≤ 231159285199322 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12705)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25410 ^ 2)
    ((5000000000000000000/798278693277166461895227))
    ((25000000000000000000/3991236386753152819801507)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25410) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25410 : ℝ)^2 / (mW 12705 : ℝ)) * (1 + 1/10^6)^2 *
    √(((20359/10000000000))/2) * ((1-firstRatio 25410) * √(1-firstRatio 25410) *
      sixthConstant (e1CovarianceRatio 25410 (mW 12705) (1/10^6) rowEps))) /
    (712/10000 - 25410*(1+1/10^6)*((20359/10000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25410 (mW 12705) /
    ((1/10^5) * ((mW 12705 : ℝ)*25410*((mW 12705 : ℝ)+25410+1)))^2 +
  8*(mW 12705 : ℝ)*25410*(25410+2)*(25410+3) /
    ((1/1000)*((mW 12705 : ℝ)*25410*(25410+2)))^2 +
  covarianceVarianceBound 25410 (mW 12705) /
    ((1/1000)*covarianceMeanBound 25410 (mW 12705))^2 +
  normVarianceBound 25410 (mW 12705) / (3*inputVarianceMean 25410 (mW 12705))^2

end BstLean.Part268.WorldRow12705
namespace BstLean.Part268.WorldRow12706
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12706 = 231222971708700 := by
  have hu : mW 12706 ≤ 231222971708700 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12706 ≤ 231222971708699 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12706)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25412 ^ 2)
    ((12500000000000000000/1995853812825595644399991))
    ((25000000000000000000/3991550546018511799125353)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25412) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25412 : ℝ)^2 / (mW 12706 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1017869/500000000000))/2) * ((1-firstRatio 25412) * √(1-firstRatio 25412) *
      sixthConstant (e1CovarianceRatio 25412 (mW 12706) (1/10^6) rowEps))) /
    (712/10000 - 25412*(1+1/10^6)*((1017869/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25412 (mW 12706) /
    ((1/10^5) * ((mW 12706 : ℝ)*25412*((mW 12706 : ℝ)+25412+1)))^2 +
  8*(mW 12706 : ℝ)*25412*(25412+2)*(25412+3) /
    ((1/1000)*((mW 12706 : ℝ)*25412*(25412+2)))^2 +
  covarianceVarianceBound 25412 (mW 12706) /
    ((1/1000)*covarianceMeanBound 25412 (mW 12706))^2 +
  normVarianceBound 25412 (mW 12706) / (3*inputVarianceMean 25412 (mW 12706))^2

end BstLean.Part268.WorldRow12706
namespace BstLean.Part268.WorldRow12707
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12707 = 231286670750105 := by
  have hu : mW 12707 ≤ 231286670750105 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12707 ≤ 231286670750104 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12707)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25414 ^ 2)
    ((25000000000000000000/3992021784916550268123829))
    ((25000000000000000000/3991864705283870778449199)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25414) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25414 : ℝ)^2 / (mW 12707 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2035577/1000000000000))/2) * ((1-firstRatio 25414) * √(1-firstRatio 25414) *
      sixthConstant (e1CovarianceRatio 25414 (mW 12707) (1/10^6) rowEps))) /
    (712/10000 - 25414*(1+1/10^6)*((2035577/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25414 (mW 12707) /
    ((1/10^5) * ((mW 12707 : ℝ)*25414*((mW 12707 : ℝ)+25414+1)))^2 +
  8*(mW 12707 : ℝ)*25414*(25414+2)*(25414+3) /
    ((1/1000)*((mW 12707 : ℝ)*25414*(25414+2)))^2 +
  covarianceVarianceBound 25414 (mW 12707) /
    ((1/1000)*covarianceMeanBound 25414 (mW 12707))^2 +
  normVarianceBound 25414 (mW 12707) / (3*inputVarianceMean 25414 (mW 12707))^2

end BstLean.Part268.WorldRow12707
namespace BstLean.Part268.WorldRow12708
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12708 = 231350382325016 := by
  have hu : mW 12708 ≤ 231350382325016 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12708 ≤ 231350382325015 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12708)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25416 ^ 2)
    ((6250000000000000000/998083986045477311861919))
    ((5000000000000000000/798435772909845951554609)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25416) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25416 : ℝ)^2 / (mW 12708 : ℝ)) * (1 + 1/10^6)^2 *
    √(((407083/200000000000))/2) * ((1-firstRatio 25416) * √(1-firstRatio 25416) *
      sixthConstant (e1CovarianceRatio 25416 (mW 12708) (1/10^6) rowEps))) /
    (712/10000 - 25416*(1+1/10^6)*((407083/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25416 (mW 12708) /
    ((1/10^5) * ((mW 12708 : ℝ)*25416*((mW 12708 : ℝ)+25416+1)))^2 +
  8*(mW 12708 : ℝ)*25416*(25416+2)*(25416+3) /
    ((1/1000)*((mW 12708 : ℝ)*25416*(25416+2)))^2 +
  covarianceVarianceBound 25416 (mW 12708) /
    ((1/1000)*covarianceMeanBound 25416 (mW 12708))^2 +
  normVarianceBound 25416 (mW 12708) / (3*inputVarianceMean 25416 (mW 12708))^2

end BstLean.Part268.WorldRow12708
namespace BstLean.Part268.WorldRow12709
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12709 = 231414106434913 := by
  have hu : mW 12709 ≤ 231414106434913 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12709 ≤ 231414106434912 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12709)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25418 ^ 2)
    ((25000000000000000000/3992650103447268226771523))
    ((25000000000000000000/3992493023814588737096891)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25418) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25418 : ℝ)^2 / (mW 12709 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2035253/1000000000000))/2) * ((1-firstRatio 25418) * √(1-firstRatio 25418) *
      sixthConstant (e1CovarianceRatio 25418 (mW 12709) (1/10^6) rowEps))) /
    (712/10000 - 25418*(1+1/10^6)*((2035253/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25418 (mW 12709) /
    ((1/10^5) * ((mW 12709 : ℝ)*25418*((mW 12709 : ℝ)+25418+1)))^2 +
  8*(mW 12709 : ℝ)*25418*(25418+2)*(25418+3) /
    ((1/1000)*((mW 12709 : ℝ)*25418*(25418+2)))^2 +
  covarianceVarianceBound 25418 (mW 12709) /
    ((1/1000)*covarianceMeanBound 25418 (mW 12709))^2 +
  normVarianceBound 25418 (mW 12709) / (3*inputVarianceMean 25418 (mW 12709))^2

end BstLean.Part268.WorldRow12709
namespace BstLean.Part268.WorldRow12710
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12710 = 231477843081276 := by
  have hu : mW 12710 ≤ 231477843081276 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12710 ≤ 231477843081275 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12710)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25420 ^ 2)
    ((2500000000000000000/399296426271262720609537))
    ((25000000000000000000/3992807183079947716420737)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25420) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25420 : ℝ)^2 / (mW 12710 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2035091/1000000000000))/2) * ((1-firstRatio 25420) * √(1-firstRatio 25420) *
      sixthConstant (e1CovarianceRatio 25420 (mW 12710) (1/10^6) rowEps))) /
    (712/10000 - 25420*(1+1/10^6)*((2035091/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25420 (mW 12710) /
    ((1/10^5) * ((mW 12710 : ℝ)*25420*((mW 12710 : ℝ)+25420+1)))^2 +
  8*(mW 12710 : ℝ)*25420*(25420+2)*(25420+3) /
    ((1/1000)*((mW 12710 : ℝ)*25420*(25420+2)))^2 +
  covarianceVarianceBound 25420 (mW 12710) /
    ((1/1000)*covarianceMeanBound 25420 (mW 12710))^2 +
  normVarianceBound 25420 (mW 12710) / (3*inputVarianceMean 25420 (mW 12710))^2

end BstLean.Part268.WorldRow12710
namespace BstLean.Part268.WorldRow12711
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12711 = 231541592265585 := by
  have hu : mW 12711 ≤ 231541592265585 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12711 ≤ 231541592265584 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12711)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25422 ^ 2)
    ((25000000000000000000/3993278421977986185419217))
    ((25000000000000000000/3993121342345306695744583)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25422) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25422 : ℝ)^2 / (mW 12711 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2034929/1000000000000))/2) * ((1-firstRatio 25422) * √(1-firstRatio 25422) *
      sixthConstant (e1CovarianceRatio 25422 (mW 12711) (1/10^6) rowEps))) /
    (712/10000 - 25422*(1+1/10^6)*((2034929/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25422 (mW 12711) /
    ((1/10^5) * ((mW 12711 : ℝ)*25422*((mW 12711 : ℝ)+25422+1)))^2 +
  8*(mW 12711 : ℝ)*25422*(25422+2)*(25422+3) /
    ((1/1000)*((mW 12711 : ℝ)*25422*(25422+2)))^2 +
  covarianceVarianceBound 25422 (mW 12711) /
    ((1/1000)*covarianceMeanBound 25422 (mW 12711))^2 +
  normVarianceBound 25422 (mW 12711) / (3*inputVarianceMean 25422 (mW 12711))^2

end BstLean.Part268.WorldRow12711
namespace BstLean.Part268.WorldRow12712
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12712 = 231605353989319 := by
  have hu : mW 12712 ≤ 231605353989319 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12712 ≤ 231605353989318 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12712)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25424 ^ 2)
    ((3125000000000000000/499199072655418145592883))
    ((25000000000000000000/3993435501610665675068429)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25424) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25424 : ℝ)^2 / (mW 12712 : ℝ)) * (1 + 1/10^6)^2 *
    √(((127173/62500000000))/2) * ((1-firstRatio 25424) * √(1-firstRatio 25424) *
      sixthConstant (e1CovarianceRatio 25424 (mW 12712) (1/10^6) rowEps))) /
    (712/10000 - 25424*(1+1/10^6)*((127173/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25424 (mW 12712) /
    ((1/10^5) * ((mW 12712 : ℝ)*25424*((mW 12712 : ℝ)+25424+1)))^2 +
  8*(mW 12712 : ℝ)*25424*(25424+2)*(25424+3) /
    ((1/1000)*((mW 12712 : ℝ)*25424*(25424+2)))^2 +
  covarianceVarianceBound 25424 (mW 12712) /
    ((1/1000)*covarianceMeanBound 25424 (mW 12712))^2 +
  normVarianceBound 25424 (mW 12712) / (3*inputVarianceMean 25424 (mW 12712))^2

end BstLean.Part268.WorldRow12712
namespace BstLean.Part268.WorldRow12713
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12713 = 231669128253957 := by
  have hu : mW 12713 ≤ 231669128253957 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12713 ≤ 231669128253956 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12713)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25426 ^ 2)
    ((25000000000000000000/3993906740508704144066911))
    ((1000000000000000000/159749986435040986175691)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25426) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25426 : ℝ)^2 / (mW 12713 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1017303/500000000000))/2) * ((1-firstRatio 25426) * √(1-firstRatio 25426) *
      sixthConstant (e1CovarianceRatio 25426 (mW 12713) (1/10^6) rowEps))) /
    (712/10000 - 25426*(1+1/10^6)*((1017303/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25426 (mW 12713) /
    ((1/10^5) * ((mW 12713 : ℝ)*25426*((mW 12713 : ℝ)+25426+1)))^2 +
  8*(mW 12713 : ℝ)*25426*(25426+2)*(25426+3) /
    ((1/1000)*((mW 12713 : ℝ)*25426*(25426+2)))^2 +
  covarianceVarianceBound 25426 (mW 12713) /
    ((1/1000)*covarianceMeanBound 25426 (mW 12713))^2 +
  normVarianceBound 25426 (mW 12713) / (3*inputVarianceMean 25426 (mW 12713))^2

end BstLean.Part268.WorldRow12713
namespace BstLean.Part268.WorldRow12714
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12714 = 231732915060981 := by
  have hu : mW 12714 ≤ 231732915060981 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12714 ≤ 231732915060980 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12714)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25428 ^ 2)
    ((12500000000000000000/1997110449887031561695379))
    ((25000000000000000000/3994063820141383633716121)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25428) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25428 : ℝ)^2 / (mW 12714 : ℝ)) * (1 + 1/10^6)^2 *
    √(((508611/250000000000))/2) * ((1-firstRatio 25428) * √(1-firstRatio 25428) *
      sixthConstant (e1CovarianceRatio 25428 (mW 12714) (1/10^6) rowEps))) /
    (712/10000 - 25428*(1+1/10^6)*((508611/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25428 (mW 12714) /
    ((1/10^5) * ((mW 12714 : ℝ)*25428*((mW 12714 : ℝ)+25428+1)))^2 +
  8*(mW 12714 : ℝ)*25428*(25428+2)*(25428+3) /
    ((1/1000)*((mW 12714 : ℝ)*25428*(25428+2)))^2 +
  covarianceVarianceBound 25428 (mW 12714) /
    ((1/1000)*covarianceMeanBound 25428 (mW 12714))^2 +
  normVarianceBound 25428 (mW 12714) / (3*inputVarianceMean 25428 (mW 12714))^2

end BstLean.Part268.WorldRow12714
namespace BstLean.Part268.WorldRow12715
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12715 = 231796714411870 := by
  have hu : mW 12715 ≤ 231796714411870 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12715 ≤ 231796714411869 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12715)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25430 ^ 2)
    ((5000000000000000000/798907011807884420542921))
    ((25000000000000000000/3994377979406742613039967)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25430) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25430 : ℝ)^2 / (mW 12715 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1017141/500000000000))/2) * ((1-firstRatio 25430) * √(1-firstRatio 25430) *
      sixthConstant (e1CovarianceRatio 25430 (mW 12715) (1/10^6) rowEps))) /
    (712/10000 - 25430*(1+1/10^6)*((1017141/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25430 (mW 12715) /
    ((1/10^5) * ((mW 12715 : ℝ)*25430*((mW 12715 : ℝ)+25430+1)))^2 +
  8*(mW 12715 : ℝ)*25430*(25430+2)*(25430+3) /
    ((1/1000)*((mW 12715 : ℝ)*25430*(25430+2)))^2 +
  covarianceVarianceBound 25430 (mW 12715) /
    ((1/1000)*covarianceMeanBound 25430 (mW 12715))^2 +
  normVarianceBound 25430 (mW 12715) / (3*inputVarianceMean 25430 (mW 12715))^2

end BstLean.Part268.WorldRow12715
namespace BstLean.Part268.WorldRow12716
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12716 = 231860526308103 := by
  have hu : mW 12716 ≤ 231860526308103 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12716 ≤ 231860526308102 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12716)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25432 ^ 2)
    ((6250000000000000000/998712304576195270509613))
    ((25000000000000000000/3994692138672101592363813)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25432) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25432 : ℝ)^2 / (mW 12716 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2034121/1000000000000))/2) * ((1-firstRatio 25432) * √(1-firstRatio 25432) *
      sixthConstant (e1CovarianceRatio 25432 (mW 12716) (1/10^6) rowEps))) /
    (712/10000 - 25432*(1+1/10^6)*((2034121/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25432 (mW 12716) /
    ((1/10^5) * ((mW 12716 : ℝ)*25432*((mW 12716 : ℝ)+25432+1)))^2 +
  8*(mW 12716 : ℝ)*25432*(25432+2)*(25432+3) /
    ((1/1000)*((mW 12716 : ℝ)*25432*(25432+2)))^2 +
  covarianceVarianceBound 25432 (mW 12716) /
    ((1/1000)*covarianceMeanBound 25432 (mW 12716))^2 +
  normVarianceBound 25432 (mW 12716) / (3*inputVarianceMean 25432 (mW 12716))^2

end BstLean.Part268.WorldRow12716
namespace BstLean.Part268.WorldRow12717
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12717 = 231924350751161 := by
  have hu : mW 12717 ≤ 231924350751161 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12717 ≤ 231924350751160 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12717)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25434 ^ 2)
    ((25000000000000000000/3995163377570140061362299))
    ((25000000000000000000/3995006297937460571687659)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25434) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25434 : ℝ)^2 / (mW 12717 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2033959/1000000000000))/2) * ((1-firstRatio 25434) * √(1-firstRatio 25434) *
      sixthConstant (e1CovarianceRatio 25434 (mW 12717) (1/10^6) rowEps))) /
    (712/10000 - 25434*(1+1/10^6)*((2033959/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25434 (mW 12717) /
    ((1/10^5) * ((mW 12717 : ℝ)*25434*((mW 12717 : ℝ)+25434+1)))^2 +
  8*(mW 12717 : ℝ)*25434*(25434+2)*(25434+3) /
    ((1/1000)*((mW 12717 : ℝ)*25434*(25434+2)))^2 +
  covarianceVarianceBound 25434 (mW 12717) /
    ((1/1000)*covarianceMeanBound 25434 (mW 12717))^2 +
  normVarianceBound 25434 (mW 12717) / (3*inputVarianceMean 25434 (mW 12717))^2

end BstLean.Part268.WorldRow12717
namespace BstLean.Part268.WorldRow12718
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12718 = 231988187742524 := by
  have hu : mW 12718 ≤ 231988187742524 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12718 ≤ 231988187742523 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12718)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25436 ^ 2)
    ((12500000000000000000/1997738768417749520343073))
    ((5000000000000000000/799064091440563910202301)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25436) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25436 : ℝ)^2 / (mW 12718 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1016899/500000000000))/2) * ((1-firstRatio 25436) * √(1-firstRatio 25436) *
      sixthConstant (e1CovarianceRatio 25436 (mW 12718) (1/10^6) rowEps))) /
    (712/10000 - 25436*(1+1/10^6)*((1016899/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25436 (mW 12718) /
    ((1/10^5) * ((mW 12718 : ℝ)*25436*((mW 12718 : ℝ)+25436+1)))^2 +
  8*(mW 12718 : ℝ)*25436*(25436+2)*(25436+3) /
    ((1/1000)*((mW 12718 : ℝ)*25436*(25436+2)))^2 +
  covarianceVarianceBound 25436 (mW 12718) /
    ((1/1000)*covarianceMeanBound 25436 (mW 12718))^2 +
  normVarianceBound 25436 (mW 12718) / (3*inputVarianceMean 25436 (mW 12718))^2

end BstLean.Part268.WorldRow12718
namespace BstLean.Part268.WorldRow12719
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12719 = 232052037283672 := by
  have hu : mW 12719 ≤ 232052037283672 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12719 ≤ 232052037283671 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12719)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25438 ^ 2)
    ((25000000000000000000/3995791696100858020009993))
    ((25000000000000000000/3995634616468178530335351)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25438) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25438 : ℝ)^2 / (mW 12719 : ℝ)) * (1 + 1/10^6)^2 *
    √(((508409/250000000000))/2) * ((1-firstRatio 25438) * √(1-firstRatio 25438) *
      sixthConstant (e1CovarianceRatio 25438 (mW 12719) (1/10^6) rowEps))) /
    (712/10000 - 25438*(1+1/10^6)*((508409/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25438 (mW 12719) /
    ((1/10^5) * ((mW 12719 : ℝ)*25438*((mW 12719 : ℝ)+25438+1)))^2 +
  8*(mW 12719 : ℝ)*25438*(25438+2)*(25438+3) /
    ((1/1000)*((mW 12719 : ℝ)*25438*(25438+2)))^2 +
  covarianceVarianceBound 25438 (mW 12719) /
    ((1/1000)*covarianceMeanBound 25438 (mW 12719))^2 +
  normVarianceBound 25438 (mW 12719) / (3*inputVarianceMean 25438 (mW 12719))^2

end BstLean.Part268.WorldRow12719
namespace BstLean.Part268.WorldRow12720
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12720 = 232115899376085 := by
  have hu : mW 12720 ≤ 232115899376085 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12720 ≤ 232115899376084 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12720)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25440 ^ 2)
    ((312500000000000000/49951323192077712491673))
    ((25000000000000000000/3995948775733537509659197)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25440) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25440 : ℝ)^2 / (mW 12720 : ℝ)) * (1 + 1/10^6)^2 *
    √(((81339/40000000000))/2) * ((1-firstRatio 25440) * √(1-firstRatio 25440) *
      sixthConstant (e1CovarianceRatio 25440 (mW 12720) (1/10^6) rowEps))) /
    (712/10000 - 25440*(1+1/10^6)*((81339/40000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25440 (mW 12720) /
    ((1/10^5) * ((mW 12720 : ℝ)*25440*((mW 12720 : ℝ)+25440+1)))^2 +
  8*(mW 12720 : ℝ)*25440*(25440+2)*(25440+3) /
    ((1/1000)*((mW 12720 : ℝ)*25440*(25440+2)))^2 +
  covarianceVarianceBound 25440 (mW 12720) /
    ((1/1000)*covarianceMeanBound 25440 (mW 12720))^2 +
  normVarianceBound 25440 (mW 12720) / (3*inputVarianceMean 25440 (mW 12720))^2

end BstLean.Part268.WorldRow12720
namespace BstLean.Part268.WorldRow12721
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12721 = 232179774021244 := by
  have hu : mW 12721 ≤ 232179774021244 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12721 ≤ 232179774021243 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12721)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25442 ^ 2)
    ((25000000000000000000/3996420014631575978657687))
    ((25000000000000000000/3996262934998896488983043)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25442) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25442 : ℝ)^2 / (mW 12721 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2033313/1000000000000))/2) * ((1-firstRatio 25442) * √(1-firstRatio 25442) *
      sixthConstant (e1CovarianceRatio 25442 (mW 12721) (1/10^6) rowEps))) /
    (712/10000 - 25442*(1+1/10^6)*((2033313/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25442 (mW 12721) /
    ((1/10^5) * ((mW 12721 : ℝ)*25442*((mW 12721 : ℝ)+25442+1)))^2 +
  8*(mW 12721 : ℝ)*25442*(25442+2)*(25442+3) /
    ((1/1000)*((mW 12721 : ℝ)*25442*(25442+2)))^2 +
  covarianceVarianceBound 25442 (mW 12721) /
    ((1/1000)*covarianceMeanBound 25442 (mW 12721))^2 +
  normVarianceBound 25442 (mW 12721) / (3*inputVarianceMean 25442 (mW 12721))^2

end BstLean.Part268.WorldRow12721
namespace BstLean.Part268.WorldRow12722
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12722 = 232243661220628 := by
  have hu : mW 12722 ≤ 232243661220628 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12722 ≤ 232243661220627 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12722)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25444 ^ 2)
    ((12500000000000000000/1998367086948467478990767))
    ((25000000000000000000/3996577094264255468306889)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25444) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25444 : ℝ)^2 / (mW 12722 : ℝ)) * (1 + 1/10^6)^2 *
    √(((3971/1953125000))/2) * ((1-firstRatio 25444) * √(1-firstRatio 25444) *
      sixthConstant (e1CovarianceRatio 25444 (mW 12722) (1/10^6) rowEps))) /
    (712/10000 - 25444*(1+1/10^6)*((3971/1953125000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25444 (mW 12722) /
    ((1/10^5) * ((mW 12722 : ℝ)*25444*((mW 12722 : ℝ)+25444+1)))^2 +
  8*(mW 12722 : ℝ)*25444*(25444+2)*(25444+3) /
    ((1/1000)*((mW 12722 : ℝ)*25444*(25444+2)))^2 +
  covarianceVarianceBound 25444 (mW 12722) /
    ((1/1000)*covarianceMeanBound 25444 (mW 12722))^2 +
  normVarianceBound 25444 (mW 12722) / (3*inputVarianceMean 25444 (mW 12722))^2

end BstLean.Part268.WorldRow12722
namespace BstLean.Part268.WorldRow12723
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12723 = 232307560975718 := by
  have hu : mW 12723 ≤ 232307560975718 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12723 ≤ 232307560975717 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12723)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25446 ^ 2)
    ((25000000000000000000/3997048333162293937305381))
    ((5000000000000000000/799378250705922889526147)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25446) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25446 : ℝ)^2 / (mW 12723 : ℝ)) * (1 + 1/10^6)^2 *
    √(((203299/100000000000))/2) * ((1-firstRatio 25446) * √(1-firstRatio 25446) *
      sixthConstant (e1CovarianceRatio 25446 (mW 12723) (1/10^6) rowEps))) /
    (712/10000 - 25446*(1+1/10^6)*((203299/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25446 (mW 12723) /
    ((1/10^5) * ((mW 12723 : ℝ)*25446*((mW 12723 : ℝ)+25446+1)))^2 +
  8*(mW 12723 : ℝ)*25446*(25446+2)*(25446+3) /
    ((1/1000)*((mW 12723 : ℝ)*25446*(25446+2)))^2 +
  covarianceVarianceBound 25446 (mW 12723) /
    ((1/1000)*covarianceMeanBound 25446 (mW 12723))^2 +
  normVarianceBound 25446 (mW 12723) / (3*inputVarianceMean 25446 (mW 12723))^2

end BstLean.Part268.WorldRow12723
namespace BstLean.Part268.WorldRow12724
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12724 = 232371473287995 := by
  have hu : mW 12724 ≤ 232371473287995 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12724 ≤ 232371473287994 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12724)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25448 ^ 2)
    ((6250000000000000000/999340623106913229157307))
    ((25000000000000000000/3997205412794973426954581)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25448) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25448 : ℝ)^2 / (mW 12724 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2032829/1000000000000))/2) * ((1-firstRatio 25448) * √(1-firstRatio 25448) *
      sixthConstant (e1CovarianceRatio 25448 (mW 12724) (1/10^6) rowEps))) /
    (712/10000 - 25448*(1+1/10^6)*((2032829/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25448 (mW 12724) /
    ((1/10^5) * ((mW 12724 : ℝ)*25448*((mW 12724 : ℝ)+25448+1)))^2 +
  8*(mW 12724 : ℝ)*25448*(25448+2)*(25448+3) /
    ((1/1000)*((mW 12724 : ℝ)*25448*(25448+2)))^2 +
  covarianceVarianceBound 25448 (mW 12724) /
    ((1/1000)*covarianceMeanBound 25448 (mW 12724))^2 +
  normVarianceBound 25448 (mW 12724) / (3*inputVarianceMean 25448 (mW 12724))^2

end BstLean.Part268.WorldRow12724
