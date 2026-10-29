import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar6
namespace BstLean.Part268.WorldRow12500
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12500 = 218366013427714 := by
  have hu : mW 12500 ≤ 218366013427714 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12500 ≤ 218366013427713 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12500)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25000 ^ 2)
    ((2000000000000000/314159265358979323847))
    ((25000000000000000000/3926833737354562058413077)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25000) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25000 : ℝ)^2 / (mW 12500 : ℝ)) * (1 + 1/10^6)^2 *
    √(((413929/200000000000))/2) * ((1-firstRatio 25000) * √(1-firstRatio 25000) *
      sixthConstant (e1CovarianceRatio 25000 (mW 12500) (1/10^6) rowEps))) /
    (712/10000 - 25000*(1+1/10^6)*((413929/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25000 (mW 12500) /
    ((1/10^5) * ((mW 12500 : ℝ)*25000*((mW 12500 : ℝ)+25000+1)))^2 +
  8*(mW 12500 : ℝ)*25000*(25000+2)*(25000+3) /
    ((1/1000)*((mW 12500 : ℝ)*25000*(25000+2)))^2 +
  covarianceVarianceBound 25000 (mW 12500) /
    ((1/1000)*covarianceMeanBound 25000 (mW 12500))^2 +
  normVarianceBound 25000 (mW 12500) / (3*inputVarianceMean 25000 (mW 12500))^2

end BstLean.Part268.WorldRow12500
namespace BstLean.Part268.WorldRow12501
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12501 = 218427162025967 := by
  have hu : mW 12501 ≤ 218427162025967 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12501 ≤ 218427162025966 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12501)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25002 ^ 2)
    ((25000000000000000000/3927304976252600527411347))
    ((25000000000000000000/3927147896619921037736923)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25002) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25002 : ℝ)^2 / (mW 12501 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1034739/500000000000))/2) * ((1-firstRatio 25002) * √(1-firstRatio 25002) *
      sixthConstant (e1CovarianceRatio 25002 (mW 12501) (1/10^6) rowEps))) /
    (712/10000 - 25002*(1+1/10^6)*((1034739/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25002 (mW 12501) /
    ((1/10^5) * ((mW 12501 : ℝ)*25002*((mW 12501 : ℝ)+25002+1)))^2 +
  8*(mW 12501 : ℝ)*25002*(25002+2)*(25002+3) /
    ((1/1000)*((mW 12501 : ℝ)*25002*(25002+2)))^2 +
  covarianceVarianceBound 25002 (mW 12501) /
    ((1/1000)*covarianceMeanBound 25002 (mW 12501))^2 +
  normVarianceBound 25002 (mW 12501) / (3*inputVarianceMean 25002 (mW 12501))^2

end BstLean.Part268.WorldRow12501
namespace BstLean.Part268.WorldRow12502
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12502 = 218488322854184 := by
  have hu : mW 12502 ≤ 218488322854184 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12502 ≤ 218488322854183 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12502)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25004 ^ 2)
    ((12500000000000000000/1963809567758979753367597))
    ((25000000000000000000/3927462055885280017060769)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25004) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25004 : ℝ)^2 / (mW 12502 : ℝ)) * (1 + 1/10^6)^2 *
    √(((206931/100000000000))/2) * ((1-firstRatio 25004) * √(1-firstRatio 25004) *
      sixthConstant (e1CovarianceRatio 25004 (mW 12502) (1/10^6) rowEps))) /
    (712/10000 - 25004*(1+1/10^6)*((206931/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25004 (mW 12502) /
    ((1/10^5) * ((mW 12502 : ℝ)*25004*((mW 12502 : ℝ)+25004+1)))^2 +
  8*(mW 12502 : ℝ)*25004*(25004+2)*(25004+3) /
    ((1/1000)*((mW 12502 : ℝ)*25004*(25004+2)))^2 +
  covarianceVarianceBound 25004 (mW 12502) /
    ((1/1000)*covarianceMeanBound 25004 (mW 12502))^2 +
  normVarianceBound 25004 (mW 12502) / (3*inputVarianceMean 25004 (mW 12502))^2

end BstLean.Part268.WorldRow12502
namespace BstLean.Part268.WorldRow12503
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12503 = 218549495913833 := by
  have hu : mW 12503 ≤ 218549495913833 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12503 ≤ 218549495913832 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12503)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25006 ^ 2)
    ((25000000000000000000/3927933294783318486059041))
    ((5000000000000000000/785555243030127799276923)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25006) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25006 : ℝ)^2 / (mW 12503 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2069143/1000000000000))/2) * ((1-firstRatio 25006) * √(1-firstRatio 25006) *
      sixthConstant (e1CovarianceRatio 25006 (mW 12503) (1/10^6) rowEps))) /
    (712/10000 - 25006*(1+1/10^6)*((2069143/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25006 (mW 12503) /
    ((1/10^5) * ((mW 12503 : ℝ)*25006*((mW 12503 : ℝ)+25006+1)))^2 +
  8*(mW 12503 : ℝ)*25006*(25006+2)*(25006+3) /
    ((1/1000)*((mW 12503 : ℝ)*25006*(25006+2)))^2 +
  covarianceVarianceBound 25006 (mW 12503) /
    ((1/1000)*covarianceMeanBound 25006 (mW 12503))^2 +
  normVarianceBound 25006 (mW 12503) / (3*inputVarianceMean 25006 (mW 12503))^2

end BstLean.Part268.WorldRow12503
namespace BstLean.Part268.WorldRow12504
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12504 = 218610681206380 := by
  have hu : mW 12504 ≤ 218610681206380 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12504 ≤ 218610681206379 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12504)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25008 ^ 2)
    ((3125000000000000000/491030931756084683172861))
    ((25000000000000000000/3928090374415997975708461)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25008) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25008 : ℝ)^2 / (mW 12504 : ℝ)) * (1 + 1/10^6)^2 *
    √(((129311/62500000000))/2) * ((1-firstRatio 25008) * √(1-firstRatio 25008) *
      sixthConstant (e1CovarianceRatio 25008 (mW 12504) (1/10^6) rowEps))) /
    (712/10000 - 25008*(1+1/10^6)*((129311/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25008 (mW 12504) /
    ((1/10^5) * ((mW 12504 : ℝ)*25008*((mW 12504 : ℝ)+25008+1)))^2 +
  8*(mW 12504 : ℝ)*25008*(25008+2)*(25008+3) /
    ((1/1000)*((mW 12504 : ℝ)*25008*(25008+2)))^2 +
  covarianceVarianceBound 25008 (mW 12504) /
    ((1/1000)*covarianceMeanBound 25008 (mW 12504))^2 +
  normVarianceBound 25008 (mW 12504) / (3*inputVarianceMean 25008 (mW 12504))^2

end BstLean.Part268.WorldRow12504
namespace BstLean.Part268.WorldRow12505
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12505 = 218671878733295 := by
  have hu : mW 12505 ≤ 218671878733295 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12505 ≤ 218671878733294 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12505)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25010 ^ 2)
    ((5000000000000000000/785712322662807288941347))
    ((25000000000000000000/3928404533681356955032307)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25010) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25010 : ℝ)^2 / (mW 12505 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2068809/1000000000000))/2) * ((1-firstRatio 25010) * √(1-firstRatio 25010) *
      sixthConstant (e1CovarianceRatio 25010 (mW 12505) (1/10^6) rowEps))) /
    (712/10000 - 25010*(1+1/10^6)*((2068809/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25010 (mW 12505) /
    ((1/10^5) * ((mW 12505 : ℝ)*25010*((mW 12505 : ℝ)+25010+1)))^2 +
  8*(mW 12505 : ℝ)*25010*(25010+2)*(25010+3) /
    ((1/1000)*((mW 12505 : ℝ)*25010*(25010+2)))^2 +
  covarianceVarianceBound 25010 (mW 12505) /
    ((1/1000)*covarianceMeanBound 25010 (mW 12505))^2 +
  normVarianceBound 25010 (mW 12505) / (3*inputVarianceMean 25010 (mW 12505))^2

end BstLean.Part268.WorldRow12505
namespace BstLean.Part268.WorldRow12506
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12506 = 218733088496045 := by
  have hu : mW 12506 ≤ 218733088496045 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12506 ≤ 218733088496044 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12506)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25012 ^ 2)
    ((12500000000000000000/1964437886289697712015291))
    ((25000000000000000000/3928718692946715934356153)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25012) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25012 : ℝ)^2 / (mW 12506 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2068641/1000000000000))/2) * ((1-firstRatio 25012) * √(1-firstRatio 25012) *
      sixthConstant (e1CovarianceRatio 25012 (mW 12506) (1/10^6) rowEps))) /
    (712/10000 - 25012*(1+1/10^6)*((2068641/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25012 (mW 12506) /
    ((1/10^5) * ((mW 12506 : ℝ)*25012*((mW 12506 : ℝ)+25012+1)))^2 +
  8*(mW 12506 : ℝ)*25012*(25012+2)*(25012+3) /
    ((1/1000)*((mW 12506 : ℝ)*25012*(25012+2)))^2 +
  covarianceVarianceBound 25012 (mW 12506) /
    ((1/1000)*covarianceMeanBound 25012 (mW 12506))^2 +
  normVarianceBound 25012 (mW 12506) / (3*inputVarianceMean 25012 (mW 12506))^2

end BstLean.Part268.WorldRow12506
namespace BstLean.Part268.WorldRow12507
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12507 = 218794310496096 := by
  have hu : mW 12507 ≤ 218794310496096 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12507 ≤ 218794310496095 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12507)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25014 ^ 2)
    ((25000000000000000000/3929189931844754403354429))
    ((25000000000000000000/3929032852212074913679999)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25014) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25014 : ℝ)^2 / (mW 12507 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1034237/500000000000))/2) * ((1-firstRatio 25014) * √(1-firstRatio 25014) *
      sixthConstant (e1CovarianceRatio 25014 (mW 12507) (1/10^6) rowEps))) /
    (712/10000 - 25014*(1+1/10^6)*((1034237/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25014 (mW 12507) /
    ((1/10^5) * ((mW 12507 : ℝ)*25014*((mW 12507 : ℝ)+25014+1)))^2 +
  8*(mW 12507 : ℝ)*25014*(25014+2)*(25014+3) /
    ((1/1000)*((mW 12507 : ℝ)*25014*(25014+2)))^2 +
  covarianceVarianceBound 25014 (mW 12507) /
    ((1/1000)*covarianceMeanBound 25014 (mW 12507))^2 +
  normVarianceBound 25014 (mW 12507) / (3*inputVarianceMean 25014 (mW 12507))^2

end BstLean.Part268.WorldRow12507
namespace BstLean.Part268.WorldRow12508
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12508 = 218855544734918 := by
  have hu : mW 12508 ≤ 218855544734918 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12508 ≤ 218855544734917 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12508)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25016 ^ 2)
    ((6250000000000000000/982376022777528345669569))
    ((5000000000000000000/785869402295486778600769)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25016) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25016 : ℝ)^2 / (mW 12508 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2068307/1000000000000))/2) * ((1-firstRatio 25016) * √(1-firstRatio 25016) *
      sixthConstant (e1CovarianceRatio 25016 (mW 12508) (1/10^6) rowEps))) /
    (712/10000 - 25016*(1+1/10^6)*((2068307/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25016 (mW 12508) /
    ((1/10^5) * ((mW 12508 : ℝ)*25016*((mW 12508 : ℝ)+25016+1)))^2 +
  8*(mW 12508 : ℝ)*25016*(25016+2)*(25016+3) /
    ((1/1000)*((mW 12508 : ℝ)*25016*(25016+2)))^2 +
  covarianceVarianceBound 25016 (mW 12508) /
    ((1/1000)*covarianceMeanBound 25016 (mW 12508))^2 +
  normVarianceBound 25016 (mW 12508) / (3*inputVarianceMean 25016 (mW 12508))^2

end BstLean.Part268.WorldRow12508
namespace BstLean.Part268.WorldRow12509
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12509 = 218916791213978 := by
  have hu : mW 12509 ≤ 218916791213978 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12509 ≤ 218916791213977 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12509)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25018 ^ 2)
    ((25000000000000000000/3929818250375472362002123))
    ((25000000000000000000/3929661170742792872327691)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25018) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25018 : ℝ)^2 / (mW 12509 : ℝ)) * (1 + 1/10^6)^2 *
    √(((103407/50000000000))/2) * ((1-firstRatio 25018) * √(1-firstRatio 25018) *
      sixthConstant (e1CovarianceRatio 25018 (mW 12509) (1/10^6) rowEps))) /
    (712/10000 - 25018*(1+1/10^6)*((103407/50000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25018 (mW 12509) /
    ((1/10^5) * ((mW 12509 : ℝ)*25018*((mW 12509 : ℝ)+25018+1)))^2 +
  8*(mW 12509 : ℝ)*25018*(25018+2)*(25018+3) /
    ((1/1000)*((mW 12509 : ℝ)*25018*(25018+2)))^2 +
  covarianceVarianceBound 25018 (mW 12509) /
    ((1/1000)*covarianceMeanBound 25018 (mW 12509))^2 +
  normVarianceBound 25018 (mW 12509) / (3*inputVarianceMean 25018 (mW 12509))^2

end BstLean.Part268.WorldRow12509
namespace BstLean.Part268.WorldRow12510
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12510 = 218978049934744 := by
  have hu : mW 12510 ≤ 218978049934744 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12510 ≤ 218978049934743 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12510)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25020 ^ 2)
    ((2500000000000000000/393013240964083134132597))
    ((25000000000000000000/3929975330008151851651537)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25020) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25020 : ℝ)^2 / (mW 12510 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2067973/1000000000000))/2) * ((1-firstRatio 25020) * √(1-firstRatio 25020) *
      sixthConstant (e1CovarianceRatio 25020 (mW 12510) (1/10^6) rowEps))) /
    (712/10000 - 25020*(1+1/10^6)*((2067973/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25020 (mW 12510) /
    ((1/10^5) * ((mW 12510 : ℝ)*25020*((mW 12510 : ℝ)+25020+1)))^2 +
  8*(mW 12510 : ℝ)*25020*(25020+2)*(25020+3) /
    ((1/1000)*((mW 12510 : ℝ)*25020*(25020+2)))^2 +
  covarianceVarianceBound 25020 (mW 12510) /
    ((1/1000)*covarianceMeanBound 25020 (mW 12510))^2 +
  normVarianceBound 25020 (mW 12510) / (3*inputVarianceMean 25020 (mW 12510))^2

end BstLean.Part268.WorldRow12510
namespace BstLean.Part268.WorldRow12511
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12511 = 219039320898684 := by
  have hu : mW 12511 ≤ 219039320898684 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12511 ≤ 219039320898683 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12511)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25022 ^ 2)
    ((25000000000000000000/3930446568906190320649817))
    ((25000000000000000000/3930289489273510830975383)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25022) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25022 : ℝ)^2 / (mW 12511 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1033903/500000000000))/2) * ((1-firstRatio 25022) * √(1-firstRatio 25022) *
      sixthConstant (e1CovarianceRatio 25022 (mW 12511) (1/10^6) rowEps))) /
    (712/10000 - 25022*(1+1/10^6)*((1033903/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25022 (mW 12511) /
    ((1/10^5) * ((mW 12511 : ℝ)*25022*((mW 12511 : ℝ)+25022+1)))^2 +
  8*(mW 12511 : ℝ)*25022*(25022+2)*(25022+3) /
    ((1/1000)*((mW 12511 : ℝ)*25022*(25022+2)))^2 +
  covarianceVarianceBound 25022 (mW 12511) /
    ((1/1000)*covarianceMeanBound 25022 (mW 12511))^2 +
  normVarianceBound 25022 (mW 12511) / (3*inputVarianceMean 25022 (mW 12511))^2

end BstLean.Part268.WorldRow12511
namespace BstLean.Part268.WorldRow12512
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12512 = 219100604107265 := by
  have hu : mW 12512 ≤ 219100604107265 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12512 ≤ 219100604107264 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12512)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25024 ^ 2)
    ((781250000000000000/122836272755360915624177))
    ((25000000000000000000/3930603648538869810299229)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25024) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25024 : ℝ)^2 / (mW 12512 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2067639/1000000000000))/2) * ((1-firstRatio 25024) * √(1-firstRatio 25024) *
      sixthConstant (e1CovarianceRatio 25024 (mW 12512) (1/10^6) rowEps))) /
    (712/10000 - 25024*(1+1/10^6)*((2067639/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25024 (mW 12512) /
    ((1/10^5) * ((mW 12512 : ℝ)*25024*((mW 12512 : ℝ)+25024+1)))^2 +
  8*(mW 12512 : ℝ)*25024*(25024+2)*(25024+3) /
    ((1/1000)*((mW 12512 : ℝ)*25024*(25024+2)))^2 +
  covarianceVarianceBound 25024 (mW 12512) /
    ((1/1000)*covarianceMeanBound 25024 (mW 12512))^2 +
  normVarianceBound 25024 (mW 12512) / (3*inputVarianceMean 25024 (mW 12512))^2

end BstLean.Part268.WorldRow12512
namespace BstLean.Part268.WorldRow12513
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12513 = 219161899561957 := by
  have hu : mW 12513 ≤ 219161899561957 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12513 ≤ 219161899561956 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12513)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25026 ^ 2)
    ((25000000000000000000/3931074887436908279297511))
    ((1000000000000000000/157236712312169151584923)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25026) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25026 : ℝ)^2 / (mW 12513 : ℝ)) * (1 + 1/10^6)^2 *
    √(((129217/62500000000))/2) * ((1-firstRatio 25026) * √(1-firstRatio 25026) *
      sixthConstant (e1CovarianceRatio 25026 (mW 12513) (1/10^6) rowEps))) /
    (712/10000 - 25026*(1+1/10^6)*((129217/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25026 (mW 12513) /
    ((1/10^5) * ((mW 12513 : ℝ)*25026*((mW 12513 : ℝ)+25026+1)))^2 +
  8*(mW 12513 : ℝ)*25026*(25026+2)*(25026+3) /
    ((1/1000)*((mW 12513 : ℝ)*25026*(25026+2)))^2 +
  covarianceVarianceBound 25026 (mW 12513) /
    ((1/1000)*covarianceMeanBound 25026 (mW 12513))^2 +
  normVarianceBound 25026 (mW 12513) / (3*inputVarianceMean 25026 (mW 12513))^2

end BstLean.Part268.WorldRow12513
namespace BstLean.Part268.WorldRow12514
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12514 = 219223207264227 := by
  have hu : mW 12514 ≤ 219223207264227 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12514 ≤ 219223207264226 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12514)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25028 ^ 2)
    ((12500000000000000000/1965694523351133629310679))
    ((25000000000000000000/3931231967069587768946921)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25028) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25028 : ℝ)^2 / (mW 12514 : ℝ)) * (1 + 1/10^6)^2 *
    √(((413461/200000000000))/2) * ((1-firstRatio 25028) * √(1-firstRatio 25028) *
      sixthConstant (e1CovarianceRatio 25028 (mW 12514) (1/10^6) rowEps))) /
    (712/10000 - 25028*(1+1/10^6)*((413461/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25028 (mW 12514) /
    ((1/10^5) * ((mW 12514 : ℝ)*25028*((mW 12514 : ℝ)+25028+1)))^2 +
  8*(mW 12514 : ℝ)*25028*(25028+2)*(25028+3) /
    ((1/1000)*((mW 12514 : ℝ)*25028*(25028+2)))^2 +
  covarianceVarianceBound 25028 (mW 12514) /
    ((1/1000)*covarianceMeanBound 25028 (mW 12514))^2 +
  normVarianceBound 25028 (mW 12514) / (3*inputVarianceMean 25028 (mW 12514))^2

end BstLean.Part268.WorldRow12514
namespace BstLean.Part268.WorldRow12515
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12515 = 219284527215543 := by
  have hu : mW 12515 ≤ 219284527215543 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12515 ≤ 219284527215542 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12515)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25030 ^ 2)
    ((5000000000000000000/786340641193525247589041))
    ((25000000000000000000/3931546126334946748270767)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25030) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25030 : ℝ)^2 / (mW 12515 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1033569/500000000000))/2) * ((1-firstRatio 25030) * √(1-firstRatio 25030) *
      sixthConstant (e1CovarianceRatio 25030 (mW 12515) (1/10^6) rowEps))) /
    (712/10000 - 25030*(1+1/10^6)*((1033569/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25030 (mW 12515) /
    ((1/10^5) * ((mW 12515 : ℝ)*25030*((mW 12515 : ℝ)+25030+1)))^2 +
  8*(mW 12515 : ℝ)*25030*(25030+2)*(25030+3) /
    ((1/1000)*((mW 12515 : ℝ)*25030*(25030+2)))^2 +
  covarianceVarianceBound 25030 (mW 12515) /
    ((1/1000)*covarianceMeanBound 25030 (mW 12515))^2 +
  normVarianceBound 25030 (mW 12515) / (3*inputVarianceMean 25030 (mW 12515))^2

end BstLean.Part268.WorldRow12515
namespace BstLean.Part268.WorldRow12516
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12516 = 219345859417373 := by
  have hu : mW 12516 ≤ 219345859417373 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12516 ≤ 219345859417372 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12516)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25032 ^ 2)
    ((6250000000000000000/983004341308246304317263))
    ((25000000000000000000/3931860285600305727594613)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25032) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25032 : ℝ)^2 / (mW 12516 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2066971/1000000000000))/2) * ((1-firstRatio 25032) * √(1-firstRatio 25032) *
      sixthConstant (e1CovarianceRatio 25032 (mW 12516) (1/10^6) rowEps))) /
    (712/10000 - 25032*(1+1/10^6)*((2066971/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25032 (mW 12516) /
    ((1/10^5) * ((mW 12516 : ℝ)*25032*((mW 12516 : ℝ)+25032+1)))^2 +
  8*(mW 12516 : ℝ)*25032*(25032+2)*(25032+3) /
    ((1/1000)*((mW 12516 : ℝ)*25032*(25032+2)))^2 +
  covarianceVarianceBound 25032 (mW 12516) /
    ((1/1000)*covarianceMeanBound 25032 (mW 12516))^2 +
  normVarianceBound 25032 (mW 12516) / (3*inputVarianceMean 25032 (mW 12516))^2

end BstLean.Part268.WorldRow12516
namespace BstLean.Part268.WorldRow12517
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12517 = 219407203871187 := by
  have hu : mW 12517 ≤ 219407203871187 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12517 ≤ 219407203871186 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12517)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25034 ^ 2)
    ((25000000000000000000/3932331524498344196592899))
    ((25000000000000000000/3932174444865664706918459)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25034) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25034 : ℝ)^2 / (mW 12517 : ℝ)) * (1 + 1/10^6)^2 *
    √(((516701/250000000000))/2) * ((1-firstRatio 25034) * √(1-firstRatio 25034) *
      sixthConstant (e1CovarianceRatio 25034 (mW 12517) (1/10^6) rowEps))) /
    (712/10000 - 25034*(1+1/10^6)*((516701/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25034 (mW 12517) /
    ((1/10^5) * ((mW 12517 : ℝ)*25034*((mW 12517 : ℝ)+25034+1)))^2 +
  8*(mW 12517 : ℝ)*25034*(25034+2)*(25034+3) /
    ((1/1000)*((mW 12517 : ℝ)*25034*(25034+2)))^2 +
  covarianceVarianceBound 25034 (mW 12517) /
    ((1/1000)*covarianceMeanBound 25034 (mW 12517))^2 +
  normVarianceBound 25034 (mW 12517) / (3*inputVarianceMean 25034 (mW 12517))^2

end BstLean.Part268.WorldRow12517
namespace BstLean.Part268.WorldRow12518
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12518 = 219468560578452 := by
  have hu : mW 12518 ≤ 219468560578452 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12518 ≤ 219468560578451 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12518)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25036 ^ 2)
    ((12500000000000000000/1966322841881851587958373))
    ((5000000000000000000/786497720826204737248461)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25036) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25036 : ℝ)^2 / (mW 12518 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2066637/1000000000000))/2) * ((1-firstRatio 25036) * √(1-firstRatio 25036) *
      sixthConstant (e1CovarianceRatio 25036 (mW 12518) (1/10^6) rowEps))) /
    (712/10000 - 25036*(1+1/10^6)*((2066637/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25036 (mW 12518) /
    ((1/10^5) * ((mW 12518 : ℝ)*25036*((mW 12518 : ℝ)+25036+1)))^2 +
  8*(mW 12518 : ℝ)*25036*(25036+2)*(25036+3) /
    ((1/1000)*((mW 12518 : ℝ)*25036*(25036+2)))^2 +
  covarianceVarianceBound 25036 (mW 12518) /
    ((1/1000)*covarianceMeanBound 25036 (mW 12518))^2 +
  normVarianceBound 25036 (mW 12518) / (3*inputVarianceMean 25036 (mW 12518))^2

end BstLean.Part268.WorldRow12518
namespace BstLean.Part268.WorldRow12519
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12519 = 219529929540637 := by
  have hu : mW 12519 ≤ 219529929540637 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12519 ≤ 219529929540636 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12519)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25038 ^ 2)
    ((25000000000000000000/3932959843029062155240593))
    ((25000000000000000000/3932802763396382665566151)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25038) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25038 : ℝ)^2 / (mW 12519 : ℝ)) * (1 + 1/10^6)^2 *
    √(((206647/100000000000))/2) * ((1-firstRatio 25038) * √(1-firstRatio 25038) *
      sixthConstant (e1CovarianceRatio 25038 (mW 12519) (1/10^6) rowEps))) /
    (712/10000 - 25038*(1+1/10^6)*((206647/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25038 (mW 12519) /
    ((1/10^5) * ((mW 12519 : ℝ)*25038*((mW 12519 : ℝ)+25038+1)))^2 +
  8*(mW 12519 : ℝ)*25038*(25038+2)*(25038+3) /
    ((1/1000)*((mW 12519 : ℝ)*25038*(25038+2)))^2 +
  covarianceVarianceBound 25038 (mW 12519) /
    ((1/1000)*covarianceMeanBound 25038 (mW 12519))^2 +
  normVarianceBound 25038 (mW 12519) / (3*inputVarianceMean 25038 (mW 12519))^2

end BstLean.Part268.WorldRow12519
namespace BstLean.Part268.WorldRow12520
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12520 = 219591310759211 := by
  have hu : mW 12520 ≤ 219591310759211 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12520 ≤ 219591310759210 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12520)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25040 ^ 2)
    ((625000000000000000/98331850057360528364111))
    ((25000000000000000000/3933116922661741644889997)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25040) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25040 : ℝ)^2 / (mW 12520 : ℝ)) * (1 + 1/10^6)^2 *
    √(((16143/7812500000))/2) * ((1-firstRatio 25040) * √(1-firstRatio 25040) *
      sixthConstant (e1CovarianceRatio 25040 (mW 12520) (1/10^6) rowEps))) /
    (712/10000 - 25040*(1+1/10^6)*((16143/7812500000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25040 (mW 12520) /
    ((1/10^5) * ((mW 12520 : ℝ)*25040*((mW 12520 : ℝ)+25040+1)))^2 +
  8*(mW 12520 : ℝ)*25040*(25040+2)*(25040+3) /
    ((1/1000)*((mW 12520 : ℝ)*25040*(25040+2)))^2 +
  covarianceVarianceBound 25040 (mW 12520) /
    ((1/1000)*covarianceMeanBound 25040 (mW 12520))^2 +
  normVarianceBound 25040 (mW 12520) / (3*inputVarianceMean 25040 (mW 12520))^2

end BstLean.Part268.WorldRow12520
namespace BstLean.Part268.WorldRow12521
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12521 = 219652704235641 := by
  have hu : mW 12521 ≤ 219652704235641 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12521 ≤ 219652704235640 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12521)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25042 ^ 2)
    ((25000000000000000000/3933588161559780113888287))
    ((25000000000000000000/3933431081927100624213843)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25042) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25042 : ℝ)^2 / (mW 12521 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2066137/1000000000000))/2) * ((1-firstRatio 25042) * √(1-firstRatio 25042) *
      sixthConstant (e1CovarianceRatio 25042 (mW 12521) (1/10^6) rowEps))) /
    (712/10000 - 25042*(1+1/10^6)*((2066137/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25042 (mW 12521) /
    ((1/10^5) * ((mW 12521 : ℝ)*25042*((mW 12521 : ℝ)+25042+1)))^2 +
  8*(mW 12521 : ℝ)*25042*(25042+2)*(25042+3) /
    ((1/1000)*((mW 12521 : ℝ)*25042*(25042+2)))^2 +
  covarianceVarianceBound 25042 (mW 12521) /
    ((1/1000)*covarianceMeanBound 25042 (mW 12521))^2 +
  normVarianceBound 25042 (mW 12521) / (3*inputVarianceMean 25042 (mW 12521))^2

end BstLean.Part268.WorldRow12521
namespace BstLean.Part268.WorldRow12522
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12522 = 219714109971397 := by
  have hu : mW 12522 ≤ 219714109971397 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12522 ≤ 219714109971396 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12522)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25044 ^ 2)
    ((12500000000000000000/1966951160412569546606067))
    ((25000000000000000000/3933745241192459603537689)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25044) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25044 : ℝ)^2 / (mW 12522 : ℝ)) * (1 + 1/10^6)^2 *
    √(((206597/100000000000))/2) * ((1-firstRatio 25044) * √(1-firstRatio 25044) *
      sixthConstant (e1CovarianceRatio 25044 (mW 12522) (1/10^6) rowEps))) /
    (712/10000 - 25044*(1+1/10^6)*((206597/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25044 (mW 12522) /
    ((1/10^5) * ((mW 12522 : ℝ)*25044*((mW 12522 : ℝ)+25044+1)))^2 +
  8*(mW 12522 : ℝ)*25044*(25044+2)*(25044+3) /
    ((1/1000)*((mW 12522 : ℝ)*25044*(25044+2)))^2 +
  covarianceVarianceBound 25044 (mW 12522) /
    ((1/1000)*covarianceMeanBound 25044 (mW 12522))^2 +
  normVarianceBound 25044 (mW 12522) / (3*inputVarianceMean 25044 (mW 12522))^2

end BstLean.Part268.WorldRow12522
namespace BstLean.Part268.WorldRow12523
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12523 = 219775527967946 := by
  have hu : mW 12523 ≤ 219775527967946 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12523 ≤ 219775527967945 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12523)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25046 ^ 2)
    ((25000000000000000000/3934216480090498072535981))
    ((5000000000000000000/786811880091563716572307)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25046) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25046 : ℝ)^2 / (mW 12523 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2065803/1000000000000))/2) * ((1-firstRatio 25046) * √(1-firstRatio 25046) *
      sixthConstant (e1CovarianceRatio 25046 (mW 12523) (1/10^6) rowEps))) /
    (712/10000 - 25046*(1+1/10^6)*((2065803/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25046 (mW 12523) /
    ((1/10^5) * ((mW 12523 : ℝ)*25046*((mW 12523 : ℝ)+25046+1)))^2 +
  8*(mW 12523 : ℝ)*25046*(25046+2)*(25046+3) /
    ((1/1000)*((mW 12523 : ℝ)*25046*(25046+2)))^2 +
  covarianceVarianceBound 25046 (mW 12523) /
    ((1/1000)*covarianceMeanBound 25046 (mW 12523))^2 +
  normVarianceBound 25046 (mW 12523) / (3*inputVarianceMean 25046 (mW 12523))^2

end BstLean.Part268.WorldRow12523
namespace BstLean.Part268.WorldRow12524
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12524 = 219836958226759 := by
  have hu : mW 12524 ≤ 219836958226759 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12524 ≤ 219836958226758 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12524)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25048 ^ 2)
    ((6250000000000000000/983632659838964262964957))
    ((25000000000000000000/3934373559723177562185381)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25048) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25048 : ℝ)^2 / (mW 12524 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2065637/1000000000000))/2) * ((1-firstRatio 25048) * √(1-firstRatio 25048) *
      sixthConstant (e1CovarianceRatio 25048 (mW 12524) (1/10^6) rowEps))) /
    (712/10000 - 25048*(1+1/10^6)*((2065637/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25048 (mW 12524) /
    ((1/10^5) * ((mW 12524 : ℝ)*25048*((mW 12524 : ℝ)+25048+1)))^2 +
  8*(mW 12524 : ℝ)*25048*(25048+2)*(25048+3) /
    ((1/1000)*((mW 12524 : ℝ)*25048*(25048+2)))^2 +
  covarianceVarianceBound 25048 (mW 12524) /
    ((1/1000)*covarianceMeanBound 25048 (mW 12524))^2 +
  normVarianceBound 25048 (mW 12524) / (3*inputVarianceMean 25048 (mW 12524))^2

end BstLean.Part268.WorldRow12524
