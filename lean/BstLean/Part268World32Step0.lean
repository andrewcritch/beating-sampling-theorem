import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar32
namespace BstLean.Part268.WorldRow13150
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13150 = 260759497160237 := by
  have hu : mW 13150 ≤ 260759497160237 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13150 ≤ 260759497160236 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13150)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26300 ^ 2)
    ((500000000000000000/82623886789411562171761))
    ((25000000000000000000/4131037259837898618912977)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26300) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26300 : ℝ)^2 / (mW 13150 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1966317/1000000000000))/2) * ((1-firstRatio 26300) * √(1-firstRatio 26300) *
      sixthConstant (e1CovarianceRatio 26300 (mW 13150) (1/10^6) rowEps))) /
    (712/10000 - 26300*(1+1/10^6)*((1966317/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26300 (mW 13150) /
    ((1/10^5) * ((mW 13150 : ℝ)*26300*((mW 13150 : ℝ)+26300+1)))^2 +
  8*(mW 13150 : ℝ)*26300*(26300+2)*(26300+3) /
    ((1/1000)*((mW 13150 : ℝ)*26300*(26300+2)))^2 +
  covarianceVarianceBound 26300 (mW 13150) /
    ((1/1000)*covarianceMeanBound 26300 (mW 13150))^2 +
  normVarianceBound 26300 (mW 13150) / (3*inputVarianceMean 26300 (mW 13150))^2

end BstLean.Part268.WorldRow13150
namespace BstLean.Part268.WorldRow13151
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13151 = 260828907426240 := by
  have hu : mW 13151 ≤ 260828907426240 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13151 ≤ 260828907426239 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13151)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26302 ^ 2)
    ((25000000000000000000/4131508498735937087911897))
    ((25000000000000000000/4131351419103257598236823)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26302) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26302 : ℝ)^2 / (mW 13151 : ℝ)) * (1 + 1/10^6)^2 *
    √(((983083/500000000000))/2) * ((1-firstRatio 26302) * √(1-firstRatio 26302) *
      sixthConstant (e1CovarianceRatio 26302 (mW 13151) (1/10^6) rowEps))) /
    (712/10000 - 26302*(1+1/10^6)*((983083/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26302 (mW 13151) /
    ((1/10^5) * ((mW 13151 : ℝ)*26302*((mW 13151 : ℝ)+26302+1)))^2 +
  8*(mW 13151 : ℝ)*26302*(26302+2)*(26302+3) /
    ((1/1000)*((mW 13151 : ℝ)*26302*(26302+2)))^2 +
  covarianceVarianceBound 26302 (mW 13151) /
    ((1/1000)*covarianceMeanBound 26302 (mW 13151))^2 +
  normVarianceBound 26302 (mW 13151) / (3*inputVarianceMean 26302 (mW 13151))^2

end BstLean.Part268.WorldRow13151
namespace BstLean.Part268.WorldRow13152
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13152 = 260898330888362 := by
  have hu : mW 13152 ≤ 260898330888362 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13152 ≤ 260898330888361 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13152)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26304 ^ 2)
    ((781250000000000000/129119458062540502101117))
    ((25000000000000000000/4131665578368616577560669)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26304) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26304 : ℝ)^2 / (mW 13152 : ℝ)) * (1 + 1/10^6)^2 *
    √(((393203/200000000000))/2) * ((1-firstRatio 26304) * √(1-firstRatio 26304) *
      sixthConstant (e1CovarianceRatio 26304 (mW 13152) (1/10^6) rowEps))) /
    (712/10000 - 26304*(1+1/10^6)*((393203/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26304 (mW 13152) /
    ((1/10^5) * ((mW 13152 : ℝ)*26304*((mW 13152 : ℝ)+26304+1)))^2 +
  8*(mW 13152 : ℝ)*26304*(26304+2)*(26304+3) /
    ((1/1000)*((mW 13152 : ℝ)*26304*(26304+2)))^2 +
  covarianceVarianceBound 26304 (mW 13152) /
    ((1/1000)*covarianceMeanBound 26304 (mW 13152))^2 +
  normVarianceBound 26304 (mW 13152) / (3*inputVarianceMean 26304 (mW 13152))^2

end BstLean.Part268.WorldRow13152
namespace BstLean.Part268.WorldRow13153
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13153 = 260967767548109 := by
  have hu : mW 13153 ≤ 260967767548109 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13153 ≤ 260967767548108 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13153)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26306 ^ 2)
    ((25000000000000000000/4132136817266655046559591))
    ((5000000000000000000/826395947526795111376903)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26306) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26306 : ℝ)^2 / (mW 13153 : ℝ)) * (1 + 1/10^6)^2 *
    √(((245733/125000000000))/2) * ((1-firstRatio 26306) * √(1-firstRatio 26306) *
      sixthConstant (e1CovarianceRatio 26306 (mW 13153) (1/10^6) rowEps))) /
    (712/10000 - 26306*(1+1/10^6)*((245733/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26306 (mW 13153) /
    ((1/10^5) * ((mW 13153 : ℝ)*26306*((mW 13153 : ℝ)+26306+1)))^2 +
  8*(mW 13153 : ℝ)*26306*(26306+2)*(26306+3) /
    ((1/1000)*((mW 13153 : ℝ)*26306*(26306+2)))^2 +
  covarianceVarianceBound 26306 (mW 13153) /
    ((1/1000)*covarianceMeanBound 26306 (mW 13153))^2 +
  normVarianceBound 26306 (mW 13153) / (3*inputVarianceMean 26306 (mW 13153))^2

end BstLean.Part268.WorldRow13153
namespace BstLean.Part268.WorldRow13154
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13154 = 261037217406984 := by
  have hu : mW 13154 ≤ 261037217406984 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13154 ≤ 261037217406983 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13154)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26308 ^ 2)
    ((12500000000000000000/2066225488266007012941719))
    ((25000000000000000000/4132293896899334536208361)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26308) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26308 : ℝ)^2 / (mW 13154 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1965713/1000000000000))/2) * ((1-firstRatio 26308) * √(1-firstRatio 26308) *
      sixthConstant (e1CovarianceRatio 26308 (mW 13154) (1/10^6) rowEps))) /
    (712/10000 - 26308*(1+1/10^6)*((1965713/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26308 (mW 13154) /
    ((1/10^5) * ((mW 13154 : ℝ)*26308*((mW 13154 : ℝ)+26308+1)))^2 +
  8*(mW 13154 : ℝ)*26308*(26308+2)*(26308+3) /
    ((1/1000)*((mW 13154 : ℝ)*26308*(26308+2)))^2 +
  covarianceVarianceBound 26308 (mW 13154) /
    ((1/1000)*covarianceMeanBound 26308 (mW 13154))^2 +
  normVarianceBound 26308 (mW 13154) / (3*inputVarianceMean 26308 (mW 13154))^2

end BstLean.Part268.WorldRow13154
namespace BstLean.Part268.WorldRow13155
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13155 = 261106680466495 := by
  have hu : mW 13155 ≤ 261106680466495 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13155 ≤ 261106680466494 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13155)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26310 ^ 2)
    ((5000000000000000000/826553027159474601041457))
    ((25000000000000000000/4132608056164693515532207)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26310) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26310 : ℝ)^2 / (mW 13155 : ℝ)) * (1 + 1/10^6)^2 *
    √(((982781/500000000000))/2) * ((1-firstRatio 26310) * √(1-firstRatio 26310) *
      sixthConstant (e1CovarianceRatio 26310 (mW 13155) (1/10^6) rowEps))) /
    (712/10000 - 26310*(1+1/10^6)*((982781/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26310 (mW 13155) /
    ((1/10^5) * ((mW 13155 : ℝ)*26310*((mW 13155 : ℝ)+26310+1)))^2 +
  8*(mW 13155 : ℝ)*26310*(26310+2)*(26310+3) /
    ((1/1000)*((mW 13155 : ℝ)*26310*(26310+2)))^2 +
  covarianceVarianceBound 26310 (mW 13155) /
    ((1/1000)*covarianceMeanBound 26310 (mW 13155))^2 +
  normVarianceBound 26310 (mW 13155) / (3*inputVarianceMean 26310 (mW 13155))^2

end BstLean.Part268.WorldRow13155
namespace BstLean.Part268.WorldRow13156
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13156 = 261176156728145 := by
  have hu : mW 13156 ≤ 261176156728145 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13156 ≤ 261176156728144 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13156)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26312 ^ 2)
    ((6250000000000000000/1033269823765682996132783))
    ((25000000000000000000/4132922215430052494856053)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26312) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26312 : ℝ)^2 / (mW 13156 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1965411/1000000000000))/2) * ((1-firstRatio 26312) * √(1-firstRatio 26312) *
      sixthConstant (e1CovarianceRatio 26312 (mW 13156) (1/10^6) rowEps))) /
    (712/10000 - 26312*(1+1/10^6)*((1965411/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26312 (mW 13156) /
    ((1/10^5) * ((mW 13156 : ℝ)*26312*((mW 13156 : ℝ)+26312+1)))^2 +
  8*(mW 13156 : ℝ)*26312*(26312+2)*(26312+3) /
    ((1/1000)*((mW 13156 : ℝ)*26312*(26312+2)))^2 +
  covarianceVarianceBound 26312 (mW 13156) /
    ((1/1000)*covarianceMeanBound 26312 (mW 13156))^2 +
  normVarianceBound 26312 (mW 13156) / (3*inputVarianceMean 26312 (mW 13156))^2

end BstLean.Part268.WorldRow13156
namespace BstLean.Part268.WorldRow13157
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13157 = 261245646193441 := by
  have hu : mW 13157 ≤ 261245646193441 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13157 ≤ 261245646193440 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13157)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26314 ^ 2)
    ((25000000000000000000/4133393454328090963854979))
    ((25000000000000000000/4133236374695411474179899)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26314) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26314 : ℝ)^2 / (mW 13157 : ℝ)) * (1 + 1/10^6)^2 *
    √(((98263/50000000000))/2) * ((1-firstRatio 26314) * √(1-firstRatio 26314) *
      sixthConstant (e1CovarianceRatio 26314 (mW 13157) (1/10^6) rowEps))) /
    (712/10000 - 26314*(1+1/10^6)*((98263/50000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26314 (mW 13157) /
    ((1/10^5) * ((mW 13157 : ℝ)*26314*((mW 13157 : ℝ)+26314+1)))^2 +
  8*(mW 13157 : ℝ)*26314*(26314+2)*(26314+3) /
    ((1/1000)*((mW 13157 : ℝ)*26314*(26314+2)))^2 +
  covarianceVarianceBound 26314 (mW 13157) /
    ((1/1000)*covarianceMeanBound 26314 (mW 13157))^2 +
  normVarianceBound 26314 (mW 13157) / (3*inputVarianceMean 26314 (mW 13157))^2

end BstLean.Part268.WorldRow13157
namespace BstLean.Part268.WorldRow13158
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13158 = 261315148863887 := by
  have hu : mW 13158 ≤ 261315148863887 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13158 ≤ 261315148863886 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13158)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26316 ^ 2)
    ((12500000000000000000/2066853806796724971589413))
    ((5000000000000000000/826710106792154090700749)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26316) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26316 : ℝ)^2 / (mW 13158 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1965109/1000000000000))/2) * ((1-firstRatio 26316) * √(1-firstRatio 26316) *
      sixthConstant (e1CovarianceRatio 26316 (mW 13158) (1/10^6) rowEps))) /
    (712/10000 - 26316*(1+1/10^6)*((1965109/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26316 (mW 13158) /
    ((1/10^5) * ((mW 13158 : ℝ)*26316*((mW 13158 : ℝ)+26316+1)))^2 +
  8*(mW 13158 : ℝ)*26316*(26316+2)*(26316+3) /
    ((1/1000)*((mW 13158 : ℝ)*26316*(26316+2)))^2 +
  covarianceVarianceBound 26316 (mW 13158) /
    ((1/1000)*covarianceMeanBound 26316 (mW 13158))^2 +
  normVarianceBound 26316 (mW 13158) / (3*inputVarianceMean 26316 (mW 13158))^2

end BstLean.Part268.WorldRow13158
namespace BstLean.Part268.WorldRow13159
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13159 = 261384664740990 := by
  have hu : mW 13159 ≤ 261384664740990 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13159 ≤ 261384664740989 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13159)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26318 ^ 2)
    ((25000000000000000000/4134021772858808922502673))
    ((25000000000000000000/4133864693226129432827591)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26318) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26318 : ℝ)^2 / (mW 13159 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1964959/1000000000000))/2) * ((1-firstRatio 26318) * √(1-firstRatio 26318) *
      sixthConstant (e1CovarianceRatio 26318 (mW 13159) (1/10^6) rowEps))) /
    (712/10000 - 26318*(1+1/10^6)*((1964959/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26318 (mW 13159) /
    ((1/10^5) * ((mW 13159 : ℝ)*26318*((mW 13159 : ℝ)+26318+1)))^2 +
  8*(mW 13159 : ℝ)*26318*(26318+2)*(26318+3) /
    ((1/1000)*((mW 13159 : ℝ)*26318*(26318+2)))^2 +
  covarianceVarianceBound 26318 (mW 13159) /
    ((1/1000)*covarianceMeanBound 26318 (mW 13159))^2 +
  normVarianceBound 26318 (mW 13159) / (3*inputVarianceMean 26318 (mW 13159))^2

end BstLean.Part268.WorldRow13159
namespace BstLean.Part268.WorldRow13160
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13160 = 261454193826254 := by
  have hu : mW 13160 ≤ 261454193826254 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13160 ≤ 261454193826253 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13160)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26320 ^ 2)
    ((625000000000000000/103358398303104197545663))
    ((25000000000000000000/4134178852491488412151437)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26320) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26320 : ℝ)^2 / (mW 13160 : ℝ)) * (1 + 1/10^6)^2 *
    √(((245601/125000000000))/2) * ((1-firstRatio 26320) * √(1-firstRatio 26320) *
      sixthConstant (e1CovarianceRatio 26320 (mW 13160) (1/10^6) rowEps))) /
    (712/10000 - 26320*(1+1/10^6)*((245601/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26320 (mW 13160) /
    ((1/10^5) * ((mW 13160 : ℝ)*26320*((mW 13160 : ℝ)+26320+1)))^2 +
  8*(mW 13160 : ℝ)*26320*(26320+2)*(26320+3) /
    ((1/1000)*((mW 13160 : ℝ)*26320*(26320+2)))^2 +
  covarianceVarianceBound 26320 (mW 13160) /
    ((1/1000)*covarianceMeanBound 26320 (mW 13160))^2 +
  normVarianceBound 26320 (mW 13160) / (3*inputVarianceMean 26320 (mW 13160))^2

end BstLean.Part268.WorldRow13160
namespace BstLean.Part268.WorldRow13161
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13161 = 261523736121186 := by
  have hu : mW 13161 ≤ 261523736121186 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13161 ≤ 261523736121185 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13161)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26322 ^ 2)
    ((25000000000000000000/4134650091389526881150367))
    ((25000000000000000000/4134493011756847391475283)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26322) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26322 : ℝ)^2 / (mW 13161 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1964657/1000000000000))/2) * ((1-firstRatio 26322) * √(1-firstRatio 26322) *
      sixthConstant (e1CovarianceRatio 26322 (mW 13161) (1/10^6) rowEps))) /
    (712/10000 - 26322*(1+1/10^6)*((1964657/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26322 (mW 13161) /
    ((1/10^5) * ((mW 13161 : ℝ)*26322*((mW 13161 : ℝ)+26322+1)))^2 +
  8*(mW 13161 : ℝ)*26322*(26322+2)*(26322+3) /
    ((1/1000)*((mW 13161 : ℝ)*26322*(26322+2)))^2 +
  covarianceVarianceBound 26322 (mW 13161) /
    ((1/1000)*covarianceMeanBound 26322 (mW 13161))^2 +
  normVarianceBound 26322 (mW 13161) / (3*inputVarianceMean 26322 (mW 13161))^2

end BstLean.Part268.WorldRow13161
namespace BstLean.Part268.WorldRow13162
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13162 = 261593291627292 := by
  have hu : mW 13162 ≤ 261593291627292 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13162 ≤ 261593291627291 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13162)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26324 ^ 2)
    ((12500000000000000000/2067482125327442930237107))
    ((25000000000000000000/4134807171022206370799129)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26324) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26324 : ℝ)^2 / (mW 13162 : ℝ)) * (1 + 1/10^6)^2 *
    √(((982253/500000000000))/2) * ((1-firstRatio 26324) * √(1-firstRatio 26324) *
      sixthConstant (e1CovarianceRatio 26324 (mW 13162) (1/10^6) rowEps))) /
    (712/10000 - 26324*(1+1/10^6)*((982253/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26324 (mW 13162) /
    ((1/10^5) * ((mW 13162 : ℝ)*26324*((mW 13162 : ℝ)+26324+1)))^2 +
  8*(mW 13162 : ℝ)*26324*(26324+2)*(26324+3) /
    ((1/1000)*((mW 13162 : ℝ)*26324*(26324+2)))^2 +
  covarianceVarianceBound 26324 (mW 13162) /
    ((1/1000)*covarianceMeanBound 26324 (mW 13162))^2 +
  normVarianceBound 26324 (mW 13162) / (3*inputVarianceMean 26324 (mW 13162))^2

end BstLean.Part268.WorldRow13162
namespace BstLean.Part268.WorldRow13163
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13163 = 261662860346076 := by
  have hu : mW 13163 ≤ 261662860346076 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13163 ≤ 261662860346075 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13163)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26326 ^ 2)
    ((25000000000000000000/4135278409920244839798061))
    ((1000000000000000000/165404853211502614004919)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26326) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26326 : ℝ)^2 / (mW 13163 : ℝ)) * (1 + 1/10^6)^2 *
    √(((491089/250000000000))/2) * ((1-firstRatio 26326) * √(1-firstRatio 26326) *
      sixthConstant (e1CovarianceRatio 26326 (mW 13163) (1/10^6) rowEps))) /
    (712/10000 - 26326*(1+1/10^6)*((491089/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26326 (mW 13163) /
    ((1/10^5) * ((mW 13163 : ℝ)*26326*((mW 13163 : ℝ)+26326+1)))^2 +
  8*(mW 13163 : ℝ)*26326*(26326+2)*(26326+3) /
    ((1/1000)*((mW 13163 : ℝ)*26326*(26326+2)))^2 +
  covarianceVarianceBound 26326 (mW 13163) /
    ((1/1000)*covarianceMeanBound 26326 (mW 13163))^2 +
  normVarianceBound 26326 (mW 13163) / (3*inputVarianceMean 26326 (mW 13163))^2

end BstLean.Part268.WorldRow13163
namespace BstLean.Part268.WorldRow13164
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13164 = 261732442279045 := by
  have hu : mW 13164 ≤ 261732442279045 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13164 ≤ 261732442279044 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13164)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26328 ^ 2)
    ((6250000000000000000/1033898142296400954780477))
    ((25000000000000000000/4135435489552924329446821)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26328) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26328 : ℝ)^2 / (mW 13164 : ℝ)) * (1 + 1/10^6)^2 *
    √(((392841/200000000000))/2) * ((1-firstRatio 26328) * √(1-firstRatio 26328) *
      sixthConstant (e1CovarianceRatio 26328 (mW 13164) (1/10^6) rowEps))) /
    (712/10000 - 26328*(1+1/10^6)*((392841/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26328 (mW 13164) /
    ((1/10^5) * ((mW 13164 : ℝ)*26328*((mW 13164 : ℝ)+26328+1)))^2 +
  8*(mW 13164 : ℝ)*26328*(26328+2)*(26328+3) /
    ((1/1000)*((mW 13164 : ℝ)*26328*(26328+2)))^2 +
  covarianceVarianceBound 26328 (mW 13164) /
    ((1/1000)*covarianceMeanBound 26328 (mW 13164))^2 +
  normVarianceBound 26328 (mW 13164) / (3*inputVarianceMean 26328 (mW 13164))^2

end BstLean.Part268.WorldRow13164
namespace BstLean.Part268.WorldRow13165
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13165 = 261802037427705 := by
  have hu : mW 13165 ≤ 261802037427705 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13165 ≤ 261802037427704 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13165)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26330 ^ 2)
    ((5000000000000000000/827181345690192559689151))
    ((25000000000000000000/4135749648818283308770667)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26330) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26330 : ℝ)^2 / (mW 13165 : ℝ)) * (1 + 1/10^6)^2 *
    √(((982027/500000000000))/2) * ((1-firstRatio 26330) * √(1-firstRatio 26330) *
      sixthConstant (e1CovarianceRatio 26330 (mW 13165) (1/10^6) rowEps))) /
    (712/10000 - 26330*(1+1/10^6)*((982027/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26330 (mW 13165) /
    ((1/10^5) * ((mW 13165 : ℝ)*26330*((mW 13165 : ℝ)+26330+1)))^2 +
  8*(mW 13165 : ℝ)*26330*(26330+2)*(26330+3) /
    ((1/1000)*((mW 13165 : ℝ)*26330*(26330+2)))^2 +
  covarianceVarianceBound 26330 (mW 13165) /
    ((1/1000)*covarianceMeanBound 26330 (mW 13165))^2 +
  normVarianceBound 26330 (mW 13165) / (3*inputVarianceMean 26330 (mW 13165))^2

end BstLean.Part268.WorldRow13165
namespace BstLean.Part268.WorldRow13166
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13166 = 261871645793561 := by
  have hu : mW 13166 ≤ 261871645793561 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13166 ≤ 261871645793560 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13166)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26332 ^ 2)
    ((12500000000000000000/2068110443858160888884801))
    ((25000000000000000000/4136063808083642288094513)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26332) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26332 : ℝ)^2 / (mW 13166 : ℝ)) * (1 + 1/10^6)^2 *
    √(((15343/7812500000))/2) * ((1-firstRatio 26332) * √(1-firstRatio 26332) *
      sixthConstant (e1CovarianceRatio 26332 (mW 13166) (1/10^6) rowEps))) /
    (712/10000 - 26332*(1+1/10^6)*((15343/7812500000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26332 (mW 13166) /
    ((1/10^5) * ((mW 13166 : ℝ)*26332*((mW 13166 : ℝ)+26332+1)))^2 +
  8*(mW 13166 : ℝ)*26332*(26332+2)*(26332+3) /
    ((1/1000)*((mW 13166 : ℝ)*26332*(26332+2)))^2 +
  covarianceVarianceBound 26332 (mW 13166) /
    ((1/1000)*covarianceMeanBound 26332 (mW 13166))^2 +
  normVarianceBound 26332 (mW 13166) / (3*inputVarianceMean 26332 (mW 13166))^2

end BstLean.Part268.WorldRow13166
namespace BstLean.Part268.WorldRow13167
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13167 = 261941267378120 := by
  have hu : mW 13167 ≤ 261941267378120 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13167 ≤ 261941267378119 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13167)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26334 ^ 2)
    ((25000000000000000000/4136535046981680757093449))
    ((25000000000000000000/4136377967349001267418359)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26334) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26334 : ℝ)^2 / (mW 13167 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1963753/1000000000000))/2) * ((1-firstRatio 26334) * √(1-firstRatio 26334) *
      sixthConstant (e1CovarianceRatio 26334 (mW 13167) (1/10^6) rowEps))) /
    (712/10000 - 26334*(1+1/10^6)*((1963753/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26334 (mW 13167) /
    ((1/10^5) * ((mW 13167 : ℝ)*26334*((mW 13167 : ℝ)+26334+1)))^2 +
  8*(mW 13167 : ℝ)*26334*(26334+2)*(26334+3) /
    ((1/1000)*((mW 13167 : ℝ)*26334*(26334+2)))^2 +
  covarianceVarianceBound 26334 (mW 13167) /
    ((1/1000)*covarianceMeanBound 26334 (mW 13167))^2 +
  normVarianceBound 26334 (mW 13167) / (3*inputVarianceMean 26334 (mW 13167))^2

end BstLean.Part268.WorldRow13167
namespace BstLean.Part268.WorldRow13168
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13168 = 262010902182887 := by
  have hu : mW 13168 ≤ 262010902182887 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13168 ≤ 262010902182886 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13168)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26336 ^ 2)
    ((1562500000000000000/258553075390439983526081))
    ((5000000000000000000/827338425322872049348441)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26336) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26336 : ℝ)^2 / (mW 13168 : ℝ)) * (1 + 1/10^6)^2 *
    √(((981801/500000000000))/2) * ((1-firstRatio 26336) * √(1-firstRatio 26336) *
      sixthConstant (e1CovarianceRatio 26336 (mW 13168) (1/10^6) rowEps))) /
    (712/10000 - 26336*(1+1/10^6)*((981801/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26336 (mW 13168) /
    ((1/10^5) * ((mW 13168 : ℝ)*26336*((mW 13168 : ℝ)+26336+1)))^2 +
  8*(mW 13168 : ℝ)*26336*(26336+2)*(26336+3) /
    ((1/1000)*((mW 13168 : ℝ)*26336*(26336+2)))^2 +
  covarianceVarianceBound 26336 (mW 13168) /
    ((1/1000)*covarianceMeanBound 26336 (mW 13168))^2 +
  normVarianceBound 26336 (mW 13168) / (3*inputVarianceMean 26336 (mW 13168))^2

end BstLean.Part268.WorldRow13168
namespace BstLean.Part268.WorldRow13169
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13169 = 262080550209369 := by
  have hu : mW 13169 ≤ 262080550209369 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13169 ≤ 262080550209368 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13169)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26338 ^ 2)
    ((25000000000000000000/4137163365512398715741143))
    ((25000000000000000000/4137006285879719226066051)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26338) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26338 : ℝ)^2 / (mW 13169 : ℝ)) * (1 + 1/10^6)^2 *
    √(((490863/250000000000))/2) * ((1-firstRatio 26338) * √(1-firstRatio 26338) *
      sixthConstant (e1CovarianceRatio 26338 (mW 13169) (1/10^6) rowEps))) /
    (712/10000 - 26338*(1+1/10^6)*((490863/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26338 (mW 13169) /
    ((1/10^5) * ((mW 13169 : ℝ)*26338*((mW 13169 : ℝ)+26338+1)))^2 +
  8*(mW 13169 : ℝ)*26338*(26338+2)*(26338+3) /
    ((1/1000)*((mW 13169 : ℝ)*26338*(26338+2)))^2 +
  covarianceVarianceBound 26338 (mW 13169) /
    ((1/1000)*covarianceMeanBound 26338 (mW 13169))^2 +
  normVarianceBound 26338 (mW 13169) / (3*inputVarianceMean 26338 (mW 13169))^2

end BstLean.Part268.WorldRow13169
namespace BstLean.Part268.WorldRow13170
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13170 = 262150211459072 := by
  have hu : mW 13170 ≤ 262150211459072 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13170 ≤ 262150211459071 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13170)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26340 ^ 2)
    ((2500000000000000000/413747752477775769506499))
    ((25000000000000000000/4137320445145078205389897)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26340) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26340 : ℝ)^2 / (mW 13170 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1963301/1000000000000))/2) * ((1-firstRatio 26340) * √(1-firstRatio 26340) *
      sixthConstant (e1CovarianceRatio 26340 (mW 13170) (1/10^6) rowEps))) /
    (712/10000 - 26340*(1+1/10^6)*((1963301/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26340 (mW 13170) /
    ((1/10^5) * ((mW 13170 : ℝ)*26340*((mW 13170 : ℝ)+26340+1)))^2 +
  8*(mW 13170 : ℝ)*26340*(26340+2)*(26340+3) /
    ((1/1000)*((mW 13170 : ℝ)*26340*(26340+2)))^2 +
  covarianceVarianceBound 26340 (mW 13170) /
    ((1/1000)*covarianceMeanBound 26340 (mW 13170))^2 +
  normVarianceBound 26340 (mW 13170) / (3*inputVarianceMean 26340 (mW 13170))^2

end BstLean.Part268.WorldRow13170
namespace BstLean.Part268.WorldRow13171
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13171 = 262219885933502 := by
  have hu : mW 13171 ≤ 262219885933502 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13171 ≤ 262219885933501 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13171)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26342 ^ 2)
    ((25000000000000000000/4137791684043116674388837))
    ((25000000000000000000/4137634604410437184713743)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26342) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26342 : ℝ)^2 / (mW 13171 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1963151/1000000000000))/2) * ((1-firstRatio 26342) * √(1-firstRatio 26342) *
      sixthConstant (e1CovarianceRatio 26342 (mW 13171) (1/10^6) rowEps))) /
    (712/10000 - 26342*(1+1/10^6)*((1963151/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26342 (mW 13171) /
    ((1/10^5) * ((mW 13171 : ℝ)*26342*((mW 13171 : ℝ)+26342+1)))^2 +
  8*(mW 13171 : ℝ)*26342*(26342+2)*(26342+3) /
    ((1/1000)*((mW 13171 : ℝ)*26342*(26342+2)))^2 +
  covarianceVarianceBound 26342 (mW 13171) /
    ((1/1000)*covarianceMeanBound 26342 (mW 13171))^2 +
  normVarianceBound 26342 (mW 13171) / (3*inputVarianceMean 26342 (mW 13171))^2

end BstLean.Part268.WorldRow13171
namespace BstLean.Part268.WorldRow13172
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13172 = 262289573634165 := by
  have hu : mW 13172 ≤ 262289573634165 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13172 ≤ 262289573634164 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13172)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26344 ^ 2)
    ((6250000000000000000/1034526460827118913428171))
    ((25000000000000000000/4137948763675796164037589)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26344) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26344 : ℝ)^2 / (mW 13172 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1963/1000000000))/2) * ((1-firstRatio 26344) * √(1-firstRatio 26344) *
      sixthConstant (e1CovarianceRatio 26344 (mW 13172) (1/10^6) rowEps))) /
    (712/10000 - 26344*(1+1/10^6)*((1963/1000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26344 (mW 13172) /
    ((1/10^5) * ((mW 13172 : ℝ)*26344*((mW 13172 : ℝ)+26344+1)))^2 +
  8*(mW 13172 : ℝ)*26344*(26344+2)*(26344+3) /
    ((1/1000)*((mW 13172 : ℝ)*26344*(26344+2)))^2 +
  covarianceVarianceBound 26344 (mW 13172) /
    ((1/1000)*covarianceMeanBound 26344 (mW 13172))^2 +
  normVarianceBound 26344 (mW 13172) / (3*inputVarianceMean 26344 (mW 13172))^2

end BstLean.Part268.WorldRow13172
namespace BstLean.Part268.WorldRow13173
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13173 = 262359274562567 := by
  have hu : mW 13173 ≤ 262359274562567 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13173 ≤ 262359274562566 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13173)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26346 ^ 2)
    ((25000000000000000000/4138420002573834633036531))
    ((5000000000000000000/827652584588231028672287)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26346) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26346 : ℝ)^2 / (mW 13173 : ℝ)) * (1 + 1/10^6)^2 *
    √(((39257/20000000000))/2) * ((1-firstRatio 26346) * √(1-firstRatio 26346) *
      sixthConstant (e1CovarianceRatio 26346 (mW 13173) (1/10^6) rowEps))) /
    (712/10000 - 26346*(1+1/10^6)*((39257/20000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26346 (mW 13173) /
    ((1/10^5) * ((mW 13173 : ℝ)*26346*((mW 13173 : ℝ)+26346+1)))^2 +
  8*(mW 13173 : ℝ)*26346*(26346+2)*(26346+3) /
    ((1/1000)*((mW 13173 : ℝ)*26346*(26346+2)))^2 +
  covarianceVarianceBound 26346 (mW 13173) /
    ((1/1000)*covarianceMeanBound 26346 (mW 13173))^2 +
  normVarianceBound 26346 (mW 13173) / (3*inputVarianceMean 26346 (mW 13173))^2

end BstLean.Part268.WorldRow13173
namespace BstLean.Part268.WorldRow13174
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13174 = 262428988720216 := by
  have hu : mW 13174 ≤ 262428988720216 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13174 ≤ 262428988720215 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13174)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26348 ^ 2)
    ((12500000000000000000/2069367080919596806180189))
    ((25000000000000000000/4138577082206514122685281)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26348) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26348 : ℝ)^2 / (mW 13174 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1962699/1000000000000))/2) * ((1-firstRatio 26348) * √(1-firstRatio 26348) *
      sixthConstant (e1CovarianceRatio 26348 (mW 13174) (1/10^6) rowEps))) /
    (712/10000 - 26348*(1+1/10^6)*((1962699/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26348 (mW 13174) /
    ((1/10^5) * ((mW 13174 : ℝ)*26348*((mW 13174 : ℝ)+26348+1)))^2 +
  8*(mW 13174 : ℝ)*26348*(26348+2)*(26348+3) /
    ((1/1000)*((mW 13174 : ℝ)*26348*(26348+2)))^2 +
  covarianceVarianceBound 26348 (mW 13174) /
    ((1/1000)*covarianceMeanBound 26348 (mW 13174))^2 +
  normVarianceBound 26348 (mW 13174) / (3*inputVarianceMean 26348 (mW 13174))^2

end BstLean.Part268.WorldRow13174
