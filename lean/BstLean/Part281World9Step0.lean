import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part281Scalar9
namespace BstLean.Part281.WorldRow12084
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12084 = 193971314134563 := by
  have hu : mW 12084 ≤ 193971314134563 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12084 ≤ 193971314134562 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12084)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24168 ^ 2)
    ((6250000000000000000/949075140649476537341787))
    ((25000000000000000000/3796143482965226659693141)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24168) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24168 : ℝ)^2 / (mW 12084 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2141691/1000000000000))/2) * ((1-firstRatio 24168) * √(1-firstRatio 24168) *
      sixthConstant (e1CovarianceRatio 24168 (mW 12084) (1/10^6) rowEps))) /
    (712/10000 - 24168*(1+1/10^6)*((2141691/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24168 (mW 12084) /
    ((1/10^5) * ((mW 12084 : ℝ)*24168*((mW 12084 : ℝ)+24168+1)))^2 +
  8*(mW 12084 : ℝ)*24168*(24168+2)*(24168+3) /
    ((1/1000)*((mW 12084 : ℝ)*24168*(24168+2)))^2 +
  covarianceVarianceBound 24168 (mW 12084) /
    ((1/1000)*covarianceMeanBound 24168 (mW 12084))^2 +
  normVarianceBound 24168 (mW 12084) / (3*inputVarianceMean 24168 (mW 12084))^2

end BstLean.Part281.WorldRow12084
namespace BstLean.Part281.WorldRow12085
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12085 = 194027501641142 := by
  have hu : mW 12085 ≤ 194027501641142 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12085 ≤ 194027501641141 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12085)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24170 ^ 2)
    ((5000000000000000000/759322944372653025738199))
    ((25000000000000000000/3796457642230585639016987)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24170) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24170 : ℝ)^2 / (mW 12085 : ℝ)) * (1 + 1/10^6)^2 *
    √(((267689/125000000000))/2) * ((1-firstRatio 24170) * √(1-firstRatio 24170) *
      sixthConstant (e1CovarianceRatio 24170 (mW 12085) (1/10^6) rowEps))) /
    (712/10000 - 24170*(1+1/10^6)*((267689/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24170 (mW 12085) /
    ((1/10^5) * ((mW 12085 : ℝ)*24170*((mW 12085 : ℝ)+24170+1)))^2 +
  8*(mW 12085 : ℝ)*24170*(24170+2)*(24170+3) /
    ((1/1000)*((mW 12085 : ℝ)*24170*(24170+2)))^2 +
  covarianceVarianceBound 24170 (mW 12085) /
    ((1/1000)*covarianceMeanBound 24170 (mW 12085))^2 +
  normVarianceBound 24170 (mW 12085) / (3*inputVarianceMean 24170 (mW 12085))^2

end BstLean.Part281.WorldRow12085
namespace BstLean.Part281.WorldRow12086
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12086 = 194083700772321 := by
  have hu : mW 12086 ≤ 194083700772321 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12086 ≤ 194083700772320 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12086)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24172 ^ 2)
    ((12500000000000000000/1898464440564312054007421))
    ((25000000000000000000/3796771801495944618340833)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24172) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24172 : ℝ)^2 / (mW 12086 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2141333/1000000000000))/2) * ((1-firstRatio 24172) * √(1-firstRatio 24172) *
      sixthConstant (e1CovarianceRatio 24172 (mW 12086) (1/10^6) rowEps))) /
    (712/10000 - 24172*(1+1/10^6)*((2141333/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24172 (mW 12086) /
    ((1/10^5) * ((mW 12086 : ℝ)*24172*((mW 12086 : ℝ)+24172+1)))^2 +
  8*(mW 12086 : ℝ)*24172*(24172+2)*(24172+3) /
    ((1/1000)*((mW 12086 : ℝ)*24172*(24172+2)))^2 +
  covarianceVarianceBound 24172 (mW 12086) /
    ((1/1000)*covarianceMeanBound 24172 (mW 12086))^2 +
  normVarianceBound 24172 (mW 12086) / (3*inputVarianceMean 24172 (mW 12086))^2

end BstLean.Part281.WorldRow12086
namespace BstLean.Part281.WorldRow12087
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12087 = 194139911529543 := by
  have hu : mW 12087 ≤ 194139911529543 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12087 ≤ 194139911529542 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12087)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24174 ^ 2)
    ((25000000000000000000/3797243040393983087338689))
    ((25000000000000000000/3797085960761303597664679)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24174) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24174 : ℝ)^2 / (mW 12087 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2141153/1000000000000))/2) * ((1-firstRatio 24174) * √(1-firstRatio 24174) *
      sixthConstant (e1CovarianceRatio 24174 (mW 12087) (1/10^6) rowEps))) /
    (712/10000 - 24174*(1+1/10^6)*((2141153/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24174 (mW 12087) /
    ((1/10^5) * ((mW 12087 : ℝ)*24174*((mW 12087 : ℝ)+24174+1)))^2 +
  8*(mW 12087 : ℝ)*24174*(24174+2)*(24174+3) /
    ((1/1000)*((mW 12087 : ℝ)*24174*(24174+2)))^2 +
  covarianceVarianceBound 24174 (mW 12087) /
    ((1/1000)*covarianceMeanBound 24174 (mW 12087))^2 +
  normVarianceBound 24174 (mW 12087) / (3*inputVarianceMean 24174 (mW 12087))^2

end BstLean.Part281.WorldRow12087
namespace BstLean.Part281.WorldRow12088
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12088 = 194196133914252 := by
  have hu : mW 12088 ≤ 194196133914252 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12088 ≤ 194196133914251 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12088)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24176 ^ 2)
    ((3125000000000000000/474694649957417758332817))
    ((1000000000000000000/151896004801066503079541)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24176) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24176 : ℝ)^2 / (mW 12088 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1070487/500000000000))/2) * ((1-firstRatio 24176) * √(1-firstRatio 24176) *
      sixthConstant (e1CovarianceRatio 24176 (mW 12088) (1/10^6) rowEps))) /
    (712/10000 - 24176*(1+1/10^6)*((1070487/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24176 (mW 12088) /
    ((1/10^5) * ((mW 12088 : ℝ)*24176*((mW 12088 : ℝ)+24176+1)))^2 +
  8*(mW 12088 : ℝ)*24176*(24176+2)*(24176+3) /
    ((1/1000)*((mW 12088 : ℝ)*24176*(24176+2)))^2 +
  covarianceVarianceBound 24176 (mW 12088) /
    ((1/1000)*covarianceMeanBound 24176 (mW 12088))^2 +
  normVarianceBound 24176 (mW 12088) / (3*inputVarianceMean 24176 (mW 12088))^2

end BstLean.Part281.WorldRow12088
namespace BstLean.Part281.WorldRow12089
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12089 = 194252367927890 := by
  have hu : mW 12089 ≤ 194252367927890 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12089 ≤ 194252367927889 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12089)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24178 ^ 2)
    ((25000000000000000000/3797871358924701045986383))
    ((25000000000000000000/3797714279292021556312371)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24178) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24178 : ℝ)^2 / (mW 12089 : ℝ)) * (1 + 1/10^6)^2 *
    √(((428159/200000000000))/2) * ((1-firstRatio 24178) * √(1-firstRatio 24178) *
      sixthConstant (e1CovarianceRatio 24178 (mW 12089) (1/10^6) rowEps))) /
    (712/10000 - 24178*(1+1/10^6)*((428159/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24178 (mW 12089) /
    ((1/10^5) * ((mW 12089 : ℝ)*24178*((mW 12089 : ℝ)+24178+1)))^2 +
  8*(mW 12089 : ℝ)*24178*(24178+2)*(24178+3) /
    ((1/1000)*((mW 12089 : ℝ)*24178*(24178+2)))^2 +
  covarianceVarianceBound 24178 (mW 12089) /
    ((1/1000)*covarianceMeanBound 24178 (mW 12089))^2 +
  normVarianceBound 24178 (mW 12089) / (3*inputVarianceMean 24178 (mW 12089))^2

end BstLean.Part281.WorldRow12089
namespace BstLean.Part281.WorldRow12090
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12090 = 194308613571900 := by
  have hu : mW 12090 ≤ 194308613571900 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12090 ≤ 194308613571899 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12090)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24180 ^ 2)
    ((2500000000000000000/379818551819006002531023))
    ((25000000000000000000/3798028438557380535636217)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24180) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24180 : ℝ)^2 / (mW 12090 : ℝ)) * (1 + 1/10^6)^2 *
    √(((267577/125000000000))/2) * ((1-firstRatio 24180) * √(1-firstRatio 24180) *
      sixthConstant (e1CovarianceRatio 24180 (mW 12090) (1/10^6) rowEps))) /
    (712/10000 - 24180*(1+1/10^6)*((267577/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24180 (mW 12090) /
    ((1/10^5) * ((mW 12090 : ℝ)*24180*((mW 12090 : ℝ)+24180+1)))^2 +
  8*(mW 12090 : ℝ)*24180*(24180+2)*(24180+3) /
    ((1/1000)*((mW 12090 : ℝ)*24180*(24180+2)))^2 +
  covarianceVarianceBound 24180 (mW 12090) /
    ((1/1000)*covarianceMeanBound 24180 (mW 12090))^2 +
  normVarianceBound 24180 (mW 12090) / (3*inputVarianceMean 24180 (mW 12090))^2

end BstLean.Part281.WorldRow12090
namespace BstLean.Part281.WorldRow12091
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12091 = 194364870847726 := by
  have hu : mW 12091 ≤ 194364870847726 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12091 ≤ 194364870847725 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12091)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24182 ^ 2)
    ((25000000000000000000/3798499677455419004634077))
    ((25000000000000000000/3798342597822739514960063)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24182) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24182 : ℝ)^2 / (mW 12091 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2140437/1000000000000))/2) * ((1-firstRatio 24182) * √(1-firstRatio 24182) *
      sixthConstant (e1CovarianceRatio 24182 (mW 12091) (1/10^6) rowEps))) /
    (712/10000 - 24182*(1+1/10^6)*((2140437/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24182 (mW 12091) /
    ((1/10^5) * ((mW 12091 : ℝ)*24182*((mW 12091 : ℝ)+24182+1)))^2 +
  8*(mW 12091 : ℝ)*24182*(24182+2)*(24182+3) /
    ((1/1000)*((mW 12091 : ℝ)*24182*(24182+2)))^2 +
  covarianceVarianceBound 24182 (mW 12091) /
    ((1/1000)*covarianceMeanBound 24182 (mW 12091))^2 +
  normVarianceBound 24182 (mW 12091) / (3*inputVarianceMean 24182 (mW 12091))^2

end BstLean.Part281.WorldRow12091
namespace BstLean.Part281.WorldRow12092
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12092 = 194421139756811 := by
  have hu : mW 12092 ≤ 194421139756811 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12092 ≤ 194421139756810 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12092)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24184 ^ 2)
    ((6250000000000000000/949703459180194495989481))
    ((25000000000000000000/3798656757088098494283909)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24184) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24184 : ℝ)^2 / (mW 12092 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1070129/500000000000))/2) * ((1-firstRatio 24184) * √(1-firstRatio 24184) *
      sixthConstant (e1CovarianceRatio 24184 (mW 12092) (1/10^6) rowEps))) /
    (712/10000 - 24184*(1+1/10^6)*((1070129/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24184 (mW 12092) /
    ((1/10^5) * ((mW 12092 : ℝ)*24184*((mW 12092 : ℝ)+24184+1)))^2 +
  8*(mW 12092 : ℝ)*24184*(24184+2)*(24184+3) /
    ((1/1000)*((mW 12092 : ℝ)*24184*(24184+2)))^2 +
  covarianceVarianceBound 24184 (mW 12092) /
    ((1/1000)*covarianceMeanBound 24184 (mW 12092))^2 +
  normVarianceBound 24184 (mW 12092) / (3*inputVarianceMean 24184 (mW 12092))^2

end BstLean.Part281.WorldRow12092
namespace BstLean.Part281.WorldRow12093
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12093 = 194477420300597 := by
  have hu : mW 12093 ≤ 194477420300597 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12093 ≤ 194477420300596 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12093)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24186 ^ 2)
    ((25000000000000000000/3799127995986136963281771))
    ((5000000000000000000/759794183270691494721551)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24186) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24186 : ℝ)^2 / (mW 12093 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2140079/1000000000000))/2) * ((1-firstRatio 24186) * √(1-firstRatio 24186) *
      sixthConstant (e1CovarianceRatio 24186 (mW 12093) (1/10^6) rowEps))) /
    (712/10000 - 24186*(1+1/10^6)*((2140079/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24186 (mW 12093) /
    ((1/10^5) * ((mW 12093 : ℝ)*24186*((mW 12093 : ℝ)+24186+1)))^2 +
  8*(mW 12093 : ℝ)*24186*(24186+2)*(24186+3) /
    ((1/1000)*((mW 12093 : ℝ)*24186*(24186+2)))^2 +
  covarianceVarianceBound 24186 (mW 12093) /
    ((1/1000)*covarianceMeanBound 24186 (mW 12093))^2 +
  normVarianceBound 24186 (mW 12093) / (3*inputVarianceMean 24186 (mW 12093))^2

end BstLean.Part281.WorldRow12093
namespace BstLean.Part281.WorldRow12094
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12094 = 194533712480529 := by
  have hu : mW 12094 ≤ 194533712480529 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12094 ≤ 194533712480528 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12094)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24188 ^ 2)
    ((12500000000000000000/1899721077625747971302809))
    ((25000000000000000000/3799285075618816452931601)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24188) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24188 : ℝ)^2 / (mW 12094 : ℝ)) * (1 + 1/10^6)^2 *
    √(((21399/10000000000))/2) * ((1-firstRatio 24188) * √(1-firstRatio 24188) *
      sixthConstant (e1CovarianceRatio 24188 (mW 12094) (1/10^6) rowEps))) /
    (712/10000 - 24188*(1+1/10^6)*((21399/10000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24188 (mW 12094) /
    ((1/10^5) * ((mW 12094 : ℝ)*24188*((mW 12094 : ℝ)+24188+1)))^2 +
  8*(mW 12094 : ℝ)*24188*(24188+2)*(24188+3) /
    ((1/1000)*((mW 12094 : ℝ)*24188*(24188+2)))^2 +
  covarianceVarianceBound 24188 (mW 12094) /
    ((1/1000)*covarianceMeanBound 24188 (mW 12094))^2 +
  normVarianceBound 24188 (mW 12094) / (3*inputVarianceMean 24188 (mW 12094))^2

end BstLean.Part281.WorldRow12094
namespace BstLean.Part281.WorldRow12095
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12095 = 194590016298049 := by
  have hu : mW 12095 ≤ 194590016298049 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12095 ≤ 194590016298048 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12095)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24190 ^ 2)
    ((5000000000000000000/759951262903370984385893))
    ((25000000000000000000/3799599234884175432255447)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24190) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24190 : ℝ)^2 / (mW 12095 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2139721/1000000000000))/2) * ((1-firstRatio 24190) * √(1-firstRatio 24190) *
      sixthConstant (e1CovarianceRatio 24190 (mW 12095) (1/10^6) rowEps))) /
    (712/10000 - 24190*(1+1/10^6)*((2139721/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24190 (mW 12095) /
    ((1/10^5) * ((mW 12095 : ℝ)*24190*((mW 12095 : ℝ)+24190+1)))^2 +
  8*(mW 12095 : ℝ)*24190*(24190+2)*(24190+3) /
    ((1/1000)*((mW 12095 : ℝ)*24190*(24190+2)))^2 +
  covarianceVarianceBound 24190 (mW 12095) /
    ((1/1000)*covarianceMeanBound 24190 (mW 12095))^2 +
  normVarianceBound 24190 (mW 12095) / (3*inputVarianceMean 24190 (mW 12095))^2

end BstLean.Part281.WorldRow12095
namespace BstLean.Part281.WorldRow12096
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12096 = 194646331754601 := by
  have hu : mW 12096 ≤ 194646331754601 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12096 ≤ 194646331754600 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12096)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24192 ^ 2)
    ((390625000000000000/59376101152847092207083))
    ((25000000000000000000/3799913394149534411579293)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24192) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24192 : ℝ)^2 / (mW 12096 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1069771/500000000000))/2) * ((1-firstRatio 24192) * √(1-firstRatio 24192) *
      sixthConstant (e1CovarianceRatio 24192 (mW 12096) (1/10^6) rowEps))) /
    (712/10000 - 24192*(1+1/10^6)*((1069771/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24192 (mW 12096) /
    ((1/10^5) * ((mW 12096 : ℝ)*24192*((mW 12096 : ℝ)+24192+1)))^2 +
  8*(mW 12096 : ℝ)*24192*(24192+2)*(24192+3) /
    ((1/1000)*((mW 12096 : ℝ)*24192*(24192+2)))^2 +
  covarianceVarianceBound 24192 (mW 12096) /
    ((1/1000)*covarianceMeanBound 24192 (mW 12096))^2 +
  normVarianceBound 24192 (mW 12096) / (3*inputVarianceMean 24192 (mW 12096))^2

end BstLean.Part281.WorldRow12096
namespace BstLean.Part281.WorldRow12097
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12097 = 194702658851629 := by
  have hu : mW 12097 ≤ 194702658851629 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12097 ≤ 194702658851628 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12097)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24194 ^ 2)
    ((25000000000000000000/3800384633047572880577159))
    ((25000000000000000000/3800227553414893390903139)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24194) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24194 : ℝ)^2 / (mW 12097 : ℝ)) * (1 + 1/10^6)^2 *
    √(((534841/250000000000))/2) * ((1-firstRatio 24194) * √(1-firstRatio 24194) *
      sixthConstant (e1CovarianceRatio 24194 (mW 12097) (1/10^6) rowEps))) /
    (712/10000 - 24194*(1+1/10^6)*((534841/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24194 (mW 12097) /
    ((1/10^5) * ((mW 12097 : ℝ)*24194*((mW 12097 : ℝ)+24194+1)))^2 +
  8*(mW 12097 : ℝ)*24194*(24194+2)*(24194+3) /
    ((1/1000)*((mW 12097 : ℝ)*24194*(24194+2)))^2 +
  covarianceVarianceBound 24194 (mW 12097) /
    ((1/1000)*covarianceMeanBound 24194 (mW 12097))^2 +
  normVarianceBound 24194 (mW 12097) / (3*inputVarianceMean 24194 (mW 12097))^2

end BstLean.Part281.WorldRow12097
namespace BstLean.Part281.WorldRow12098
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12098 = 194758997590576 := by
  have hu : mW 12098 ≤ 194758997590576 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12098 ≤ 194758997590575 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12098)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24196 ^ 2)
    ((12500000000000000000/1900349396156465929950503))
    ((5000000000000000000/760108342536050474045397)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24196) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24196 : ℝ)^2 / (mW 12098 : ℝ)) * (1 + 1/10^6)^2 *
    √(((427837/200000000000))/2) * ((1-firstRatio 24196) * √(1-firstRatio 24196) *
      sixthConstant (e1CovarianceRatio 24196 (mW 12098) (1/10^6) rowEps))) /
    (712/10000 - 24196*(1+1/10^6)*((427837/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24196 (mW 12098) /
    ((1/10^5) * ((mW 12098 : ℝ)*24196*((mW 12098 : ℝ)+24196+1)))^2 +
  8*(mW 12098 : ℝ)*24196*(24196+2)*(24196+3) /
    ((1/1000)*((mW 12098 : ℝ)*24196*(24196+2)))^2 +
  covarianceVarianceBound 24196 (mW 12098) /
    ((1/1000)*covarianceMeanBound 24196 (mW 12098))^2 +
  normVarianceBound 24196 (mW 12098) / (3*inputVarianceMean 24196 (mW 12098))^2

end BstLean.Part281.WorldRow12098
namespace BstLean.Part281.WorldRow12099
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12099 = 194815347972885 := by
  have hu : mW 12099 ≤ 194815347972885 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12099 ≤ 194815347972884 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12099)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24198 ^ 2)
    ((25000000000000000000/3801012951578290839224853))
    ((25000000000000000000/3800855871945611349550831)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24198) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24198 : ℝ)^2 / (mW 12099 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1069503/500000000000))/2) * ((1-firstRatio 24198) * √(1-firstRatio 24198) *
      sixthConstant (e1CovarianceRatio 24198 (mW 12099) (1/10^6) rowEps))) /
    (712/10000 - 24198*(1+1/10^6)*((1069503/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24198 (mW 12099) /
    ((1/10^5) * ((mW 12099 : ℝ)*24198*((mW 12099 : ℝ)+24198+1)))^2 +
  8*(mW 12099 : ℝ)*24198*(24198+2)*(24198+3) /
    ((1/1000)*((mW 12099 : ℝ)*24198*(24198+2)))^2 +
  covarianceVarianceBound 24198 (mW 12099) /
    ((1/1000)*covarianceMeanBound 24198 (mW 12099))^2 +
  normVarianceBound 24198 (mW 12099) / (3*inputVarianceMean 24198 (mW 12099))^2

end BstLean.Part281.WorldRow12099
namespace BstLean.Part281.WorldRow12100
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12100 = 194871710000000 := by
  have hu : mW 12100 ≤ 194871710000000 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12100 ≤ 194871709999999 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12100)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24200 ^ 2)
    ((250000000000000000/38013271108436498185487))
    ((25000000000000000000/3801170031210970328874677)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24200) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24200 : ℝ)^2 / (mW 12100 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2138827/1000000000000))/2) * ((1-firstRatio 24200) * √(1-firstRatio 24200) *
      sixthConstant (e1CovarianceRatio 24200 (mW 12100) (1/10^6) rowEps))) /
    (712/10000 - 24200*(1+1/10^6)*((2138827/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24200 (mW 12100) /
    ((1/10^5) * ((mW 12100 : ℝ)*24200*((mW 12100 : ℝ)+24200+1)))^2 +
  8*(mW 12100 : ℝ)*24200*(24200+2)*(24200+3) /
    ((1/1000)*((mW 12100 : ℝ)*24200*(24200+2)))^2 +
  covarianceVarianceBound 24200 (mW 12100) /
    ((1/1000)*covarianceMeanBound 24200 (mW 12100))^2 +
  normVarianceBound 24200 (mW 12100) / (3*inputVarianceMean 24200 (mW 12100))^2

end BstLean.Part281.WorldRow12100
namespace BstLean.Part281.WorldRow12101
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12101 = 194928083673366 := by
  have hu : mW 12101 ≤ 194928083673366 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12101 ≤ 194928083673365 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12101)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24202 ^ 2)
    ((25000000000000000000/3801641270109008797872547))
    ((25000000000000000000/3801484190476329308198523)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24202) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24202 : ℝ)^2 / (mW 12101 : ℝ)) * (1 + 1/10^6)^2 *
    √(((267331/125000000000))/2) * ((1-firstRatio 24202) * √(1-firstRatio 24202) *
      sixthConstant (e1CovarianceRatio 24202 (mW 12101) (1/10^6) rowEps))) /
    (712/10000 - 24202*(1+1/10^6)*((267331/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24202 (mW 12101) /
    ((1/10^5) * ((mW 12101 : ℝ)*24202*((mW 12101 : ℝ)+24202+1)))^2 +
  8*(mW 12101 : ℝ)*24202*(24202+2)*(24202+3) /
    ((1/1000)*((mW 12101 : ℝ)*24202*(24202+2)))^2 +
  covarianceVarianceBound 24202 (mW 12101) /
    ((1/1000)*covarianceMeanBound 24202 (mW 12101))^2 +
  normVarianceBound 24202 (mW 12101) / (3*inputVarianceMean 24202 (mW 12101))^2

end BstLean.Part281.WorldRow12101
namespace BstLean.Part281.WorldRow12102
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12102 = 194984468994426 := by
  have hu : mW 12102 ≤ 194984468994426 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12102 ≤ 194984468994425 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12102)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24204 ^ 2)
    ((12500000000000000000/1900977714687183888598197))
    ((25000000000000000000/3801798349741688287522369)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24204) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24204 : ℝ)^2 / (mW 12102 : ℝ)) * (1 + 1/10^6)^2 *
    √(((213847/100000000000))/2) * ((1-firstRatio 24204) * √(1-firstRatio 24204) *
      sixthConstant (e1CovarianceRatio 24204 (mW 12102) (1/10^6) rowEps))) /
    (712/10000 - 24204*(1+1/10^6)*((213847/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24204 (mW 12102) /
    ((1/10^5) * ((mW 12102 : ℝ)*24204*((mW 12102 : ℝ)+24204+1)))^2 +
  8*(mW 12102 : ℝ)*24204*(24204+2)*(24204+3) /
    ((1/1000)*((mW 12102 : ℝ)*24204*(24204+2)))^2 +
  covarianceVarianceBound 24204 (mW 12102) /
    ((1/1000)*covarianceMeanBound 24204 (mW 12102))^2 +
  normVarianceBound 24204 (mW 12102) / (3*inputVarianceMean 24204 (mW 12102))^2

end BstLean.Part281.WorldRow12102
namespace BstLean.Part281.WorldRow12103
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12103 = 195040865964623 := by
  have hu : mW 12103 ≤ 195040865964623 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12103 ≤ 195040865964622 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12103)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24206 ^ 2)
    ((25000000000000000000/3802269588639726756520241))
    ((5000000000000000000/760422501801409453369243)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24206) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24206 : ℝ)^2 / (mW 12103 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2138291/1000000000000))/2) * ((1-firstRatio 24206) * √(1-firstRatio 24206) *
      sixthConstant (e1CovarianceRatio 24206 (mW 12103) (1/10^6) rowEps))) /
    (712/10000 - 24206*(1+1/10^6)*((2138291/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24206 (mW 12103) /
    ((1/10^5) * ((mW 12103 : ℝ)*24206*((mW 12103 : ℝ)+24206+1)))^2 +
  8*(mW 12103 : ℝ)*24206*(24206+2)*(24206+3) /
    ((1/1000)*((mW 12103 : ℝ)*24206*(24206+2)))^2 +
  covarianceVarianceBound 24206 (mW 12103) /
    ((1/1000)*covarianceMeanBound 24206 (mW 12103))^2 +
  normVarianceBound 24206 (mW 12103) / (3*inputVarianceMean 24206 (mW 12103))^2

end BstLean.Part281.WorldRow12103
namespace BstLean.Part281.WorldRow12104
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12104 = 195097274585401 := by
  have hu : mW 12104 ≤ 195097274585401 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12104 ≤ 195097274585400 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12104)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24208 ^ 2)
    ((3125000000000000000/475322968488135716980511))
    ((25000000000000000000/3802426668272406246170061)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24208) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24208 : ℝ)^2 / (mW 12104 : ℝ)) * (1 + 1/10^6)^2 *
    √(((522/244140625))/2) * ((1-firstRatio 24208) * √(1-firstRatio 24208) *
      sixthConstant (e1CovarianceRatio 24208 (mW 12104) (1/10^6) rowEps))) /
    (712/10000 - 24208*(1+1/10^6)*((522/244140625)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24208 (mW 12104) /
    ((1/10^5) * ((mW 12104 : ℝ)*24208*((mW 12104 : ℝ)+24208+1)))^2 +
  8*(mW 12104 : ℝ)*24208*(24208+2)*(24208+3) /
    ((1/1000)*((mW 12104 : ℝ)*24208*(24208+2)))^2 +
  covarianceVarianceBound 24208 (mW 12104) /
    ((1/1000)*covarianceMeanBound 24208 (mW 12104))^2 +
  normVarianceBound 24208 (mW 12104) / (3*inputVarianceMean 24208 (mW 12104))^2

end BstLean.Part281.WorldRow12104
namespace BstLean.Part281.WorldRow12105
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12105 = 195153694858205 := by
  have hu : mW 12105 ≤ 195153694858205 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12105 ≤ 195153694858204 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12105)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24210 ^ 2)
    ((5000000000000000000/760579581434088943033587))
    ((25000000000000000000/3802740827537765225493907)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24210) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24210 : ℝ)^2 / (mW 12105 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1068967/500000000000))/2) * ((1-firstRatio 24210) * √(1-firstRatio 24210) *
      sixthConstant (e1CovarianceRatio 24210 (mW 12105) (1/10^6) rowEps))) /
    (712/10000 - 24210*(1+1/10^6)*((1068967/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24210 (mW 12105) /
    ((1/10^5) * ((mW 12105 : ℝ)*24210*((mW 12105 : ℝ)+24210+1)))^2 +
  8*(mW 12105 : ℝ)*24210*(24210+2)*(24210+3) /
    ((1/1000)*((mW 12105 : ℝ)*24210*(24210+2)))^2 +
  covarianceVarianceBound 24210 (mW 12105) /
    ((1/1000)*covarianceMeanBound 24210 (mW 12105))^2 +
  normVarianceBound 24210 (mW 12105) / (3*inputVarianceMean 24210 (mW 12105))^2

end BstLean.Part281.WorldRow12105
namespace BstLean.Part281.WorldRow12106
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12106 = 195210126784479 := by
  have hu : mW 12106 ≤ 195210126784479 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12106 ≤ 195210126784478 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12106)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24212 ^ 2)
    ((12500000000000000000/1901606033217901847245891))
    ((25000000000000000000/3803054986803124204817753)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24212) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24212 : ℝ)^2 / (mW 12106 : ℝ)) * (1 + 1/10^6)^2 *
    √(((427551/200000000000))/2) * ((1-firstRatio 24212) * √(1-firstRatio 24212) *
      sixthConstant (e1CovarianceRatio 24212 (mW 12106) (1/10^6) rowEps))) /
    (712/10000 - 24212*(1+1/10^6)*((427551/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24212 (mW 12106) /
    ((1/10^5) * ((mW 12106 : ℝ)*24212*((mW 12106 : ℝ)+24212+1)))^2 +
  8*(mW 12106 : ℝ)*24212*(24212+2)*(24212+3) /
    ((1/1000)*((mW 12106 : ℝ)*24212*(24212+2)))^2 +
  covarianceVarianceBound 24212 (mW 12106) /
    ((1/1000)*covarianceMeanBound 24212 (mW 12106))^2 +
  normVarianceBound 24212 (mW 12106) / (3*inputVarianceMean 24212 (mW 12106))^2

end BstLean.Part281.WorldRow12106
namespace BstLean.Part281.WorldRow12107
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12107 = 195266570365666 := by
  have hu : mW 12107 ≤ 195266570365666 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12107 ≤ 195266570365665 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12107)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24214 ^ 2)
    ((25000000000000000000/3803526225701162673815629))
    ((25000000000000000000/3803369146068483184141599)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24214) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24214 : ℝ)^2 / (mW 12107 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2137577/1000000000000))/2) * ((1-firstRatio 24214) * √(1-firstRatio 24214) *
      sixthConstant (e1CovarianceRatio 24214 (mW 12107) (1/10^6) rowEps))) /
    (712/10000 - 24214*(1+1/10^6)*((2137577/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24214 (mW 12107) /
    ((1/10^5) * ((mW 12107 : ℝ)*24214*((mW 12107 : ℝ)+24214+1)))^2 +
  8*(mW 12107 : ℝ)*24214*(24214+2)*(24214+3) /
    ((1/1000)*((mW 12107 : ℝ)*24214*(24214+2)))^2 +
  covarianceVarianceBound 24214 (mW 12107) /
    ((1/1000)*covarianceMeanBound 24214 (mW 12107))^2 +
  normVarianceBound 24214 (mW 12107) / (3*inputVarianceMean 24214 (mW 12107))^2

end BstLean.Part281.WorldRow12107
namespace BstLean.Part281.WorldRow12108
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12108 = 195323025603211 := by
  have hu : mW 12108 ≤ 195323025603211 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12108 ≤ 195323025603210 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12108)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24216 ^ 2)
    ((6250000000000000000/950960096241630413284869))
    ((5000000000000000000/760736661066768432693089)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24216) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24216 : ℝ)^2 / (mW 12108 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1068699/500000000000))/2) * ((1-firstRatio 24216) * √(1-firstRatio 24216) *
      sixthConstant (e1CovarianceRatio 24216 (mW 12108) (1/10^6) rowEps))) /
    (712/10000 - 24216*(1+1/10^6)*((1068699/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24216 (mW 12108) /
    ((1/10^5) * ((mW 12108 : ℝ)*24216*((mW 12108 : ℝ)+24216+1)))^2 +
  8*(mW 12108 : ℝ)*24216*(24216+2)*(24216+3) /
    ((1/1000)*((mW 12108 : ℝ)*24216*(24216+2)))^2 +
  covarianceVarianceBound 24216 (mW 12108) /
    ((1/1000)*covarianceMeanBound 24216 (mW 12108))^2 +
  normVarianceBound 24216 (mW 12108) / (3*inputVarianceMean 24216 (mW 12108))^2

end BstLean.Part281.WorldRow12108
