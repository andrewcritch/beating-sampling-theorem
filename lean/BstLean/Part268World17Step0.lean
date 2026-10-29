import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar17
namespace BstLean.Part268.WorldRow12775
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12775 = 235647686742144 := by
  have hu : mW 12775 ≤ 235647686742144 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12775 ≤ 235647686742143 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12775)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25550 ^ 2)
    ((1000000000000000000/160535384598438434485817))
    ((25000000000000000000/4013227535328281372470727)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25550) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25550 : ℝ)^2 / (mW 12775 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2024629/1000000000000))/2) * ((1-firstRatio 25550) * √(1-firstRatio 25550) *
      sixthConstant (e1CovarianceRatio 25550 (mW 12775) (1/10^6) rowEps))) /
    (712/10000 - 25550*(1+1/10^6)*((2024629/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25550 (mW 12775) /
    ((1/10^5) * ((mW 12775 : ℝ)*25550*((mW 12775 : ℝ)+25550+1)))^2 +
  8*(mW 12775 : ℝ)*25550*(25550+2)*(25550+3) /
    ((1/1000)*((mW 12775 : ℝ)*25550*(25550+2)))^2 +
  covarianceVarianceBound 25550 (mW 12775) /
    ((1/1000)*covarianceMeanBound 25550 (mW 12775))^2 +
  normVarianceBound 25550 (mW 12775) / (3*inputVarianceMean 25550 (mW 12775))^2

end BstLean.Part268.WorldRow12775
namespace BstLean.Part268.WorldRow12776
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12776 = 235712254069581 := by
  have hu : mW 12776 ≤ 235712254069581 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12776 ≤ 235712254069580 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12776)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25552 ^ 2)
    ((3125000000000000000/501712346778289980183659))
    ((25000000000000000000/4013541694593640351794573)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25552) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25552 : ℝ)^2 / (mW 12776 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2024469/1000000000000))/2) * ((1-firstRatio 25552) * √(1-firstRatio 25552) *
      sixthConstant (e1CovarianceRatio 25552 (mW 12776) (1/10^6) rowEps))) /
    (712/10000 - 25552*(1+1/10^6)*((2024469/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25552 (mW 12776) /
    ((1/10^5) * ((mW 12776 : ℝ)*25552*((mW 12776 : ℝ)+25552+1)))^2 +
  8*(mW 12776 : ℝ)*25552*(25552+2)*(25552+3) /
    ((1/1000)*((mW 12776 : ℝ)*25552*(25552+2)))^2 +
  covarianceVarianceBound 25552 (mW 12776) /
    ((1/1000)*covarianceMeanBound 25552 (mW 12776))^2 +
  normVarianceBound 25552 (mW 12776) / (3*inputVarianceMean 25552 (mW 12776))^2

end BstLean.Part268.WorldRow12776
namespace BstLean.Part268.WorldRow12777
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12777 = 235776834032751 := by
  have hu : mW 12777 ≤ 235776834032751 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12777 ≤ 235776834032750 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12777)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25554 ^ 2)
    ((25000000000000000000/4014012933491678820793119))
    ((25000000000000000000/4013855853858999331118419)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25554) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25554 : ℝ)^2 / (mW 12777 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2024309/1000000000000))/2) * ((1-firstRatio 25554) * √(1-firstRatio 25554) *
      sixthConstant (e1CovarianceRatio 25554 (mW 12777) (1/10^6) rowEps))) /
    (712/10000 - 25554*(1+1/10^6)*((2024309/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25554 (mW 12777) /
    ((1/10^5) * ((mW 12777 : ℝ)*25554*((mW 12777 : ℝ)+25554+1)))^2 +
  8*(mW 12777 : ℝ)*25554*(25554+2)*(25554+3) /
    ((1/1000)*((mW 12777 : ℝ)*25554*(25554+2)))^2 +
  covarianceVarianceBound 25554 (mW 12777) /
    ((1/1000)*covarianceMeanBound 25554 (mW 12777))^2 +
  normVarianceBound 25554 (mW 12777) / (3*inputVarianceMean 25554 (mW 12777))^2

end BstLean.Part268.WorldRow12777
namespace BstLean.Part268.WorldRow12778
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12778 = 235841426633137 := by
  have hu : mW 12778 ≤ 235841426633137 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12778 ≤ 235841426633136 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12778)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25556 ^ 2)
    ((12500000000000000000/2007163546378518900058483))
    ((5000000000000000000/802834002624871662088453)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25556) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25556 : ℝ)^2 / (mW 12778 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2024149/1000000000000))/2) * ((1-firstRatio 25556) * √(1-firstRatio 25556) *
      sixthConstant (e1CovarianceRatio 25556 (mW 12778) (1/10^6) rowEps))) /
    (712/10000 - 25556*(1+1/10^6)*((2024149/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25556 (mW 12778) /
    ((1/10^5) * ((mW 12778 : ℝ)*25556*((mW 12778 : ℝ)+25556+1)))^2 +
  8*(mW 12778 : ℝ)*25556*(25556+2)*(25556+3) /
    ((1/1000)*((mW 12778 : ℝ)*25556*(25556+2)))^2 +
  covarianceVarianceBound 25556 (mW 12778) /
    ((1/1000)*covarianceMeanBound 25556 (mW 12778))^2 +
  normVarianceBound 25556 (mW 12778) / (3*inputVarianceMean 25556 (mW 12778))^2

end BstLean.Part268.WorldRow12778
namespace BstLean.Part268.WorldRow12779
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12779 = 235906031872222 := by
  have hu : mW 12779 ≤ 235906031872222 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12779 ≤ 235906031872221 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12779)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25558 ^ 2)
    ((25000000000000000000/4014641252022396779440813))
    ((25000000000000000000/4014484172389717289766111)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25558) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25558 : ℝ)^2 / (mW 12779 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2023989/1000000000000))/2) * ((1-firstRatio 25558) * √(1-firstRatio 25558) *
      sixthConstant (e1CovarianceRatio 25558 (mW 12779) (1/10^6) rowEps))) /
    (712/10000 - 25558*(1+1/10^6)*((2023989/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25558 (mW 12779) /
    ((1/10^5) * ((mW 12779 : ℝ)*25558*((mW 12779 : ℝ)+25558+1)))^2 +
  8*(mW 12779 : ℝ)*25558*(25558+2)*(25558+3) /
    ((1/1000)*((mW 12779 : ℝ)*25558*(25558+2)))^2 +
  covarianceVarianceBound 25558 (mW 12779) /
    ((1/1000)*covarianceMeanBound 25558 (mW 12779))^2 +
  normVarianceBound 25558 (mW 12779) / (3*inputVarianceMean 25558 (mW 12779))^2

end BstLean.Part268.WorldRow12779
namespace BstLean.Part268.WorldRow12780
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12780 = 235970649751489 := by
  have hu : mW 12780 ≤ 235970649751489 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12780 ≤ 235970649751488 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12780)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25560 ^ 2)
    ((1250000000000000000/200747770564387787938233))
    ((25000000000000000000/4014798331655076269089957)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25560) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25560 : ℝ)^2 / (mW 12780 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2023829/1000000000000))/2) * ((1-firstRatio 25560) * √(1-firstRatio 25560) *
      sixthConstant (e1CovarianceRatio 25560 (mW 12780) (1/10^6) rowEps))) /
    (712/10000 - 25560*(1+1/10^6)*((2023829/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25560 (mW 12780) /
    ((1/10^5) * ((mW 12780 : ℝ)*25560*((mW 12780 : ℝ)+25560+1)))^2 +
  8*(mW 12780 : ℝ)*25560*(25560+2)*(25560+3) /
    ((1/1000)*((mW 12780 : ℝ)*25560*(25560+2)))^2 +
  covarianceVarianceBound 25560 (mW 12780) /
    ((1/1000)*covarianceMeanBound 25560 (mW 12780))^2 +
  normVarianceBound 25560 (mW 12780) / (3*inputVarianceMean 25560 (mW 12780))^2

end BstLean.Part268.WorldRow12780
namespace BstLean.Part268.WorldRow12781
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12781 = 236035280272424 := by
  have hu : mW 12781 ≤ 236035280272424 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12781 ≤ 236035280272423 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12781)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25562 ^ 2)
    ((25000000000000000000/4015269570553114738088507))
    ((25000000000000000000/4015112490920435248413803)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25562) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25562 : ℝ)^2 / (mW 12781 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2023669/1000000000000))/2) * ((1-firstRatio 25562) * √(1-firstRatio 25562) *
      sixthConstant (e1CovarianceRatio 25562 (mW 12781) (1/10^6) rowEps))) /
    (712/10000 - 25562*(1+1/10^6)*((2023669/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25562 (mW 12781) /
    ((1/10^5) * ((mW 12781 : ℝ)*25562*((mW 12781 : ℝ)+25562+1)))^2 +
  8*(mW 12781 : ℝ)*25562*(25562+2)*(25562+3) /
    ((1/1000)*((mW 12781 : ℝ)*25562*(25562+2)))^2 +
  covarianceVarianceBound 25562 (mW 12781) /
    ((1/1000)*covarianceMeanBound 25562 (mW 12781))^2 +
  normVarianceBound 25562 (mW 12781) / (3*inputVarianceMean 25562 (mW 12781))^2

end BstLean.Part268.WorldRow12781
namespace BstLean.Part268.WorldRow12782
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12782 = 236099923436508 := by
  have hu : mW 12782 ≤ 236099923436508 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12782 ≤ 236099923436507 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12782)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25564 ^ 2)
    ((12500000000000000000/2007791864909236858706177))
    ((25000000000000000000/4015426650185794227737649)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25564) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25564 : ℝ)^2 / (mW 12782 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2023509/1000000000000))/2) * ((1-firstRatio 25564) * √(1-firstRatio 25564) *
      sixthConstant (e1CovarianceRatio 25564 (mW 12782) (1/10^6) rowEps))) /
    (712/10000 - 25564*(1+1/10^6)*((2023509/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25564 (mW 12782) /
    ((1/10^5) * ((mW 12782 : ℝ)*25564*((mW 12782 : ℝ)+25564+1)))^2 +
  8*(mW 12782 : ℝ)*25564*(25564+2)*(25564+3) /
    ((1/1000)*((mW 12782 : ℝ)*25564*(25564+2)))^2 +
  covarianceVarianceBound 25564 (mW 12782) /
    ((1/1000)*covarianceMeanBound 25564 (mW 12782))^2 +
  normVarianceBound 25564 (mW 12782) / (3*inputVarianceMean 25564 (mW 12782))^2

end BstLean.Part268.WorldRow12782
namespace BstLean.Part268.WorldRow12783
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12783 = 236164579245227 := by
  have hu : mW 12783 ≤ 236164579245227 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12783 ≤ 236164579245226 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12783)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25566 ^ 2)
    ((25000000000000000000/4015897889083832696736201))
    ((5000000000000000000/803148161890230641412299)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25566) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25566 : ℝ)^2 / (mW 12783 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2023349/1000000000000))/2) * ((1-firstRatio 25566) * √(1-firstRatio 25566) *
      sixthConstant (e1CovarianceRatio 25566 (mW 12783) (1/10^6) rowEps))) /
    (712/10000 - 25566*(1+1/10^6)*((2023349/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25566 (mW 12783) /
    ((1/10^5) * ((mW 12783 : ℝ)*25566*((mW 12783 : ℝ)+25566+1)))^2 +
  8*(mW 12783 : ℝ)*25566*(25566+2)*(25566+3) /
    ((1/1000)*((mW 12783 : ℝ)*25566*(25566+2)))^2 +
  covarianceVarianceBound 25566 (mW 12783) /
    ((1/1000)*covarianceMeanBound 25566 (mW 12783))^2 +
  normVarianceBound 25566 (mW 12783) / (3*inputVarianceMean 25566 (mW 12783))^2

end BstLean.Part268.WorldRow12783
namespace BstLean.Part268.WorldRow12784
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12784 = 236229247700065 := by
  have hu : mW 12784 ≤ 236229247700065 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12784 ≤ 236229247700064 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12784)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25568 ^ 2)
    ((1562500000000000000/251013253021824479753753))
    ((25000000000000000000/4016054968716512186385341)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25568) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25568 : ℝ)^2 / (mW 12784 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2023189/1000000000000))/2) * ((1-firstRatio 25568) * √(1-firstRatio 25568) *
      sixthConstant (e1CovarianceRatio 25568 (mW 12784) (1/10^6) rowEps))) /
    (712/10000 - 25568*(1+1/10^6)*((2023189/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25568 (mW 12784) /
    ((1/10^5) * ((mW 12784 : ℝ)*25568*((mW 12784 : ℝ)+25568+1)))^2 +
  8*(mW 12784 : ℝ)*25568*(25568+2)*(25568+3) /
    ((1/1000)*((mW 12784 : ℝ)*25568*(25568+2)))^2 +
  covarianceVarianceBound 25568 (mW 12784) /
    ((1/1000)*covarianceMeanBound 25568 (mW 12784))^2 +
  normVarianceBound 25568 (mW 12784) / (3*inputVarianceMean 25568 (mW 12784))^2

end BstLean.Part268.WorldRow12784
namespace BstLean.Part268.WorldRow12785
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12785 = 236293928802504 := by
  have hu : mW 12785 ≤ 236293928802504 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12785 ≤ 236293928802503 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12785)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25570 ^ 2)
    ((5000000000000000000/803305241522910131076779))
    ((25000000000000000000/4016369127981871165709187)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25570) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25570 : ℝ)^2 / (mW 12785 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2023029/1000000000000))/2) * ((1-firstRatio 25570) * √(1-firstRatio 25570) *
      sixthConstant (e1CovarianceRatio 25570 (mW 12785) (1/10^6) rowEps))) /
    (712/10000 - 25570*(1+1/10^6)*((2023029/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25570 (mW 12785) /
    ((1/10^5) * ((mW 12785 : ℝ)*25570*((mW 12785 : ℝ)+25570+1)))^2 +
  8*(mW 12785 : ℝ)*25570*(25570+2)*(25570+3) /
    ((1/1000)*((mW 12785 : ℝ)*25570*(25570+2)))^2 +
  covarianceVarianceBound 25570 (mW 12785) /
    ((1/1000)*covarianceMeanBound 25570 (mW 12785))^2 +
  normVarianceBound 25570 (mW 12785) / (3*inputVarianceMean 25570 (mW 12785))^2

end BstLean.Part268.WorldRow12785
namespace BstLean.Part268.WorldRow12786
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12786 = 236358622554030 := by
  have hu : mW 12786 ≤ 236358622554030 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12786 ≤ 236358622554029 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12786)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25572 ^ 2)
    ((12500000000000000000/2008420183439954817353871))
    ((25000000000000000000/4016683287247230145033033)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25572) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25572 : ℝ)^2 / (mW 12786 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2022869/1000000000000))/2) * ((1-firstRatio 25572) * √(1-firstRatio 25572) *
      sixthConstant (e1CovarianceRatio 25572 (mW 12786) (1/10^6) rowEps))) /
    (712/10000 - 25572*(1+1/10^6)*((2022869/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25572 (mW 12786) /
    ((1/10^5) * ((mW 12786 : ℝ)*25572*((mW 12786 : ℝ)+25572+1)))^2 +
  8*(mW 12786 : ℝ)*25572*(25572+2)*(25572+3) /
    ((1/1000)*((mW 12786 : ℝ)*25572*(25572+2)))^2 +
  covarianceVarianceBound 25572 (mW 12786) /
    ((1/1000)*covarianceMeanBound 25572 (mW 12786))^2 +
  normVarianceBound 25572 (mW 12786) / (3*inputVarianceMean 25572 (mW 12786))^2

end BstLean.Part268.WorldRow12786
namespace BstLean.Part268.WorldRow12787
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12787 = 236423328956125 := by
  have hu : mW 12787 ≤ 236423328956125 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12787 ≤ 236423328956124 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12787)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25574 ^ 2)
    ((25000000000000000000/4017154526145268614031589))
    ((25000000000000000000/4016997446512589124356879)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25574) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25574 : ℝ)^2 / (mW 12787 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2022709/1000000000000))/2) * ((1-firstRatio 25574) * √(1-firstRatio 25574) *
      sixthConstant (e1CovarianceRatio 25574 (mW 12787) (1/10^6) rowEps))) /
    (712/10000 - 25574*(1+1/10^6)*((2022709/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25574 (mW 12787) /
    ((1/10^5) * ((mW 12787 : ℝ)*25574*((mW 12787 : ℝ)+25574+1)))^2 +
  8*(mW 12787 : ℝ)*25574*(25574+2)*(25574+3) /
    ((1/1000)*((mW 12787 : ℝ)*25574*(25574+2)))^2 +
  covarianceVarianceBound 25574 (mW 12787) /
    ((1/1000)*covarianceMeanBound 25574 (mW 12787))^2 +
  normVarianceBound 25574 (mW 12787) / (3*inputVarianceMean 25574 (mW 12787))^2

end BstLean.Part268.WorldRow12787
namespace BstLean.Part268.WorldRow12788
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12788 = 236488048010276 := by
  have hu : mW 12788 ≤ 236488048010276 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12788 ≤ 236488048010275 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12788)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25576 ^ 2)
    ((6250000000000000000/1004367171352656898338859))
    ((1000000000000000000/160692464231117924147229)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25576) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25576 : ℝ)^2 / (mW 12788 : ℝ)) * (1 + 1/10^6)^2 *
    √(((40451/20000000000))/2) * ((1-firstRatio 25576) * √(1-firstRatio 25576) *
      sixthConstant (e1CovarianceRatio 25576 (mW 12788) (1/10^6) rowEps))) /
    (712/10000 - 25576*(1+1/10^6)*((40451/20000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25576 (mW 12788) /
    ((1/10^5) * ((mW 12788 : ℝ)*25576*((mW 12788 : ℝ)+25576+1)))^2 +
  8*(mW 12788 : ℝ)*25576*(25576+2)*(25576+3) /
    ((1/1000)*((mW 12788 : ℝ)*25576*(25576+2)))^2 +
  covarianceVarianceBound 25576 (mW 12788) /
    ((1/1000)*covarianceMeanBound 25576 (mW 12788))^2 +
  normVarianceBound 25576 (mW 12788) / (3*inputVarianceMean 25576 (mW 12788))^2

end BstLean.Part268.WorldRow12788
namespace BstLean.Part268.WorldRow12789
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12789 = 236552779717965 := by
  have hu : mW 12789 ≤ 236552779717965 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12789 ≤ 236552779717964 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12789)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25578 ^ 2)
    ((25000000000000000000/4017782844675986572679283))
    ((25000000000000000000/4017625765043307083004571)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25578) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25578 : ℝ)^2 / (mW 12789 : ℝ)) * (1 + 1/10^6)^2 *
    √(((202239/100000000000))/2) * ((1-firstRatio 25578) * √(1-firstRatio 25578) *
      sixthConstant (e1CovarianceRatio 25578 (mW 12789) (1/10^6) rowEps))) /
    (712/10000 - 25578*(1+1/10^6)*((202239/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25578 (mW 12789) /
    ((1/10^5) * ((mW 12789 : ℝ)*25578*((mW 12789 : ℝ)+25578+1)))^2 +
  8*(mW 12789 : ℝ)*25578*(25578+2)*(25578+3) /
    ((1/1000)*((mW 12789 : ℝ)*25578*(25578+2)))^2 +
  covarianceVarianceBound 25578 (mW 12789) /
    ((1/1000)*covarianceMeanBound 25578 (mW 12789))^2 +
  normVarianceBound 25578 (mW 12789) / (3*inputVarianceMean 25578 (mW 12789))^2

end BstLean.Part268.WorldRow12789
namespace BstLean.Part268.WorldRow12790
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12790 = 236617524080676 := by
  have hu : mW 12790 ≤ 236617524080676 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12790 ≤ 236617524080675 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12790)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25580 ^ 2)
    ((2500000000000000000/401809700394134555200313))
    ((25000000000000000000/4017939924308666062328417)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25580) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25580 : ℝ)^2 / (mW 12790 : ℝ)) * (1 + 1/10^6)^2 *
    √(((202223/100000000000))/2) * ((1-firstRatio 25580) * √(1-firstRatio 25580) *
      sixthConstant (e1CovarianceRatio 25580 (mW 12790) (1/10^6) rowEps))) /
    (712/10000 - 25580*(1+1/10^6)*((202223/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25580 (mW 12790) /
    ((1/10^5) * ((mW 12790 : ℝ)*25580*((mW 12790 : ℝ)+25580+1)))^2 +
  8*(mW 12790 : ℝ)*25580*(25580+2)*(25580+3) /
    ((1/1000)*((mW 12790 : ℝ)*25580*(25580+2)))^2 +
  covarianceVarianceBound 25580 (mW 12790) /
    ((1/1000)*covarianceMeanBound 25580 (mW 12790))^2 +
  normVarianceBound 25580 (mW 12790) / (3*inputVarianceMean 25580 (mW 12790))^2

end BstLean.Part268.WorldRow12790
namespace BstLean.Part268.WorldRow12791
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12791 = 236682281099895 := by
  have hu : mW 12791 ≤ 236682281099895 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12791 ≤ 236682281099894 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12791)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25582 ^ 2)
    ((25000000000000000000/4018411163206704531326977))
    ((25000000000000000000/4018254083574025041652263)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25582) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25582 : ℝ)^2 / (mW 12791 : ℝ)) * (1 + 1/10^6)^2 *
    √(((202207/100000000000))/2) * ((1-firstRatio 25582) * √(1-firstRatio 25582) *
      sixthConstant (e1CovarianceRatio 25582 (mW 12791) (1/10^6) rowEps))) /
    (712/10000 - 25582*(1+1/10^6)*((202207/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25582 (mW 12791) /
    ((1/10^5) * ((mW 12791 : ℝ)*25582*((mW 12791 : ℝ)+25582+1)))^2 +
  8*(mW 12791 : ℝ)*25582*(25582+2)*(25582+3) /
    ((1/1000)*((mW 12791 : ℝ)*25582*(25582+2)))^2 +
  covarianceVarianceBound 25582 (mW 12791) /
    ((1/1000)*covarianceMeanBound 25582 (mW 12791))^2 +
  normVarianceBound 25582 (mW 12791) / (3*inputVarianceMean 25582 (mW 12791))^2

end BstLean.Part268.WorldRow12791
namespace BstLean.Part268.WorldRow12792
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12792 = 236747050777106 := by
  have hu : mW 12792 ≤ 236747050777106 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12792 ≤ 236747050777105 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12792)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25584 ^ 2)
    ((3125000000000000000/502340665309007938831353))
    ((25000000000000000000/4018568242839384020976109)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25584) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25584 : ℝ)^2 / (mW 12792 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2021911/1000000000000))/2) * ((1-firstRatio 25584) * √(1-firstRatio 25584) *
      sixthConstant (e1CovarianceRatio 25584 (mW 12792) (1/10^6) rowEps))) /
    (712/10000 - 25584*(1+1/10^6)*((2021911/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25584 (mW 12792) /
    ((1/10^5) * ((mW 12792 : ℝ)*25584*((mW 12792 : ℝ)+25584+1)))^2 +
  8*(mW 12792 : ℝ)*25584*(25584+2)*(25584+3) /
    ((1/1000)*((mW 12792 : ℝ)*25584*(25584+2)))^2 +
  covarianceVarianceBound 25584 (mW 12792) /
    ((1/1000)*covarianceMeanBound 25584 (mW 12792))^2 +
  normVarianceBound 25584 (mW 12792) / (3*inputVarianceMean 25584 (mW 12792))^2

end BstLean.Part268.WorldRow12792
namespace BstLean.Part268.WorldRow12793
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12793 = 236811833113792 := by
  have hu : mW 12793 ≤ 236811833113792 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12793 ≤ 236811833113791 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12793)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25586 ^ 2)
    ((25000000000000000000/4019039481737422489974671))
    ((5000000000000000000/803776480420948600059991)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25586) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25586 : ℝ)^2 / (mW 12793 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2021751/1000000000000))/2) * ((1-firstRatio 25586) * √(1-firstRatio 25586) *
      sixthConstant (e1CovarianceRatio 25586 (mW 12793) (1/10^6) rowEps))) /
    (712/10000 - 25586*(1+1/10^6)*((2021751/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25586 (mW 12793) /
    ((1/10^5) * ((mW 12793 : ℝ)*25586*((mW 12793 : ℝ)+25586+1)))^2 +
  8*(mW 12793 : ℝ)*25586*(25586+2)*(25586+3) /
    ((1/1000)*((mW 12793 : ℝ)*25586*(25586+2)))^2 +
  covarianceVarianceBound 25586 (mW 12793) /
    ((1/1000)*covarianceMeanBound 25586 (mW 12793))^2 +
  normVarianceBound 25586 (mW 12793) / (3*inputVarianceMean 25586 (mW 12793))^2

end BstLean.Part268.WorldRow12793
namespace BstLean.Part268.WorldRow12794
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12794 = 236876628111439 := by
  have hu : mW 12794 ≤ 236876628111439 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12794 ≤ 236876628111438 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12794)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25588 ^ 2)
    ((12500000000000000000/2009676820501390734649259))
    ((25000000000000000000/4019196561370101979623801)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25588) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25588 : ℝ)^2 / (mW 12794 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2021591/1000000000000))/2) * ((1-firstRatio 25588) * √(1-firstRatio 25588) *
      sixthConstant (e1CovarianceRatio 25588 (mW 12794) (1/10^6) rowEps))) /
    (712/10000 - 25588*(1+1/10^6)*((2021591/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25588 (mW 12794) /
    ((1/10^5) * ((mW 12794 : ℝ)*25588*((mW 12794 : ℝ)+25588+1)))^2 +
  8*(mW 12794 : ℝ)*25588*(25588+2)*(25588+3) /
    ((1/1000)*((mW 12794 : ℝ)*25588*(25588+2)))^2 +
  covarianceVarianceBound 25588 (mW 12794) /
    ((1/1000)*covarianceMeanBound 25588 (mW 12794))^2 +
  normVarianceBound 25588 (mW 12794) / (3*inputVarianceMean 25588 (mW 12794))^2

end BstLean.Part268.WorldRow12794
namespace BstLean.Part268.WorldRow12795
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12795 = 236941435771531 := by
  have hu : mW 12795 ≤ 236941435771531 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12795 ≤ 236941435771530 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12795)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25590 ^ 2)
    ((5000000000000000000/803933560053628089724473))
    ((25000000000000000000/4019510720635460958947647)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25590) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25590 : ℝ)^2 / (mW 12795 : ℝ)) * (1 + 1/10^6)^2 *
    √(((252679/125000000000))/2) * ((1-firstRatio 25590) * √(1-firstRatio 25590) *
      sixthConstant (e1CovarianceRatio 25590 (mW 12795) (1/10^6) rowEps))) /
    (712/10000 - 25590*(1+1/10^6)*((252679/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25590 (mW 12795) /
    ((1/10^5) * ((mW 12795 : ℝ)*25590*((mW 12795 : ℝ)+25590+1)))^2 +
  8*(mW 12795 : ℝ)*25590*(25590+2)*(25590+3) /
    ((1/1000)*((mW 12795 : ℝ)*25590*(25590+2)))^2 +
  covarianceVarianceBound 25590 (mW 12795) /
    ((1/1000)*covarianceMeanBound 25590 (mW 12795))^2 +
  normVarianceBound 25590 (mW 12795) / (3*inputVarianceMean 25590 (mW 12795))^2

end BstLean.Part268.WorldRow12795
namespace BstLean.Part268.WorldRow12796
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12796 = 237006256095553 := by
  have hu : mW 12796 ≤ 237006256095553 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12796 ≤ 237006256095552 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12796)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25592 ^ 2)
    ((6250000000000000000/1004995489883374856986553))
    ((25000000000000000000/4019824879900819938271493)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25592) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25592 : ℝ)^2 / (mW 12796 : ℝ)) * (1 + 1/10^6)^2 *
    √(((252659/125000000000))/2) * ((1-firstRatio 25592) * √(1-firstRatio 25592) *
      sixthConstant (e1CovarianceRatio 25592 (mW 12796) (1/10^6) rowEps))) /
    (712/10000 - 25592*(1+1/10^6)*((252659/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25592 (mW 12796) /
    ((1/10^5) * ((mW 12796 : ℝ)*25592*((mW 12796 : ℝ)+25592+1)))^2 +
  8*(mW 12796 : ℝ)*25592*(25592+2)*(25592+3) /
    ((1/1000)*((mW 12796 : ℝ)*25592*(25592+2)))^2 +
  covarianceVarianceBound 25592 (mW 12796) /
    ((1/1000)*covarianceMeanBound 25592 (mW 12796))^2 +
  normVarianceBound 25592 (mW 12796) / (3*inputVarianceMean 25592 (mW 12796))^2

end BstLean.Part268.WorldRow12796
namespace BstLean.Part268.WorldRow12797
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12797 = 237071089084989 := by
  have hu : mW 12797 ≤ 237071089084989 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12797 ≤ 237071089084988 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12797)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25594 ^ 2)
    ((25000000000000000000/4020296118798858407270059))
    ((25000000000000000000/4020139039166178917595339)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25594) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25594 : ℝ)^2 / (mW 12797 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2021113/1000000000000))/2) * ((1-firstRatio 25594) * √(1-firstRatio 25594) *
      sixthConstant (e1CovarianceRatio 25594 (mW 12797) (1/10^6) rowEps))) /
    (712/10000 - 25594*(1+1/10^6)*((2021113/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25594 (mW 12797) /
    ((1/10^5) * ((mW 12797 : ℝ)*25594*((mW 12797 : ℝ)+25594+1)))^2 +
  8*(mW 12797 : ℝ)*25594*(25594+2)*(25594+3) /
    ((1/1000)*((mW 12797 : ℝ)*25594*(25594+2)))^2 +
  covarianceVarianceBound 25594 (mW 12797) /
    ((1/1000)*covarianceMeanBound 25594 (mW 12797))^2 +
  normVarianceBound 25594 (mW 12797) / (3*inputVarianceMean 25594 (mW 12797))^2

end BstLean.Part268.WorldRow12797
namespace BstLean.Part268.WorldRow12798
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12798 = 237135934741323 := by
  have hu : mW 12798 ≤ 237135934741323 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12798 ≤ 237135934741322 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12798)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25596 ^ 2)
    ((12500000000000000000/2010305139032108693296953))
    ((5000000000000000000/804090639686307579383837)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25596) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25596 : ℝ)^2 / (mW 12798 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2020953/1000000000000))/2) * ((1-firstRatio 25596) * √(1-firstRatio 25596) *
      sixthConstant (e1CovarianceRatio 25596 (mW 12798) (1/10^6) rowEps))) /
    (712/10000 - 25596*(1+1/10^6)*((2020953/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25596 (mW 12798) /
    ((1/10^5) * ((mW 12798 : ℝ)*25596*((mW 12798 : ℝ)+25596+1)))^2 +
  8*(mW 12798 : ℝ)*25596*(25596+2)*(25596+3) /
    ((1/1000)*((mW 12798 : ℝ)*25596*(25596+2)))^2 +
  covarianceVarianceBound 25596 (mW 12798) /
    ((1/1000)*covarianceMeanBound 25596 (mW 12798))^2 +
  normVarianceBound 25596 (mW 12798) / (3*inputVarianceMean 25596 (mW 12798))^2

end BstLean.Part268.WorldRow12798
namespace BstLean.Part268.WorldRow12799
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12799 = 237200793066042 := by
  have hu : mW 12799 ≤ 237200793066042 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12799 ≤ 237200793066041 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12799)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25598 ^ 2)
    ((25000000000000000000/4020924437329576365917753))
    ((25000000000000000000/4020767357696896876243031)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25598) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25598 : ℝ)^2 / (mW 12799 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2020793/1000000000000))/2) * ((1-firstRatio 25598) * √(1-firstRatio 25598) *
      sixthConstant (e1CovarianceRatio 25598 (mW 12799) (1/10^6) rowEps))) /
    (712/10000 - 25598*(1+1/10^6)*((2020793/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25598 (mW 12799) /
    ((1/10^5) * ((mW 12799 : ℝ)*25598*((mW 12799 : ℝ)+25598+1)))^2 +
  8*(mW 12799 : ℝ)*25598*(25598+2)*(25598+3) /
    ((1/1000)*((mW 12799 : ℝ)*25598*(25598+2)))^2 +
  covarianceVarianceBound 25598 (mW 12799) /
    ((1/1000)*covarianceMeanBound 25598 (mW 12799))^2 +
  normVarianceBound 25598 (mW 12799) / (3*inputVarianceMean 25598 (mW 12799))^2

end BstLean.Part268.WorldRow12799
