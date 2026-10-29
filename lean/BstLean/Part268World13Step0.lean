import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar13
namespace BstLean.Part268.WorldRow12675
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12675 = 229254509974781 := by
  have hu : mW 12675 ≤ 229254509974781 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12675 ≤ 229254509974780 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12675)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25350 ^ 2)
    ((1000000000000000000/159278747537002517190429))
    ((25000000000000000000/3981811608792383440086127)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25350) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25350 : ℝ)^2 / (mW 12675 : ℝ)) * (1 + 1/10^6)^2 *
    √(((204077/100000000000))/2) * ((1-firstRatio 25350) * √(1-firstRatio 25350) *
      sixthConstant (e1CovarianceRatio 25350 (mW 12675) (1/10^6) rowEps))) /
    (712/10000 - 25350*(1+1/10^6)*((204077/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25350 (mW 12675) /
    ((1/10^5) * ((mW 12675 : ℝ)*25350*((mW 12675 : ℝ)+25350+1)))^2 +
  8*(mW 12675 : ℝ)*25350*(25350+2)*(25350+3) /
    ((1/1000)*((mW 12675 : ℝ)*25350*(25350+2)))^2 +
  covarianceVarianceBound 25350 (mW 12675) /
    ((1/1000)*covarianceMeanBound 25350 (mW 12675))^2 +
  normVarianceBound 25350 (mW 12675) / (3*inputVarianceMean 25350 (mW 12675))^2

end BstLean.Part268.WorldRow12675
namespace BstLean.Part268.WorldRow12676
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12676 = 229317821211015 := by
  have hu : mW 12676 ≤ 229317821211015 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12676 ≤ 229317821211014 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12676)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25352 ^ 2)
    ((6250000000000000000/995570711922605477271143))
    ((25000000000000000000/3982125768057742419409973)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25352) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25352 : ℝ)^2 / (mW 12676 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2040607/1000000000000))/2) * ((1-firstRatio 25352) * √(1-firstRatio 25352) *
      sixthConstant (e1CovarianceRatio 25352 (mW 12676) (1/10^6) rowEps))) /
    (712/10000 - 25352*(1+1/10^6)*((2040607/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25352 (mW 12676) /
    ((1/10^5) * ((mW 12676 : ℝ)*25352*((mW 12676 : ℝ)+25352+1)))^2 +
  8*(mW 12676 : ℝ)*25352*(25352+2)*(25352+3) /
    ((1/1000)*((mW 12676 : ℝ)*25352*(25352+2)))^2 +
  covarianceVarianceBound 25352 (mW 12676) /
    ((1/1000)*covarianceMeanBound 25352 (mW 12676))^2 +
  normVarianceBound 25352 (mW 12676) / (3*inputVarianceMean 25352 (mW 12676))^2

end BstLean.Part268.WorldRow12676
namespace BstLean.Part268.WorldRow12677
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12677 = 229381144934919 := by
  have hu : mW 12677 ≤ 229381144934919 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12677 ≤ 229381144934918 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12677)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25354 ^ 2)
    ((25000000000000000000/3982597006955780888408419))
    ((25000000000000000000/3982439927323101398733819)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25354) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25354 : ℝ)^2 / (mW 12677 : ℝ)) * (1 + 1/10^6)^2 *
    √(((510111/250000000000))/2) * ((1-firstRatio 25354) * √(1-firstRatio 25354) *
      sixthConstant (e1CovarianceRatio 25354 (mW 12677) (1/10^6) rowEps))) /
    (712/10000 - 25354*(1+1/10^6)*((510111/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25354 (mW 12677) /
    ((1/10^5) * ((mW 12677 : ℝ)*25354*((mW 12677 : ℝ)+25354+1)))^2 +
  8*(mW 12677 : ℝ)*25354*(25354+2)*(25354+3) /
    ((1/1000)*((mW 12677 : ℝ)*25354*(25354+2)))^2 +
  covarianceVarianceBound 25354 (mW 12677) /
    ((1/1000)*covarianceMeanBound 25354 (mW 12677))^2 +
  normVarianceBound 25354 (mW 12677) / (3*inputVarianceMean 25354 (mW 12677))^2

end BstLean.Part268.WorldRow12677
namespace BstLean.Part268.WorldRow12678
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12678 = 229444481147971 := by
  have hu : mW 12678 ≤ 229444481147971 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12678 ≤ 229444481147970 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12678)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25356 ^ 2)
    ((12500000000000000000/1991455583110569933866133))
    ((5000000000000000000/796550817317692075611533)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25356) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25356 : ℝ)^2 / (mW 12678 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1020141/500000000000))/2) * ((1-firstRatio 25356) * √(1-firstRatio 25356) *
      sixthConstant (e1CovarianceRatio 25356 (mW 12678) (1/10^6) rowEps))) /
    (712/10000 - 25356*(1+1/10^6)*((1020141/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25356 (mW 12678) /
    ((1/10^5) * ((mW 12678 : ℝ)*25356*((mW 12678 : ℝ)+25356+1)))^2 +
  8*(mW 12678 : ℝ)*25356*(25356+2)*(25356+3) /
    ((1/1000)*((mW 12678 : ℝ)*25356*(25356+2)))^2 +
  covarianceVarianceBound 25356 (mW 12678) /
    ((1/1000)*covarianceMeanBound 25356 (mW 12678))^2 +
  normVarianceBound 25356 (mW 12678) / (3*inputVarianceMean 25356 (mW 12678))^2

end BstLean.Part268.WorldRow12678
namespace BstLean.Part268.WorldRow12679
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12679 = 229507829851648 := by
  have hu : mW 12679 ≤ 229507829851648 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12679 ≤ 229507829851647 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12679)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25358 ^ 2)
    ((25000000000000000000/3983225325486498847056113))
    ((25000000000000000000/3983068245853819357381511)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25358) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25358 : ℝ)^2 / (mW 12679 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2040119/1000000000000))/2) * ((1-firstRatio 25358) * √(1-firstRatio 25358) *
      sixthConstant (e1CovarianceRatio 25358 (mW 12679) (1/10^6) rowEps))) /
    (712/10000 - 25358*(1+1/10^6)*((2040119/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25358 (mW 12679) /
    ((1/10^5) * ((mW 12679 : ℝ)*25358*((mW 12679 : ℝ)+25358+1)))^2 +
  8*(mW 12679 : ℝ)*25358*(25358+2)*(25358+3) /
    ((1/1000)*((mW 12679 : ℝ)*25358*(25358+2)))^2 +
  covarianceVarianceBound 25358 (mW 12679) /
    ((1/1000)*covarianceMeanBound 25358 (mW 12679))^2 +
  normVarianceBound 25358 (mW 12679) / (3*inputVarianceMean 25358 (mW 12679))^2

end BstLean.Part268.WorldRow12679
namespace BstLean.Part268.WorldRow12680
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12680 = 229571191047427 := by
  have hu : mW 12680 ≤ 229571191047427 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12680 ≤ 229571191047426 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12680)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25360 ^ 2)
    ((625000000000000000/99588487118796445659499))
    ((25000000000000000000/3983382405119178336705357)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25360) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25360 : ℝ)^2 / (mW 12680 : ℝ)) * (1 + 1/10^6)^2 *
    √(((509989/250000000000))/2) * ((1-firstRatio 25360) * √(1-firstRatio 25360) *
      sixthConstant (e1CovarianceRatio 25360 (mW 12680) (1/10^6) rowEps))) /
    (712/10000 - 25360*(1+1/10^6)*((509989/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25360 (mW 12680) /
    ((1/10^5) * ((mW 12680 : ℝ)*25360*((mW 12680 : ℝ)+25360+1)))^2 +
  8*(mW 12680 : ℝ)*25360*(25360+2)*(25360+3) /
    ((1/1000)*((mW 12680 : ℝ)*25360*(25360+2)))^2 +
  covarianceVarianceBound 25360 (mW 12680) /
    ((1/1000)*covarianceMeanBound 25360 (mW 12680))^2 +
  normVarianceBound 25360 (mW 12680) / (3*inputVarianceMean 25360 (mW 12680))^2

end BstLean.Part268.WorldRow12680
namespace BstLean.Part268.WorldRow12681
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12681 = 229634564736788 := by
  have hu : mW 12681 ≤ 229634564736788 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12681 ≤ 229634564736787 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12681)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25362 ^ 2)
    ((25000000000000000000/3983853644017216805703807))
    ((25000000000000000000/3983696564384537316029203)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25362) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25362 : ℝ)^2 / (mW 12681 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1019897/500000000000))/2) * ((1-firstRatio 25362) * √(1-firstRatio 25362) *
      sixthConstant (e1CovarianceRatio 25362 (mW 12681) (1/10^6) rowEps))) /
    (712/10000 - 25362*(1+1/10^6)*((1019897/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25362 (mW 12681) /
    ((1/10^5) * ((mW 12681 : ℝ)*25362*((mW 12681 : ℝ)+25362+1)))^2 +
  8*(mW 12681 : ℝ)*25362*(25362+2)*(25362+3) /
    ((1/1000)*((mW 12681 : ℝ)*25362*(25362+2)))^2 +
  covarianceVarianceBound 25362 (mW 12681) /
    ((1/1000)*covarianceMeanBound 25362 (mW 12681))^2 +
  normVarianceBound 25362 (mW 12681) / (3*inputVarianceMean 25362 (mW 12681))^2

end BstLean.Part268.WorldRow12681
namespace BstLean.Part268.WorldRow12682
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12682 = 229697950921207 := by
  have hu : mW 12682 ≤ 229697950921207 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12682 ≤ 229697950921206 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12682)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25364 ^ 2)
    ((12500000000000000000/1992083901641287892513827))
    ((25000000000000000000/3984010723649896295353049)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25364) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25364 : ℝ)^2 / (mW 12682 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2039631/1000000000000))/2) * ((1-firstRatio 25364) * √(1-firstRatio 25364) *
      sixthConstant (e1CovarianceRatio 25364 (mW 12682) (1/10^6) rowEps))) /
    (712/10000 - 25364*(1+1/10^6)*((2039631/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25364 (mW 12682) /
    ((1/10^5) * ((mW 12682 : ℝ)*25364*((mW 12682 : ℝ)+25364+1)))^2 +
  8*(mW 12682 : ℝ)*25364*(25364+2)*(25364+3) /
    ((1/1000)*((mW 12682 : ℝ)*25364*(25364+2)))^2 +
  covarianceVarianceBound 25364 (mW 12682) /
    ((1/1000)*covarianceMeanBound 25364 (mW 12682))^2 +
  normVarianceBound 25364 (mW 12682) / (3*inputVarianceMean 25364 (mW 12682))^2

end BstLean.Part268.WorldRow12682
namespace BstLean.Part268.WorldRow12683
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12683 = 229761349602164 := by
  have hu : mW 12683 ≤ 229761349602164 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12683 ≤ 229761349602163 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12683)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25366 ^ 2)
    ((25000000000000000000/3984481962547934764351501))
    ((5000000000000000000/796864976583051054935379)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25366) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25366 : ℝ)^2 / (mW 12683 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2039469/1000000000000))/2) * ((1-firstRatio 25366) * √(1-firstRatio 25366) *
      sixthConstant (e1CovarianceRatio 25366 (mW 12683) (1/10^6) rowEps))) /
    (712/10000 - 25366*(1+1/10^6)*((2039469/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25366 (mW 12683) /
    ((1/10^5) * ((mW 12683 : ℝ)*25366*((mW 12683 : ℝ)+25366+1)))^2 +
  8*(mW 12683 : ℝ)*25366*(25366+2)*(25366+3) /
    ((1/1000)*((mW 12683 : ℝ)*25366*(25366+2)))^2 +
  covarianceVarianceBound 25366 (mW 12683) /
    ((1/1000)*covarianceMeanBound 25366 (mW 12683))^2 +
  normVarianceBound 25366 (mW 12683) / (3*inputVarianceMean 25366 (mW 12683))^2

end BstLean.Part268.WorldRow12683
namespace BstLean.Part268.WorldRow12684
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12684 = 229824760781135 := by
  have hu : mW 12684 ≤ 229824760781135 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12684 ≤ 229824760781134 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12684)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25368 ^ 2)
    ((6250000000000000000/996199030453323435918837))
    ((25000000000000000000/3984639042180614254000741)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25368) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25368 : ℝ)^2 / (mW 12684 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1019653/500000000000))/2) * ((1-firstRatio 25368) * √(1-firstRatio 25368) *
      sixthConstant (e1CovarianceRatio 25368 (mW 12684) (1/10^6) rowEps))) /
    (712/10000 - 25368*(1+1/10^6)*((1019653/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25368 (mW 12684) /
    ((1/10^5) * ((mW 12684 : ℝ)*25368*((mW 12684 : ℝ)+25368+1)))^2 +
  8*(mW 12684 : ℝ)*25368*(25368+2)*(25368+3) /
    ((1/1000)*((mW 12684 : ℝ)*25368*(25368+2)))^2 +
  covarianceVarianceBound 25368 (mW 12684) /
    ((1/1000)*covarianceMeanBound 25368 (mW 12684))^2 +
  normVarianceBound 25368 (mW 12684) / (3*inputVarianceMean 25368 (mW 12684))^2

end BstLean.Part268.WorldRow12684
namespace BstLean.Part268.WorldRow12685
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12685 = 229888184459600 := by
  have hu : mW 12685 ≤ 229888184459600 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12685 ≤ 229888184459599 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12685)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25370 ^ 2)
    ((5000000000000000000/797022056215730544599839))
    ((25000000000000000000/3984953201445973233324587)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25370) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25370 : ℝ)^2 / (mW 12685 : ℝ)) * (1 + 1/10^6)^2 *
    √(((254893/125000000000))/2) * ((1-firstRatio 25370) * √(1-firstRatio 25370) *
      sixthConstant (e1CovarianceRatio 25370 (mW 12685) (1/10^6) rowEps))) /
    (712/10000 - 25370*(1+1/10^6)*((254893/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25370 (mW 12685) /
    ((1/10^5) * ((mW 12685 : ℝ)*25370*((mW 12685 : ℝ)+25370+1)))^2 +
  8*(mW 12685 : ℝ)*25370*(25370+2)*(25370+3) /
    ((1/1000)*((mW 12685 : ℝ)*25370*(25370+2)))^2 +
  covarianceVarianceBound 25370 (mW 12685) /
    ((1/1000)*covarianceMeanBound 25370 (mW 12685))^2 +
  normVarianceBound 25370 (mW 12685) / (3*inputVarianceMean 25370 (mW 12685))^2

end BstLean.Part268.WorldRow12685
namespace BstLean.Part268.WorldRow12686
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12686 = 229951620639036 := by
  have hu : mW 12686 ≤ 229951620639036 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12686 ≤ 229951620639035 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12686)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25372 ^ 2)
    ((12500000000000000000/1992712220172005851161521))
    ((25000000000000000000/3985267360711332212648433)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25372) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25372 : ℝ)^2 / (mW 12686 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2038981/1000000000000))/2) * ((1-firstRatio 25372) * √(1-firstRatio 25372) *
      sixthConstant (e1CovarianceRatio 25372 (mW 12686) (1/10^6) rowEps))) /
    (712/10000 - 25372*(1+1/10^6)*((2038981/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25372 (mW 12686) /
    ((1/10^5) * ((mW 12686 : ℝ)*25372*((mW 12686 : ℝ)+25372+1)))^2 +
  8*(mW 12686 : ℝ)*25372*(25372+2)*(25372+3) /
    ((1/1000)*((mW 12686 : ℝ)*25372*(25372+2)))^2 +
  covarianceVarianceBound 25372 (mW 12686) /
    ((1/1000)*covarianceMeanBound 25372 (mW 12686))^2 +
  normVarianceBound 25372 (mW 12686) / (3*inputVarianceMean 25372 (mW 12686))^2

end BstLean.Part268.WorldRow12686
namespace BstLean.Part268.WorldRow12687
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12687 = 230015069320921 := by
  have hu : mW 12687 ≤ 230015069320921 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12687 ≤ 230015069320920 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12687)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25374 ^ 2)
    ((25000000000000000000/3985738599609370681646889))
    ((25000000000000000000/3985581519976691191972279)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25374) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25374 : ℝ)^2 / (mW 12687 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2038819/1000000000000))/2) * ((1-firstRatio 25374) * √(1-firstRatio 25374) *
      sixthConstant (e1CovarianceRatio 25374 (mW 12687) (1/10^6) rowEps))) /
    (712/10000 - 25374*(1+1/10^6)*((2038819/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25374 (mW 12687) /
    ((1/10^5) * ((mW 12687 : ℝ)*25374*((mW 12687 : ℝ)+25374+1)))^2 +
  8*(mW 12687 : ℝ)*25374*(25374+2)*(25374+3) /
    ((1/1000)*((mW 12687 : ℝ)*25374*(25374+2)))^2 +
  covarianceVarianceBound 25374 (mW 12687) /
    ((1/1000)*covarianceMeanBound 25374 (mW 12687))^2 +
  normVarianceBound 25374 (mW 12687) / (3*inputVarianceMean 25374 (mW 12687))^2

end BstLean.Part268.WorldRow12687
namespace BstLean.Part268.WorldRow12688
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12688 = 230078530506735 := by
  have hu : mW 12688 ≤ 230078530506735 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12688 ≤ 230078530506734 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12688)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25376 ^ 2)
    ((1562500000000000000/249128297429670603810671))
    ((200000000000000000/31887165433936401370369)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25376) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25376 : ℝ)^2 / (mW 12688 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2038657/1000000000000))/2) * ((1-firstRatio 25376) * √(1-firstRatio 25376) *
      sixthConstant (e1CovarianceRatio 25376 (mW 12688) (1/10^6) rowEps))) /
    (712/10000 - 25376*(1+1/10^6)*((2038657/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25376 (mW 12688) /
    ((1/10^5) * ((mW 12688 : ℝ)*25376*((mW 12688 : ℝ)+25376+1)))^2 +
  8*(mW 12688 : ℝ)*25376*(25376+2)*(25376+3) /
    ((1/1000)*((mW 12688 : ℝ)*25376*(25376+2)))^2 +
  covarianceVarianceBound 25376 (mW 12688) /
    ((1/1000)*covarianceMeanBound 25376 (mW 12688))^2 +
  normVarianceBound 25376 (mW 12688) / (3*inputVarianceMean 25376 (mW 12688))^2

end BstLean.Part268.WorldRow12688
namespace BstLean.Part268.WorldRow12689
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12689 = 230142004197955 := by
  have hu : mW 12689 ≤ 230142004197955 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12689 ≤ 230142004197954 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12689)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25378 ^ 2)
    ((25000000000000000000/3986366918140088640294583))
    ((25000000000000000000/3986209838507409150619971)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25378) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25378 : ℝ)^2 / (mW 12689 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1019247/500000000000))/2) * ((1-firstRatio 25378) * √(1-firstRatio 25378) *
      sixthConstant (e1CovarianceRatio 25378 (mW 12689) (1/10^6) rowEps))) /
    (712/10000 - 25378*(1+1/10^6)*((1019247/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25378 (mW 12689) /
    ((1/10^5) * ((mW 12689 : ℝ)*25378*((mW 12689 : ℝ)+25378+1)))^2 +
  8*(mW 12689 : ℝ)*25378*(25378+2)*(25378+3) /
    ((1/1000)*((mW 12689 : ℝ)*25378*(25378+2)))^2 +
  covarianceVarianceBound 25378 (mW 12689) /
    ((1/1000)*covarianceMeanBound 25378 (mW 12689))^2 +
  normVarianceBound 25378 (mW 12689) / (3*inputVarianceMean 25378 (mW 12689))^2

end BstLean.Part268.WorldRow12689
namespace BstLean.Part268.WorldRow12690
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12690 = 230205490396059 := by
  have hu : mW 12690 ≤ 230205490396059 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12690 ≤ 230205490396058 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12690)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25380 ^ 2)
    ((2500000000000000000/398668107740544761961843))
    ((25000000000000000000/3986523997772768129943817)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25380) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25380 : ℝ)^2 / (mW 12690 : ℝ)) * (1 + 1/10^6)^2 *
    √(((509583/250000000000))/2) * ((1-firstRatio 25380) * √(1-firstRatio 25380) *
      sixthConstant (e1CovarianceRatio 25380 (mW 12690) (1/10^6) rowEps))) /
    (712/10000 - 25380*(1+1/10^6)*((509583/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25380 (mW 12690) /
    ((1/10^5) * ((mW 12690 : ℝ)*25380*((mW 12690 : ℝ)+25380+1)))^2 +
  8*(mW 12690 : ℝ)*25380*(25380+2)*(25380+3) /
    ((1/1000)*((mW 12690 : ℝ)*25380*(25380+2)))^2 +
  covarianceVarianceBound 25380 (mW 12690) /
    ((1/1000)*covarianceMeanBound 25380 (mW 12690))^2 +
  normVarianceBound 25380 (mW 12690) / (3*inputVarianceMean 25380 (mW 12690))^2

end BstLean.Part268.WorldRow12690
namespace BstLean.Part268.WorldRow12691
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12691 = 230268989102527 := by
  have hu : mW 12691 ≤ 230268989102527 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12691 ≤ 230268989102526 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12691)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25382 ^ 2)
    ((25000000000000000000/3986995236670806598942277))
    ((25000000000000000000/3986838157038127109267663)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25382) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25382 : ℝ)^2 / (mW 12691 : ℝ)) * (1 + 1/10^6)^2 *
    √(((203817/100000000000))/2) * ((1-firstRatio 25382) * √(1-firstRatio 25382) *
      sixthConstant (e1CovarianceRatio 25382 (mW 12691) (1/10^6) rowEps))) /
    (712/10000 - 25382*(1+1/10^6)*((203817/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25382 (mW 12691) /
    ((1/10^5) * ((mW 12691 : ℝ)*25382*((mW 12691 : ℝ)+25382+1)))^2 +
  8*(mW 12691 : ℝ)*25382*(25382+2)*(25382+3) /
    ((1/1000)*((mW 12691 : ℝ)*25382*(25382+2)))^2 +
  covarianceVarianceBound 25382 (mW 12691) /
    ((1/1000)*covarianceMeanBound 25382 (mW 12691))^2 +
  normVarianceBound 25382 (mW 12691) / (3*inputVarianceMean 25382 (mW 12691))^2

end BstLean.Part268.WorldRow12691
namespace BstLean.Part268.WorldRow12692
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12692 = 230332500318837 := by
  have hu : mW 12692 ≤ 230332500318837 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12692 ≤ 230332500318836 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12692)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25384 ^ 2)
    ((6250000000000000000/996827348984041394566531))
    ((25000000000000000000/3987152316303486088591509)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25384) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25384 : ℝ)^2 / (mW 12692 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2038007/1000000000000))/2) * ((1-firstRatio 25384) * √(1-firstRatio 25384) *
      sixthConstant (e1CovarianceRatio 25384 (mW 12692) (1/10^6) rowEps))) /
    (712/10000 - 25384*(1+1/10^6)*((2038007/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25384 (mW 12692) /
    ((1/10^5) * ((mW 12692 : ℝ)*25384*((mW 12692 : ℝ)+25384+1)))^2 +
  8*(mW 12692 : ℝ)*25384*(25384+2)*(25384+3) /
    ((1/1000)*((mW 12692 : ℝ)*25384*(25384+2)))^2 +
  covarianceVarianceBound 25384 (mW 12692) /
    ((1/1000)*covarianceMeanBound 25384 (mW 12692))^2 +
  normVarianceBound 25384 (mW 12692) / (3*inputVarianceMean 25384 (mW 12692))^2

end BstLean.Part268.WorldRow12692
namespace BstLean.Part268.WorldRow12693
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12693 = 230396024046467 := by
  have hu : mW 12693 ≤ 230396024046467 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12693 ≤ 230396024046466 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12693)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25386 ^ 2)
    ((25000000000000000000/3987623555201524557589971))
    ((5000000000000000000/797493295113769013583071)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25386) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25386 : ℝ)^2 / (mW 12693 : ℝ)) * (1 + 1/10^6)^2 *
    √(((407569/200000000000))/2) * ((1-firstRatio 25386) * √(1-firstRatio 25386) *
      sixthConstant (e1CovarianceRatio 25386 (mW 12693) (1/10^6) rowEps))) /
    (712/10000 - 25386*(1+1/10^6)*((407569/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25386 (mW 12693) /
    ((1/10^5) * ((mW 12693 : ℝ)*25386*((mW 12693 : ℝ)+25386+1)))^2 +
  8*(mW 12693 : ℝ)*25386*(25386+2)*(25386+3) /
    ((1/1000)*((mW 12693 : ℝ)*25386*(25386+2)))^2 +
  covarianceVarianceBound 25386 (mW 12693) /
    ((1/1000)*covarianceMeanBound 25386 (mW 12693))^2 +
  normVarianceBound 25386 (mW 12693) / (3*inputVarianceMean 25386 (mW 12693))^2

end BstLean.Part268.WorldRow12693
namespace BstLean.Part268.WorldRow12694
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12694 = 230459560286897 := by
  have hu : mW 12694 ≤ 230459560286897 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12694 ≤ 230459560286896 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12694)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25388 ^ 2)
    ((12500000000000000000/1993968857233441768456909))
    ((25000000000000000000/3987780634834204047239201)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25388) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25388 : ℝ)^2 / (mW 12694 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2037683/1000000000000))/2) * ((1-firstRatio 25388) * √(1-firstRatio 25388) *
      sixthConstant (e1CovarianceRatio 25388 (mW 12694) (1/10^6) rowEps))) /
    (712/10000 - 25388*(1+1/10^6)*((2037683/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25388 (mW 12694) /
    ((1/10^5) * ((mW 12694 : ℝ)*25388*((mW 12694 : ℝ)+25388+1)))^2 +
  8*(mW 12694 : ℝ)*25388*(25388+2)*(25388+3) /
    ((1/1000)*((mW 12694 : ℝ)*25388*(25388+2)))^2 +
  covarianceVarianceBound 25388 (mW 12694) /
    ((1/1000)*covarianceMeanBound 25388 (mW 12694))^2 +
  normVarianceBound 25388 (mW 12694) / (3*inputVarianceMean 25388 (mW 12694))^2

end BstLean.Part268.WorldRow12694
namespace BstLean.Part268.WorldRow12695
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12695 = 230523109041604 := by
  have hu : mW 12695 ≤ 230523109041604 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12695 ≤ 230523109041603 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12695)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25390 ^ 2)
    ((5000000000000000000/797650374746448503247533))
    ((25000000000000000000/3988094794099563026563047)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25390) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25390 : ℝ)^2 / (mW 12695 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2037521/1000000000000))/2) * ((1-firstRatio 25390) * √(1-firstRatio 25390) *
      sixthConstant (e1CovarianceRatio 25390 (mW 12695) (1/10^6) rowEps))) /
    (712/10000 - 25390*(1+1/10^6)*((2037521/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25390 (mW 12695) /
    ((1/10^5) * ((mW 12695 : ℝ)*25390*((mW 12695 : ℝ)+25390+1)))^2 +
  8*(mW 12695 : ℝ)*25390*(25390+2)*(25390+3) /
    ((1/1000)*((mW 12695 : ℝ)*25390*(25390+2)))^2 +
  covarianceVarianceBound 25390 (mW 12695) /
    ((1/1000)*covarianceMeanBound 25390 (mW 12695))^2 +
  normVarianceBound 25390 (mW 12695) / (3*inputVarianceMean 25390 (mW 12695))^2

end BstLean.Part268.WorldRow12695
namespace BstLean.Part268.WorldRow12696
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12696 = 230586670312068 := by
  have hu : mW 12696 ≤ 230586670312068 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12696 ≤ 230586670312067 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12696)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25392 ^ 2)
    ((3125000000000000000/498570754124700186945189))
    ((25000000000000000000/3988408953364922005886893)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25392) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25392 : ℝ)^2 / (mW 12696 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2037359/1000000000000))/2) * ((1-firstRatio 25392) * √(1-firstRatio 25392) *
      sixthConstant (e1CovarianceRatio 25392 (mW 12696) (1/10^6) rowEps))) /
    (712/10000 - 25392*(1+1/10^6)*((2037359/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25392 (mW 12696) /
    ((1/10^5) * ((mW 12696 : ℝ)*25392*((mW 12696 : ℝ)+25392+1)))^2 +
  8*(mW 12696 : ℝ)*25392*(25392+2)*(25392+3) /
    ((1/1000)*((mW 12696 : ℝ)*25392*(25392+2)))^2 +
  covarianceVarianceBound 25392 (mW 12696) /
    ((1/1000)*covarianceMeanBound 25392 (mW 12696))^2 +
  normVarianceBound 25392 (mW 12696) / (3*inputVarianceMean 25392 (mW 12696))^2

end BstLean.Part268.WorldRow12696
namespace BstLean.Part268.WorldRow12697
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12697 = 230650244099768 := by
  have hu : mW 12697 ≤ 230650244099768 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12697 ≤ 230650244099767 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12697)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25394 ^ 2)
    ((25000000000000000000/3988880192262960474885359))
    ((25000000000000000000/3988723112630280985210739)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25394) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25394 : ℝ)^2 / (mW 12697 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2037197/1000000000000))/2) * ((1-firstRatio 25394) * √(1-firstRatio 25394) *
      sixthConstant (e1CovarianceRatio 25394 (mW 12697) (1/10^6) rowEps))) /
    (712/10000 - 25394*(1+1/10^6)*((2037197/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25394 (mW 12697) /
    ((1/10^5) * ((mW 12697 : ℝ)*25394*((mW 12697 : ℝ)+25394+1)))^2 +
  8*(mW 12697 : ℝ)*25394*(25394+2)*(25394+3) /
    ((1/1000)*((mW 12697 : ℝ)*25394*(25394+2)))^2 +
  covarianceVarianceBound 25394 (mW 12697) /
    ((1/1000)*covarianceMeanBound 25394 (mW 12697))^2 +
  normVarianceBound 25394 (mW 12697) / (3*inputVarianceMean 25394 (mW 12697))^2

end BstLean.Part268.WorldRow12697
namespace BstLean.Part268.WorldRow12698
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12698 = 230713830406182 := by
  have hu : mW 12698 ≤ 230713830406182 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12698 ≤ 230713830406181 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12698)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25396 ^ 2)
    ((12500000000000000000/1994597175764159727104603))
    ((5000000000000000000/797807454379127992906917)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25396) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25396 : ℝ)^2 / (mW 12698 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1018517/500000000000))/2) * ((1-firstRatio 25396) * √(1-firstRatio 25396) *
      sixthConstant (e1CovarianceRatio 25396 (mW 12698) (1/10^6) rowEps))) /
    (712/10000 - 25396*(1+1/10^6)*((1018517/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25396 (mW 12698) /
    ((1/10^5) * ((mW 12698 : ℝ)*25396*((mW 12698 : ℝ)+25396+1)))^2 +
  8*(mW 12698 : ℝ)*25396*(25396+2)*(25396+3) /
    ((1/1000)*((mW 12698 : ℝ)*25396*(25396+2)))^2 +
  covarianceVarianceBound 25396 (mW 12698) /
    ((1/1000)*covarianceMeanBound 25396 (mW 12698))^2 +
  normVarianceBound 25396 (mW 12698) / (3*inputVarianceMean 25396 (mW 12698))^2

end BstLean.Part268.WorldRow12698
namespace BstLean.Part268.WorldRow12699
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12699 = 230777429232789 := by
  have hu : mW 12699 ≤ 230777429232789 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12699 ≤ 230777429232788 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12699)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25398 ^ 2)
    ((25000000000000000000/3989508510793678433533053))
    ((25000000000000000000/3989351431160998943858431)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25398) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25398 : ℝ)^2 / (mW 12699 : ℝ)) * (1 + 1/10^6)^2 *
    √(((254609/125000000000))/2) * ((1-firstRatio 25398) * √(1-firstRatio 25398) *
      sixthConstant (e1CovarianceRatio 25398 (mW 12699) (1/10^6) rowEps))) /
    (712/10000 - 25398*(1+1/10^6)*((254609/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25398 (mW 12699) /
    ((1/10^5) * ((mW 12699 : ℝ)*25398*((mW 12699 : ℝ)+25398+1)))^2 +
  8*(mW 12699 : ℝ)*25398*(25398+2)*(25398+3) /
    ((1/1000)*((mW 12699 : ℝ)*25398*(25398+2)))^2 +
  covarianceVarianceBound 25398 (mW 12699) /
    ((1/1000)*covarianceMeanBound 25398 (mW 12699))^2 +
  normVarianceBound 25398 (mW 12699) / (3*inputVarianceMean 25398 (mW 12699))^2

end BstLean.Part268.WorldRow12699
