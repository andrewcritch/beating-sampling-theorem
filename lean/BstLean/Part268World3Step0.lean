import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar3
namespace BstLean.Part268.WorldRow12425
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12425 = 213814616692336 := by
  have hu : mW 12425 ≤ 213814616692336 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12425 ≤ 213814616692335 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12425)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24850 ^ 2)
    ((1000000000000000000/156137154883412723951959))
    ((25000000000000000000/3903271792452638609124627)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24850) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24850 : ℝ)^2 / (mW 12425 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2082273/1000000000000))/2) * ((1-firstRatio 24850) * √(1-firstRatio 24850) *
      sixthConstant (e1CovarianceRatio 24850 (mW 12425) (1/10^6) rowEps))) /
    (712/10000 - 24850*(1+1/10^6)*((2082273/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24850 (mW 12425) /
    ((1/10^5) * ((mW 12425 : ℝ)*24850*((mW 12425 : ℝ)+24850+1)))^2 +
  8*(mW 12425 : ℝ)*24850*(24850+2)*(24850+3) /
    ((1/1000)*((mW 12425 : ℝ)*24850*(24850+2)))^2 +
  covarianceVarianceBound 24850 (mW 12425) /
    ((1/1000)*covarianceMeanBound 24850 (mW 12425))^2 +
  normVarianceBound 24850 (mW 12425) / (3*inputVarianceMean 24850 (mW 12425))^2

end BstLean.Part268.WorldRow12425
namespace BstLean.Part268.WorldRow12426
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12426 = 213874852221373 := by
  have hu : mW 12426 ≤ 213874852221373 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12426 ≤ 213874852221372 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12426)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24852 ^ 2)
    ((12500000000000000000/1951871515675338539061411))
    ((25000000000000000000/3903585951717997588448473)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24852) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24852 : ℝ)^2 / (mW 12426 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2082103/1000000000000))/2) * ((1-firstRatio 24852) * √(1-firstRatio 24852) *
      sixthConstant (e1CovarianceRatio 24852 (mW 12426) (1/10^6) rowEps))) /
    (712/10000 - 24852*(1+1/10^6)*((2082103/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24852 (mW 12426) /
    ((1/10^5) * ((mW 12426 : ℝ)*24852*((mW 12426 : ℝ)+24852+1)))^2 +
  8*(mW 12426 : ℝ)*24852*(24852+2)*(24852+3) /
    ((1/1000)*((mW 12426 : ℝ)*24852*(24852+2)))^2 +
  covarianceVarianceBound 24852 (mW 12426) /
    ((1/1000)*covarianceMeanBound 24852 (mW 12426))^2 +
  normVarianceBound 24852 (mW 12426) / (3*inputVarianceMean 24852 (mW 12426))^2

end BstLean.Part268.WorldRow12426
namespace BstLean.Part268.WorldRow12427
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12427 = 213935099870479 := by
  have hu : mW 12427 ≤ 213935099870479 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12427 ≤ 213935099870478 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12427)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24854 ^ 2)
    ((25000000000000000000/3904057190616036057446669))
    ((25000000000000000000/3903900110983356567772319)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24854) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24854 : ℝ)^2 / (mW 12427 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1040967/500000000000))/2) * ((1-firstRatio 24854) * √(1-firstRatio 24854) *
      sixthConstant (e1CovarianceRatio 24854 (mW 12427) (1/10^6) rowEps))) /
    (712/10000 - 24854*(1+1/10^6)*((1040967/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24854 (mW 12427) /
    ((1/10^5) * ((mW 12427 : ℝ)*24854*((mW 12427 : ℝ)+24854+1)))^2 +
  8*(mW 12427 : ℝ)*24854*(24854+2)*(24854+3) /
    ((1/1000)*((mW 12427 : ℝ)*24854*(24854+2)))^2 +
  covarianceVarianceBound 24854 (mW 12427) /
    ((1/1000)*covarianceMeanBound 24854 (mW 12427))^2 +
  normVarianceBound 24854 (mW 12427) / (3*inputVarianceMean 24854 (mW 12427))^2

end BstLean.Part268.WorldRow12427
namespace BstLean.Part268.WorldRow12428
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12428 = 213995359641117 := by
  have hu : mW 12428 ≤ 213995359641117 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12428 ≤ 213995359641116 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12428)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24856 ^ 2)
    ((6250000000000000000/976092837470348759192629))
    ((5000000000000000000/780842854049743109419233)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24856) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24856 : ℝ)^2 / (mW 12428 : ℝ)) * (1 + 1/10^6)^2 *
    √(((416353/200000000000))/2) * ((1-firstRatio 24856) * √(1-firstRatio 24856) *
      sixthConstant (e1CovarianceRatio 24856 (mW 12428) (1/10^6) rowEps))) /
    (712/10000 - 24856*(1+1/10^6)*((416353/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24856 (mW 12428) /
    ((1/10^5) * ((mW 12428 : ℝ)*24856*((mW 12428 : ℝ)+24856+1)))^2 +
  8*(mW 12428 : ℝ)*24856*(24856+2)*(24856+3) /
    ((1/1000)*((mW 12428 : ℝ)*24856*(24856+2)))^2 +
  covarianceVarianceBound 24856 (mW 12428) /
    ((1/1000)*covarianceMeanBound 24856 (mW 12428))^2 +
  normVarianceBound 24856 (mW 12428) / (3*inputVarianceMean 24856 (mW 12428))^2

end BstLean.Part268.WorldRow12428
namespace BstLean.Part268.WorldRow12429
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12429 = 214055631534749 := by
  have hu : mW 12429 ≤ 214055631534749 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12429 ≤ 214055631534748 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12429)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24858 ^ 2)
    ((25000000000000000000/3904685509146754016094363))
    ((25000000000000000000/3904528429514074526420011)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24858) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24858 : ℝ)^2 / (mW 12429 : ℝ)) * (1 + 1/10^6)^2 *
    √(((416319/200000000000))/2) * ((1-firstRatio 24858) * √(1-firstRatio 24858) *
      sixthConstant (e1CovarianceRatio 24858 (mW 12429) (1/10^6) rowEps))) /
    (712/10000 - 24858*(1+1/10^6)*((416319/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24858 (mW 12429) /
    ((1/10^5) * ((mW 12429 : ℝ)*24858*((mW 12429 : ℝ)+24858+1)))^2 +
  8*(mW 12429 : ℝ)*24858*(24858+2)*(24858+3) /
    ((1/1000)*((mW 12429 : ℝ)*24858*(24858+2)))^2 +
  covarianceVarianceBound 24858 (mW 12429) /
    ((1/1000)*covarianceMeanBound 24858 (mW 12429))^2 +
  normVarianceBound 24858 (mW 12429) / (3*inputVarianceMean 24858 (mW 12429))^2

end BstLean.Part268.WorldRow12429
namespace BstLean.Part268.WorldRow12430
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12430 = 214115915552840 := by
  have hu : mW 12430 ≤ 214115915552840 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12430 ≤ 214115915552839 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12430)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24860 ^ 2)
    ((2500000000000000000/390499966841211299541821))
    ((25000000000000000000/3904842588779433505743857)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24860) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24860 : ℝ)^2 / (mW 12430 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1040713/500000000000))/2) * ((1-firstRatio 24860) * √(1-firstRatio 24860) *
      sixthConstant (e1CovarianceRatio 24860 (mW 12430) (1/10^6) rowEps))) /
    (712/10000 - 24860*(1+1/10^6)*((1040713/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24860 (mW 12430) /
    ((1/10^5) * ((mW 12430 : ℝ)*24860*((mW 12430 : ℝ)+24860+1)))^2 +
  8*(mW 12430 : ℝ)*24860*(24860+2)*(24860+3) /
    ((1/1000)*((mW 12430 : ℝ)*24860*(24860+2)))^2 +
  covarianceVarianceBound 24860 (mW 12430) /
    ((1/1000)*covarianceMeanBound 24860 (mW 12430))^2 +
  normVarianceBound 24860 (mW 12430) / (3*inputVarianceMean 24860 (mW 12430))^2

end BstLean.Part268.WorldRow12430
namespace BstLean.Part268.WorldRow12431
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12431 = 214176211696852 := by
  have hu : mW 12431 ≤ 214176211696852 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12431 ≤ 214176211696851 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12431)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24862 ^ 2)
    ((25000000000000000000/3905313827677471974742057))
    ((25000000000000000000/3905156748044792485067703)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24862) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24862 : ℝ)^2 / (mW 12431 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2081257/1000000000000))/2) * ((1-firstRatio 24862) * √(1-firstRatio 24862) *
      sixthConstant (e1CovarianceRatio 24862 (mW 12431) (1/10^6) rowEps))) /
    (712/10000 - 24862*(1+1/10^6)*((2081257/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24862 (mW 12431) /
    ((1/10^5) * ((mW 12431 : ℝ)*24862*((mW 12431 : ℝ)+24862+1)))^2 +
  8*(mW 12431 : ℝ)*24862*(24862+2)*(24862+3) /
    ((1/1000)*((mW 12431 : ℝ)*24862*(24862+2)))^2 +
  covarianceVarianceBound 24862 (mW 12431) /
    ((1/1000)*covarianceMeanBound 24862 (mW 12431))^2 +
  normVarianceBound 24862 (mW 12431) / (3*inputVarianceMean 24862 (mW 12431))^2

end BstLean.Part268.WorldRow12431
namespace BstLean.Part268.WorldRow12432
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12432 = 214236519968248 := by
  have hu : mW 12432 ≤ 214236519968248 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12432 ≤ 214236519968247 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12432)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24864 ^ 2)
    ((1562500000000000000/244101749183926934629119))
    ((25000000000000000000/3905470907310151464391549)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24864) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24864 : ℝ)^2 / (mW 12432 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2081087/1000000000000))/2) * ((1-firstRatio 24864) * √(1-firstRatio 24864) *
      sixthConstant (e1CovarianceRatio 24864 (mW 12432) (1/10^6) rowEps))) /
    (712/10000 - 24864*(1+1/10^6)*((2081087/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24864 (mW 12432) /
    ((1/10^5) * ((mW 12432 : ℝ)*24864*((mW 12432 : ℝ)+24864+1)))^2 +
  8*(mW 12432 : ℝ)*24864*(24864+2)*(24864+3) /
    ((1/1000)*((mW 12432 : ℝ)*24864*(24864+2)))^2 +
  covarianceVarianceBound 24864 (mW 12432) /
    ((1/1000)*covarianceMeanBound 24864 (mW 12432))^2 +
  normVarianceBound 24864 (mW 12432) / (3*inputVarianceMean 24864 (mW 12432))^2

end BstLean.Part268.WorldRow12432
namespace BstLean.Part268.WorldRow12433
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12433 = 214296840368493 := by
  have hu : mW 12433 ≤ 214296840368493 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12433 ≤ 214296840368492 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12433)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24866 ^ 2)
    ((25000000000000000000/3905942146208189933389751))
    ((5000000000000000000/781157013315102088743079)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24866) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24866 : ℝ)^2 / (mW 12433 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1040459/500000000000))/2) * ((1-firstRatio 24866) * √(1-firstRatio 24866) *
      sixthConstant (e1CovarianceRatio 24866 (mW 12433) (1/10^6) rowEps))) /
    (712/10000 - 24866*(1+1/10^6)*((1040459/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24866 (mW 12433) /
    ((1/10^5) * ((mW 12433 : ℝ)*24866*((mW 12433 : ℝ)+24866+1)))^2 +
  8*(mW 12433 : ℝ)*24866*(24866+2)*(24866+3) /
    ((1/1000)*((mW 12433 : ℝ)*24866*(24866+2)))^2 +
  covarianceVarianceBound 24866 (mW 12433) /
    ((1/1000)*covarianceMeanBound 24866 (mW 12433))^2 +
  normVarianceBound 24866 (mW 12433) / (3*inputVarianceMean 24866 (mW 12433))^2

end BstLean.Part268.WorldRow12433
namespace BstLean.Part268.WorldRow12434
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12434 = 214357172899049 := by
  have hu : mW 12434 ≤ 214357172899049 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12434 ≤ 214357172899048 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12434)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24868 ^ 2)
    ((12500000000000000000/1953128152736774456356799))
    ((25000000000000000000/3906099225840869423039241)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24868) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24868 : ℝ)^2 / (mW 12434 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2080749/1000000000000))/2) * ((1-firstRatio 24868) * √(1-firstRatio 24868) *
      sixthConstant (e1CovarianceRatio 24868 (mW 12434) (1/10^6) rowEps))) /
    (712/10000 - 24868*(1+1/10^6)*((2080749/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24868 (mW 12434) /
    ((1/10^5) * ((mW 12434 : ℝ)*24868*((mW 12434 : ℝ)+24868+1)))^2 +
  8*(mW 12434 : ℝ)*24868*(24868+2)*(24868+3) /
    ((1/1000)*((mW 12434 : ℝ)*24868*(24868+2)))^2 +
  covarianceVarianceBound 24868 (mW 12434) /
    ((1/1000)*covarianceMeanBound 24868 (mW 12434))^2 +
  normVarianceBound 24868 (mW 12434) / (3*inputVarianceMean 24868 (mW 12434))^2

end BstLean.Part268.WorldRow12434
namespace BstLean.Part268.WorldRow12435
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12435 = 214417517561380 := by
  have hu : mW 12435 ≤ 214417517561380 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12435 ≤ 214417517561379 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12435)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24870 ^ 2)
    ((5000000000000000000/781314092947781578407489))
    ((25000000000000000000/3906413385106228402363087)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24870) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24870 : ℝ)^2 / (mW 12435 : ℝ)) * (1 + 1/10^6)^2 *
    √(((104029/50000000000))/2) * ((1-firstRatio 24870) * √(1-firstRatio 24870) *
      sixthConstant (e1CovarianceRatio 24870 (mW 12435) (1/10^6) rowEps))) /
    (712/10000 - 24870*(1+1/10^6)*((104029/50000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24870 (mW 12435) /
    ((1/10^5) * ((mW 12435 : ℝ)*24870*((mW 12435 : ℝ)+24870+1)))^2 +
  8*(mW 12435 : ℝ)*24870*(24870+2)*(24870+3) /
    ((1/1000)*((mW 12435 : ℝ)*24870*(24870+2)))^2 +
  covarianceVarianceBound 24870 (mW 12435) /
    ((1/1000)*covarianceMeanBound 24870 (mW 12435))^2 +
  normVarianceBound 24870 (mW 12435) / (3*inputVarianceMean 24870 (mW 12435))^2

end BstLean.Part268.WorldRow12435
namespace BstLean.Part268.WorldRow12436
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12436 = 214477874356950 := by
  have hu : mW 12436 ≤ 214477874356950 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12436 ≤ 214477874356949 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12436)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24872 ^ 2)
    ((6250000000000000000/976721156001066717840323))
    ((25000000000000000000/3906727544371587381686933)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24872) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24872 : ℝ)^2 / (mW 12436 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2080411/1000000000000))/2) * ((1-firstRatio 24872) * √(1-firstRatio 24872) *
      sixthConstant (e1CovarianceRatio 24872 (mW 12436) (1/10^6) rowEps))) /
    (712/10000 - 24872*(1+1/10^6)*((2080411/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24872 (mW 12436) /
    ((1/10^5) * ((mW 12436 : ℝ)*24872*((mW 12436 : ℝ)+24872+1)))^2 +
  8*(mW 12436 : ℝ)*24872*(24872+2)*(24872+3) /
    ((1/1000)*((mW 12436 : ℝ)*24872*(24872+2)))^2 +
  covarianceVarianceBound 24872 (mW 12436) /
    ((1/1000)*covarianceMeanBound 24872 (mW 12436))^2 +
  normVarianceBound 24872 (mW 12436) / (3*inputVarianceMean 24872 (mW 12436))^2

end BstLean.Part268.WorldRow12436
namespace BstLean.Part268.WorldRow12437
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12437 = 214538243287222 := by
  have hu : mW 12437 ≤ 214538243287222 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12437 ≤ 214538243287221 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12437)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24874 ^ 2)
    ((25000000000000000000/3907198783269625850685139))
    ((25000000000000000000/3907041703636946361010779)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24874) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24874 : ℝ)^2 / (mW 12437 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1040121/500000000000))/2) * ((1-firstRatio 24874) * √(1-firstRatio 24874) *
      sixthConstant (e1CovarianceRatio 24874 (mW 12437) (1/10^6) rowEps))) /
    (712/10000 - 24874*(1+1/10^6)*((1040121/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24874 (mW 12437) /
    ((1/10^5) * ((mW 12437 : ℝ)*24874*((mW 12437 : ℝ)+24874+1)))^2 +
  8*(mW 12437 : ℝ)*24874*(24874+2)*(24874+3) /
    ((1/1000)*((mW 12437 : ℝ)*24874*(24874+2)))^2 +
  covarianceVarianceBound 24874 (mW 12437) /
    ((1/1000)*covarianceMeanBound 24874 (mW 12437))^2 +
  normVarianceBound 24874 (mW 12437) / (3*inputVarianceMean 24874 (mW 12437))^2

end BstLean.Part268.WorldRow12437
namespace BstLean.Part268.WorldRow12438
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12438 = 214598624353659 := by
  have hu : mW 12438 ≤ 214598624353659 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12438 ≤ 214598624353658 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12438)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24876 ^ 2)
    ((12500000000000000000/1953756471267492415004493))
    ((200000000000000000/31258846903218442722677)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24876) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24876 : ℝ)^2 / (mW 12438 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2080073/1000000000000))/2) * ((1-firstRatio 24876) * √(1-firstRatio 24876) *
      sixthConstant (e1CovarianceRatio 24876 (mW 12438) (1/10^6) rowEps))) /
    (712/10000 - 24876*(1+1/10^6)*((2080073/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24876 (mW 12438) /
    ((1/10^5) * ((mW 12438 : ℝ)*24876*((mW 12438 : ℝ)+24876+1)))^2 +
  8*(mW 12438 : ℝ)*24876*(24876+2)*(24876+3) /
    ((1/1000)*((mW 12438 : ℝ)*24876*(24876+2)))^2 +
  covarianceVarianceBound 24876 (mW 12438) /
    ((1/1000)*covarianceMeanBound 24876 (mW 12438))^2 +
  normVarianceBound 24876 (mW 12438) / (3*inputVarianceMean 24876 (mW 12438))^2

end BstLean.Part268.WorldRow12438
namespace BstLean.Part268.WorldRow12439
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12439 = 214659017557727 := by
  have hu : mW 12439 ≤ 214659017557727 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12439 ≤ 214659017557726 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12439)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24878 ^ 2)
    ((25000000000000000000/3907827101800343809332833))
    ((25000000000000000000/3907670022167664319658471)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24878) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24878 : ℝ)^2 / (mW 12439 : ℝ)) * (1 + 1/10^6)^2 *
    √(((64997/31250000000))/2) * ((1-firstRatio 24878) * √(1-firstRatio 24878) *
      sixthConstant (e1CovarianceRatio 24878 (mW 12439) (1/10^6) rowEps))) /
    (712/10000 - 24878*(1+1/10^6)*((64997/31250000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24878 (mW 12439) /
    ((1/10^5) * ((mW 12439 : ℝ)*24878*((mW 12439 : ℝ)+24878+1)))^2 +
  8*(mW 12439 : ℝ)*24878*(24878+2)*(24878+3) /
    ((1/1000)*((mW 12439 : ℝ)*24878*(24878+2)))^2 +
  covarianceVarianceBound 24878 (mW 12439) /
    ((1/1000)*covarianceMeanBound 24878 (mW 12439))^2 +
  normVarianceBound 24878 (mW 12439) / (3*inputVarianceMean 24878 (mW 12439))^2

end BstLean.Part268.WorldRow12439
namespace BstLean.Part268.WorldRow12440
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12440 = 214719422900888 := by
  have hu : mW 12440 ≤ 214719422900888 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12440 ≤ 214719422900887 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12440)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24880 ^ 2)
    ((625000000000000000/97703531526642569716417))
    ((25000000000000000000/3907984181433023298982317)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24880) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24880 : ℝ)^2 / (mW 12440 : ℝ)) * (1 + 1/10^6)^2 *
    √(((415947/200000000000))/2) * ((1-firstRatio 24880) * √(1-firstRatio 24880) *
      sixthConstant (e1CovarianceRatio 24880 (mW 12440) (1/10^6) rowEps))) /
    (712/10000 - 24880*(1+1/10^6)*((415947/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24880 (mW 12440) /
    ((1/10^5) * ((mW 12440 : ℝ)*24880*((mW 12440 : ℝ)+24880+1)))^2 +
  8*(mW 12440 : ℝ)*24880*(24880+2)*(24880+3) /
    ((1/1000)*((mW 12440 : ℝ)*24880*(24880+2)))^2 +
  covarianceVarianceBound 24880 (mW 12440) /
    ((1/1000)*covarianceMeanBound 24880 (mW 12440))^2 +
  normVarianceBound 24880 (mW 12440) / (3*inputVarianceMean 24880 (mW 12440))^2

end BstLean.Part268.WorldRow12440
namespace BstLean.Part268.WorldRow12441
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12441 = 214779840384606 := by
  have hu : mW 12441 ≤ 214779840384606 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12441 ≤ 214779840384605 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12441)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24882 ^ 2)
    ((25000000000000000000/3908455420331061767980527))
    ((25000000000000000000/3908298340698382278306163)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24882) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24882 : ℝ)^2 / (mW 12441 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1039783/500000000000))/2) * ((1-firstRatio 24882) * √(1-firstRatio 24882) *
      sixthConstant (e1CovarianceRatio 24882 (mW 12441) (1/10^6) rowEps))) /
    (712/10000 - 24882*(1+1/10^6)*((1039783/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24882 (mW 12441) /
    ((1/10^5) * ((mW 12441 : ℝ)*24882*((mW 12441 : ℝ)+24882+1)))^2 +
  8*(mW 12441 : ℝ)*24882*(24882+2)*(24882+3) /
    ((1/1000)*((mW 12441 : ℝ)*24882*(24882+2)))^2 +
  covarianceVarianceBound 24882 (mW 12441) /
    ((1/1000)*covarianceMeanBound 24882 (mW 12441))^2 +
  normVarianceBound 24882 (mW 12441) / (3*inputVarianceMean 24882 (mW 12441))^2

end BstLean.Part268.WorldRow12441
namespace BstLean.Part268.WorldRow12442
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12442 = 214840270010345 := by
  have hu : mW 12442 ≤ 214840270010345 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12442 ≤ 214840270010344 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12442)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24884 ^ 2)
    ((12500000000000000000/1954384789798210373652187))
    ((25000000000000000000/3908612499963741257630009)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24884) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24884 : ℝ)^2 / (mW 12442 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2079397/1000000000000))/2) * ((1-firstRatio 24884) * √(1-firstRatio 24884) *
      sixthConstant (e1CovarianceRatio 24884 (mW 12442) (1/10^6) rowEps))) /
    (712/10000 - 24884*(1+1/10^6)*((2079397/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24884 (mW 12442) /
    ((1/10^5) * ((mW 12442 : ℝ)*24884*((mW 12442 : ℝ)+24884+1)))^2 +
  8*(mW 12442 : ℝ)*24884*(24884+2)*(24884+3) /
    ((1/1000)*((mW 12442 : ℝ)*24884*(24884+2)))^2 +
  covarianceVarianceBound 24884 (mW 12442) /
    ((1/1000)*covarianceMeanBound 24884 (mW 12442))^2 +
  normVarianceBound 24884 (mW 12442) / (3*inputVarianceMean 24884 (mW 12442))^2

end BstLean.Part268.WorldRow12442
namespace BstLean.Part268.WorldRow12443
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12443 = 214900711779570 := by
  have hu : mW 12443 ≤ 214900711779570 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12443 ≤ 214900711779569 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12443)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24886 ^ 2)
    ((25000000000000000000/3909083738861779726628221))
    ((5000000000000000000/781785331845820047390771)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24886) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24886 : ℝ)^2 / (mW 12443 : ℝ)) * (1 + 1/10^6)^2 *
    √(((519807/250000000000))/2) * ((1-firstRatio 24886) * √(1-firstRatio 24886) *
      sixthConstant (e1CovarianceRatio 24886 (mW 12443) (1/10^6) rowEps))) /
    (712/10000 - 24886*(1+1/10^6)*((519807/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24886 (mW 12443) /
    ((1/10^5) * ((mW 12443 : ℝ)*24886*((mW 12443 : ℝ)+24886+1)))^2 +
  8*(mW 12443 : ℝ)*24886*(24886+2)*(24886+3) /
    ((1/1000)*((mW 12443 : ℝ)*24886*(24886+2)))^2 +
  covarianceVarianceBound 24886 (mW 12443) /
    ((1/1000)*covarianceMeanBound 24886 (mW 12443))^2 +
  normVarianceBound 24886 (mW 12443) / (3*inputVarianceMean 24886 (mW 12443))^2

end BstLean.Part268.WorldRow12443
namespace BstLean.Part268.WorldRow12444
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12444 = 214961165693744 := by
  have hu : mW 12444 ≤ 214961165693744 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12444 ≤ 214961165693743 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12444)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24888 ^ 2)
    ((6250000000000000000/977349474531784676488017))
    ((25000000000000000000/3909240818494459216277701)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24888) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24888 : ℝ)^2 / (mW 12444 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2079059/1000000000000))/2) * ((1-firstRatio 24888) * √(1-firstRatio 24888) *
      sixthConstant (e1CovarianceRatio 24888 (mW 12444) (1/10^6) rowEps))) /
    (712/10000 - 24888*(1+1/10^6)*((2079059/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24888 (mW 12444) /
    ((1/10^5) * ((mW 12444 : ℝ)*24888*((mW 12444 : ℝ)+24888+1)))^2 +
  8*(mW 12444 : ℝ)*24888*(24888+2)*(24888+3) /
    ((1/1000)*((mW 12444 : ℝ)*24888*(24888+2)))^2 +
  covarianceVarianceBound 24888 (mW 12444) /
    ((1/1000)*covarianceMeanBound 24888 (mW 12444))^2 +
  normVarianceBound 24888 (mW 12444) / (3*inputVarianceMean 24888 (mW 12444))^2

end BstLean.Part268.WorldRow12444
namespace BstLean.Part268.WorldRow12445
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12445 = 215021631754331 := by
  have hu : mW 12445 ≤ 215021631754331 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12445 ≤ 215021631754330 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12445)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24890 ^ 2)
    ((5000000000000000000/781942411478499537055183))
    ((25000000000000000000/3909554977759818195601547)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24890) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24890 : ℝ)^2 / (mW 12445 : ℝ)) * (1 + 1/10^6)^2 *
    √(((207889/100000000000))/2) * ((1-firstRatio 24890) * √(1-firstRatio 24890) *
      sixthConstant (e1CovarianceRatio 24890 (mW 12445) (1/10^6) rowEps))) /
    (712/10000 - 24890*(1+1/10^6)*((207889/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24890 (mW 12445) /
    ((1/10^5) * ((mW 12445 : ℝ)*24890*((mW 12445 : ℝ)+24890+1)))^2 +
  8*(mW 12445 : ℝ)*24890*(24890+2)*(24890+3) /
    ((1/1000)*((mW 12445 : ℝ)*24890*(24890+2)))^2 +
  covarianceVarianceBound 24890 (mW 12445) /
    ((1/1000)*covarianceMeanBound 24890 (mW 12445))^2 +
  normVarianceBound 24890 (mW 12445) / (3*inputVarianceMean 24890 (mW 12445))^2

end BstLean.Part268.WorldRow12445
namespace BstLean.Part268.WorldRow12446
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12446 = 215082109962796 := by
  have hu : mW 12446 ≤ 215082109962796 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12446 ≤ 215082109962795 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12446)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24892 ^ 2)
    ((12500000000000000000/1955013108328928332299881))
    ((25000000000000000000/3909869137025177174925393)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24892) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24892 : ℝ)^2 / (mW 12446 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2078721/1000000000000))/2) * ((1-firstRatio 24892) * √(1-firstRatio 24892) *
      sixthConstant (e1CovarianceRatio 24892 (mW 12446) (1/10^6) rowEps))) /
    (712/10000 - 24892*(1+1/10^6)*((2078721/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24892 (mW 12446) /
    ((1/10^5) * ((mW 12446 : ℝ)*24892*((mW 12446 : ℝ)+24892+1)))^2 +
  8*(mW 12446 : ℝ)*24892*(24892+2)*(24892+3) /
    ((1/1000)*((mW 12446 : ℝ)*24892*(24892+2)))^2 +
  covarianceVarianceBound 24892 (mW 12446) /
    ((1/1000)*covarianceMeanBound 24892 (mW 12446))^2 +
  normVarianceBound 24892 (mW 12446) / (3*inputVarianceMean 24892 (mW 12446))^2

end BstLean.Part268.WorldRow12446
namespace BstLean.Part268.WorldRow12447
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12447 = 215142600320603 := by
  have hu : mW 12447 ≤ 215142600320603 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12447 ≤ 215142600320602 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12447)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24894 ^ 2)
    ((25000000000000000000/3910340375923215643923609))
    ((25000000000000000000/3910183296290536154249239)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24894) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24894 : ℝ)^2 / (mW 12447 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2078553/1000000000000))/2) * ((1-firstRatio 24894) * √(1-firstRatio 24894) *
      sixthConstant (e1CovarianceRatio 24894 (mW 12447) (1/10^6) rowEps))) /
    (712/10000 - 24894*(1+1/10^6)*((2078553/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24894 (mW 12447) /
    ((1/10^5) * ((mW 12447 : ℝ)*24894*((mW 12447 : ℝ)+24894+1)))^2 +
  8*(mW 12447 : ℝ)*24894*(24894+2)*(24894+3) /
    ((1/1000)*((mW 12447 : ℝ)*24894*(24894+2)))^2 +
  covarianceVarianceBound 24894 (mW 12447) /
    ((1/1000)*covarianceMeanBound 24894 (mW 12447))^2 +
  normVarianceBound 24894 (mW 12447) / (3*inputVarianceMean 24894 (mW 12447))^2

end BstLean.Part268.WorldRow12447
namespace BstLean.Part268.WorldRow12448
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12448 = 215203102829215 := by
  have hu : mW 12448 ≤ 215203102829215 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12448 ≤ 215203102829214 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12448)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24896 ^ 2)
    ((781250000000000000/122207954224642956976483))
    ((5000000000000000000/782099491111179026714617)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24896) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24896 : ℝ)^2 / (mW 12448 : ℝ)) * (1 + 1/10^6)^2 *
    √(((129899/62500000000))/2) * ((1-firstRatio 24896) * √(1-firstRatio 24896) *
      sixthConstant (e1CovarianceRatio 24896 (mW 12448) (1/10^6) rowEps))) /
    (712/10000 - 24896*(1+1/10^6)*((129899/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24896 (mW 12448) /
    ((1/10^5) * ((mW 12448 : ℝ)*24896*((mW 12448 : ℝ)+24896+1)))^2 +
  8*(mW 12448 : ℝ)*24896*(24896+2)*(24896+3) /
    ((1/1000)*((mW 12448 : ℝ)*24896*(24896+2)))^2 +
  covarianceVarianceBound 24896 (mW 12448) /
    ((1/1000)*covarianceMeanBound 24896 (mW 12448))^2 +
  normVarianceBound 24896 (mW 12448) / (3*inputVarianceMean 24896 (mW 12448))^2

end BstLean.Part268.WorldRow12448
namespace BstLean.Part268.WorldRow12449
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12449 = 215263617490098 := by
  have hu : mW 12449 ≤ 215263617490098 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12449 ≤ 215263617490097 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12449)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24898 ^ 2)
    ((25000000000000000000/3910968694453933602571303))
    ((25000000000000000000/3910811614821254112896931)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24898) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24898 : ℝ)^2 / (mW 12449 : ℝ)) * (1 + 1/10^6)^2 *
    √(((415643/200000000000))/2) * ((1-firstRatio 24898) * √(1-firstRatio 24898) *
      sixthConstant (e1CovarianceRatio 24898 (mW 12449) (1/10^6) rowEps))) /
    (712/10000 - 24898*(1+1/10^6)*((415643/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24898 (mW 12449) /
    ((1/10^5) * ((mW 12449 : ℝ)*24898*((mW 12449 : ℝ)+24898+1)))^2 +
  8*(mW 12449 : ℝ)*24898*(24898+2)*(24898+3) /
    ((1/1000)*((mW 12449 : ℝ)*24898*(24898+2)))^2 +
  covarianceVarianceBound 24898 (mW 12449) /
    ((1/1000)*covarianceMeanBound 24898 (mW 12449))^2 +
  normVarianceBound 24898 (mW 12449) / (3*inputVarianceMean 24898 (mW 12449))^2

end BstLean.Part268.WorldRow12449
