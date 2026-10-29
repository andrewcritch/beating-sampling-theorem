import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar4
namespace BstLean.Part268.WorldRow12450
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12450 = 215324144304716 := by
  have hu : mW 12450 ≤ 215324144304716 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12450 ≤ 215324144304715 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12450)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24900 ^ 2)
    ((500000000000000000/78225657074385851637903))
    ((25000000000000000000/3911125774086613092220777)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24900) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24900 : ℝ)^2 / (mW 12450 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1039023/500000000000))/2) * ((1-firstRatio 24900) * √(1-firstRatio 24900) *
      sixthConstant (e1CovarianceRatio 24900 (mW 12450) (1/10^6) rowEps))) /
    (712/10000 - 24900*(1+1/10^6)*((1039023/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24900 (mW 12450) /
    ((1/10^5) * ((mW 12450 : ℝ)*24900*((mW 12450 : ℝ)+24900+1)))^2 +
  8*(mW 12450 : ℝ)*24900*(24900+2)*(24900+3) /
    ((1/1000)*((mW 12450 : ℝ)*24900*(24900+2)))^2 +
  covarianceVarianceBound 24900 (mW 12450) /
    ((1/1000)*covarianceMeanBound 24900 (mW 12450))^2 +
  normVarianceBound 24900 (mW 12450) / (3*inputVarianceMean 24900 (mW 12450))^2

end BstLean.Part268.WorldRow12450
namespace BstLean.Part268.WorldRow12451
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12451 = 215384683274533 := by
  have hu : mW 12451 ≤ 215384683274533 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12451 ≤ 215384683274532 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12451)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24902 ^ 2)
    ((25000000000000000000/3911597012984651561218997))
    ((25000000000000000000/3911439933351972071544623)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24902) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24902 : ℝ)^2 / (mW 12451 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1038939/500000000000))/2) * ((1-firstRatio 24902) * √(1-firstRatio 24902) *
      sixthConstant (e1CovarianceRatio 24902 (mW 12451) (1/10^6) rowEps))) /
    (712/10000 - 24902*(1+1/10^6)*((1038939/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24902 (mW 12451) /
    ((1/10^5) * ((mW 12451 : ℝ)*24902*((mW 12451 : ℝ)+24902+1)))^2 +
  8*(mW 12451 : ℝ)*24902*(24902+2)*(24902+3) /
    ((1/1000)*((mW 12451 : ℝ)*24902*(24902+2)))^2 +
  covarianceVarianceBound 24902 (mW 12451) /
    ((1/1000)*covarianceMeanBound 24902 (mW 12451))^2 +
  normVarianceBound 24902 (mW 12451) / (3*inputVarianceMean 24902 (mW 12451))^2

end BstLean.Part268.WorldRow12451
namespace BstLean.Part268.WorldRow12452
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12452 = 215445234401014 := by
  have hu : mW 12452 ≤ 215445234401014 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12452 ≤ 215445234401013 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12452)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24904 ^ 2)
    ((6250000000000000000/977977793062502635135711))
    ((25000000000000000000/3911754092617331050868469)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24904) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24904 : ℝ)^2 / (mW 12452 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2077709/1000000000000))/2) * ((1-firstRatio 24904) * √(1-firstRatio 24904) *
      sixthConstant (e1CovarianceRatio 24904 (mW 12452) (1/10^6) rowEps))) /
    (712/10000 - 24904*(1+1/10^6)*((2077709/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24904 (mW 12452) /
    ((1/10^5) * ((mW 12452 : ℝ)*24904*((mW 12452 : ℝ)+24904+1)))^2 +
  8*(mW 12452 : ℝ)*24904*(24904+2)*(24904+3) /
    ((1/1000)*((mW 12452 : ℝ)*24904*(24904+2)))^2 +
  covarianceVarianceBound 24904 (mW 12452) /
    ((1/1000)*covarianceMeanBound 24904 (mW 12452))^2 +
  normVarianceBound 24904 (mW 12452) / (3*inputVarianceMean 24904 (mW 12452))^2

end BstLean.Part268.WorldRow12452
namespace BstLean.Part268.WorldRow12453
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12453 = 215505797685623 := by
  have hu : mW 12453 ≤ 215505797685623 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12453 ≤ 215505797685622 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12453)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24906 ^ 2)
    ((25000000000000000000/3912225331515369519866691))
    ((5000000000000000000/782413650376538006038463)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24906) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24906 : ℝ)^2 / (mW 12453 : ℝ)) * (1 + 1/10^6)^2 *
    √(((103877/50000000000))/2) * ((1-firstRatio 24906) * √(1-firstRatio 24906) *
      sixthConstant (e1CovarianceRatio 24906 (mW 12453) (1/10^6) rowEps))) /
    (712/10000 - 24906*(1+1/10^6)*((103877/50000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24906 (mW 12453) /
    ((1/10^5) * ((mW 12453 : ℝ)*24906*((mW 12453 : ℝ)+24906+1)))^2 +
  8*(mW 12453 : ℝ)*24906*(24906+2)*(24906+3) /
    ((1/1000)*((mW 12453 : ℝ)*24906*(24906+2)))^2 +
  covarianceVarianceBound 24906 (mW 12453) /
    ((1/1000)*covarianceMeanBound 24906 (mW 12453))^2 +
  normVarianceBound 24906 (mW 12453) / (3*inputVarianceMean 24906 (mW 12453))^2

end BstLean.Part268.WorldRow12453
namespace BstLean.Part268.WorldRow12454
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12454 = 215566373129824 := by
  have hu : mW 12454 ≤ 215566373129824 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12454 ≤ 215566373129823 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12454)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24908 ^ 2)
    ((12500000000000000000/1956269745390364249595269))
    ((25000000000000000000/3912382411148049009516161)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24908) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24908 : ℝ)^2 / (mW 12454 : ℝ)) * (1 + 1/10^6)^2 *
    √(((519343/250000000000))/2) * ((1-firstRatio 24908) * √(1-firstRatio 24908) *
      sixthConstant (e1CovarianceRatio 24908 (mW 12454) (1/10^6) rowEps))) /
    (712/10000 - 24908*(1+1/10^6)*((519343/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24908 (mW 12454) /
    ((1/10^5) * ((mW 12454 : ℝ)*24908*((mW 12454 : ℝ)+24908+1)))^2 +
  8*(mW 12454 : ℝ)*24908*(24908+2)*(24908+3) /
    ((1/1000)*((mW 12454 : ℝ)*24908*(24908+2)))^2 +
  covarianceVarianceBound 24908 (mW 12454) /
    ((1/1000)*covarianceMeanBound 24908 (mW 12454))^2 +
  normVarianceBound 24908 (mW 12454) / (3*inputVarianceMean 24908 (mW 12454))^2

end BstLean.Part268.WorldRow12454
namespace BstLean.Part268.WorldRow12455
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12455 = 215626960735084 := by
  have hu : mW 12455 ≤ 215626960735084 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12455 ≤ 215626960735083 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12455)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24910 ^ 2)
    ((5000000000000000000/782570730009217495702877))
    ((25000000000000000000/3912696570413407988840007)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24910) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24910 : ℝ)^2 / (mW 12455 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2077203/1000000000000))/2) * ((1-firstRatio 24910) * √(1-firstRatio 24910) *
      sixthConstant (e1CovarianceRatio 24910 (mW 12455) (1/10^6) rowEps))) /
    (712/10000 - 24910*(1+1/10^6)*((2077203/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24910 (mW 12455) /
    ((1/10^5) * ((mW 12455 : ℝ)*24910*((mW 12455 : ℝ)+24910+1)))^2 +
  8*(mW 12455 : ℝ)*24910*(24910+2)*(24910+3) /
    ((1/1000)*((mW 12455 : ℝ)*24910*(24910+2)))^2 +
  covarianceVarianceBound 24910 (mW 12455) /
    ((1/1000)*covarianceMeanBound 24910 (mW 12455))^2 +
  normVarianceBound 24910 (mW 12455) / (3*inputVarianceMean 24910 (mW 12455))^2

end BstLean.Part268.WorldRow12455
namespace BstLean.Part268.WorldRow12456
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12456 = 215687560502865 := by
  have hu : mW 12456 ≤ 215687560502865 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12456 ≤ 215687560502864 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12456)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24912 ^ 2)
    ((3125000000000000000/489145976163930807229779))
    ((25000000000000000000/3913010729678766968163853)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24912) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24912 : ℝ)^2 / (mW 12456 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1038517/500000000000))/2) * ((1-firstRatio 24912) * √(1-firstRatio 24912) *
      sixthConstant (e1CovarianceRatio 24912 (mW 12456) (1/10^6) rowEps))) /
    (712/10000 - 24912*(1+1/10^6)*((1038517/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24912 (mW 12456) /
    ((1/10^5) * ((mW 12456 : ℝ)*24912*((mW 12456 : ℝ)+24912+1)))^2 +
  8*(mW 12456 : ℝ)*24912*(24912+2)*(24912+3) /
    ((1/1000)*((mW 12456 : ℝ)*24912*(24912+2)))^2 +
  covarianceVarianceBound 24912 (mW 12456) /
    ((1/1000)*covarianceMeanBound 24912 (mW 12456))^2 +
  normVarianceBound 24912 (mW 12456) / (3*inputVarianceMean 24912 (mW 12456))^2

end BstLean.Part268.WorldRow12456
namespace BstLean.Part268.WorldRow12457
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12457 = 215748172434634 := by
  have hu : mW 12457 ≤ 215748172434634 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12457 ≤ 215748172434633 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12457)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24914 ^ 2)
    ((25000000000000000000/3913481968576805437162079))
    ((25000000000000000000/3913324888944125947487699)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24914) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24914 : ℝ)^2 / (mW 12457 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1038433/500000000000))/2) * ((1-firstRatio 24914) * √(1-firstRatio 24914) *
      sixthConstant (e1CovarianceRatio 24914 (mW 12457) (1/10^6) rowEps))) /
    (712/10000 - 24914*(1+1/10^6)*((1038433/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24914 (mW 12457) /
    ((1/10^5) * ((mW 12457 : ℝ)*24914*((mW 12457 : ℝ)+24914+1)))^2 +
  8*(mW 12457 : ℝ)*24914*(24914+2)*(24914+3) /
    ((1/1000)*((mW 12457 : ℝ)*24914*(24914+2)))^2 +
  covarianceVarianceBound 24914 (mW 12457) /
    ((1/1000)*covarianceMeanBound 24914 (mW 12457))^2 +
  normVarianceBound 24914 (mW 12457) / (3*inputVarianceMean 24914 (mW 12457))^2

end BstLean.Part268.WorldRow12457
namespace BstLean.Part268.WorldRow12458
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12458 = 215808796531855 := by
  have hu : mW 12458 ≤ 215808796531855 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12458 ≤ 215808796531854 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12458)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24916 ^ 2)
    ((12500000000000000000/1956898063921082208242963))
    ((5000000000000000000/782727809641896985362309)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24916) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24916 : ℝ)^2 / (mW 12458 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2076697/1000000000000))/2) * ((1-firstRatio 24916) * √(1-firstRatio 24916) *
      sixthConstant (e1CovarianceRatio 24916 (mW 12458) (1/10^6) rowEps))) /
    (712/10000 - 24916*(1+1/10^6)*((2076697/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24916 (mW 12458) /
    ((1/10^5) * ((mW 12458 : ℝ)*24916*((mW 12458 : ℝ)+24916+1)))^2 +
  8*(mW 12458 : ℝ)*24916*(24916+2)*(24916+3) /
    ((1/1000)*((mW 12458 : ℝ)*24916*(24916+2)))^2 +
  covarianceVarianceBound 24916 (mW 12458) /
    ((1/1000)*covarianceMeanBound 24916 (mW 12458))^2 +
  normVarianceBound 24916 (mW 12458) / (3*inputVarianceMean 24916 (mW 12458))^2

end BstLean.Part268.WorldRow12458
namespace BstLean.Part268.WorldRow12459
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12459 = 215869432795993 := by
  have hu : mW 12459 ≤ 215869432795993 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12459 ≤ 215869432795992 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12459)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24918 ^ 2)
    ((25000000000000000000/3914110287107523395809773))
    ((25000000000000000000/3913953207474843906135391)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24918) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24918 : ℝ)^2 / (mW 12459 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2076529/1000000000000))/2) * ((1-firstRatio 24918) * √(1-firstRatio 24918) *
      sixthConstant (e1CovarianceRatio 24918 (mW 12459) (1/10^6) rowEps))) /
    (712/10000 - 24918*(1+1/10^6)*((2076529/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24918 (mW 12459) /
    ((1/10^5) * ((mW 12459 : ℝ)*24918*((mW 12459 : ℝ)+24918+1)))^2 +
  8*(mW 12459 : ℝ)*24918*(24918+2)*(24918+3) /
    ((1/1000)*((mW 12459 : ℝ)*24918*(24918+2)))^2 +
  covarianceVarianceBound 24918 (mW 12459) /
    ((1/1000)*covarianceMeanBound 24918 (mW 12459))^2 +
  normVarianceBound 24918 (mW 12459) / (3*inputVarianceMean 24918 (mW 12459))^2

end BstLean.Part268.WorldRow12459
namespace BstLean.Part268.WorldRow12460
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12460 = 215930081228513 := by
  have hu : mW 12460 ≤ 215930081228513 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12460 ≤ 215930081228512 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12460)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24920 ^ 2)
    ((1250000000000000000/195721222318644118756681))
    ((25000000000000000000/3914267366740202885459237)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24920) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24920 : ℝ)^2 / (mW 12460 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2076361/1000000000000))/2) * ((1-firstRatio 24920) * √(1-firstRatio 24920) *
      sixthConstant (e1CovarianceRatio 24920 (mW 12460) (1/10^6) rowEps))) /
    (712/10000 - 24920*(1+1/10^6)*((2076361/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24920 (mW 12460) /
    ((1/10^5) * ((mW 12460 : ℝ)*24920*((mW 12460 : ℝ)+24920+1)))^2 +
  8*(mW 12460 : ℝ)*24920*(24920+2)*(24920+3) /
    ((1/1000)*((mW 12460 : ℝ)*24920*(24920+2)))^2 +
  covarianceVarianceBound 24920 (mW 12460) /
    ((1/1000)*covarianceMeanBound 24920 (mW 12460))^2 +
  normVarianceBound 24920 (mW 12460) / (3*inputVarianceMean 24920 (mW 12460))^2

end BstLean.Part268.WorldRow12460
namespace BstLean.Part268.WorldRow12461
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12461 = 215990741830879 := by
  have hu : mW 12461 ≤ 215990741830879 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12461 ≤ 215990741830878 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12461)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24922 ^ 2)
    ((25000000000000000000/3914738605638241354457467))
    ((25000000000000000000/3914581526005561864783083)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24922) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24922 : ℝ)^2 / (mW 12461 : ℝ)) * (1 + 1/10^6)^2 *
    √(((64881/31250000000))/2) * ((1-firstRatio 24922) * √(1-firstRatio 24922) *
      sixthConstant (e1CovarianceRatio 24922 (mW 12461) (1/10^6) rowEps))) /
    (712/10000 - 24922*(1+1/10^6)*((64881/31250000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24922 (mW 12461) /
    ((1/10^5) * ((mW 12461 : ℝ)*24922*((mW 12461 : ℝ)+24922+1)))^2 +
  8*(mW 12461 : ℝ)*24922*(24922+2)*(24922+3) /
    ((1/1000)*((mW 12461 : ℝ)*24922*(24922+2)))^2 +
  covarianceVarianceBound 24922 (mW 12461) /
    ((1/1000)*covarianceMeanBound 24922 (mW 12461))^2 +
  normVarianceBound 24922 (mW 12461) / (3*inputVarianceMean 24922 (mW 12461))^2

end BstLean.Part268.WorldRow12461
namespace BstLean.Part268.WorldRow12462
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12462 = 216051414604558 := by
  have hu : mW 12462 ≤ 216051414604558 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12462 ≤ 216051414604557 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12462)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24924 ^ 2)
    ((12500000000000000000/1957526382451800166890657))
    ((25000000000000000000/3914895685270920844106929)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24924) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24924 : ℝ)^2 / (mW 12462 : ℝ)) * (1 + 1/10^6)^2 *
    √(((259503/125000000000))/2) * ((1-firstRatio 24924) * √(1-firstRatio 24924) *
      sixthConstant (e1CovarianceRatio 24924 (mW 12462) (1/10^6) rowEps))) /
    (712/10000 - 24924*(1+1/10^6)*((259503/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24924 (mW 12462) /
    ((1/10^5) * ((mW 12462 : ℝ)*24924*((mW 12462 : ℝ)+24924+1)))^2 +
  8*(mW 12462 : ℝ)*24924*(24924+2)*(24924+3) /
    ((1/1000)*((mW 12462 : ℝ)*24924*(24924+2)))^2 +
  covarianceVarianceBound 24924 (mW 12462) /
    ((1/1000)*covarianceMeanBound 24924 (mW 12462))^2 +
  normVarianceBound 24924 (mW 12462) / (3*inputVarianceMean 24924 (mW 12462))^2

end BstLean.Part268.WorldRow12462
namespace BstLean.Part268.WorldRow12463
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12463 = 216112099551014 := by
  have hu : mW 12463 ≤ 216112099551014 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12463 ≤ 216112099551013 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12463)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24926 ^ 2)
    ((25000000000000000000/3915366924168959313105161))
    ((1000000000000000000/156608393781451192937231)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24926) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24926 : ℝ)^2 / (mW 12463 : ℝ)) * (1 + 1/10^6)^2 *
    √(((415171/200000000000))/2) * ((1-firstRatio 24926) * √(1-firstRatio 24926) *
      sixthConstant (e1CovarianceRatio 24926 (mW 12463) (1/10^6) rowEps))) /
    (712/10000 - 24926*(1+1/10^6)*((415171/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24926 (mW 12463) /
    ((1/10^5) * ((mW 12463 : ℝ)*24926*((mW 12463 : ℝ)+24926+1)))^2 +
  8*(mW 12463 : ℝ)*24926*(24926+2)*(24926+3) /
    ((1/1000)*((mW 12463 : ℝ)*24926*(24926+2)))^2 +
  covarianceVarianceBound 24926 (mW 12463) /
    ((1/1000)*covarianceMeanBound 24926 (mW 12463))^2 +
  normVarianceBound 24926 (mW 12463) / (3*inputVarianceMean 24926 (mW 12463))^2

end BstLean.Part268.WorldRow12463
namespace BstLean.Part268.WorldRow12464
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12464 = 216172796671712 := by
  have hu : mW 12464 ≤ 216172796671712 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12464 ≤ 216172796671711 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12464)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24928 ^ 2)
    ((1562500000000000000/244730067714644893276813))
    ((25000000000000000000/3915524003801638802754621)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24928) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24928 : ℝ)^2 / (mW 12464 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2075687/1000000000000))/2) * ((1-firstRatio 24928) * √(1-firstRatio 24928) *
      sixthConstant (e1CovarianceRatio 24928 (mW 12464) (1/10^6) rowEps))) /
    (712/10000 - 24928*(1+1/10^6)*((2075687/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24928 (mW 12464) /
    ((1/10^5) * ((mW 12464 : ℝ)*24928*((mW 12464 : ℝ)+24928+1)))^2 +
  8*(mW 12464 : ℝ)*24928*(24928+2)*(24928+3) /
    ((1/1000)*((mW 12464 : ℝ)*24928*(24928+2)))^2 +
  covarianceVarianceBound 24928 (mW 12464) /
    ((1/1000)*covarianceMeanBound 24928 (mW 12464))^2 +
  normVarianceBound 24928 (mW 12464) / (3*inputVarianceMean 24928 (mW 12464))^2

end BstLean.Part268.WorldRow12464
namespace BstLean.Part268.WorldRow12465
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12465 = 216233505968118 := by
  have hu : mW 12465 ≤ 216233505968118 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12465 ≤ 216233505968117 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12465)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24930 ^ 2)
    ((5000000000000000000/783199048539935454350571))
    ((25000000000000000000/3915838163066997782078467)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24930) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24930 : ℝ)^2 / (mW 12465 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2075519/1000000000000))/2) * ((1-firstRatio 24930) * √(1-firstRatio 24930) *
      sixthConstant (e1CovarianceRatio 24930 (mW 12465) (1/10^6) rowEps))) /
    (712/10000 - 24930*(1+1/10^6)*((2075519/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24930 (mW 12465) /
    ((1/10^5) * ((mW 12465 : ℝ)*24930*((mW 12465 : ℝ)+24930+1)))^2 +
  8*(mW 12465 : ℝ)*24930*(24930+2)*(24930+3) /
    ((1/1000)*((mW 12465 : ℝ)*24930*(24930+2)))^2 +
  covarianceVarianceBound 24930 (mW 12465) /
    ((1/1000)*covarianceMeanBound 24930 (mW 12465))^2 +
  normVarianceBound 24930 (mW 12465) / (3*inputVarianceMean 24930 (mW 12465))^2

end BstLean.Part268.WorldRow12465
namespace BstLean.Part268.WorldRow12466
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12466 = 216294227441698 := by
  have hu : mW 12466 ≤ 216294227441698 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12466 ≤ 216294227441697 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12466)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24932 ^ 2)
    ((12500000000000000000/1958154700982518125538351))
    ((25000000000000000000/3916152322332356761402313)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24932) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24932 : ℝ)^2 / (mW 12466 : ℝ)) * (1 + 1/10^6)^2 *
    √(((41507/20000000000))/2) * ((1-firstRatio 24932) * √(1-firstRatio 24932) *
      sixthConstant (e1CovarianceRatio 24932 (mW 12466) (1/10^6) rowEps))) /
    (712/10000 - 24932*(1+1/10^6)*((41507/20000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24932 (mW 12466) /
    ((1/10^5) * ((mW 12466 : ℝ)*24932*((mW 12466 : ℝ)+24932+1)))^2 +
  8*(mW 12466 : ℝ)*24932*(24932+2)*(24932+3) /
    ((1/1000)*((mW 12466 : ℝ)*24932*(24932+2)))^2 +
  covarianceVarianceBound 24932 (mW 12466) /
    ((1/1000)*covarianceMeanBound 24932 (mW 12466))^2 +
  normVarianceBound 24932 (mW 12466) / (3*inputVarianceMean 24932 (mW 12466))^2

end BstLean.Part268.WorldRow12466
namespace BstLean.Part268.WorldRow12467
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12467 = 216354961093915 := by
  have hu : mW 12467 ≤ 216354961093915 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12467 ≤ 216354961093914 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12467)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24934 ^ 2)
    ((25000000000000000000/3916623561230395230400549))
    ((25000000000000000000/3916466481597715740726159)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24934) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24934 : ℝ)^2 / (mW 12467 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1037591/500000000000))/2) * ((1-firstRatio 24934) * √(1-firstRatio 24934) *
      sixthConstant (e1CovarianceRatio 24934 (mW 12467) (1/10^6) rowEps))) /
    (712/10000 - 24934*(1+1/10^6)*((1037591/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24934 (mW 12467) /
    ((1/10^5) * ((mW 12467 : ℝ)*24934*((mW 12467 : ℝ)+24934+1)))^2 +
  8*(mW 12467 : ℝ)*24934*(24934+2)*(24934+3) /
    ((1/1000)*((mW 12467 : ℝ)*24934*(24934+2)))^2 +
  covarianceVarianceBound 24934 (mW 12467) /
    ((1/1000)*covarianceMeanBound 24934 (mW 12467))^2 +
  normVarianceBound 24934 (mW 12467) / (3*inputVarianceMean 24934 (mW 12467))^2

end BstLean.Part268.WorldRow12467
namespace BstLean.Part268.WorldRow12468
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12468 = 216415706926237 := by
  have hu : mW 12468 ≤ 216415706926237 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12468 ≤ 216415706926236 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12468)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24936 ^ 2)
    ((6250000000000000000/979234430123938552431099))
    ((5000000000000000000/783356128172614944010001)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24936) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24936 : ℝ)^2 / (mW 12468 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1037507/500000000000))/2) * ((1-firstRatio 24936) * √(1-firstRatio 24936) *
      sixthConstant (e1CovarianceRatio 24936 (mW 12468) (1/10^6) rowEps))) /
    (712/10000 - 24936*(1+1/10^6)*((1037507/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24936 (mW 12468) /
    ((1/10^5) * ((mW 12468 : ℝ)*24936*((mW 12468 : ℝ)+24936+1)))^2 +
  8*(mW 12468 : ℝ)*24936*(24936+2)*(24936+3) /
    ((1/1000)*((mW 12468 : ℝ)*24936*(24936+2)))^2 +
  covarianceVarianceBound 24936 (mW 12468) /
    ((1/1000)*covarianceMeanBound 24936 (mW 12468))^2 +
  normVarianceBound 24936 (mW 12468) / (3*inputVarianceMean 24936 (mW 12468))^2

end BstLean.Part268.WorldRow12468
namespace BstLean.Part268.WorldRow12469
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12469 = 216476464940127 := by
  have hu : mW 12469 ≤ 216476464940127 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12469 ≤ 216476464940126 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12469)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24938 ^ 2)
    ((25000000000000000000/3917251879761113189048243))
    ((25000000000000000000/3917094800128433699373851)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24938) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24938 : ℝ)^2 / (mW 12469 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1037423/500000000000))/2) * ((1-firstRatio 24938) * √(1-firstRatio 24938) *
      sixthConstant (e1CovarianceRatio 24938 (mW 12469) (1/10^6) rowEps))) /
    (712/10000 - 24938*(1+1/10^6)*((1037423/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24938 (mW 12469) /
    ((1/10^5) * ((mW 12469 : ℝ)*24938*((mW 12469 : ℝ)+24938+1)))^2 +
  8*(mW 12469 : ℝ)*24938*(24938+2)*(24938+3) /
    ((1/1000)*((mW 12469 : ℝ)*24938*(24938+2)))^2 +
  covarianceVarianceBound 24938 (mW 12469) /
    ((1/1000)*covarianceMeanBound 24938 (mW 12469))^2 +
  normVarianceBound 24938 (mW 12469) / (3*inputVarianceMean 24938 (mW 12469))^2

end BstLean.Part268.WorldRow12469
namespace BstLean.Part268.WorldRow12470
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12470 = 216537235137053 := by
  have hu : mW 12470 ≤ 216537235137053 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12470 ≤ 216537235137052 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12470)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24940 ^ 2)
    ((2500000000000000000/391756603902647216837209))
    ((25000000000000000000/3917408959393792678697697)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24940) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24940 : ℝ)^2 / (mW 12470 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1037339/500000000000))/2) * ((1-firstRatio 24940) * √(1-firstRatio 24940) *
      sixthConstant (e1CovarianceRatio 24940 (mW 12470) (1/10^6) rowEps))) /
    (712/10000 - 24940*(1+1/10^6)*((1037339/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24940 (mW 12470) /
    ((1/10^5) * ((mW 12470 : ℝ)*24940*((mW 12470 : ℝ)+24940+1)))^2 +
  8*(mW 12470 : ℝ)*24940*(24940+2)*(24940+3) /
    ((1/1000)*((mW 12470 : ℝ)*24940*(24940+2)))^2 +
  covarianceVarianceBound 24940 (mW 12470) /
    ((1/1000)*covarianceMeanBound 24940 (mW 12470))^2 +
  normVarianceBound 24940 (mW 12470) / (3*inputVarianceMean 24940 (mW 12470))^2

end BstLean.Part268.WorldRow12470
namespace BstLean.Part268.WorldRow12471
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12471 = 216598017518480 := by
  have hu : mW 12471 ≤ 216598017518480 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12471 ≤ 216598017518479 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12471)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24942 ^ 2)
    ((25000000000000000000/3917880198291831147695937))
    ((25000000000000000000/3917723118659151658021543)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24942) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24942 : ℝ)^2 / (mW 12471 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2074509/1000000000000))/2) * ((1-firstRatio 24942) * √(1-firstRatio 24942) *
      sixthConstant (e1CovarianceRatio 24942 (mW 12471) (1/10^6) rowEps))) /
    (712/10000 - 24942*(1+1/10^6)*((2074509/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24942 (mW 12471) /
    ((1/10^5) * ((mW 12471 : ℝ)*24942*((mW 12471 : ℝ)+24942+1)))^2 +
  8*(mW 12471 : ℝ)*24942*(24942+2)*(24942+3) /
    ((1/1000)*((mW 12471 : ℝ)*24942*(24942+2)))^2 +
  covarianceVarianceBound 24942 (mW 12471) /
    ((1/1000)*covarianceMeanBound 24942 (mW 12471))^2 +
  normVarianceBound 24942 (mW 12471) / (3*inputVarianceMean 24942 (mW 12471))^2

end BstLean.Part268.WorldRow12471
namespace BstLean.Part268.WorldRow12472
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12472 = 216658812085872 := by
  have hu : mW 12472 ≤ 216658812085872 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12472 ≤ 216658812085871 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12472)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24944 ^ 2)
    ((3125000000000000000/489774294694648765877473))
    ((25000000000000000000/3918037277924510637345389)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24944) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24944 : ℝ)^2 / (mW 12472 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2074341/1000000000000))/2) * ((1-firstRatio 24944) * √(1-firstRatio 24944) *
      sixthConstant (e1CovarianceRatio 24944 (mW 12472) (1/10^6) rowEps))) /
    (712/10000 - 24944*(1+1/10^6)*((2074341/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24944 (mW 12472) /
    ((1/10^5) * ((mW 12472 : ℝ)*24944*((mW 12472 : ℝ)+24944+1)))^2 +
  8*(mW 12472 : ℝ)*24944*(24944+2)*(24944+3) /
    ((1/1000)*((mW 12472 : ℝ)*24944*(24944+2)))^2 +
  covarianceVarianceBound 24944 (mW 12472) /
    ((1/1000)*covarianceMeanBound 24944 (mW 12472))^2 +
  normVarianceBound 24944 (mW 12472) / (3*inputVarianceMean 24944 (mW 12472))^2

end BstLean.Part268.WorldRow12472
namespace BstLean.Part268.WorldRow12473
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12473 = 216719618840697 := by
  have hu : mW 12473 ≤ 216719618840697 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12473 ≤ 216719618840696 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12473)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24946 ^ 2)
    ((25000000000000000000/3918508516822549106343631))
    ((5000000000000000000/783670287437973923333847)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24946) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24946 : ℝ)^2 / (mW 12473 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2074173/1000000000000))/2) * ((1-firstRatio 24946) * √(1-firstRatio 24946) *
      sixthConstant (e1CovarianceRatio 24946 (mW 12473) (1/10^6) rowEps))) /
    (712/10000 - 24946*(1+1/10^6)*((2074173/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24946 (mW 12473) /
    ((1/10^5) * ((mW 12473 : ℝ)*24946*((mW 12473 : ℝ)+24946+1)))^2 +
  8*(mW 12473 : ℝ)*24946*(24946+2)*(24946+3) /
    ((1/1000)*((mW 12473 : ℝ)*24946*(24946+2)))^2 +
  covarianceVarianceBound 24946 (mW 12473) /
    ((1/1000)*covarianceMeanBound 24946 (mW 12473))^2 +
  normVarianceBound 24946 (mW 12473) / (3*inputVarianceMean 24946 (mW 12473))^2

end BstLean.Part268.WorldRow12473
namespace BstLean.Part268.WorldRow12474
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12474 = 216780437784419 := by
  have hu : mW 12474 ≤ 216780437784419 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12474 ≤ 216780437784418 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12474)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24948 ^ 2)
    ((12500000000000000000/1959411338043954042833739))
    ((25000000000000000000/3918665596455228595993081)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24948) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24948 : ℝ)^2 / (mW 12474 : ℝ)) * (1 + 1/10^6)^2 *
    √(((414801/200000000000))/2) * ((1-firstRatio 24948) * √(1-firstRatio 24948) *
      sixthConstant (e1CovarianceRatio 24948 (mW 12474) (1/10^6) rowEps))) /
    (712/10000 - 24948*(1+1/10^6)*((414801/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24948 (mW 12474) /
    ((1/10^5) * ((mW 12474 : ℝ)*24948*((mW 12474 : ℝ)+24948+1)))^2 +
  8*(mW 12474 : ℝ)*24948*(24948+2)*(24948+3) /
    ((1/1000)*((mW 12474 : ℝ)*24948*(24948+2)))^2 +
  covarianceVarianceBound 24948 (mW 12474) /
    ((1/1000)*covarianceMeanBound 24948 (mW 12474))^2 +
  normVarianceBound 24948 (mW 12474) / (3*inputVarianceMean 24948 (mW 12474))^2

end BstLean.Part268.WorldRow12474
