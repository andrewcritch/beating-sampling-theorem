import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar28
namespace BstLean.Part268.WorldRow13050
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13050 = 253884852774992 := by
  have hu : mW 13050 ≤ 253884852774992 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13050 ≤ 253884852774991 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13050)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26100 ^ 2)
    ((500000000000000000/81995568258693603524067))
    ((25000000000000000000/4099621333302000686528377)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26100) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26100 : ℝ)^2 / (mW 13050 : ℝ)) * (1 + 1/10^6)^2 *
    √(((396307/200000000000))/2) * ((1-firstRatio 26100) * √(1-firstRatio 26100) *
      sixthConstant (e1CovarianceRatio 26100 (mW 13050) (1/10^6) rowEps))) /
    (712/10000 - 26100*(1+1/10^6)*((396307/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26100 (mW 13050) /
    ((1/10^5) * ((mW 13050 : ℝ)*26100*((mW 13050 : ℝ)+26100+1)))^2 +
  8*(mW 13050 : ℝ)*26100*(26100+2)*(26100+3) /
    ((1/1000)*((mW 13050 : ℝ)*26100*(26100+2)))^2 +
  covarianceVarianceBound 26100 (mW 13050) /
    ((1/1000)*covarianceMeanBound 26100 (mW 13050))^2 +
  normVarianceBound 26100 (mW 13050) / (3*inputVarianceMean 26100 (mW 13050))^2

end BstLean.Part268.WorldRow13050
namespace BstLean.Part268.WorldRow13051
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13051 = 253952951020404 := by
  have hu : mW 13051 ≤ 253952951020404 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13051 ≤ 253952951020403 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13051)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26102 ^ 2)
    ((25000000000000000000/4100092572200039155527197))
    ((25000000000000000000/4099935492567359665852223)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26102) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26102 : ℝ)^2 / (mW 13051 : ℝ)) * (1 + 1/10^6)^2 *
    √(((990691/500000000000))/2) * ((1-firstRatio 26102) * √(1-firstRatio 26102) *
      sixthConstant (e1CovarianceRatio 26102 (mW 13051) (1/10^6) rowEps))) /
    (712/10000 - 26102*(1+1/10^6)*((990691/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26102 (mW 13051) /
    ((1/10^5) * ((mW 13051 : ℝ)*26102*((mW 13051 : ℝ)+26102+1)))^2 +
  8*(mW 13051 : ℝ)*26102*(26102+2)*(26102+3) /
    ((1/1000)*((mW 13051 : ℝ)*26102*(26102+2)))^2 +
  covarianceVarianceBound 26102 (mW 13051) /
    ((1/1000)*covarianceMeanBound 26102 (mW 13051))^2 +
  normVarianceBound 26102 (mW 13051) / (3*inputVarianceMean 26102 (mW 13051))^2

end BstLean.Part268.WorldRow13051
namespace BstLean.Part268.WorldRow13052
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13052 = 254021062311707 := by
  have hu : mW 13052 ≤ 254021062311707 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13052 ≤ 254021062311706 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13052)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26104 ^ 2)
    ((6250000000000000000/1025101682866349533712761))
    ((25000000000000000000/4100249651832718645176069)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26104) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26104 : ℝ)^2 / (mW 13052 : ℝ)) * (1 + 1/10^6)^2 *
    √(((495307/250000000000))/2) * ((1-firstRatio 26104) * √(1-firstRatio 26104) *
      sixthConstant (e1CovarianceRatio 26104 (mW 13052) (1/10^6) rowEps))) /
    (712/10000 - 26104*(1+1/10^6)*((495307/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26104 (mW 13052) /
    ((1/10^5) * ((mW 13052 : ℝ)*26104*((mW 13052 : ℝ)+26104+1)))^2 +
  8*(mW 13052 : ℝ)*26104*(26104+2)*(26104+3) /
    ((1/1000)*((mW 13052 : ℝ)*26104*(26104+2)))^2 +
  covarianceVarianceBound 26104 (mW 13052) /
    ((1/1000)*covarianceMeanBound 26104 (mW 13052))^2 +
  normVarianceBound 26104 (mW 13052) / (3*inputVarianceMean 26104 (mW 13052))^2

end BstLean.Part268.WorldRow13052
namespace BstLean.Part268.WorldRow13053
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13053 = 254089186650400 := by
  have hu : mW 13053 ≤ 254089186650400 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13053 ≤ 254089186650399 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13053)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26106 ^ 2)
    ((25000000000000000000/4100720890730757114174891))
    ((5000000000000000000/820112762219615524899983)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26106) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26106 : ℝ)^2 / (mW 13053 : ℝ)) * (1 + 1/10^6)^2 *
    √(((79243/40000000000))/2) * ((1-firstRatio 26106) * √(1-firstRatio 26106) *
      sixthConstant (e1CovarianceRatio 26106 (mW 13053) (1/10^6) rowEps))) /
    (712/10000 - 26106*(1+1/10^6)*((79243/40000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26106 (mW 13053) /
    ((1/10^5) * ((mW 13053 : ℝ)*26106*((mW 13053 : ℝ)+26106+1)))^2 +
  8*(mW 13053 : ℝ)*26106*(26106+2)*(26106+3) /
    ((1/1000)*((mW 13053 : ℝ)*26106*(26106+2)))^2 +
  covarianceVarianceBound 26106 (mW 13053) /
    ((1/1000)*covarianceMeanBound 26106 (mW 13053))^2 +
  normVarianceBound 26106 (mW 13053) / (3*inputVarianceMean 26106 (mW 13053))^2

end BstLean.Part268.WorldRow13053
namespace BstLean.Part268.WorldRow13054
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13054 = 254157324037983 := by
  have hu : mW 13054 ≤ 254157324037983 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13054 ≤ 254157324037982 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13054)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26108 ^ 2)
    ((12500000000000000000/2050517524998058046749369))
    ((25000000000000000000/4100877970363436603823761)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26108) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26108 : ℝ)^2 / (mW 13054 : ℝ)) * (1 + 1/10^6)^2 *
    √(((990461/500000000000))/2) * ((1-firstRatio 26108) * √(1-firstRatio 26108) *
      sixthConstant (e1CovarianceRatio 26108 (mW 13054) (1/10^6) rowEps))) /
    (712/10000 - 26108*(1+1/10^6)*((990461/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26108 (mW 13054) /
    ((1/10^5) * ((mW 13054 : ℝ)*26108*((mW 13054 : ℝ)+26108+1)))^2 +
  8*(mW 13054 : ℝ)*26108*(26108+2)*(26108+3) /
    ((1/1000)*((mW 13054 : ℝ)*26108*(26108+2)))^2 +
  covarianceVarianceBound 26108 (mW 13054) /
    ((1/1000)*covarianceMeanBound 26108 (mW 13054))^2 +
  normVarianceBound 26108 (mW 13054) / (3*inputVarianceMean 26108 (mW 13054))^2

end BstLean.Part268.WorldRow13054
namespace BstLean.Part268.WorldRow13055
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13055 = 254225474475955 := by
  have hu : mW 13055 ≤ 254225474475955 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13055 ≤ 254225474475954 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13055)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26110 ^ 2)
    ((5000000000000000000/820269841852295014564517))
    ((25000000000000000000/4101192129628795583147607)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26110) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26110 : ℝ)^2 / (mW 13055 : ℝ)) * (1 + 1/10^6)^2 *
    √(((61899/31250000000))/2) * ((1-firstRatio 26110) * √(1-firstRatio 26110) *
      sixthConstant (e1CovarianceRatio 26110 (mW 13055) (1/10^6) rowEps))) /
    (712/10000 - 26110*(1+1/10^6)*((61899/31250000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26110 (mW 13055) /
    ((1/10^5) * ((mW 13055 : ℝ)*26110*((mW 13055 : ℝ)+26110+1)))^2 +
  8*(mW 13055 : ℝ)*26110*(26110+2)*(26110+3) /
    ((1/1000)*((mW 13055 : ℝ)*26110*(26110+2)))^2 +
  covarianceVarianceBound 26110 (mW 13055) /
    ((1/1000)*covarianceMeanBound 26110 (mW 13055))^2 +
  normVarianceBound 26110 (mW 13055) / (3*inputVarianceMean 26110 (mW 13055))^2

end BstLean.Part268.WorldRow13055
namespace BstLean.Part268.WorldRow13056
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13056 = 254293637965816 := by
  have hu : mW 13056 ≤ 254293637965816 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13056 ≤ 254293637965815 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13056)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26112 ^ 2)
    ((97656250000000000/16022122533307945516197))
    ((25000000000000000000/4101506288894154562471453)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26112) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26112 : ℝ)^2 / (mW 13056 : ℝ)) * (1 + 1/10^6)^2 *
    √(((396123/200000000000))/2) * ((1-firstRatio 26112) * √(1-firstRatio 26112) *
      sixthConstant (e1CovarianceRatio 26112 (mW 13056) (1/10^6) rowEps))) /
    (712/10000 - 26112*(1+1/10^6)*((396123/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26112 (mW 13056) /
    ((1/10^5) * ((mW 13056 : ℝ)*26112*((mW 13056 : ℝ)+26112+1)))^2 +
  8*(mW 13056 : ℝ)*26112*(26112+2)*(26112+3) /
    ((1/1000)*((mW 13056 : ℝ)*26112*(26112+2)))^2 +
  covarianceVarianceBound 26112 (mW 13056) /
    ((1/1000)*covarianceMeanBound 26112 (mW 13056))^2 +
  normVarianceBound 26112 (mW 13056) / (3*inputVarianceMean 26112 (mW 13056))^2

end BstLean.Part268.WorldRow13056
namespace BstLean.Part268.WorldRow13057
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13057 = 254361814509065 := by
  have hu : mW 13057 ≤ 254361814509065 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13057 ≤ 254361814509064 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13057)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26114 ^ 2)
    ((25000000000000000000/4101977527792193031470279))
    ((25000000000000000000/4101820448159513541795299)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26114) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26114 : ℝ)^2 / (mW 13057 : ℝ)) * (1 + 1/10^6)^2 *
    √(((990231/500000000000))/2) * ((1-firstRatio 26114) * √(1-firstRatio 26114) *
      sixthConstant (e1CovarianceRatio 26114 (mW 13057) (1/10^6) rowEps))) /
    (712/10000 - 26114*(1+1/10^6)*((990231/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26114 (mW 13057) /
    ((1/10^5) * ((mW 13057 : ℝ)*26114*((mW 13057 : ℝ)+26114+1)))^2 +
  8*(mW 13057 : ℝ)*26114*(26114+2)*(26114+3) /
    ((1/1000)*((mW 13057 : ℝ)*26114*(26114+2)))^2 +
  covarianceVarianceBound 26114 (mW 13057) /
    ((1/1000)*covarianceMeanBound 26114 (mW 13057))^2 +
  normVarianceBound 26114 (mW 13057) / (3*inputVarianceMean 26114 (mW 13057))^2

end BstLean.Part268.WorldRow13057
namespace BstLean.Part268.WorldRow13058
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13058 = 254430004107203 := by
  have hu : mW 13058 ≤ 254430004107203 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13058 ≤ 254430004107202 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13058)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26116 ^ 2)
    ((12500000000000000000/2051145843528776005397063))
    ((5000000000000000000/820426921484974504223829)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26116) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26116 : ℝ)^2 / (mW 13058 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1980309/1000000000000))/2) * ((1-firstRatio 26116) * √(1-firstRatio 26116) *
      sixthConstant (e1CovarianceRatio 26116 (mW 13058) (1/10^6) rowEps))) /
    (712/10000 - 26116*(1+1/10^6)*((1980309/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26116 (mW 13058) /
    ((1/10^5) * ((mW 13058 : ℝ)*26116*((mW 13058 : ℝ)+26116+1)))^2 +
  8*(mW 13058 : ℝ)*26116*(26116+2)*(26116+3) /
    ((1/1000)*((mW 13058 : ℝ)*26116*(26116+2)))^2 +
  covarianceVarianceBound 26116 (mW 13058) /
    ((1/1000)*covarianceMeanBound 26116 (mW 13058))^2 +
  normVarianceBound 26116 (mW 13058) / (3*inputVarianceMean 26116 (mW 13058))^2

end BstLean.Part268.WorldRow13058
namespace BstLean.Part268.WorldRow13059
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13059 = 254498206761728 := by
  have hu : mW 13059 ≤ 254498206761728 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13059 ≤ 254498206761727 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13059)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26118 ^ 2)
    ((25000000000000000000/4102605846322910990117973))
    ((25000000000000000000/4102448766690231500442991)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26118) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26118 : ℝ)^2 / (mW 13059 : ℝ)) * (1 + 1/10^6)^2 *
    √(((495039/250000000000))/2) * ((1-firstRatio 26118) * √(1-firstRatio 26118) *
      sixthConstant (e1CovarianceRatio 26118 (mW 13059) (1/10^6) rowEps))) /
    (712/10000 - 26118*(1+1/10^6)*((495039/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26118 (mW 13059) /
    ((1/10^5) * ((mW 13059 : ℝ)*26118*((mW 13059 : ℝ)+26118+1)))^2 +
  8*(mW 13059 : ℝ)*26118*(26118+2)*(26118+3) /
    ((1/1000)*((mW 13059 : ℝ)*26118*(26118+2)))^2 +
  covarianceVarianceBound 26118 (mW 13059) /
    ((1/1000)*covarianceMeanBound 26118 (mW 13059))^2 +
  normVarianceBound 26118 (mW 13059) / (3*inputVarianceMean 26118 (mW 13059))^2

end BstLean.Part268.WorldRow13059
namespace BstLean.Part268.WorldRow13060
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13060 = 254566422474142 := by
  have hu : mW 13060 ≤ 254566422474142 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13060 ≤ 254566422474141 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13060)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26120 ^ 2)
    ((1250000000000000000/205146000279413498472091))
    ((25000000000000000000/4102762925955590479766837)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26120) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26120 : ℝ)^2 / (mW 13060 : ℝ)) * (1 + 1/10^6)^2 *
    √(((990001/500000000000))/2) * ((1-firstRatio 26120) * √(1-firstRatio 26120) *
      sixthConstant (e1CovarianceRatio 26120 (mW 13060) (1/10^6) rowEps))) /
    (712/10000 - 26120*(1+1/10^6)*((990001/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26120 (mW 13060) /
    ((1/10^5) * ((mW 13060 : ℝ)*26120*((mW 13060 : ℝ)+26120+1)))^2 +
  8*(mW 13060 : ℝ)*26120*(26120+2)*(26120+3) /
    ((1/1000)*((mW 13060 : ℝ)*26120*(26120+2)))^2 +
  covarianceVarianceBound 26120 (mW 13060) /
    ((1/1000)*covarianceMeanBound 26120 (mW 13060))^2 +
  normVarianceBound 26120 (mW 13060) / (3*inputVarianceMean 26120 (mW 13060))^2

end BstLean.Part268.WorldRow13060
namespace BstLean.Part268.WorldRow13061
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13061 = 254634651245944 := by
  have hu : mW 13061 ≤ 254634651245944 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13061 ≤ 254634651245943 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13061)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26122 ^ 2)
    ((25000000000000000000/4103234164853628948765667))
    ((25000000000000000000/4103077085220949459090683)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26122) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26122 : ℝ)^2 / (mW 13061 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1979849/1000000000000))/2) * ((1-firstRatio 26122) * √(1-firstRatio 26122) *
      sixthConstant (e1CovarianceRatio 26122 (mW 13061) (1/10^6) rowEps))) /
    (712/10000 - 26122*(1+1/10^6)*((1979849/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26122 (mW 13061) /
    ((1/10^5) * ((mW 13061 : ℝ)*26122*((mW 13061 : ℝ)+26122+1)))^2 +
  8*(mW 13061 : ℝ)*26122*(26122+2)*(26122+3) /
    ((1/1000)*((mW 13061 : ℝ)*26122*(26122+2)))^2 +
  covarianceVarianceBound 26122 (mW 13061) /
    ((1/1000)*covarianceMeanBound 26122 (mW 13061))^2 +
  normVarianceBound 26122 (mW 13061) / (3*inputVarianceMean 26122 (mW 13061))^2

end BstLean.Part268.WorldRow13061
namespace BstLean.Part268.WorldRow13062
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13062 = 254702893078633 := by
  have hu : mW 13062 ≤ 254702893078633 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13062 ≤ 254702893078632 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13062)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26124 ^ 2)
    ((12500000000000000000/2051774162059493964044757))
    ((25000000000000000000/4103391244486308438414529)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26124) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26124 : ℝ)^2 / (mW 13062 : ℝ)) * (1 + 1/10^6)^2 *
    √(((123731/62500000000))/2) * ((1-firstRatio 26124) * √(1-firstRatio 26124) *
      sixthConstant (e1CovarianceRatio 26124 (mW 13062) (1/10^6) rowEps))) /
    (712/10000 - 26124*(1+1/10^6)*((123731/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26124 (mW 13062) /
    ((1/10^5) * ((mW 13062 : ℝ)*26124*((mW 13062 : ℝ)+26124+1)))^2 +
  8*(mW 13062 : ℝ)*26124*(26124+2)*(26124+3) /
    ((1/1000)*((mW 13062 : ℝ)*26124*(26124+2)))^2 +
  covarianceVarianceBound 26124 (mW 13062) /
    ((1/1000)*covarianceMeanBound 26124 (mW 13062))^2 +
  normVarianceBound 26124 (mW 13062) / (3*inputVarianceMean 26124 (mW 13062))^2

end BstLean.Part268.WorldRow13062
namespace BstLean.Part268.WorldRow13063
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13063 = 254771147973710 := by
  have hu : mW 13063 ≤ 254771147973710 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13063 ≤ 254771147973709 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13063)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26126 ^ 2)
    ((25000000000000000000/4103862483384346907413361))
    ((200000000000000000/32829643230013339341907)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26126) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26126 : ℝ)^2 / (mW 13063 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1979543/1000000000000))/2) * ((1-firstRatio 26126) * √(1-firstRatio 26126) *
      sixthConstant (e1CovarianceRatio 26126 (mW 13063) (1/10^6) rowEps))) /
    (712/10000 - 26126*(1+1/10^6)*((1979543/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26126 (mW 13063) /
    ((1/10^5) * ((mW 13063 : ℝ)*26126*((mW 13063 : ℝ)+26126+1)))^2 +
  8*(mW 13063 : ℝ)*26126*(26126+2)*(26126+3) /
    ((1/1000)*((mW 13063 : ℝ)*26126*(26126+2)))^2 +
  covarianceVarianceBound 26126 (mW 13063) /
    ((1/1000)*covarianceMeanBound 26126 (mW 13063))^2 +
  normVarianceBound 26126 (mW 13063) / (3*inputVarianceMean 26126 (mW 13063))^2

end BstLean.Part268.WorldRow13063
namespace BstLean.Part268.WorldRow13064
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13064 = 254839415932675 := by
  have hu : mW 13064 ≤ 254839415932675 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13064 ≤ 254839415932674 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13064)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26128 ^ 2)
    ((3125000000000000000/513022080331213235842151))
    ((25000000000000000000/4104019563017026397062221)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26128) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26128 : ℝ)^2 / (mW 13064 : ℝ)) * (1 + 1/10^6)^2 *
    √(((197939/100000000000))/2) * ((1-firstRatio 26128) * √(1-firstRatio 26128) *
      sixthConstant (e1CovarianceRatio 26128 (mW 13064) (1/10^6) rowEps))) /
    (712/10000 - 26128*(1+1/10^6)*((197939/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26128 (mW 13064) /
    ((1/10^5) * ((mW 13064 : ℝ)*26128*((mW 13064 : ℝ)+26128+1)))^2 +
  8*(mW 13064 : ℝ)*26128*(26128+2)*(26128+3) /
    ((1/1000)*((mW 13064 : ℝ)*26128*(26128+2)))^2 +
  covarianceVarianceBound 26128 (mW 13064) /
    ((1/1000)*covarianceMeanBound 26128 (mW 13064))^2 +
  normVarianceBound 26128 (mW 13064) / (3*inputVarianceMean 26128 (mW 13064))^2

end BstLean.Part268.WorldRow13064
namespace BstLean.Part268.WorldRow13065
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13065 = 254907696957027 := by
  have hu : mW 13065 ≤ 254907696957027 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13065 ≤ 254907696957026 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13065)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26130 ^ 2)
    ((5000000000000000000/820898160383012973212211))
    ((25000000000000000000/4104333722282385376386067)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26130) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26130 : ℝ)^2 / (mW 13065 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1979237/1000000000000))/2) * ((1-firstRatio 26130) * √(1-firstRatio 26130) *
      sixthConstant (e1CovarianceRatio 26130 (mW 13065) (1/10^6) rowEps))) /
    (712/10000 - 26130*(1+1/10^6)*((1979237/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26130 (mW 13065) /
    ((1/10^5) * ((mW 13065 : ℝ)*26130*((mW 13065 : ℝ)+26130+1)))^2 +
  8*(mW 13065 : ℝ)*26130*(26130+2)*(26130+3) /
    ((1/1000)*((mW 13065 : ℝ)*26130*(26130+2)))^2 +
  covarianceVarianceBound 26130 (mW 13065) /
    ((1/1000)*covarianceMeanBound 26130 (mW 13065))^2 +
  normVarianceBound 26130 (mW 13065) / (3*inputVarianceMean 26130 (mW 13065))^2

end BstLean.Part268.WorldRow13065
namespace BstLean.Part268.WorldRow13066
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13066 = 254975991048268 := by
  have hu : mW 13066 ≤ 254975991048268 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13066 ≤ 254975991048267 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13066)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26132 ^ 2)
    ((12500000000000000000/2052402480590211922692451))
    ((25000000000000000000/4104647881547744355709913)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26132) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26132 : ℝ)^2 / (mW 13066 : ℝ)) * (1 + 1/10^6)^2 *
    √(((494771/250000000000))/2) * ((1-firstRatio 26132) * √(1-firstRatio 26132) *
      sixthConstant (e1CovarianceRatio 26132 (mW 13066) (1/10^6) rowEps))) /
    (712/10000 - 26132*(1+1/10^6)*((494771/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26132 (mW 13066) /
    ((1/10^5) * ((mW 13066 : ℝ)*26132*((mW 13066 : ℝ)+26132+1)))^2 +
  8*(mW 13066 : ℝ)*26132*(26132+2)*(26132+3) /
    ((1/1000)*((mW 13066 : ℝ)*26132*(26132+2)))^2 +
  covarianceVarianceBound 26132 (mW 13066) /
    ((1/1000)*covarianceMeanBound 26132 (mW 13066))^2 +
  normVarianceBound 26132 (mW 13066) / (3*inputVarianceMean 26132 (mW 13066))^2

end BstLean.Part268.WorldRow13066
namespace BstLean.Part268.WorldRow13067
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13067 = 255044298207898 := by
  have hu : mW 13067 ≤ 255044298207898 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13067 ≤ 255044298207897 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13067)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26134 ^ 2)
    ((25000000000000000000/4105119120445782824708749))
    ((25000000000000000000/4104962040813103335033759)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26134) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26134 : ℝ)^2 / (mW 13067 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1978931/1000000000000))/2) * ((1-firstRatio 26134) * √(1-firstRatio 26134) *
      sixthConstant (e1CovarianceRatio 26134 (mW 13067) (1/10^6) rowEps))) /
    (712/10000 - 26134*(1+1/10^6)*((1978931/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26134 (mW 13067) /
    ((1/10^5) * ((mW 13067 : ℝ)*26134*((mW 13067 : ℝ)+26134+1)))^2 +
  8*(mW 13067 : ℝ)*26134*(26134+2)*(26134+3) /
    ((1/1000)*((mW 13067 : ℝ)*26134*(26134+2)))^2 +
  covarianceVarianceBound 26134 (mW 13067) /
    ((1/1000)*covarianceMeanBound 26134 (mW 13067))^2 +
  normVarianceBound 26134 (mW 13067) / (3*inputVarianceMean 26134 (mW 13067))^2

end BstLean.Part268.WorldRow13067
namespace BstLean.Part268.WorldRow13068
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13068 = 255112618437416 := by
  have hu : mW 13068 ≤ 255112618437416 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13068 ≤ 255112618437415 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13068)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26136 ^ 2)
    ((6250000000000000000/1026358319927785451008149))
    ((5000000000000000000/821055240015692462871521)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26136) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26136 : ℝ)^2 / (mW 13068 : ℝ)) * (1 + 1/10^6)^2 *
    √(((989389/500000000000))/2) * ((1-firstRatio 26136) * √(1-firstRatio 26136) *
      sixthConstant (e1CovarianceRatio 26136 (mW 13068) (1/10^6) rowEps))) /
    (712/10000 - 26136*(1+1/10^6)*((989389/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26136 (mW 13068) /
    ((1/10^5) * ((mW 13068 : ℝ)*26136*((mW 13068 : ℝ)+26136+1)))^2 +
  8*(mW 13068 : ℝ)*26136*(26136+2)*(26136+3) /
    ((1/1000)*((mW 13068 : ℝ)*26136*(26136+2)))^2 +
  covarianceVarianceBound 26136 (mW 13068) /
    ((1/1000)*covarianceMeanBound 26136 (mW 13068))^2 +
  normVarianceBound 26136 (mW 13068) / (3*inputVarianceMean 26136 (mW 13068))^2

end BstLean.Part268.WorldRow13068
namespace BstLean.Part268.WorldRow13069
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13069 = 255180951738323 := by
  have hu : mW 13069 ≤ 255180951738323 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13069 ≤ 255180951738322 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13069)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26138 ^ 2)
    ((25000000000000000000/4105747438976500783356443))
    ((25000000000000000000/4105590359343821293681451)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26138) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26138 : ℝ)^2 / (mW 13069 : ℝ)) * (1 + 1/10^6)^2 *
    √(((15829/8000000000))/2) * ((1-firstRatio 26138) * √(1-firstRatio 26138) *
      sixthConstant (e1CovarianceRatio 26138 (mW 13069) (1/10^6) rowEps))) /
    (712/10000 - 26138*(1+1/10^6)*((15829/8000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26138 (mW 13069) /
    ((1/10^5) * ((mW 13069 : ℝ)*26138*((mW 13069 : ℝ)+26138+1)))^2 +
  8*(mW 13069 : ℝ)*26138*(26138+2)*(26138+3) /
    ((1/1000)*((mW 13069 : ℝ)*26138*(26138+2)))^2 +
  covarianceVarianceBound 26138 (mW 13069) /
    ((1/1000)*covarianceMeanBound 26138 (mW 13069))^2 +
  normVarianceBound 26138 (mW 13069) / (3*inputVarianceMean 26138 (mW 13069))^2

end BstLean.Part268.WorldRow13069
namespace BstLean.Part268.WorldRow13070
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13070 = 255249298112120 := by
  have hu : mW 13070 ≤ 255249298112120 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13070 ≤ 255249298112119 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13070)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26140 ^ 2)
    ((2500000000000000000/410606159824185976268029))
    ((25000000000000000000/4105904518609180273005297)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26140) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26140 : ℝ)^2 / (mW 13070 : ℝ)) * (1 + 1/10^6)^2 *
    √(((247309/125000000000))/2) * ((1-firstRatio 26140) * √(1-firstRatio 26140) *
      sixthConstant (e1CovarianceRatio 26140 (mW 13070) (1/10^6) rowEps))) /
    (712/10000 - 26140*(1+1/10^6)*((247309/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26140 (mW 13070) /
    ((1/10^5) * ((mW 13070 : ℝ)*26140*((mW 13070 : ℝ)+26140+1)))^2 +
  8*(mW 13070 : ℝ)*26140*(26140+2)*(26140+3) /
    ((1/1000)*((mW 13070 : ℝ)*26140*(26140+2)))^2 +
  covarianceVarianceBound 26140 (mW 13070) /
    ((1/1000)*covarianceMeanBound 26140 (mW 13070))^2 +
  normVarianceBound 26140 (mW 13070) / (3*inputVarianceMean 26140 (mW 13070))^2

end BstLean.Part268.WorldRow13070
namespace BstLean.Part268.WorldRow13071
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13071 = 255317657560306 := by
  have hu : mW 13071 ≤ 255317657560306 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13071 ≤ 255317657560305 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13071)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26142 ^ 2)
    ((25000000000000000000/4106375757507218742004137))
    ((25000000000000000000/4106218677874539252329143)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26142) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26142 : ℝ)^2 / (mW 13071 : ℝ)) * (1 + 1/10^6)^2 *
    √(((24729/12500000000))/2) * ((1-firstRatio 26142) * √(1-firstRatio 26142) *
      sixthConstant (e1CovarianceRatio 26142 (mW 13071) (1/10^6) rowEps))) /
    (712/10000 - 26142*(1+1/10^6)*((24729/12500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26142 (mW 13071) /
    ((1/10^5) * ((mW 13071 : ℝ)*26142*((mW 13071 : ℝ)+26142+1)))^2 +
  8*(mW 13071 : ℝ)*26142*(26142+2)*(26142+3) /
    ((1/1000)*((mW 13071 : ℝ)*26142*(26142+2)))^2 +
  covarianceVarianceBound 26142 (mW 13071) /
    ((1/1000)*covarianceMeanBound 26142 (mW 13071))^2 +
  normVarianceBound 26142 (mW 13071) / (3*inputVarianceMean 26142 (mW 13071))^2

end BstLean.Part268.WorldRow13071
namespace BstLean.Part268.WorldRow13072
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13072 = 255386030084383 := by
  have hu : mW 13072 ≤ 255386030084383 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13072 ≤ 255386030084382 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13072)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26144 ^ 2)
    ((1562500000000000000/256668119798286107582999))
    ((25000000000000000000/4106532837139898231652989)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26144) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26144 : ℝ)^2 / (mW 13072 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1978167/1000000000000))/2) * ((1-firstRatio 26144) * √(1-firstRatio 26144) *
      sixthConstant (e1CovarianceRatio 26144 (mW 13072) (1/10^6) rowEps))) /
    (712/10000 - 26144*(1+1/10^6)*((1978167/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26144 (mW 13072) /
    ((1/10^5) * ((mW 13072 : ℝ)*26144*((mW 13072 : ℝ)+26144+1)))^2 +
  8*(mW 13072 : ℝ)*26144*(26144+2)*(26144+3) /
    ((1/1000)*((mW 13072 : ℝ)*26144*(26144+2)))^2 +
  covarianceVarianceBound 26144 (mW 13072) /
    ((1/1000)*covarianceMeanBound 26144 (mW 13072))^2 +
  normVarianceBound 26144 (mW 13072) / (3*inputVarianceMean 26144 (mW 13072))^2

end BstLean.Part268.WorldRow13072
namespace BstLean.Part268.WorldRow13073
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13073 = 255454415685852 := by
  have hu : mW 13073 ≤ 255454415685852 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13073 ≤ 255454415685851 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13073)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26146 ^ 2)
    ((25000000000000000000/4107004076037936700651831))
    ((5000000000000000000/821369399281051442195367)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26146) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26146 : ℝ)^2 / (mW 13073 : ℝ)) * (1 + 1/10^6)^2 *
    √(((989007/500000000000))/2) * ((1-firstRatio 26146) * √(1-firstRatio 26146) *
      sixthConstant (e1CovarianceRatio 26146 (mW 13073) (1/10^6) rowEps))) /
    (712/10000 - 26146*(1+1/10^6)*((989007/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26146 (mW 13073) /
    ((1/10^5) * ((mW 13073 : ℝ)*26146*((mW 13073 : ℝ)+26146+1)))^2 +
  8*(mW 13073 : ℝ)*26146*(26146+2)*(26146+3) /
    ((1/1000)*((mW 13073 : ℝ)*26146*(26146+2)))^2 +
  covarianceVarianceBound 26146 (mW 13073) /
    ((1/1000)*covarianceMeanBound 26146 (mW 13073))^2 +
  normVarianceBound 26146 (mW 13073) / (3*inputVarianceMean 26146 (mW 13073))^2

end BstLean.Part268.WorldRow13073
namespace BstLean.Part268.WorldRow13074
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13074 = 255522814366212 := by
  have hu : mW 13074 ≤ 255522814366212 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13074 ≤ 255522814366211 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13074)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26148 ^ 2)
    ((12500000000000000000/2053659117651647839987839))
    ((25000000000000000000/4107161155670616190300681)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26148) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26148 : ℝ)^2 / (mW 13074 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1977861/1000000000000))/2) * ((1-firstRatio 26148) * √(1-firstRatio 26148) *
      sixthConstant (e1CovarianceRatio 26148 (mW 13074) (1/10^6) rowEps))) /
    (712/10000 - 26148*(1+1/10^6)*((1977861/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26148 (mW 13074) /
    ((1/10^5) * ((mW 13074 : ℝ)*26148*((mW 13074 : ℝ)+26148+1)))^2 +
  8*(mW 13074 : ℝ)*26148*(26148+2)*(26148+3) /
    ((1/1000)*((mW 13074 : ℝ)*26148*(26148+2)))^2 +
  covarianceVarianceBound 26148 (mW 13074) /
    ((1/1000)*covarianceMeanBound 26148 (mW 13074))^2 +
  normVarianceBound 26148 (mW 13074) / (3*inputVarianceMean 26148 (mW 13074))^2

end BstLean.Part268.WorldRow13074
