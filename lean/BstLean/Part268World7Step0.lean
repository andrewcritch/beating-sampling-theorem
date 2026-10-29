import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar7
namespace BstLean.Part268.WorldRow12525
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12525 = 219898400749304 := by
  have hu : mW 12525 ≤ 219898400749304 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12525 ≤ 219898400749303 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12525)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25050 ^ 2)
    ((1000000000000000000/157393791944848641247347))
    ((25000000000000000000/3934687718988536541509227)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25050) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25050 : ℝ)^2 / (mW 12525 : ℝ)) * (1 + 1/10^6)^2 *
    √(((206547/100000000000))/2) * ((1-firstRatio 25050) * √(1-firstRatio 25050) *
      sixthConstant (e1CovarianceRatio 25050 (mW 12525) (1/10^6) rowEps))) /
    (712/10000 - 25050*(1+1/10^6)*((206547/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25050 (mW 12525) /
    ((1/10^5) * ((mW 12525 : ℝ)*25050*((mW 12525 : ℝ)+25050+1)))^2 +
  8*(mW 12525 : ℝ)*25050*(25050+2)*(25050+3) /
    ((1/1000)*((mW 12525 : ℝ)*25050*(25050+2)))^2 +
  covarianceVarianceBound 25050 (mW 12525) /
    ((1/1000)*covarianceMeanBound 25050 (mW 12525))^2 +
  normVarianceBound 25050 (mW 12525) / (3*inputVarianceMean 25050 (mW 12525))^2

end BstLean.Part268.WorldRow12525
namespace BstLean.Part268.WorldRow12526
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12526 = 219959855537049 := by
  have hu : mW 12526 ≤ 219959855537049 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12526 ≤ 219959855537048 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12526)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25052 ^ 2)
    ((12500000000000000000/1967579478943287505253761))
    ((25000000000000000000/3935001878253895520833073)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25052) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25052 : ℝ)^2 / (mW 12526 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2065303/1000000000000))/2) * ((1-firstRatio 25052) * √(1-firstRatio 25052) *
      sixthConstant (e1CovarianceRatio 25052 (mW 12526) (1/10^6) rowEps))) /
    (712/10000 - 25052*(1+1/10^6)*((2065303/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25052 (mW 12526) /
    ((1/10^5) * ((mW 12526 : ℝ)*25052*((mW 12526 : ℝ)+25052+1)))^2 +
  8*(mW 12526 : ℝ)*25052*(25052+2)*(25052+3) /
    ((1/1000)*((mW 12526 : ℝ)*25052*(25052+2)))^2 +
  covarianceVarianceBound 25052 (mW 12526) /
    ((1/1000)*covarianceMeanBound 25052 (mW 12526))^2 +
  normVarianceBound 25052 (mW 12526) / (3*inputVarianceMean 25052 (mW 12526))^2

end BstLean.Part268.WorldRow12526
namespace BstLean.Part268.WorldRow12527
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12527 = 220021322591463 := by
  have hu : mW 12527 ≤ 220021322591463 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12527 ≤ 220021322591462 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12527)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25054 ^ 2)
    ((25000000000000000000/3935473117151933989831369))
    ((25000000000000000000/3935316037519254500156919)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25054) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25054 : ℝ)^2 / (mW 12527 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2065137/1000000000000))/2) * ((1-firstRatio 25054) * √(1-firstRatio 25054) *
      sixthConstant (e1CovarianceRatio 25054 (mW 12527) (1/10^6) rowEps))) /
    (712/10000 - 25054*(1+1/10^6)*((2065137/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25054 (mW 12527) /
    ((1/10^5) * ((mW 12527 : ℝ)*25054*((mW 12527 : ℝ)+25054+1)))^2 +
  8*(mW 12527 : ℝ)*25054*(25054+2)*(25054+3) /
    ((1/1000)*((mW 12527 : ℝ)*25054*(25054+2)))^2 +
  covarianceVarianceBound 25054 (mW 12527) /
    ((1/1000)*covarianceMeanBound 25054 (mW 12527))^2 +
  normVarianceBound 25054 (mW 12527) / (3*inputVarianceMean 25054 (mW 12527))^2

end BstLean.Part268.WorldRow12527
namespace BstLean.Part268.WorldRow12528
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12528 = 220082801914017 := by
  have hu : mW 12528 ≤ 220082801914017 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12528 ≤ 220082801914016 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12528)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25056 ^ 2)
    ((1562500000000000000/245986704776080810572201))
    ((5000000000000000000/787126039356922695896153)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25056) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25056 : ℝ)^2 / (mW 12528 : ℝ)) * (1 + 1/10^6)^2 *
    √(((206497/100000000000))/2) * ((1-firstRatio 25056) * √(1-firstRatio 25056) *
      sixthConstant (e1CovarianceRatio 25056 (mW 12528) (1/10^6) rowEps))) /
    (712/10000 - 25056*(1+1/10^6)*((206497/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25056 (mW 12528) /
    ((1/10^5) * ((mW 12528 : ℝ)*25056*((mW 12528 : ℝ)+25056+1)))^2 +
  8*(mW 12528 : ℝ)*25056*(25056+2)*(25056+3) /
    ((1/1000)*((mW 12528 : ℝ)*25056*(25056+2)))^2 +
  covarianceVarianceBound 25056 (mW 12528) /
    ((1/1000)*covarianceMeanBound 25056 (mW 12528))^2 +
  normVarianceBound 25056 (mW 12528) / (3*inputVarianceMean 25056 (mW 12528))^2

end BstLean.Part268.WorldRow12528
namespace BstLean.Part268.WorldRow12529
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12529 = 220144293506177 := by
  have hu : mW 12529 ≤ 220144293506177 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12529 ≤ 220144293506176 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12529)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25058 ^ 2)
    ((25000000000000000000/3936101435682651948479063))
    ((25000000000000000000/3935944356049972458804611)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25058) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25058 : ℝ)^2 / (mW 12529 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2064803/1000000000000))/2) * ((1-firstRatio 25058) * √(1-firstRatio 25058) *
      sixthConstant (e1CovarianceRatio 25058 (mW 12529) (1/10^6) rowEps))) /
    (712/10000 - 25058*(1+1/10^6)*((2064803/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25058 (mW 12529) /
    ((1/10^5) * ((mW 12529 : ℝ)*25058*((mW 12529 : ℝ)+25058+1)))^2 +
  8*(mW 12529 : ℝ)*25058*(25058+2)*(25058+3) /
    ((1/1000)*((mW 12529 : ℝ)*25058*(25058+2)))^2 +
  covarianceVarianceBound 25058 (mW 12529) /
    ((1/1000)*covarianceMeanBound 25058 (mW 12529))^2 +
  normVarianceBound 25058 (mW 12529) / (3*inputVarianceMean 25058 (mW 12529))^2

end BstLean.Part268.WorldRow12529
namespace BstLean.Part268.WorldRow12530
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12530 = 220205797369414 := by
  have hu : mW 12530 ≤ 220205797369414 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12530 ≤ 220205797369413 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12530)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25060 ^ 2)
    ((2500000000000000000/393641559494801092780291))
    ((25000000000000000000/3936258515315331438128457)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25060) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25060 : ℝ)^2 / (mW 12530 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2064637/1000000000000))/2) * ((1-firstRatio 25060) * √(1-firstRatio 25060) *
      sixthConstant (e1CovarianceRatio 25060 (mW 12530) (1/10^6) rowEps))) /
    (712/10000 - 25060*(1+1/10^6)*((2064637/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25060 (mW 12530) /
    ((1/10^5) * ((mW 12530 : ℝ)*25060*((mW 12530 : ℝ)+25060+1)))^2 +
  8*(mW 12530 : ℝ)*25060*(25060+2)*(25060+3) /
    ((1/1000)*((mW 12530 : ℝ)*25060*(25060+2)))^2 +
  covarianceVarianceBound 25060 (mW 12530) /
    ((1/1000)*covarianceMeanBound 25060 (mW 12530))^2 +
  normVarianceBound 25060 (mW 12530) / (3*inputVarianceMean 25060 (mW 12530))^2

end BstLean.Part268.WorldRow12530
namespace BstLean.Part268.WorldRow12531
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12531 = 220267313505197 := by
  have hu : mW 12531 ≤ 220267313505197 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12531 ≤ 220267313505196 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12531)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25062 ^ 2)
    ((25000000000000000000/3936729754213369907126757))
    ((25000000000000000000/3936572674580690417452303)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25062) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25062 : ℝ)^2 / (mW 12531 : ℝ)) * (1 + 1/10^6)^2 *
    √(((206447/100000000000))/2) * ((1-firstRatio 25062) * √(1-firstRatio 25062) *
      sixthConstant (e1CovarianceRatio 25062 (mW 12531) (1/10^6) rowEps))) /
    (712/10000 - 25062*(1+1/10^6)*((206447/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25062 (mW 12531) /
    ((1/10^5) * ((mW 12531 : ℝ)*25062*((mW 12531 : ℝ)+25062+1)))^2 +
  8*(mW 12531 : ℝ)*25062*(25062+2)*(25062+3) /
    ((1/1000)*((mW 12531 : ℝ)*25062*(25062+2)))^2 +
  covarianceVarianceBound 25062 (mW 12531) /
    ((1/1000)*covarianceMeanBound 25062 (mW 12531))^2 +
  normVarianceBound 25062 (mW 12531) / (3*inputVarianceMean 25062 (mW 12531))^2

end BstLean.Part268.WorldRow12531
namespace BstLean.Part268.WorldRow12532
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12532 = 220328841914995 := by
  have hu : mW 12532 ≤ 220328841914995 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12532 ≤ 220328841914994 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12532)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25064 ^ 2)
    ((6250000000000000000/984260978369682221612651))
    ((25000000000000000000/3936886833846049396776149)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25064) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25064 : ℝ)^2 / (mW 12532 : ℝ)) * (1 + 1/10^6)^2 *
    √(((129019/62500000000))/2) * ((1-firstRatio 25064) * √(1-firstRatio 25064) *
      sixthConstant (e1CovarianceRatio 25064 (mW 12532) (1/10^6) rowEps))) /
    (712/10000 - 25064*(1+1/10^6)*((129019/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25064 (mW 12532) /
    ((1/10^5) * ((mW 12532 : ℝ)*25064*((mW 12532 : ℝ)+25064+1)))^2 +
  8*(mW 12532 : ℝ)*25064*(25064+2)*(25064+3) /
    ((1/1000)*((mW 12532 : ℝ)*25064*(25064+2)))^2 +
  covarianceVarianceBound 25064 (mW 12532) /
    ((1/1000)*covarianceMeanBound 25064 (mW 12532))^2 +
  normVarianceBound 25064 (mW 12532) / (3*inputVarianceMean 25064 (mW 12532))^2

end BstLean.Part268.WorldRow12532
namespace BstLean.Part268.WorldRow12533
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12533 = 220390382600277 := by
  have hu : mW 12533 ≤ 220390382600277 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12533 ≤ 220390382600276 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12533)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25066 ^ 2)
    ((25000000000000000000/3937358072744087865774451))
    ((5000000000000000000/787440198622281675219999)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25066) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25066 : ℝ)^2 / (mW 12533 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2064137/1000000000000))/2) * ((1-firstRatio 25066) * √(1-firstRatio 25066) *
      sixthConstant (e1CovarianceRatio 25066 (mW 12533) (1/10^6) rowEps))) /
    (712/10000 - 25066*(1+1/10^6)*((2064137/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25066 (mW 12533) /
    ((1/10^5) * ((mW 12533 : ℝ)*25066*((mW 12533 : ℝ)+25066+1)))^2 +
  8*(mW 12533 : ℝ)*25066*(25066+2)*(25066+3) /
    ((1/1000)*((mW 12533 : ℝ)*25066*(25066+2)))^2 +
  covarianceVarianceBound 25066 (mW 12533) /
    ((1/1000)*covarianceMeanBound 25066 (mW 12533))^2 +
  normVarianceBound 25066 (mW 12533) / (3*inputVarianceMean 25066 (mW 12533))^2

end BstLean.Part268.WorldRow12533
namespace BstLean.Part268.WorldRow12534
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12534 = 220451935562513 := by
  have hu : mW 12534 ≤ 220451935562513 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12534 ≤ 220451935562512 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12534)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25068 ^ 2)
    ((12500000000000000000/1968836116004723422549149))
    ((25000000000000000000/3937515152376767355423841)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25068) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25068 : ℝ)^2 / (mW 12534 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2063971/1000000000000))/2) * ((1-firstRatio 25068) * √(1-firstRatio 25068) *
      sixthConstant (e1CovarianceRatio 25068 (mW 12534) (1/10^6) rowEps))) /
    (712/10000 - 25068*(1+1/10^6)*((2063971/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25068 (mW 12534) /
    ((1/10^5) * ((mW 12534 : ℝ)*25068*((mW 12534 : ℝ)+25068+1)))^2 +
  8*(mW 12534 : ℝ)*25068*(25068+2)*(25068+3) /
    ((1/1000)*((mW 12534 : ℝ)*25068*(25068+2)))^2 +
  covarianceVarianceBound 25068 (mW 12534) /
    ((1/1000)*covarianceMeanBound 25068 (mW 12534))^2 +
  normVarianceBound 25068 (mW 12534) / (3*inputVarianceMean 25068 (mW 12534))^2

end BstLean.Part268.WorldRow12534
namespace BstLean.Part268.WorldRow12535
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12535 = 220513500803172 := by
  have hu : mW 12535 ≤ 220513500803172 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12535 ≤ 220513500803171 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12535)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25070 ^ 2)
    ((5000000000000000000/787597278254961164884429))
    ((25000000000000000000/3937829311642126334747687)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25070) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25070 : ℝ)^2 / (mW 12535 : ℝ)) * (1 + 1/10^6)^2 *
    √(((412761/200000000000))/2) * ((1-firstRatio 25070) * √(1-firstRatio 25070) *
      sixthConstant (e1CovarianceRatio 25070 (mW 12535) (1/10^6) rowEps))) /
    (712/10000 - 25070*(1+1/10^6)*((412761/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25070 (mW 12535) /
    ((1/10^5) * ((mW 12535 : ℝ)*25070*((mW 12535 : ℝ)+25070+1)))^2 +
  8*(mW 12535 : ℝ)*25070*(25070+2)*(25070+3) /
    ((1/1000)*((mW 12535 : ℝ)*25070*(25070+2)))^2 +
  covarianceVarianceBound 25070 (mW 12535) /
    ((1/1000)*covarianceMeanBound 25070 (mW 12535))^2 +
  normVarianceBound 25070 (mW 12535) / (3*inputVarianceMean 25070 (mW 12535))^2

end BstLean.Part268.WorldRow12535
namespace BstLean.Part268.WorldRow12536
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12536 = 220575078323723 := by
  have hu : mW 12536 ≤ 220575078323723 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12536 ≤ 220575078323722 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12536)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25072 ^ 2)
    ((3125000000000000000/492287568817520600468249))
    ((25000000000000000000/3938143470907485314071533)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25072) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25072 : ℝ)^2 / (mW 12536 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1031819/500000000000))/2) * ((1-firstRatio 25072) * √(1-firstRatio 25072) *
      sixthConstant (e1CovarianceRatio 25072 (mW 12536) (1/10^6) rowEps))) /
    (712/10000 - 25072*(1+1/10^6)*((1031819/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25072 (mW 12536) /
    ((1/10^5) * ((mW 12536 : ℝ)*25072*((mW 12536 : ℝ)+25072+1)))^2 +
  8*(mW 12536 : ℝ)*25072*(25072+2)*(25072+3) /
    ((1/1000)*((mW 12536 : ℝ)*25072*(25072+2)))^2 +
  covarianceVarianceBound 25072 (mW 12536) /
    ((1/1000)*covarianceMeanBound 25072 (mW 12536))^2 +
  normVarianceBound 25072 (mW 12536) / (3*inputVarianceMean 25072 (mW 12536))^2

end BstLean.Part268.WorldRow12536
namespace BstLean.Part268.WorldRow12537
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12537 = 220636668125635 := by
  have hu : mW 12537 ≤ 220636668125635 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12537 ≤ 220636668125634 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12537)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25074 ^ 2)
    ((25000000000000000000/3938614709805523783069839))
    ((25000000000000000000/3938457630172844293395379)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25074) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25074 : ℝ)^2 / (mW 12537 : ℝ)) * (1 + 1/10^6)^2 *
    √(((128967/62500000000))/2) * ((1-firstRatio 25074) * √(1-firstRatio 25074) *
      sixthConstant (e1CovarianceRatio 25074 (mW 12537) (1/10^6) rowEps))) /
    (712/10000 - 25074*(1+1/10^6)*((128967/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25074 (mW 12537) /
    ((1/10^5) * ((mW 12537 : ℝ)*25074*((mW 12537 : ℝ)+25074+1)))^2 +
  8*(mW 12537 : ℝ)*25074*(25074+2)*(25074+3) /
    ((1/1000)*((mW 12537 : ℝ)*25074*(25074+2)))^2 +
  covarianceVarianceBound 25074 (mW 12537) /
    ((1/1000)*covarianceMeanBound 25074 (mW 12537))^2 +
  normVarianceBound 25074 (mW 12537) / (3*inputVarianceMean 25074 (mW 12537))^2

end BstLean.Part268.WorldRow12537
namespace BstLean.Part268.WorldRow12538
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12538 = 220698270210380 := by
  have hu : mW 12538 ≤ 220698270210380 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12538 ≤ 220698270210379 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12538)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25076 ^ 2)
    ((12500000000000000000/1969464434535441381196843))
    ((1000000000000000000/157550871577528130908769)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25076) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25076 : ℝ)^2 / (mW 12538 : ℝ)) * (1 + 1/10^6)^2 *
    √(((412661/200000000000))/2) * ((1-firstRatio 25076) * √(1-firstRatio 25076) *
      sixthConstant (e1CovarianceRatio 25076 (mW 12538) (1/10^6) rowEps))) /
    (712/10000 - 25076*(1+1/10^6)*((412661/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25076 (mW 12538) /
    ((1/10^5) * ((mW 12538 : ℝ)*25076*((mW 12538 : ℝ)+25076+1)))^2 +
  8*(mW 12538 : ℝ)*25076*(25076+2)*(25076+3) /
    ((1/1000)*((mW 12538 : ℝ)*25076*(25076+2)))^2 +
  covarianceVarianceBound 25076 (mW 12538) /
    ((1/1000)*covarianceMeanBound 25076 (mW 12538))^2 +
  normVarianceBound 25076 (mW 12538) / (3*inputVarianceMean 25076 (mW 12538))^2

end BstLean.Part268.WorldRow12538
namespace BstLean.Part268.WorldRow12539
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12539 = 220759884579425 := by
  have hu : mW 12539 ≤ 220759884579425 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12539 ≤ 220759884579424 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12539)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25078 ^ 2)
    ((25000000000000000000/3939243028336241741717533))
    ((25000000000000000000/3939085948703562252043071)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25078) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25078 : ℝ)^2 / (mW 12539 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2063139/1000000000000))/2) * ((1-firstRatio 25078) * √(1-firstRatio 25078) *
      sixthConstant (e1CovarianceRatio 25078 (mW 12539) (1/10^6) rowEps))) /
    (712/10000 - 25078*(1+1/10^6)*((2063139/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25078 (mW 12539) /
    ((1/10^5) * ((mW 12539 : ℝ)*25078*((mW 12539 : ℝ)+25078+1)))^2 +
  8*(mW 12539 : ℝ)*25078*(25078+2)*(25078+3) /
    ((1/1000)*((mW 12539 : ℝ)*25078*(25078+2)))^2 +
  covarianceVarianceBound 25078 (mW 12539) /
    ((1/1000)*covarianceMeanBound 25078 (mW 12539))^2 +
  normVarianceBound 25078 (mW 12539) / (3*inputVarianceMean 25078 (mW 12539))^2

end BstLean.Part268.WorldRow12539
namespace BstLean.Part268.WorldRow12540
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12540 = 220821511234241 := by
  have hu : mW 12540 ≤ 220821511234241 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12540 ≤ 220821511234240 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12540)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25080 ^ 2)
    ((1250000000000000000/196977859380080036052069))
    ((25000000000000000000/3939400107968921231366917)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25080) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25080 : ℝ)^2 / (mW 12540 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2062973/1000000000000))/2) * ((1-firstRatio 25080) * √(1-firstRatio 25080) *
      sixthConstant (e1CovarianceRatio 25080 (mW 12540) (1/10^6) rowEps))) /
    (712/10000 - 25080*(1+1/10^6)*((2062973/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25080 (mW 12540) /
    ((1/10^5) * ((mW 12540 : ℝ)*25080*((mW 12540 : ℝ)+25080+1)))^2 +
  8*(mW 12540 : ℝ)*25080*(25080+2)*(25080+3) /
    ((1/1000)*((mW 12540 : ℝ)*25080*(25080+2)))^2 +
  covarianceVarianceBound 25080 (mW 12540) /
    ((1/1000)*covarianceMeanBound 25080 (mW 12540))^2 +
  normVarianceBound 25080 (mW 12540) / (3*inputVarianceMean 25080 (mW 12540))^2

end BstLean.Part268.WorldRow12540
namespace BstLean.Part268.WorldRow12541
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12541 = 220883150176298 := by
  have hu : mW 12541 ≤ 220883150176298 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12541 ≤ 220883150176297 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12541)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25082 ^ 2)
    ((25000000000000000000/3939871346866959700365227))
    ((25000000000000000000/3939714267234280210690763)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25082) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25082 : ℝ)^2 / (mW 12541 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2062807/1000000000000))/2) * ((1-firstRatio 25082) * √(1-firstRatio 25082) *
      sixthConstant (e1CovarianceRatio 25082 (mW 12541) (1/10^6) rowEps))) /
    (712/10000 - 25082*(1+1/10^6)*((2062807/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25082 (mW 12541) /
    ((1/10^5) * ((mW 12541 : ℝ)*25082*((mW 12541 : ℝ)+25082+1)))^2 +
  8*(mW 12541 : ℝ)*25082*(25082+2)*(25082+3) /
    ((1/1000)*((mW 12541 : ℝ)*25082*(25082+2)))^2 +
  covarianceVarianceBound 25082 (mW 12541) /
    ((1/1000)*covarianceMeanBound 25082 (mW 12541))^2 +
  normVarianceBound 25082 (mW 12541) / (3*inputVarianceMean 25082 (mW 12541))^2

end BstLean.Part268.WorldRow12541
namespace BstLean.Part268.WorldRow12542
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12542 = 220944801407065 := by
  have hu : mW 12542 ≤ 220944801407065 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12542 ≤ 220944801407064 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12542)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25084 ^ 2)
    ((12500000000000000000/1970092753066159339844537))
    ((25000000000000000000/3940028426499639190014609)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25084) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25084 : ℝ)^2 / (mW 12542 : ℝ)) * (1 + 1/10^6)^2 *
    √(((25783/12500000000))/2) * ((1-firstRatio 25084) * √(1-firstRatio 25084) *
      sixthConstant (e1CovarianceRatio 25084 (mW 12542) (1/10^6) rowEps))) /
    (712/10000 - 25084*(1+1/10^6)*((25783/12500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25084 (mW 12542) /
    ((1/10^5) * ((mW 12542 : ℝ)*25084*((mW 12542 : ℝ)+25084+1)))^2 +
  8*(mW 12542 : ℝ)*25084*(25084+2)*(25084+3) /
    ((1/1000)*((mW 12542 : ℝ)*25084*(25084+2)))^2 +
  covarianceVarianceBound 25084 (mW 12542) /
    ((1/1000)*covarianceMeanBound 25084 (mW 12542))^2 +
  normVarianceBound 25084 (mW 12542) / (3*inputVarianceMean 25084 (mW 12542))^2

end BstLean.Part268.WorldRow12542
namespace BstLean.Part268.WorldRow12543
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12543 = 221006464928012 := by
  have hu : mW 12543 ≤ 221006464928012 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12543 ≤ 221006464928011 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12543)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25086 ^ 2)
    ((25000000000000000000/3940499665397677659012921))
    ((5000000000000000000/788068517152999633867691)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25086) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25086 : ℝ)^2 / (mW 12543 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1031237/500000000000))/2) * ((1-firstRatio 25086) * √(1-firstRatio 25086) *
      sixthConstant (e1CovarianceRatio 25086 (mW 12543) (1/10^6) rowEps))) /
    (712/10000 - 25086*(1+1/10^6)*((1031237/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25086 (mW 12543) /
    ((1/10^5) * ((mW 12543 : ℝ)*25086*((mW 12543 : ℝ)+25086+1)))^2 +
  8*(mW 12543 : ℝ)*25086*(25086+2)*(25086+3) /
    ((1/1000)*((mW 12543 : ℝ)*25086*(25086+2)))^2 +
  covarianceVarianceBound 25086 (mW 12543) /
    ((1/1000)*covarianceMeanBound 25086 (mW 12543))^2 +
  normVarianceBound 25086 (mW 12543) / (3*inputVarianceMean 25086 (mW 12543))^2

end BstLean.Part268.WorldRow12543
namespace BstLean.Part268.WorldRow12544
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12544 = 221068140740608 := by
  have hu : mW 12544 ≤ 221068140740608 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12544 ≤ 221068140740607 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12544)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25088 ^ 2)
    ((97656250000000000/15393804002589986868503))
    ((25000000000000000000/3940656745030357148662301)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25088) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25088 : ℝ)^2 / (mW 12544 : ℝ)) * (1 + 1/10^6)^2 *
    √(((515577/250000000000))/2) * ((1-firstRatio 25088) * √(1-firstRatio 25088) *
      sixthConstant (e1CovarianceRatio 25088 (mW 12544) (1/10^6) rowEps))) /
    (712/10000 - 25088*(1+1/10^6)*((515577/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25088 (mW 12544) /
    ((1/10^5) * ((mW 12544 : ℝ)*25088*((mW 12544 : ℝ)+25088+1)))^2 +
  8*(mW 12544 : ℝ)*25088*(25088+2)*(25088+3) /
    ((1/1000)*((mW 12544 : ℝ)*25088*(25088+2)))^2 +
  covarianceVarianceBound 25088 (mW 12544) /
    ((1/1000)*covarianceMeanBound 25088 (mW 12544))^2 +
  normVarianceBound 25088 (mW 12544) / (3*inputVarianceMean 25088 (mW 12544))^2

end BstLean.Part268.WorldRow12544
namespace BstLean.Part268.WorldRow12545
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12545 = 221129828846326 := by
  have hu : mW 12545 ≤ 221129828846326 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12545 ≤ 221129828846325 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12545)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25090 ^ 2)
    ((5000000000000000000/788225596785679123532123))
    ((25000000000000000000/3940970904295716127986147)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25090) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25090 : ℝ)^2 / (mW 12545 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1031071/500000000000))/2) * ((1-firstRatio 25090) * √(1-firstRatio 25090) *
      sixthConstant (e1CovarianceRatio 25090 (mW 12545) (1/10^6) rowEps))) /
    (712/10000 - 25090*(1+1/10^6)*((1031071/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25090 (mW 12545) /
    ((1/10^5) * ((mW 12545 : ℝ)*25090*((mW 12545 : ℝ)+25090+1)))^2 +
  8*(mW 12545 : ℝ)*25090*(25090+2)*(25090+3) /
    ((1/1000)*((mW 12545 : ℝ)*25090*(25090+2)))^2 +
  covarianceVarianceBound 25090 (mW 12545) /
    ((1/1000)*covarianceMeanBound 25090 (mW 12545))^2 +
  normVarianceBound 25090 (mW 12545) / (3*inputVarianceMean 25090 (mW 12545))^2

end BstLean.Part268.WorldRow12545
namespace BstLean.Part268.WorldRow12546
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12546 = 221191529246633 := by
  have hu : mW 12546 ≤ 221191529246633 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12546 ≤ 221191529246632 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12546)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25092 ^ 2)
    ((12500000000000000000/1970721071596877298492231))
    ((25000000000000000000/3941285063561075107309993)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25092) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25092 : ℝ)^2 / (mW 12546 : ℝ)) * (1 + 1/10^6)^2 *
    √(((257747/125000000000))/2) * ((1-firstRatio 25092) * √(1-firstRatio 25092) *
      sixthConstant (e1CovarianceRatio 25092 (mW 12546) (1/10^6) rowEps))) /
    (712/10000 - 25092*(1+1/10^6)*((257747/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25092 (mW 12546) /
    ((1/10^5) * ((mW 12546 : ℝ)*25092*((mW 12546 : ℝ)+25092+1)))^2 +
  8*(mW 12546 : ℝ)*25092*(25092+2)*(25092+3) /
    ((1/1000)*((mW 12546 : ℝ)*25092*(25092+2)))^2 +
  covarianceVarianceBound 25092 (mW 12546) /
    ((1/1000)*covarianceMeanBound 25092 (mW 12546))^2 +
  normVarianceBound 25092 (mW 12546) / (3*inputVarianceMean 25092 (mW 12546))^2

end BstLean.Part268.WorldRow12546
namespace BstLean.Part268.WorldRow12547
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12547 = 221253241943000 := by
  have hu : mW 12547 ≤ 221253241943000 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12547 ≤ 221253241942999 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12547)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25094 ^ 2)
    ((25000000000000000000/3941756302459113576308309))
    ((25000000000000000000/3941599222826434086633839)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25094) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25094 : ℝ)^2 / (mW 12547 : ℝ)) * (1 + 1/10^6)^2 *
    √(((206181/100000000000))/2) * ((1-firstRatio 25094) * √(1-firstRatio 25094) *
      sixthConstant (e1CovarianceRatio 25094 (mW 12547) (1/10^6) rowEps))) /
    (712/10000 - 25094*(1+1/10^6)*((206181/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25094 (mW 12547) /
    ((1/10^5) * ((mW 12547 : ℝ)*25094*((mW 12547 : ℝ)+25094+1)))^2 +
  8*(mW 12547 : ℝ)*25094*(25094+2)*(25094+3) /
    ((1/1000)*((mW 12547 : ℝ)*25094*(25094+2)))^2 +
  covarianceVarianceBound 25094 (mW 12547) /
    ((1/1000)*covarianceMeanBound 25094 (mW 12547))^2 +
  normVarianceBound 25094 (mW 12547) / (3*inputVarianceMean 25094 (mW 12547))^2

end BstLean.Part268.WorldRow12547
namespace BstLean.Part268.WorldRow12548
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12548 = 221314966936897 := by
  have hu : mW 12548 ≤ 221314966936897 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12548 ≤ 221314966936896 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12548)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25096 ^ 2)
    ((6250000000000000000/985517615431118138908039))
    ((5000000000000000000/788382676418358613191537)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25096) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25096 : ℝ)^2 / (mW 12548 : ℝ)) * (1 + 1/10^6)^2 *
    √(((515411/250000000000))/2) * ((1-firstRatio 25096) * √(1-firstRatio 25096) *
      sixthConstant (e1CovarianceRatio 25096 (mW 12548) (1/10^6) rowEps))) /
    (712/10000 - 25096*(1+1/10^6)*((515411/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25096 (mW 12548) /
    ((1/10^5) * ((mW 12548 : ℝ)*25096*((mW 12548 : ℝ)+25096+1)))^2 +
  8*(mW 12548 : ℝ)*25096*(25096+2)*(25096+3) /
    ((1/1000)*((mW 12548 : ℝ)*25096*(25096+2)))^2 +
  covarianceVarianceBound 25096 (mW 12548) /
    ((1/1000)*covarianceMeanBound 25096 (mW 12548))^2 +
  normVarianceBound 25096 (mW 12548) / (3*inputVarianceMean 25096 (mW 12548))^2

end BstLean.Part268.WorldRow12548
namespace BstLean.Part268.WorldRow12549
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12549 = 221376704229795 := by
  have hu : mW 12549 ≤ 221376704229795 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12549 ≤ 221376704229794 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12549)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25098 ^ 2)
    ((25000000000000000000/3942384620989831534956003))
    ((25000000000000000000/3942227541357152045281531)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25098) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25098 : ℝ)^2 / (mW 12549 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1030739/500000000000))/2) * ((1-firstRatio 25098) * √(1-firstRatio 25098) *
      sixthConstant (e1CovarianceRatio 25098 (mW 12549) (1/10^6) rowEps))) /
    (712/10000 - 25098*(1+1/10^6)*((1030739/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25098 (mW 12549) /
    ((1/10^5) * ((mW 12549 : ℝ)*25098*((mW 12549 : ℝ)+25098+1)))^2 +
  8*(mW 12549 : ℝ)*25098*(25098+2)*(25098+3) /
    ((1/1000)*((mW 12549 : ℝ)*25098*(25098+2)))^2 +
  covarianceVarianceBound 25098 (mW 12549) /
    ((1/1000)*covarianceMeanBound 25098 (mW 12549))^2 +
  normVarianceBound 25098 (mW 12549) / (3*inputVarianceMean 25098 (mW 12549))^2

end BstLean.Part268.WorldRow12549
