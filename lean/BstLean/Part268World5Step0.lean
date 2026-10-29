import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar5
namespace BstLean.Part268.WorldRow12475
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12475 = 216841268918506 := by
  have hu : mW 12475 ≤ 216841268918506 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12475 ≤ 216841268918505 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12475)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24950 ^ 2)
    ((1000000000000000000/156765473414130682599653))
    ((25000000000000000000/3918979755720587575316927)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24950) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24950 : ℝ)^2 / (mW 12475 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2073837/1000000000000))/2) * ((1-firstRatio 24950) * √(1-firstRatio 24950) *
      sixthConstant (e1CovarianceRatio 24950 (mW 12475) (1/10^6) rowEps))) /
    (712/10000 - 24950*(1+1/10^6)*((2073837/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24950 (mW 12475) /
    ((1/10^5) * ((mW 12475 : ℝ)*24950*((mW 12475 : ℝ)+24950+1)))^2 +
  8*(mW 12475 : ℝ)*24950*(24950+2)*(24950+3) /
    ((1/1000)*((mW 12475 : ℝ)*24950*(24950+2)))^2 +
  covarianceVarianceBound 24950 (mW 12475) /
    ((1/1000)*covarianceMeanBound 24950 (mW 12475))^2 +
  normVarianceBound 24950 (mW 12475) / (3*inputVarianceMean 24950 (mW 12475))^2

end BstLean.Part268.WorldRow12475
namespace BstLean.Part268.WorldRow12476
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12476 = 216902112244421 := by
  have hu : mW 12476 ≤ 216902112244421 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12476 ≤ 216902112244420 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12476)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24952 ^ 2)
    ((6250000000000000000/979862748654656511078793))
    ((25000000000000000000/3919293914985946554640773)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24952) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24952 : ℝ)^2 / (mW 12476 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2073669/1000000000000))/2) * ((1-firstRatio 24952) * √(1-firstRatio 24952) *
      sixthConstant (e1CovarianceRatio 24952 (mW 12476) (1/10^6) rowEps))) /
    (712/10000 - 24952*(1+1/10^6)*((2073669/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24952 (mW 12476) /
    ((1/10^5) * ((mW 12476 : ℝ)*24952*((mW 12476 : ℝ)+24952+1)))^2 +
  8*(mW 12476 : ℝ)*24952*(24952+2)*(24952+3) /
    ((1/1000)*((mW 12476 : ℝ)*24952*(24952+2)))^2 +
  covarianceVarianceBound 24952 (mW 12476) /
    ((1/1000)*covarianceMeanBound 24952 (mW 12476))^2 +
  normVarianceBound 24952 (mW 12476) / (3*inputVarianceMean 24952 (mW 12476))^2

end BstLean.Part268.WorldRow12476
namespace BstLean.Part268.WorldRow12477
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12477 = 216962967763633 := by
  have hu : mW 12477 ≤ 216962967763633 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12477 ≤ 216962967763632 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12477)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24954 ^ 2)
    ((25000000000000000000/3919765153883985023639019))
    ((25000000000000000000/3919608074251305533964619)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24954) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24954 : ℝ)^2 / (mW 12477 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2073501/1000000000000))/2) * ((1-firstRatio 24954) * √(1-firstRatio 24954) *
      sixthConstant (e1CovarianceRatio 24954 (mW 12477) (1/10^6) rowEps))) /
    (712/10000 - 24954*(1+1/10^6)*((2073501/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24954 (mW 12477) /
    ((1/10^5) * ((mW 12477 : ℝ)*24954*((mW 12477 : ℝ)+24954+1)))^2 +
  8*(mW 12477 : ℝ)*24954*(24954+2)*(24954+3) /
    ((1/1000)*((mW 12477 : ℝ)*24954*(24954+2)))^2 +
  covarianceVarianceBound 24954 (mW 12477) /
    ((1/1000)*covarianceMeanBound 24954 (mW 12477))^2 +
  normVarianceBound 24954 (mW 12477) / (3*inputVarianceMean 24954 (mW 12477))^2

end BstLean.Part268.WorldRow12477
namespace BstLean.Part268.WorldRow12478
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12478 = 217023835477606 := by
  have hu : mW 12478 ≤ 217023835477606 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12478 ≤ 217023835477605 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12478)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24956 ^ 2)
    ((12500000000000000000/1960039656574672001481433))
    ((5000000000000000000/783984446703332902657693)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24956) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24956 : ℝ)^2 / (mW 12478 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2073333/1000000000000))/2) * ((1-firstRatio 24956) * √(1-firstRatio 24956) *
      sixthConstant (e1CovarianceRatio 24956 (mW 12478) (1/10^6) rowEps))) /
    (712/10000 - 24956*(1+1/10^6)*((2073333/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24956 (mW 12478) /
    ((1/10^5) * ((mW 12478 : ℝ)*24956*((mW 12478 : ℝ)+24956+1)))^2 +
  8*(mW 12478 : ℝ)*24956*(24956+2)*(24956+3) /
    ((1/1000)*((mW 12478 : ℝ)*24956*(24956+2)))^2 +
  covarianceVarianceBound 24956 (mW 12478) /
    ((1/1000)*covarianceMeanBound 24956 (mW 12478))^2 +
  normVarianceBound 24956 (mW 12478) / (3*inputVarianceMean 24956 (mW 12478))^2

end BstLean.Part268.WorldRow12478
namespace BstLean.Part268.WorldRow12479
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12479 = 217084715387807 := by
  have hu : mW 12479 ≤ 217084715387807 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12479 ≤ 217084715387806 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12479)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24958 ^ 2)
    ((25000000000000000000/3920393472414702982286713))
    ((25000000000000000000/3920236392782023492612311)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24958) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24958 : ℝ)^2 / (mW 12479 : ℝ)) * (1 + 1/10^6)^2 *
    √(((414633/200000000000))/2) * ((1-firstRatio 24958) * √(1-firstRatio 24958) *
      sixthConstant (e1CovarianceRatio 24958 (mW 12479) (1/10^6) rowEps))) /
    (712/10000 - 24958*(1+1/10^6)*((414633/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24958 (mW 12479) /
    ((1/10^5) * ((mW 12479 : ℝ)*24958*((mW 12479 : ℝ)+24958+1)))^2 +
  8*(mW 12479 : ℝ)*24958*(24958+2)*(24958+3) /
    ((1/1000)*((mW 12479 : ℝ)*24958*(24958+2)))^2 +
  covarianceVarianceBound 24958 (mW 12479) /
    ((1/1000)*covarianceMeanBound 24958 (mW 12479))^2 +
  normVarianceBound 24958 (mW 12479) / (3*inputVarianceMean 24958 (mW 12479))^2

end BstLean.Part268.WorldRow12479
namespace BstLean.Part268.WorldRow12480
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12480 = 217145607495701 := by
  have hu : mW 12480 ≤ 217145607495701 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12480 ≤ 217145607495700 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12480)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24960 ^ 2)
    ((78125000000000000/12252211349000193630033))
    ((25000000000000000000/3920550552047382471936157)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24960) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24960 : ℝ)^2 / (mW 12480 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2072997/1000000000000))/2) * ((1-firstRatio 24960) * √(1-firstRatio 24960) *
      sixthConstant (e1CovarianceRatio 24960 (mW 12480) (1/10^6) rowEps))) /
    (712/10000 - 24960*(1+1/10^6)*((2072997/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24960 (mW 12480) /
    ((1/10^5) * ((mW 12480 : ℝ)*24960*((mW 12480 : ℝ)+24960+1)))^2 +
  8*(mW 12480 : ℝ)*24960*(24960+2)*(24960+3) /
    ((1/1000)*((mW 12480 : ℝ)*24960*(24960+2)))^2 +
  covarianceVarianceBound 24960 (mW 12480) /
    ((1/1000)*covarianceMeanBound 24960 (mW 12480))^2 +
  normVarianceBound 24960 (mW 12480) / (3*inputVarianceMean 24960 (mW 12480))^2

end BstLean.Part268.WorldRow12480
namespace BstLean.Part268.WorldRow12481
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12481 = 217206511802756 := by
  have hu : mW 12481 ≤ 217206511802756 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12481 ≤ 217206511802755 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12481)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24962 ^ 2)
    ((25000000000000000000/3921021790945420940934407))
    ((25000000000000000000/3920864711312741451260003)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24962) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24962 : ℝ)^2 / (mW 12481 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2072829/1000000000000))/2) * ((1-firstRatio 24962) * √(1-firstRatio 24962) *
      sixthConstant (e1CovarianceRatio 24962 (mW 12481) (1/10^6) rowEps))) /
    (712/10000 - 24962*(1+1/10^6)*((2072829/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24962 (mW 12481) /
    ((1/10^5) * ((mW 12481 : ℝ)*24962*((mW 12481 : ℝ)+24962+1)))^2 +
  8*(mW 12481 : ℝ)*24962*(24962+2)*(24962+3) /
    ((1/1000)*((mW 12481 : ℝ)*24962*(24962+2)))^2 +
  covarianceVarianceBound 24962 (mW 12481) /
    ((1/1000)*covarianceMeanBound 24962 (mW 12481))^2 +
  normVarianceBound 24962 (mW 12481) / (3*inputVarianceMean 24962 (mW 12481))^2

end BstLean.Part268.WorldRow12481
namespace BstLean.Part268.WorldRow12482
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12482 = 217267428310437 := by
  have hu : mW 12482 ≤ 217267428310437 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12482 ≤ 217267428310436 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12482)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24964 ^ 2)
    ((12500000000000000000/1960667975105389960129127))
    ((25000000000000000000/3921178870578100430583849)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24964) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24964 : ℝ)^2 / (mW 12482 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1036331/500000000000))/2) * ((1-firstRatio 24964) * √(1-firstRatio 24964) *
      sixthConstant (e1CovarianceRatio 24964 (mW 12482) (1/10^6) rowEps))) /
    (712/10000 - 24964*(1+1/10^6)*((1036331/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24964 (mW 12482) /
    ((1/10^5) * ((mW 12482 : ℝ)*24964*((mW 12482 : ℝ)+24964+1)))^2 +
  8*(mW 12482 : ℝ)*24964*(24964+2)*(24964+3) /
    ((1/1000)*((mW 12482 : ℝ)*24964*(24964+2)))^2 +
  covarianceVarianceBound 24964 (mW 12482) /
    ((1/1000)*covarianceMeanBound 24964 (mW 12482))^2 +
  normVarianceBound 24964 (mW 12482) / (3*inputVarianceMean 24964 (mW 12482))^2

end BstLean.Part268.WorldRow12482
namespace BstLean.Part268.WorldRow12483
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12483 = 217328357020211 := by
  have hu : mW 12483 ≤ 217328357020211 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12483 ≤ 217328357020210 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12483)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24966 ^ 2)
    ((25000000000000000000/3921650109476138899582101))
    ((5000000000000000000/784298605968691881981539)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24966) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24966 : ℝ)^2 / (mW 12483 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1036247/500000000000))/2) * ((1-firstRatio 24966) * √(1-firstRatio 24966) *
      sixthConstant (e1CovarianceRatio 24966 (mW 12483) (1/10^6) rowEps))) /
    (712/10000 - 24966*(1+1/10^6)*((1036247/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24966 (mW 12483) /
    ((1/10^5) * ((mW 12483 : ℝ)*24966*((mW 12483 : ℝ)+24966+1)))^2 +
  8*(mW 12483 : ℝ)*24966*(24966+2)*(24966+3) /
    ((1/1000)*((mW 12483 : ℝ)*24966*(24966+2)))^2 +
  covarianceVarianceBound 24966 (mW 12483) /
    ((1/1000)*covarianceMeanBound 24966 (mW 12483))^2 +
  normVarianceBound 24966 (mW 12483) / (3*inputVarianceMean 24966 (mW 12483))^2

end BstLean.Part268.WorldRow12483
namespace BstLean.Part268.WorldRow12484
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12484 = 217389297933544 := by
  have hu : mW 12484 ≤ 217389297933544 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12484 ≤ 217389297933543 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12484)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24968 ^ 2)
    ((6250000000000000000/980491067185374469726487))
    ((25000000000000000000/3921807189108818389231541)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24968) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24968 : ℝ)^2 / (mW 12484 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1036163/500000000000))/2) * ((1-firstRatio 24968) * √(1-firstRatio 24968) *
      sixthConstant (e1CovarianceRatio 24968 (mW 12484) (1/10^6) rowEps))) /
    (712/10000 - 24968*(1+1/10^6)*((1036163/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24968 (mW 12484) /
    ((1/10^5) * ((mW 12484 : ℝ)*24968*((mW 12484 : ℝ)+24968+1)))^2 +
  8*(mW 12484 : ℝ)*24968*(24968+2)*(24968+3) /
    ((1/1000)*((mW 12484 : ℝ)*24968*(24968+2)))^2 +
  covarianceVarianceBound 24968 (mW 12484) /
    ((1/1000)*covarianceMeanBound 24968 (mW 12484))^2 +
  normVarianceBound 24968 (mW 12484) / (3*inputVarianceMean 24968 (mW 12484))^2

end BstLean.Part268.WorldRow12484
namespace BstLean.Part268.WorldRow12485
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12485 = 217450251051903 := by
  have hu : mW 12485 ≤ 217450251051903 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12485 ≤ 217450251051902 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12485)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24970 ^ 2)
    ((5000000000000000000/784455685601371371645959))
    ((25000000000000000000/3922121348374177368555387)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24970) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24970 : ℝ)^2 / (mW 12485 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1036079/500000000000))/2) * ((1-firstRatio 24970) * √(1-firstRatio 24970) *
      sixthConstant (e1CovarianceRatio 24970 (mW 12485) (1/10^6) rowEps))) /
    (712/10000 - 24970*(1+1/10^6)*((1036079/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24970 (mW 12485) /
    ((1/10^5) * ((mW 12485 : ℝ)*24970*((mW 12485 : ℝ)+24970+1)))^2 +
  8*(mW 12485 : ℝ)*24970*(24970+2)*(24970+3) /
    ((1/1000)*((mW 12485 : ℝ)*24970*(24970+2)))^2 +
  covarianceVarianceBound 24970 (mW 12485) /
    ((1/1000)*covarianceMeanBound 24970 (mW 12485))^2 +
  normVarianceBound 24970 (mW 12485) / (3*inputVarianceMean 24970 (mW 12485))^2

end BstLean.Part268.WorldRow12485
namespace BstLean.Part268.WorldRow12486
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12486 = 217511216376753 := by
  have hu : mW 12486 ≤ 217511216376753 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12486 ≤ 217511216376752 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12486)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24972 ^ 2)
    ((12500000000000000000/1961296293636107918776821))
    ((25000000000000000000/3922435507639536347879233)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24972) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24972 : ℝ)^2 / (mW 12486 : ℝ)) * (1 + 1/10^6)^2 *
    √(((207199/100000000000))/2) * ((1-firstRatio 24972) * √(1-firstRatio 24972) *
      sixthConstant (e1CovarianceRatio 24972 (mW 12486) (1/10^6) rowEps))) /
    (712/10000 - 24972*(1+1/10^6)*((207199/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24972 (mW 12486) /
    ((1/10^5) * ((mW 12486 : ℝ)*24972*((mW 12486 : ℝ)+24972+1)))^2 +
  8*(mW 12486 : ℝ)*24972*(24972+2)*(24972+3) /
    ((1/1000)*((mW 12486 : ℝ)*24972*(24972+2)))^2 +
  covarianceVarianceBound 24972 (mW 12486) /
    ((1/1000)*covarianceMeanBound 24972 (mW 12486))^2 +
  normVarianceBound 24972 (mW 12486) / (3*inputVarianceMean 24972 (mW 12486))^2

end BstLean.Part268.WorldRow12486
namespace BstLean.Part268.WorldRow12487
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12487 = 217572193909563 := by
  have hu : mW 12487 ≤ 217572193909563 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12487 ≤ 217572193909562 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12487)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24974 ^ 2)
    ((25000000000000000000/3922906746537574816877489))
    ((25000000000000000000/3922749666904895327203079)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24974) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24974 : ℝ)^2 / (mW 12487 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2071823/1000000000000))/2) * ((1-firstRatio 24974) * √(1-firstRatio 24974) *
      sixthConstant (e1CovarianceRatio 24974 (mW 12487) (1/10^6) rowEps))) /
    (712/10000 - 24974*(1+1/10^6)*((2071823/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24974 (mW 12487) /
    ((1/10^5) * ((mW 12487 : ℝ)*24974*((mW 12487 : ℝ)+24974+1)))^2 +
  8*(mW 12487 : ℝ)*24974*(24974+2)*(24974+3) /
    ((1/1000)*((mW 12487 : ℝ)*24974*(24974+2)))^2 +
  covarianceVarianceBound 24974 (mW 12487) /
    ((1/1000)*covarianceMeanBound 24974 (mW 12487))^2 +
  normVarianceBound 24974 (mW 12487) / (3*inputVarianceMean 24974 (mW 12487))^2

end BstLean.Part268.WorldRow12487
namespace BstLean.Part268.WorldRow12488
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12488 = 217633183651797 := by
  have hu : mW 12488 ≤ 217633183651797 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12488 ≤ 217633183651796 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12488)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24976 ^ 2)
    ((3125000000000000000/490402613225366724525167))
    ((1000000000000000000/156922553046810172261077)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24976) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24976 : ℝ)^2 / (mW 12488 : ℝ)) * (1 + 1/10^6)^2 *
    √(((414331/200000000000))/2) * ((1-firstRatio 24976) * √(1-firstRatio 24976) *
      sixthConstant (e1CovarianceRatio 24976 (mW 12488) (1/10^6) rowEps))) /
    (712/10000 - 24976*(1+1/10^6)*((414331/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24976 (mW 12488) /
    ((1/10^5) * ((mW 12488 : ℝ)*24976*((mW 12488 : ℝ)+24976+1)))^2 +
  8*(mW 12488 : ℝ)*24976*(24976+2)*(24976+3) /
    ((1/1000)*((mW 12488 : ℝ)*24976*(24976+2)))^2 +
  covarianceVarianceBound 24976 (mW 12488) /
    ((1/1000)*covarianceMeanBound 24976 (mW 12488))^2 +
  normVarianceBound 24976 (mW 12488) / (3*inputVarianceMean 24976 (mW 12488))^2

end BstLean.Part268.WorldRow12488
namespace BstLean.Part268.WorldRow12489
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12489 = 217694185604924 := by
  have hu : mW 12489 ≤ 217694185604924 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12489 ≤ 217694185604923 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12489)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24978 ^ 2)
    ((25000000000000000000/3923535065068292775525183))
    ((25000000000000000000/3923377985435613285850771)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24978) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24978 : ℝ)^2 / (mW 12489 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2071487/1000000000000))/2) * ((1-firstRatio 24978) * √(1-firstRatio 24978) *
      sixthConstant (e1CovarianceRatio 24978 (mW 12489) (1/10^6) rowEps))) /
    (712/10000 - 24978*(1+1/10^6)*((2071487/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24978 (mW 12489) /
    ((1/10^5) * ((mW 12489 : ℝ)*24978*((mW 12489 : ℝ)+24978+1)))^2 +
  8*(mW 12489 : ℝ)*24978*(24978+2)*(24978+3) /
    ((1/1000)*((mW 12489 : ℝ)*24978*(24978+2)))^2 +
  covarianceVarianceBound 24978 (mW 12489) /
    ((1/1000)*covarianceMeanBound 24978 (mW 12489))^2 +
  normVarianceBound 24978 (mW 12489) / (3*inputVarianceMean 24978 (mW 12489))^2

end BstLean.Part268.WorldRow12489
namespace BstLean.Part268.WorldRow12490
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12490 = 217755199770409 := by
  have hu : mW 12490 ≤ 217755199770409 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12490 ≤ 217755199770408 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12490)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24980 ^ 2)
    ((2500000000000000000/392384922433365175484903))
    ((25000000000000000000/3923692144700972265174617)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24980) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24980 : ℝ)^2 / (mW 12490 : ℝ)) * (1 + 1/10^6)^2 *
    √(((51783/25000000000))/2) * ((1-firstRatio 24980) * √(1-firstRatio 24980) *
      sixthConstant (e1CovarianceRatio 24980 (mW 12490) (1/10^6) rowEps))) /
    (712/10000 - 24980*(1+1/10^6)*((51783/25000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24980 (mW 12490) /
    ((1/10^5) * ((mW 12490 : ℝ)*24980*((mW 12490 : ℝ)+24980+1)))^2 +
  8*(mW 12490 : ℝ)*24980*(24980+2)*(24980+3) /
    ((1/1000)*((mW 12490 : ℝ)*24980*(24980+2)))^2 +
  covarianceVarianceBound 24980 (mW 12490) /
    ((1/1000)*covarianceMeanBound 24980 (mW 12490))^2 +
  normVarianceBound 24980 (mW 12490) / (3*inputVarianceMean 24980 (mW 12490))^2

end BstLean.Part268.WorldRow12490
namespace BstLean.Part268.WorldRow12491
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12491 = 217816226149720 := by
  have hu : mW 12491 ≤ 217816226149720 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12491 ≤ 217816226149719 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12491)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24982 ^ 2)
    ((25000000000000000000/3924163383599010734172877))
    ((25000000000000000000/3924006303966331244498463)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24982) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24982 : ℝ)^2 / (mW 12491 : ℝ)) * (1 + 1/10^6)^2 *
    √(((129447/62500000000))/2) * ((1-firstRatio 24982) * √(1-firstRatio 24982) *
      sixthConstant (e1CovarianceRatio 24982 (mW 12491) (1/10^6) rowEps))) /
    (712/10000 - 24982*(1+1/10^6)*((129447/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24982 (mW 12491) /
    ((1/10^5) * ((mW 12491 : ℝ)*24982*((mW 12491 : ℝ)+24982+1)))^2 +
  8*(mW 12491 : ℝ)*24982*(24982+2)*(24982+3) /
    ((1/1000)*((mW 12491 : ℝ)*24982*(24982+2)))^2 +
  covarianceVarianceBound 24982 (mW 12491) /
    ((1/1000)*covarianceMeanBound 24982 (mW 12491))^2 +
  normVarianceBound 24982 (mW 12491) / (3*inputVarianceMean 24982 (mW 12491))^2

end BstLean.Part268.WorldRow12491
namespace BstLean.Part268.WorldRow12492
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12492 = 217877264744323 := by
  have hu : mW 12492 ≤ 217877264744323 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12492 ≤ 217877264744322 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12492)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24984 ^ 2)
    ((6250000000000000000/981119385716092428374181))
    ((25000000000000000000/3924320463231690223822309)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24984) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24984 : ℝ)^2 / (mW 12492 : ℝ)) * (1 + 1/10^6)^2 *
    √(((414197/200000000000))/2) * ((1-firstRatio 24984) * √(1-firstRatio 24984) *
      sixthConstant (e1CovarianceRatio 24984 (mW 12492) (1/10^6) rowEps))) /
    (712/10000 - 24984*(1+1/10^6)*((414197/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24984 (mW 12492) /
    ((1/10^5) * ((mW 12492 : ℝ)*24984*((mW 12492 : ℝ)+24984+1)))^2 +
  8*(mW 12492 : ℝ)*24984*(24984+2)*(24984+3) /
    ((1/1000)*((mW 12492 : ℝ)*24984*(24984+2)))^2 +
  covarianceVarianceBound 24984 (mW 12492) /
    ((1/1000)*covarianceMeanBound 24984 (mW 12492))^2 +
  normVarianceBound 24984 (mW 12492) / (3*inputVarianceMean 24984 (mW 12492))^2

end BstLean.Part268.WorldRow12492
namespace BstLean.Part268.WorldRow12493
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12493 = 217938315555685 := by
  have hu : mW 12493 ≤ 217938315555685 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12493 ≤ 217938315555684 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12493)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24986 ^ 2)
    ((25000000000000000000/3924791702129728692820571))
    ((5000000000000000000/784926924499409840629231)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24986) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24986 : ℝ)^2 / (mW 12493 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2070817/1000000000000))/2) * ((1-firstRatio 24986) * √(1-firstRatio 24986) *
      sixthConstant (e1CovarianceRatio 24986 (mW 12493) (1/10^6) rowEps))) /
    (712/10000 - 24986*(1+1/10^6)*((2070817/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24986 (mW 12493) /
    ((1/10^5) * ((mW 12493 : ℝ)*24986*((mW 12493 : ℝ)+24986+1)))^2 +
  8*(mW 12493 : ℝ)*24986*(24986+2)*(24986+3) /
    ((1/1000)*((mW 12493 : ℝ)*24986*(24986+2)))^2 +
  covarianceVarianceBound 24986 (mW 12493) /
    ((1/1000)*covarianceMeanBound 24986 (mW 12493))^2 +
  normVarianceBound 24986 (mW 12493) / (3*inputVarianceMean 24986 (mW 12493))^2

end BstLean.Part268.WorldRow12493
namespace BstLean.Part268.WorldRow12494
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12494 = 217999378585273 := by
  have hu : mW 12494 ≤ 217999378585273 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12494 ≤ 217999378585272 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12494)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24988 ^ 2)
    ((12500000000000000000/1962552930697543836072209))
    ((25000000000000000000/3924948781762408182470001)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24988) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24988 : ℝ)^2 / (mW 12494 : ℝ)) * (1 + 1/10^6)^2 *
    √(((41413/20000000000))/2) * ((1-firstRatio 24988) * √(1-firstRatio 24988) *
      sixthConstant (e1CovarianceRatio 24988 (mW 12494) (1/10^6) rowEps))) /
    (712/10000 - 24988*(1+1/10^6)*((41413/20000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24988 (mW 12494) /
    ((1/10^5) * ((mW 12494 : ℝ)*24988*((mW 12494 : ℝ)+24988+1)))^2 +
  8*(mW 12494 : ℝ)*24988*(24988+2)*(24988+3) /
    ((1/1000)*((mW 12494 : ℝ)*24988*(24988+2)))^2 +
  covarianceVarianceBound 24988 (mW 12494) /
    ((1/1000)*covarianceMeanBound 24988 (mW 12494))^2 +
  normVarianceBound 24988 (mW 12494) / (3*inputVarianceMean 24988 (mW 12494))^2

end BstLean.Part268.WorldRow12494
namespace BstLean.Part268.WorldRow12495
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12495 = 218060453834555 := by
  have hu : mW 12495 ≤ 218060453834555 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12495 ≤ 218060453834554 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12495)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24990 ^ 2)
    ((5000000000000000000/785084004132089330293653))
    ((25000000000000000000/3925262941027767161793847)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24990) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24990 : ℝ)^2 / (mW 12495 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1035241/500000000000))/2) * ((1-firstRatio 24990) * √(1-firstRatio 24990) *
      sixthConstant (e1CovarianceRatio 24990 (mW 12495) (1/10^6) rowEps))) /
    (712/10000 - 24990*(1+1/10^6)*((1035241/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24990 (mW 12495) /
    ((1/10^5) * ((mW 12495 : ℝ)*24990*((mW 12495 : ℝ)+24990+1)))^2 +
  8*(mW 12495 : ℝ)*24990*(24990+2)*(24990+3) /
    ((1/1000)*((mW 12495 : ℝ)*24990*(24990+2)))^2 +
  covarianceVarianceBound 24990 (mW 12495) /
    ((1/1000)*covarianceMeanBound 24990 (mW 12495))^2 +
  normVarianceBound 24990 (mW 12495) / (3*inputVarianceMean 24990 (mW 12495))^2

end BstLean.Part268.WorldRow12495
namespace BstLean.Part268.WorldRow12496
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12496 = 218121541304997 := by
  have hu : mW 12496 ≤ 218121541304997 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12496 ≤ 218121541304996 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12496)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24992 ^ 2)
    ((1562500000000000000/245358386245362851924507))
    ((25000000000000000000/3925577100293126141117693)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24992) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24992 : ℝ)^2 / (mW 12496 : ℝ)) * (1 + 1/10^6)^2 *
    √(((414063/200000000000))/2) * ((1-firstRatio 24992) * √(1-firstRatio 24992) *
      sixthConstant (e1CovarianceRatio 24992 (mW 12496) (1/10^6) rowEps))) /
    (712/10000 - 24992*(1+1/10^6)*((414063/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24992 (mW 12496) /
    ((1/10^5) * ((mW 12496 : ℝ)*24992*((mW 12496 : ℝ)+24992+1)))^2 +
  8*(mW 12496 : ℝ)*24992*(24992+2)*(24992+3) /
    ((1/1000)*((mW 12496 : ℝ)*24992*(24992+2)))^2 +
  covarianceVarianceBound 24992 (mW 12496) /
    ((1/1000)*covarianceMeanBound 24992 (mW 12496))^2 +
  normVarianceBound 24992 (mW 12496) / (3*inputVarianceMean 24992 (mW 12496))^2

end BstLean.Part268.WorldRow12496
namespace BstLean.Part268.WorldRow12497
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12497 = 218182640998067 := by
  have hu : mW 12497 ≤ 218182640998067 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12497 ≤ 218182640998066 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12497)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24994 ^ 2)
    ((25000000000000000000/3926048339191164610115959))
    ((25000000000000000000/3925891259558485120441539)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24994) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24994 : ℝ)^2 / (mW 12497 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2070147/1000000000000))/2) * ((1-firstRatio 24994) * √(1-firstRatio 24994) *
      sixthConstant (e1CovarianceRatio 24994 (mW 12497) (1/10^6) rowEps))) /
    (712/10000 - 24994*(1+1/10^6)*((2070147/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24994 (mW 12497) /
    ((1/10^5) * ((mW 12497 : ℝ)*24994*((mW 12497 : ℝ)+24994+1)))^2 +
  8*(mW 12497 : ℝ)*24994*(24994+2)*(24994+3) /
    ((1/1000)*((mW 12497 : ℝ)*24994*(24994+2)))^2 +
  covarianceVarianceBound 24994 (mW 12497) /
    ((1/1000)*covarianceMeanBound 24994 (mW 12497))^2 +
  normVarianceBound 24994 (mW 12497) / (3*inputVarianceMean 24994 (mW 12497))^2

end BstLean.Part268.WorldRow12497
namespace BstLean.Part268.WorldRow12498
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12498 = 218243752915232 := by
  have hu : mW 12498 ≤ 218243752915232 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12498 ≤ 218243752915231 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12498)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24996 ^ 2)
    ((12500000000000000000/1963181249228261794719903))
    ((5000000000000000000/785241083764768819953077)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24996) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24996 : ℝ)^2 / (mW 12498 : ℝ)) * (1 + 1/10^6)^2 *
    √(((103499/50000000000))/2) * ((1-firstRatio 24996) * √(1-firstRatio 24996) *
      sixthConstant (e1CovarianceRatio 24996 (mW 12498) (1/10^6) rowEps))) /
    (712/10000 - 24996*(1+1/10^6)*((103499/50000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24996 (mW 12498) /
    ((1/10^5) * ((mW 12498 : ℝ)*24996*((mW 12498 : ℝ)+24996+1)))^2 +
  8*(mW 12498 : ℝ)*24996*(24996+2)*(24996+3) /
    ((1/1000)*((mW 12498 : ℝ)*24996*(24996+2)))^2 +
  covarianceVarianceBound 24996 (mW 12498) /
    ((1/1000)*covarianceMeanBound 24996 (mW 12498))^2 +
  normVarianceBound 24996 (mW 12498) / (3*inputVarianceMean 24996 (mW 12498))^2

end BstLean.Part268.WorldRow12498
namespace BstLean.Part268.WorldRow12499
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12499 = 218304877057958 := by
  have hu : mW 12499 ≤ 218304877057958 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12499 ≤ 218304877057957 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12499)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24998 ^ 2)
    ((25000000000000000000/3926676657721882568763653))
    ((25000000000000000000/3926519578089203079089231)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24998) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24998 : ℝ)^2 / (mW 12499 : ℝ)) * (1 + 1/10^6)^2 *
    √(((517453/250000000000))/2) * ((1-firstRatio 24998) * √(1-firstRatio 24998) *
      sixthConstant (e1CovarianceRatio 24998 (mW 12499) (1/10^6) rowEps))) /
    (712/10000 - 24998*(1+1/10^6)*((517453/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24998 (mW 12499) /
    ((1/10^5) * ((mW 12499 : ℝ)*24998*((mW 12499 : ℝ)+24998+1)))^2 +
  8*(mW 12499 : ℝ)*24998*(24998+2)*(24998+3) /
    ((1/1000)*((mW 12499 : ℝ)*24998*(24998+2)))^2 +
  covarianceVarianceBound 24998 (mW 12499) /
    ((1/1000)*covarianceMeanBound 24998 (mW 12499))^2 +
  normVarianceBound 24998 (mW 12499) / (3*inputVarianceMean 24998 (mW 12499))^2

end BstLean.Part268.WorldRow12499
