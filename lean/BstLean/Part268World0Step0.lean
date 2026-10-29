import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar0
namespace BstLean.Part268.WorldRow12350
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12350 = 209331387268305 := by
  have hu : mW 12350 ≤ 209331387268305 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12350 ≤ 209331387268304 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12350)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24700 ^ 2)
    ((500000000000000000/77597338543667892990209))
    ((25000000000000000000/3879709847550715159836177)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24700) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24700 : ℝ)^2 / (mW 12350 : ℝ)) * (1 + 1/10^6)^2 *
    √(((130941/62500000000))/2) * ((1-firstRatio 24700) * √(1-firstRatio 24700) *
      sixthConstant (e1CovarianceRatio 24700 (mW 12350) (1/10^6) rowEps))) /
    (712/10000 - 24700*(1+1/10^6)*((130941/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24700 (mW 12350) /
    ((1/10^5) * ((mW 12350 : ℝ)*24700*((mW 12350 : ℝ)+24700+1)))^2 +
  8*(mW 12350 : ℝ)*24700*(24700+2)*(24700+3) /
    ((1/1000)*((mW 12350 : ℝ)*24700*(24700+2)))^2 +
  covarianceVarianceBound 24700 (mW 12350) /
    ((1/1000)*covarianceMeanBound 24700 (mW 12350))^2 +
  normVarianceBound 24700 (mW 12350) / (3*inputVarianceMean 24700 (mW 12350))^2

end BstLean.Part268.WorldRow12350
namespace BstLean.Part268.WorldRow12351
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12351 = 209390717957721 := by
  have hu : mW 12351 ≤ 209390717957721 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12351 ≤ 209390717957720 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12351)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24702 ^ 2)
    ((25000000000000000000/3880181086448753628834297))
    ((25000000000000000000/3880024006816074139160023)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24702) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24702 : ℝ)^2 / (mW 12351 : ℝ)) * (1 + 1/10^6)^2 *
    √(((523721/250000000000))/2) * ((1-firstRatio 24702) * √(1-firstRatio 24702) *
      sixthConstant (e1CovarianceRatio 24702 (mW 12351) (1/10^6) rowEps))) /
    (712/10000 - 24702*(1+1/10^6)*((523721/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24702 (mW 12351) /
    ((1/10^5) * ((mW 12351 : ℝ)*24702*((mW 12351 : ℝ)+24702+1)))^2 +
  8*(mW 12351 : ℝ)*24702*(24702+2)*(24702+3) /
    ((1/1000)*((mW 12351 : ℝ)*24702*(24702+2)))^2 +
  covarianceVarianceBound 24702 (mW 12351) /
    ((1/1000)*covarianceMeanBound 24702 (mW 12351))^2 +
  normVarianceBound 24702 (mW 12351) / (3*inputVarianceMean 24702 (mW 12351))^2

end BstLean.Part268.WorldRow12351
namespace BstLean.Part268.WorldRow12352
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12352 = 209450060657642 := by
  have hu : mW 12352 ≤ 209450060657642 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12352 ≤ 209450060657641 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12352)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24704 ^ 2)
    ((390625000000000000/60632738214283009502471))
    ((25000000000000000000/3880338166081433118483869)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24704) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24704 : ℝ)^2 / (mW 12352 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2094713/1000000000000))/2) * ((1-firstRatio 24704) * √(1-firstRatio 24704) *
      sixthConstant (e1CovarianceRatio 24704 (mW 12352) (1/10^6) rowEps))) /
    (712/10000 - 24704*(1+1/10^6)*((2094713/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24704 (mW 12352) /
    ((1/10^5) * ((mW 12352 : ℝ)*24704*((mW 12352 : ℝ)+24704+1)))^2 +
  8*(mW 12352 : ℝ)*24704*(24704+2)*(24704+3) /
    ((1/1000)*((mW 12352 : ℝ)*24704*(24704+2)))^2 +
  covarianceVarianceBound 24704 (mW 12352) /
    ((1/1000)*covarianceMeanBound 24704 (mW 12352))^2 +
  normVarianceBound 24704 (mW 12352) / (3*inputVarianceMean 24704 (mW 12352))^2

end BstLean.Part268.WorldRow12352
namespace BstLean.Part268.WorldRow12353
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12353 = 209509415369526 := by
  have hu : mW 12353 ≤ 209509415369526 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12353 ≤ 209509415369525 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12353)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24706 ^ 2)
    ((25000000000000000000/3880809404979471587481991))
    ((5000000000000000000/776130465069358419561543)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24706) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24706 : ℝ)^2 / (mW 12353 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2094541/1000000000000))/2) * ((1-firstRatio 24706) * √(1-firstRatio 24706) *
      sixthConstant (e1CovarianceRatio 24706 (mW 12353) (1/10^6) rowEps))) /
    (712/10000 - 24706*(1+1/10^6)*((2094541/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24706 (mW 12353) /
    ((1/10^5) * ((mW 12353 : ℝ)*24706*((mW 12353 : ℝ)+24706+1)))^2 +
  8*(mW 12353 : ℝ)*24706*(24706+2)*(24706+3) /
    ((1/1000)*((mW 12353 : ℝ)*24706*(24706+2)))^2 +
  covarianceVarianceBound 24706 (mW 12353) /
    ((1/1000)*covarianceMeanBound 24706 (mW 12353))^2 +
  normVarianceBound 24706 (mW 12353) / (3*inputVarianceMean 24706 (mW 12353))^2

end BstLean.Part268.WorldRow12353
namespace BstLean.Part268.WorldRow12354
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12354 = 209568782094831 := by
  have hu : mW 12354 ≤ 209568782094831 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12354 ≤ 209568782094830 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12354)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24708 ^ 2)
    ((12500000000000000000/1940561782122415283402919))
    ((25000000000000000000/3880966484612151077131561)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24708) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24708 : ℝ)^2 / (mW 12354 : ℝ)) * (1 + 1/10^6)^2 *
    √(((209437/100000000000))/2) * ((1-firstRatio 24708) * √(1-firstRatio 24708) *
      sixthConstant (e1CovarianceRatio 24708 (mW 12354) (1/10^6) rowEps))) /
    (712/10000 - 24708*(1+1/10^6)*((209437/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24708 (mW 12354) /
    ((1/10^5) * ((mW 12354 : ℝ)*24708*((mW 12354 : ℝ)+24708+1)))^2 +
  8*(mW 12354 : ℝ)*24708*(24708+2)*(24708+3) /
    ((1/1000)*((mW 12354 : ℝ)*24708*(24708+2)))^2 +
  covarianceVarianceBound 24708 (mW 12354) /
    ((1/1000)*covarianceMeanBound 24708 (mW 12354))^2 +
  normVarianceBound 24708 (mW 12354) / (3*inputVarianceMean 24708 (mW 12354))^2

end BstLean.Part268.WorldRow12354
namespace BstLean.Part268.WorldRow12355
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12355 = 209628160835017 := by
  have hu : mW 12355 ≤ 209628160835017 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12355 ≤ 209628160835016 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12355)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24710 ^ 2)
    ((5000000000000000000/776287544702037909225937))
    ((25000000000000000000/3881280643877510056455407)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24710) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24710 : ℝ)^2 / (mW 12355 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2094199/1000000000000))/2) * ((1-firstRatio 24710) * √(1-firstRatio 24710) *
      sixthConstant (e1CovarianceRatio 24710 (mW 12355) (1/10^6) rowEps))) /
    (712/10000 - 24710*(1+1/10^6)*((2094199/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24710 (mW 12355) /
    ((1/10^5) * ((mW 12355 : ℝ)*24710*((mW 12355 : ℝ)+24710+1)))^2 +
  8*(mW 12355 : ℝ)*24710*(24710+2)*(24710+3) /
    ((1/1000)*((mW 12355 : ℝ)*24710*(24710+2)))^2 +
  covarianceVarianceBound 24710 (mW 12355) /
    ((1/1000)*covarianceMeanBound 24710 (mW 12355))^2 +
  normVarianceBound 24710 (mW 12355) / (3*inputVarianceMean 24710 (mW 12355))^2

end BstLean.Part268.WorldRow12355
namespace BstLean.Part268.WorldRow12356
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12356 = 209687551591541 := by
  have hu : mW 12356 ≤ 209687551591541 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12356 ≤ 209687551591540 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12356)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24712 ^ 2)
    ((6250000000000000000/970437970693887131363383))
    ((25000000000000000000/3881594803142869035779253)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24712) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24712 : ℝ)^2 / (mW 12356 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2094027/1000000000000))/2) * ((1-firstRatio 24712) * √(1-firstRatio 24712) *
      sixthConstant (e1CovarianceRatio 24712 (mW 12356) (1/10^6) rowEps))) /
    (712/10000 - 24712*(1+1/10^6)*((2094027/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24712 (mW 12356) /
    ((1/10^5) * ((mW 12356 : ℝ)*24712*((mW 12356 : ℝ)+24712+1)))^2 +
  8*(mW 12356 : ℝ)*24712*(24712+2)*(24712+3) /
    ((1/1000)*((mW 12356 : ℝ)*24712*(24712+2)))^2 +
  covarianceVarianceBound 24712 (mW 12356) /
    ((1/1000)*covarianceMeanBound 24712 (mW 12356))^2 +
  normVarianceBound 24712 (mW 12356) / (3*inputVarianceMean 24712 (mW 12356))^2

end BstLean.Part268.WorldRow12356
namespace BstLean.Part268.WorldRow12357
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12357 = 209746954365864 := by
  have hu : mW 12357 ≤ 209746954365864 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12357 ≤ 209746954365863 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12357)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24714 ^ 2)
    ((25000000000000000000/3882066042040907504777379))
    ((25000000000000000000/3881908962408228015103099)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24714) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24714 : ℝ)^2 / (mW 12357 : ℝ)) * (1 + 1/10^6)^2 *
    √(((65433/31250000000))/2) * ((1-firstRatio 24714) * √(1-firstRatio 24714) *
      sixthConstant (e1CovarianceRatio 24714 (mW 12357) (1/10^6) rowEps))) /
    (712/10000 - 24714*(1+1/10^6)*((65433/31250000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24714 (mW 12357) /
    ((1/10^5) * ((mW 12357 : ℝ)*24714*((mW 12357 : ℝ)+24714+1)))^2 +
  8*(mW 12357 : ℝ)*24714*(24714+2)*(24714+3) /
    ((1/1000)*((mW 12357 : ℝ)*24714*(24714+2)))^2 +
  covarianceVarianceBound 24714 (mW 12357) /
    ((1/1000)*covarianceMeanBound 24714 (mW 12357))^2 +
  normVarianceBound 24714 (mW 12357) / (3*inputVarianceMean 24714 (mW 12357))^2

end BstLean.Part268.WorldRow12357
namespace BstLean.Part268.WorldRow12358
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12358 = 209806369159444 := by
  have hu : mW 12358 ≤ 209806369159444 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12358 ≤ 209806369159443 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12358)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24716 ^ 2)
    ((12500000000000000000/1941190100653133242050613))
    ((5000000000000000000/776444624334717398885389)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24716) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24716 : ℝ)^2 / (mW 12358 : ℝ)) * (1 + 1/10^6)^2 *
    √(((418737/200000000000))/2) * ((1-firstRatio 24716) * √(1-firstRatio 24716) *
      sixthConstant (e1CovarianceRatio 24716 (mW 12358) (1/10^6) rowEps))) /
    (712/10000 - 24716*(1+1/10^6)*((418737/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24716 (mW 12358) /
    ((1/10^5) * ((mW 12358 : ℝ)*24716*((mW 12358 : ℝ)+24716+1)))^2 +
  8*(mW 12358 : ℝ)*24716*(24716+2)*(24716+3) /
    ((1/1000)*((mW 12358 : ℝ)*24716*(24716+2)))^2 +
  covarianceVarianceBound 24716 (mW 12358) /
    ((1/1000)*covarianceMeanBound 24716 (mW 12358))^2 +
  normVarianceBound 24716 (mW 12358) / (3*inputVarianceMean 24716 (mW 12358))^2

end BstLean.Part268.WorldRow12358
namespace BstLean.Part268.WorldRow12359
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12359 = 209865795973739 := by
  have hu : mW 12359 ≤ 209865795973739 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12359 ≤ 209865795973738 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12359)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24718 ^ 2)
    ((25000000000000000000/3882694360571625463425073))
    ((25000000000000000000/3882537280938945973750791)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24718) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24718 : ℝ)^2 / (mW 12359 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2093513/1000000000000))/2) * ((1-firstRatio 24718) * √(1-firstRatio 24718) *
      sixthConstant (e1CovarianceRatio 24718 (mW 12359) (1/10^6) rowEps))) /
    (712/10000 - 24718*(1+1/10^6)*((2093513/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24718 (mW 12359) /
    ((1/10^5) * ((mW 12359 : ℝ)*24718*((mW 12359 : ℝ)+24718+1)))^2 +
  8*(mW 12359 : ℝ)*24718*(24718+2)*(24718+3) /
    ((1/1000)*((mW 12359 : ℝ)*24718*(24718+2)))^2 +
  covarianceVarianceBound 24718 (mW 12359) /
    ((1/1000)*covarianceMeanBound 24718 (mW 12359))^2 +
  normVarianceBound 24718 (mW 12359) / (3*inputVarianceMean 24718 (mW 12359))^2

end BstLean.Part268.WorldRow12359
namespace BstLean.Part268.WorldRow12360
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12360 = 209925234810210 := by
  have hu : mW 12360 ≤ 209925234810210 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12360 ≤ 209925234810209 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12360)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24720 ^ 2)
    ((625000000000000000/97075212995924611068723))
    ((25000000000000000000/3882851440204304953074637)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24720) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24720 : ℝ)^2 / (mW 12360 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1046671/500000000000))/2) * ((1-firstRatio 24720) * √(1-firstRatio 24720) *
      sixthConstant (e1CovarianceRatio 24720 (mW 12360) (1/10^6) rowEps))) /
    (712/10000 - 24720*(1+1/10^6)*((1046671/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24720 (mW 12360) /
    ((1/10^5) * ((mW 12360 : ℝ)*24720*((mW 12360 : ℝ)+24720+1)))^2 +
  8*(mW 12360 : ℝ)*24720*(24720+2)*(24720+3) /
    ((1/1000)*((mW 12360 : ℝ)*24720*(24720+2)))^2 +
  covarianceVarianceBound 24720 (mW 12360) /
    ((1/1000)*covarianceMeanBound 24720 (mW 12360))^2 +
  normVarianceBound 24720 (mW 12360) / (3*inputVarianceMean 24720 (mW 12360))^2

end BstLean.Part268.WorldRow12360
namespace BstLean.Part268.WorldRow12361
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12361 = 209984685670316 := by
  have hu : mW 12361 ≤ 209984685670316 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12361 ≤ 209984685670315 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12361)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24722 ^ 2)
    ((25000000000000000000/3883322679102343422072767))
    ((25000000000000000000/3883165599469663932398483)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24722) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24722 : ℝ)^2 / (mW 12361 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2093171/1000000000000))/2) * ((1-firstRatio 24722) * √(1-firstRatio 24722) *
      sixthConstant (e1CovarianceRatio 24722 (mW 12361) (1/10^6) rowEps))) /
    (712/10000 - 24722*(1+1/10^6)*((2093171/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24722 (mW 12361) /
    ((1/10^5) * ((mW 12361 : ℝ)*24722*((mW 12361 : ℝ)+24722+1)))^2 +
  8*(mW 12361 : ℝ)*24722*(24722+2)*(24722+3) /
    ((1/1000)*((mW 12361 : ℝ)*24722*(24722+2)))^2 +
  covarianceVarianceBound 24722 (mW 12361) /
    ((1/1000)*covarianceMeanBound 24722 (mW 12361))^2 +
  normVarianceBound 24722 (mW 12361) / (3*inputVarianceMean 24722 (mW 12361))^2

end BstLean.Part268.WorldRow12361
namespace BstLean.Part268.WorldRow12362
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12362 = 210044148555515 := by
  have hu : mW 12362 ≤ 210044148555515 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12362 ≤ 210044148555514 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12362)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24724 ^ 2)
    ((12500000000000000000/1941818419183851200698307))
    ((25000000000000000000/3883479758735022911722329)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24724) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24724 : ℝ)^2 / (mW 12362 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2093/1000000000))/2) * ((1-firstRatio 24724) * √(1-firstRatio 24724) *
      sixthConstant (e1CovarianceRatio 24724 (mW 12362) (1/10^6) rowEps))) /
    (712/10000 - 24724*(1+1/10^6)*((2093/1000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24724 (mW 12362) /
    ((1/10^5) * ((mW 12362 : ℝ)*24724*((mW 12362 : ℝ)+24724+1)))^2 +
  8*(mW 12362 : ℝ)*24724*(24724+2)*(24724+3) /
    ((1/1000)*((mW 12362 : ℝ)*24724*(24724+2)))^2 +
  covarianceVarianceBound 24724 (mW 12362) /
    ((1/1000)*covarianceMeanBound 24724 (mW 12362))^2 +
  normVarianceBound 24724 (mW 12362) / (3*inputVarianceMean 24724 (mW 12362))^2

end BstLean.Part268.WorldRow12362
namespace BstLean.Part268.WorldRow12363
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12363 = 210103623467266 := by
  have hu : mW 12363 ≤ 210103623467266 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12363 ≤ 210103623467265 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12363)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24726 ^ 2)
    ((25000000000000000000/3883950997633061380720461))
    ((1000000000000000000/155351756720015275641847)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24726) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24726 : ℝ)^2 / (mW 12363 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2092829/1000000000000))/2) * ((1-firstRatio 24726) * √(1-firstRatio 24726) *
      sixthConstant (e1CovarianceRatio 24726 (mW 12363) (1/10^6) rowEps))) /
    (712/10000 - 24726*(1+1/10^6)*((2092829/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24726 (mW 12363) /
    ((1/10^5) * ((mW 12363 : ℝ)*24726*((mW 12363 : ℝ)+24726+1)))^2 +
  8*(mW 12363 : ℝ)*24726*(24726+2)*(24726+3) /
    ((1/1000)*((mW 12363 : ℝ)*24726*(24726+2)))^2 +
  covarianceVarianceBound 24726 (mW 12363) /
    ((1/1000)*covarianceMeanBound 24726 (mW 12363))^2 +
  normVarianceBound 24726 (mW 12363) / (3*inputVarianceMean 24726 (mW 12363))^2

end BstLean.Part268.WorldRow12363
namespace BstLean.Part268.WorldRow12364
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12364 = 210163110407030 := by
  have hu : mW 12364 ≤ 210163110407030 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12364 ≤ 210163110407029 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12364)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24728 ^ 2)
    ((6250000000000000000/971066289224605090011077))
    ((25000000000000000000/3884108077265740870370021)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24728) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24728 : ℝ)^2 / (mW 12364 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1046329/500000000000))/2) * ((1-firstRatio 24728) * √(1-firstRatio 24728) *
      sixthConstant (e1CovarianceRatio 24728 (mW 12364) (1/10^6) rowEps))) /
    (712/10000 - 24728*(1+1/10^6)*((1046329/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24728 (mW 12364) /
    ((1/10^5) * ((mW 12364 : ℝ)*24728*((mW 12364 : ℝ)+24728+1)))^2 +
  8*(mW 12364 : ℝ)*24728*(24728+2)*(24728+3) /
    ((1/1000)*((mW 12364 : ℝ)*24728*(24728+2)))^2 +
  covarianceVarianceBound 24728 (mW 12364) /
    ((1/1000)*covarianceMeanBound 24728 (mW 12364))^2 +
  normVarianceBound 24728 (mW 12364) / (3*inputVarianceMean 24728 (mW 12364))^2

end BstLean.Part268.WorldRow12364
namespace BstLean.Part268.WorldRow12365
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12365 = 210222609376265 := by
  have hu : mW 12365 ≤ 210222609376265 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12365 ≤ 210222609376264 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12365)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24730 ^ 2)
    ((5000000000000000000/776915863232755867873631))
    ((25000000000000000000/3884422236531099849693867)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24730) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24730 : ℝ)^2 / (mW 12365 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2092487/1000000000000))/2) * ((1-firstRatio 24730) * √(1-firstRatio 24730) *
      sixthConstant (e1CovarianceRatio 24730 (mW 12365) (1/10^6) rowEps))) /
    (712/10000 - 24730*(1+1/10^6)*((2092487/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24730 (mW 12365) /
    ((1/10^5) * ((mW 12365 : ℝ)*24730*((mW 12365 : ℝ)+24730+1)))^2 +
  8*(mW 12365 : ℝ)*24730*(24730+2)*(24730+3) /
    ((1/1000)*((mW 12365 : ℝ)*24730*(24730+2)))^2 +
  covarianceVarianceBound 24730 (mW 12365) /
    ((1/1000)*covarianceMeanBound 24730 (mW 12365))^2 +
  normVarianceBound 24730 (mW 12365) / (3*inputVarianceMean 24730 (mW 12365))^2

end BstLean.Part268.WorldRow12365
namespace BstLean.Part268.WorldRow12366
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12366 = 210282120376431 := by
  have hu : mW 12366 ≤ 210282120376431 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12366 ≤ 210282120376430 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12366)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24732 ^ 2)
    ((12500000000000000000/1942446737714569159346001))
    ((25000000000000000000/3884736395796458829017713)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24732) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24732 : ℝ)^2 / (mW 12366 : ℝ)) * (1 + 1/10^6)^2 *
    √(((418463/200000000000))/2) * ((1-firstRatio 24732) * √(1-firstRatio 24732) *
      sixthConstant (e1CovarianceRatio 24732 (mW 12366) (1/10^6) rowEps))) /
    (712/10000 - 24732*(1+1/10^6)*((418463/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24732 (mW 12366) /
    ((1/10^5) * ((mW 12366 : ℝ)*24732*((mW 12366 : ℝ)+24732+1)))^2 +
  8*(mW 12366 : ℝ)*24732*(24732+2)*(24732+3) /
    ((1/1000)*((mW 12366 : ℝ)*24732*(24732+2)))^2 +
  covarianceVarianceBound 24732 (mW 12366) /
    ((1/1000)*covarianceMeanBound 24732 (mW 12366))^2 +
  normVarianceBound 24732 (mW 12366) / (3*inputVarianceMean 24732 (mW 12366))^2

end BstLean.Part268.WorldRow12366
namespace BstLean.Part268.WorldRow12367
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12367 = 210341643408988 := by
  have hu : mW 12367 ≤ 210341643408988 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12367 ≤ 210341643408987 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12367)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24734 ^ 2)
    ((25000000000000000000/3885207634694497298015849))
    ((25000000000000000000/3885050555061817808341559)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24734) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24734 : ℝ)^2 / (mW 12367 : ℝ)) * (1 + 1/10^6)^2 *
    √(((130759/62500000000))/2) * ((1-firstRatio 24734) * √(1-firstRatio 24734) *
      sixthConstant (e1CovarianceRatio 24734 (mW 12367) (1/10^6) rowEps))) /
    (712/10000 - 24734*(1+1/10^6)*((130759/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24734 (mW 12367) /
    ((1/10^5) * ((mW 12367 : ℝ)*24734*((mW 12367 : ℝ)+24734+1)))^2 +
  8*(mW 12367 : ℝ)*24734*(24734+2)*(24734+3) /
    ((1/1000)*((mW 12367 : ℝ)*24734*(24734+2)))^2 +
  covarianceVarianceBound 24734 (mW 12367) /
    ((1/1000)*covarianceMeanBound 24734 (mW 12367))^2 +
  normVarianceBound 24734 (mW 12367) / (3*inputVarianceMean 24734 (mW 12367))^2

end BstLean.Part268.WorldRow12367
namespace BstLean.Part268.WorldRow12368
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12368 = 210401178475395 := by
  have hu : mW 12368 ≤ 210401178475395 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12368 ≤ 210401178475394 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12368)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24736 ^ 2)
    ((1562500000000000000/242845112122491017333731))
    ((5000000000000000000/777072942865435357533081)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24736) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24736 : ℝ)^2 / (mW 12368 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2091973/1000000000000))/2) * ((1-firstRatio 24736) * √(1-firstRatio 24736) *
      sixthConstant (e1CovarianceRatio 24736 (mW 12368) (1/10^6) rowEps))) /
    (712/10000 - 24736*(1+1/10^6)*((2091973/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24736 (mW 12368) /
    ((1/10^5) * ((mW 12368 : ℝ)*24736*((mW 12368 : ℝ)+24736+1)))^2 +
  8*(mW 12368 : ℝ)*24736*(24736+2)*(24736+3) /
    ((1/1000)*((mW 12368 : ℝ)*24736*(24736+2)))^2 +
  covarianceVarianceBound 24736 (mW 12368) /
    ((1/1000)*covarianceMeanBound 24736 (mW 12368))^2 +
  normVarianceBound 24736 (mW 12368) / (3*inputVarianceMean 24736 (mW 12368))^2

end BstLean.Part268.WorldRow12368
namespace BstLean.Part268.WorldRow12369
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12369 = 210460725577111 := by
  have hu : mW 12369 ≤ 210460725577111 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12369 ≤ 210460725577110 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12369)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24738 ^ 2)
    ((25000000000000000000/3885835953225215256663543))
    ((25000000000000000000/3885678873592535766989251)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24738) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24738 : ℝ)^2 / (mW 12369 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1045901/500000000000))/2) * ((1-firstRatio 24738) * √(1-firstRatio 24738) *
      sixthConstant (e1CovarianceRatio 24738 (mW 12369) (1/10^6) rowEps))) /
    (712/10000 - 24738*(1+1/10^6)*((1045901/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24738 (mW 12369) /
    ((1/10^5) * ((mW 12369 : ℝ)*24738*((mW 12369 : ℝ)+24738+1)))^2 +
  8*(mW 12369 : ℝ)*24738*(24738+2)*(24738+3) /
    ((1/1000)*((mW 12369 : ℝ)*24738*(24738+2)))^2 +
  covarianceVarianceBound 24738 (mW 12369) /
    ((1/1000)*covarianceMeanBound 24738 (mW 12369))^2 +
  normVarianceBound 24738 (mW 12369) / (3*inputVarianceMean 24738 (mW 12369))^2

end BstLean.Part268.WorldRow12369
namespace BstLean.Part268.WorldRow12370
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12370 = 210520284715597 := by
  have hu : mW 12370 ≤ 210520284715597 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12370 ≤ 210520284715596 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12370)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24740 ^ 2)
    ((2500000000000000000/388615011249057423598739))
    ((25000000000000000000/3885993032857894746313097)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24740) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24740 : ℝ)^2 / (mW 12370 : ℝ)) * (1 + 1/10^6)^2 *
    √(((130727/62500000000))/2) * ((1-firstRatio 24740) * √(1-firstRatio 24740) *
      sixthConstant (e1CovarianceRatio 24740 (mW 12370) (1/10^6) rowEps))) /
    (712/10000 - 24740*(1+1/10^6)*((130727/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24740 (mW 12370) /
    ((1/10^5) * ((mW 12370 : ℝ)*24740*((mW 12370 : ℝ)+24740+1)))^2 +
  8*(mW 12370 : ℝ)*24740*(24740+2)*(24740+3) /
    ((1/1000)*((mW 12370 : ℝ)*24740*(24740+2)))^2 +
  covarianceVarianceBound 24740 (mW 12370) /
    ((1/1000)*covarianceMeanBound 24740 (mW 12370))^2 +
  normVarianceBound 24740 (mW 12370) / (3*inputVarianceMean 24740 (mW 12370))^2

end BstLean.Part268.WorldRow12370
namespace BstLean.Part268.WorldRow12371
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12371 = 210579855892312 := by
  have hu : mW 12371 ≤ 210579855892312 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12371 ≤ 210579855892311 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12371)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24742 ^ 2)
    ((25000000000000000000/3886464271755933215311237))
    ((25000000000000000000/3886307192123253725636943)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24742) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24742 : ℝ)^2 / (mW 12371 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2091461/1000000000000))/2) * ((1-firstRatio 24742) * √(1-firstRatio 24742) *
      sixthConstant (e1CovarianceRatio 24742 (mW 12371) (1/10^6) rowEps))) /
    (712/10000 - 24742*(1+1/10^6)*((2091461/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24742 (mW 12371) /
    ((1/10^5) * ((mW 12371 : ℝ)*24742*((mW 12371 : ℝ)+24742+1)))^2 +
  8*(mW 12371 : ℝ)*24742*(24742+2)*(24742+3) /
    ((1/1000)*((mW 12371 : ℝ)*24742*(24742+2)))^2 +
  covarianceVarianceBound 24742 (mW 12371) /
    ((1/1000)*covarianceMeanBound 24742 (mW 12371))^2 +
  normVarianceBound 24742 (mW 12371) / (3*inputVarianceMean 24742 (mW 12371))^2

end BstLean.Part268.WorldRow12371
namespace BstLean.Part268.WorldRow12372
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12372 = 210639439108715 := by
  have hu : mW 12372 ≤ 210639439108715 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12372 ≤ 210639439108714 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12372)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24744 ^ 2)
    ((6250000000000000000/971694607755323048658771))
    ((25000000000000000000/3886621351388612704960789)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24744) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24744 : ℝ)^2 / (mW 12372 : ℝ)) * (1 + 1/10^6)^2 *
    √(((209129/100000000000))/2) * ((1-firstRatio 24744) * √(1-firstRatio 24744) *
      sixthConstant (e1CovarianceRatio 24744 (mW 12372) (1/10^6) rowEps))) /
    (712/10000 - 24744*(1+1/10^6)*((209129/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24744 (mW 12372) /
    ((1/10^5) * ((mW 12372 : ℝ)*24744*((mW 12372 : ℝ)+24744+1)))^2 +
  8*(mW 12372 : ℝ)*24744*(24744+2)*(24744+3) /
    ((1/1000)*((mW 12372 : ℝ)*24744*(24744+2)))^2 +
  covarianceVarianceBound 24744 (mW 12372) /
    ((1/1000)*covarianceMeanBound 24744 (mW 12372))^2 +
  normVarianceBound 24744 (mW 12372) / (3*inputVarianceMean 24744 (mW 12372))^2

end BstLean.Part268.WorldRow12372
namespace BstLean.Part268.WorldRow12373
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12373 = 210699034366267 := by
  have hu : mW 12373 ≤ 210699034366267 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12373 ≤ 210699034366266 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12373)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24746 ^ 2)
    ((25000000000000000000/3887092590286651173958931))
    ((5000000000000000000/777387102130794336856927)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24746) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24746 : ℝ)^2 / (mW 12373 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2091119/1000000000000))/2) * ((1-firstRatio 24746) * √(1-firstRatio 24746) *
      sixthConstant (e1CovarianceRatio 24746 (mW 12373) (1/10^6) rowEps))) /
    (712/10000 - 24746*(1+1/10^6)*((2091119/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24746 (mW 12373) /
    ((1/10^5) * ((mW 12373 : ℝ)*24746*((mW 12373 : ℝ)+24746+1)))^2 +
  8*(mW 12373 : ℝ)*24746*(24746+2)*(24746+3) /
    ((1/1000)*((mW 12373 : ℝ)*24746*(24746+2)))^2 +
  covarianceVarianceBound 24746 (mW 12373) /
    ((1/1000)*covarianceMeanBound 24746 (mW 12373))^2 +
  normVarianceBound 24746 (mW 12373) / (3*inputVarianceMean 24746 (mW 12373))^2

end BstLean.Part268.WorldRow12373
namespace BstLean.Part268.WorldRow12374
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12374 = 210758641666428 := by
  have hu : mW 12374 ≤ 210758641666428 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12374 ≤ 210758641666427 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12374)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24748 ^ 2)
    ((12500000000000000000/1943703374776005076641389))
    ((25000000000000000000/3887249669919330663608481)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24748) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24748 : ℝ)^2 / (mW 12374 : ℝ)) * (1 + 1/10^6)^2 *
    √(((522737/250000000000))/2) * ((1-firstRatio 24748) * √(1-firstRatio 24748) *
      sixthConstant (e1CovarianceRatio 24748 (mW 12374) (1/10^6) rowEps))) /
    (712/10000 - 24748*(1+1/10^6)*((522737/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24748 (mW 12374) /
    ((1/10^5) * ((mW 12374 : ℝ)*24748*((mW 12374 : ℝ)+24748+1)))^2 +
  8*(mW 12374 : ℝ)*24748*(24748+2)*(24748+3) /
    ((1/1000)*((mW 12374 : ℝ)*24748*(24748+2)))^2 +
  covarianceVarianceBound 24748 (mW 12374) /
    ((1/1000)*covarianceMeanBound 24748 (mW 12374))^2 +
  normVarianceBound 24748 (mW 12374) / (3*inputVarianceMean 24748 (mW 12374))^2

end BstLean.Part268.WorldRow12374
