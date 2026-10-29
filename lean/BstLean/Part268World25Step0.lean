import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar25
namespace BstLean.Part268.WorldRow12975
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12975 = 248814555555600 := by
  have hu : mW 12975 ≤ 248814555555600 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12975 ≤ 248814555555599 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12975)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25950 ^ 2)
    ((1000000000000000000/163048658721310269076593))
    ((25000000000000000000/4076059388400077237239927)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25950) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25950 : ℝ)^2 / (mW 12975 : ℝ)) * (1 + 1/10^6)^2 *
    √(((124569/62500000000))/2) * ((1-firstRatio 25950) * √(1-firstRatio 25950) *
      sixthConstant (e1CovarianceRatio 25950 (mW 12975) (1/10^6) rowEps))) /
    (712/10000 - 25950*(1+1/10^6)*((124569/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25950 (mW 12975) /
    ((1/10^5) * ((mW 12975 : ℝ)*25950*((mW 12975 : ℝ)+25950+1)))^2 +
  8*(mW 12975 : ℝ)*25950*(25950+2)*(25950+3) /
    ((1/1000)*((mW 12975 : ℝ)*25950*(25950+2)))^2 +
  covarianceVarianceBound 25950 (mW 12975) /
    ((1/1000)*covarianceMeanBound 25950 (mW 12975))^2 +
  normVarianceBound 25950 (mW 12975) / (3*inputVarianceMean 25950 (mW 12975))^2

end BstLean.Part268.WorldRow12975
namespace BstLean.Part268.WorldRow12976
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12976 = 248881679628408 := by
  have hu : mW 12976 ≤ 248881679628408 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12976 ≤ 248881679628407 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12976)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25952 ^ 2)
    ((1562500000000000000/254783164206132231639917))
    ((25000000000000000000/4076373547665436216563773)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25952) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25952 : ℝ)^2 / (mW 12976 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1992949/1000000000000))/2) * ((1-firstRatio 25952) * √(1-firstRatio 25952) *
      sixthConstant (e1CovarianceRatio 25952 (mW 12976) (1/10^6) rowEps))) /
    (712/10000 - 25952*(1+1/10^6)*((1992949/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25952 (mW 12976) /
    ((1/10^5) * ((mW 12976 : ℝ)*25952*((mW 12976 : ℝ)+25952+1)))^2 +
  8*(mW 12976 : ℝ)*25952*(25952+2)*(25952+3) /
    ((1/1000)*((mW 12976 : ℝ)*25952*(25952+2)))^2 +
  covarianceVarianceBound 25952 (mW 12976) /
    ((1/1000)*covarianceMeanBound 25952 (mW 12976))^2 +
  normVarianceBound 25952 (mW 12976) / (3*inputVarianceMean 25952 (mW 12976))^2

end BstLean.Part268.WorldRow12976
namespace BstLean.Part268.WorldRow12977
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12977 = 248948816634813 := by
  have hu : mW 12977 ≤ 248948816634813 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12977 ≤ 248948816634812 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12977)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25954 ^ 2)
    ((25000000000000000000/4076844786563474685562519))
    ((25000000000000000000/4076687706930795195887619)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25954) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25954 : ℝ)^2 / (mW 12977 : ℝ)) * (1 + 1/10^6)^2 *
    √(((996397/500000000000))/2) * ((1-firstRatio 25954) * √(1-firstRatio 25954) *
      sixthConstant (e1CovarianceRatio 25954 (mW 12977) (1/10^6) rowEps))) /
    (712/10000 - 25954*(1+1/10^6)*((996397/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25954 (mW 12977) /
    ((1/10^5) * ((mW 12977 : ℝ)*25954*((mW 12977 : ℝ)+25954+1)))^2 +
  8*(mW 12977 : ℝ)*25954*(25954+2)*(25954+3) /
    ((1/1000)*((mW 12977 : ℝ)*25954*(25954+2)))^2 +
  covarianceVarianceBound 25954 (mW 12977) /
    ((1/1000)*covarianceMeanBound 25954 (mW 12977))^2 +
  normVarianceBound 25954 (mW 12977) / (3*inputVarianceMean 25954 (mW 12977))^2

end BstLean.Part268.WorldRow12977
namespace BstLean.Part268.WorldRow12978
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12978 = 249015966576309 := by
  have hu : mW 12978 ≤ 249015966576309 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12978 ≤ 249015966576308 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12978)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25956 ^ 2)
    ((12500000000000000000/2038579472914416832443183))
    ((5000000000000000000/815400373239230835042293)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25956) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25956 : ℝ)^2 / (mW 12978 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1992639/1000000000000))/2) * ((1-firstRatio 25956) * √(1-firstRatio 25956) *
      sixthConstant (e1CovarianceRatio 25956 (mW 12978) (1/10^6) rowEps))) /
    (712/10000 - 25956*(1+1/10^6)*((1992639/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25956 (mW 12978) /
    ((1/10^5) * ((mW 12978 : ℝ)*25956*((mW 12978 : ℝ)+25956+1)))^2 +
  8*(mW 12978 : ℝ)*25956*(25956+2)*(25956+3) /
    ((1/1000)*((mW 12978 : ℝ)*25956*(25956+2)))^2 +
  covarianceVarianceBound 25956 (mW 12978) /
    ((1/1000)*covarianceMeanBound 25956 (mW 12978))^2 +
  normVarianceBound 25956 (mW 12978) / (3*inputVarianceMean 25956 (mW 12978))^2

end BstLean.Part268.WorldRow12978
namespace BstLean.Part268.WorldRow12979
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12979 = 249083129454392 := by
  have hu : mW 12979 ≤ 249083129454392 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12979 ≤ 249083129454391 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12979)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25958 ^ 2)
    ((25000000000000000000/4077473105094192644210213))
    ((25000000000000000000/4077316025461513154535311)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25958) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25958 : ℝ)^2 / (mW 12979 : ℝ)) * (1 + 1/10^6)^2 *
    √(((498121/250000000000))/2) * ((1-firstRatio 25958) * √(1-firstRatio 25958) *
      sixthConstant (e1CovarianceRatio 25958 (mW 12979) (1/10^6) rowEps))) /
    (712/10000 - 25958*(1+1/10^6)*((498121/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25958 (mW 12979) /
    ((1/10^5) * ((mW 12979 : ℝ)*25958*((mW 12979 : ℝ)+25958+1)))^2 +
  8*(mW 12979 : ℝ)*25958*(25958+2)*(25958+3) /
    ((1/1000)*((mW 12979 : ℝ)*25958*(25958+2)))^2 +
  covarianceVarianceBound 25958 (mW 12979) /
    ((1/1000)*covarianceMeanBound 25958 (mW 12979))^2 +
  normVarianceBound 25958 (mW 12979) / (3*inputVarianceMean 25958 (mW 12979))^2

end BstLean.Part268.WorldRow12979
namespace BstLean.Part268.WorldRow12980
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12980 = 249150305270558 := by
  have hu : mW 12980 ≤ 249150305270558 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12980 ≤ 249150305270557 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12980)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25960 ^ 2)
    ((1250000000000000000/203889363217977581176703))
    ((25000000000000000000/4077630184726872133859157)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25960) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25960 : ℝ)^2 / (mW 12980 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1992329/1000000000000))/2) * ((1-firstRatio 25960) * √(1-firstRatio 25960) *
      sixthConstant (e1CovarianceRatio 25960 (mW 12980) (1/10^6) rowEps))) /
    (712/10000 - 25960*(1+1/10^6)*((1992329/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25960 (mW 12980) /
    ((1/10^5) * ((mW 12980 : ℝ)*25960*((mW 12980 : ℝ)+25960+1)))^2 +
  8*(mW 12980 : ℝ)*25960*(25960+2)*(25960+3) /
    ((1/1000)*((mW 12980 : ℝ)*25960*(25960+2)))^2 +
  covarianceVarianceBound 25960 (mW 12980) /
    ((1/1000)*covarianceMeanBound 25960 (mW 12980))^2 +
  normVarianceBound 25960 (mW 12980) / (3*inputVarianceMean 25960 (mW 12980))^2

end BstLean.Part268.WorldRow12980
namespace BstLean.Part268.WorldRow12981
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12981 = 249217494026300 := by
  have hu : mW 12981 ≤ 249217494026300 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12981 ≤ 249217494026299 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12981)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25962 ^ 2)
    ((25000000000000000000/4078101423624910602857907))
    ((25000000000000000000/4077944343992231113183003)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25962) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25962 : ℝ)^2 / (mW 12981 : ℝ)) * (1 + 1/10^6)^2 *
    √(((996087/500000000000))/2) * ((1-firstRatio 25962) * √(1-firstRatio 25962) *
      sixthConstant (e1CovarianceRatio 25962 (mW 12981) (1/10^6) rowEps))) /
    (712/10000 - 25962*(1+1/10^6)*((996087/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25962 (mW 12981) /
    ((1/10^5) * ((mW 12981 : ℝ)*25962*((mW 12981 : ℝ)+25962+1)))^2 +
  8*(mW 12981 : ℝ)*25962*(25962+2)*(25962+3) /
    ((1/1000)*((mW 12981 : ℝ)*25962*(25962+2)))^2 +
  covarianceVarianceBound 25962 (mW 12981) /
    ((1/1000)*covarianceMeanBound 25962 (mW 12981))^2 +
  normVarianceBound 25962 (mW 12981) / (3*inputVarianceMean 25962 (mW 12981))^2

end BstLean.Part268.WorldRow12981
namespace BstLean.Part268.WorldRow12982
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12982 = 249284695723116 := by
  have hu : mW 12982 ≤ 249284695723116 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12982 ≤ 249284695723115 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12982)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25964 ^ 2)
    ((12500000000000000000/2039207791445134791090877))
    ((25000000000000000000/4078258503257590092506849)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25964) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25964 : ℝ)^2 / (mW 12982 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1992019/1000000000000))/2) * ((1-firstRatio 25964) * √(1-firstRatio 25964) *
      sixthConstant (e1CovarianceRatio 25964 (mW 12982) (1/10^6) rowEps))) /
    (712/10000 - 25964*(1+1/10^6)*((1992019/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25964 (mW 12982) /
    ((1/10^5) * ((mW 12982 : ℝ)*25964*((mW 12982 : ℝ)+25964+1)))^2 +
  8*(mW 12982 : ℝ)*25964*(25964+2)*(25964+3) /
    ((1/1000)*((mW 12982 : ℝ)*25964*(25964+2)))^2 +
  covarianceVarianceBound 25964 (mW 12982) /
    ((1/1000)*covarianceMeanBound 25964 (mW 12982))^2 +
  normVarianceBound 25964 (mW 12982) / (3*inputVarianceMean 25964 (mW 12982))^2

end BstLean.Part268.WorldRow12982
namespace BstLean.Part268.WorldRow12983
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12983 = 249351910362499 := by
  have hu : mW 12983 ≤ 249351910362499 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12983 ≤ 249351910362498 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12983)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25966 ^ 2)
    ((25000000000000000000/4078729742155628561505601))
    ((5000000000000000000/815714532504589814366139)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25966) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25966 : ℝ)^2 / (mW 12983 : ℝ)) * (1 + 1/10^6)^2 *
    √(((248983/125000000000))/2) * ((1-firstRatio 25966) * √(1-firstRatio 25966) *
      sixthConstant (e1CovarianceRatio 25966 (mW 12983) (1/10^6) rowEps))) /
    (712/10000 - 25966*(1+1/10^6)*((248983/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25966 (mW 12983) /
    ((1/10^5) * ((mW 12983 : ℝ)*25966*((mW 12983 : ℝ)+25966+1)))^2 +
  8*(mW 12983 : ℝ)*25966*(25966+2)*(25966+3) /
    ((1/1000)*((mW 12983 : ℝ)*25966*(25966+2)))^2 +
  covarianceVarianceBound 25966 (mW 12983) /
    ((1/1000)*covarianceMeanBound 25966 (mW 12983))^2 +
  normVarianceBound 25966 (mW 12983) / (3*inputVarianceMean 25966 (mW 12983))^2

end BstLean.Part268.WorldRow12983
namespace BstLean.Part268.WorldRow12984
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12984 = 249419137945946 := by
  have hu : mW 12984 ≤ 249419137945946 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12984 ≤ 249419137945945 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12984)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25968 ^ 2)
    ((3125000000000000000/509880487677623442603681))
    ((25000000000000000000/4078886821788308051154541)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25968) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25968 : ℝ)^2 / (mW 12984 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1991709/1000000000000))/2) * ((1-firstRatio 25968) * √(1-firstRatio 25968) *
      sixthConstant (e1CovarianceRatio 25968 (mW 12984) (1/10^6) rowEps))) /
    (712/10000 - 25968*(1+1/10^6)*((1991709/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25968 (mW 12984) /
    ((1/10^5) * ((mW 12984 : ℝ)*25968*((mW 12984 : ℝ)+25968+1)))^2 +
  8*(mW 12984 : ℝ)*25968*(25968+2)*(25968+3) /
    ((1/1000)*((mW 12984 : ℝ)*25968*(25968+2)))^2 +
  covarianceVarianceBound 25968 (mW 12984) /
    ((1/1000)*covarianceMeanBound 25968 (mW 12984))^2 +
  normVarianceBound 25968 (mW 12984) / (3*inputVarianceMean 25968 (mW 12984))^2

end BstLean.Part268.WorldRow12984
namespace BstLean.Part268.WorldRow12985
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12985 = 249486378474952 := by
  have hu : mW 12985 ≤ 249486378474952 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12985 ≤ 249486378474951 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12985)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25970 ^ 2)
    ((5000000000000000000/815871612137269304030659))
    ((25000000000000000000/4079200981053667030478387)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25970) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25970 : ℝ)^2 / (mW 12985 : ℝ)) * (1 + 1/10^6)^2 *
    √(((995777/500000000000))/2) * ((1-firstRatio 25970) * √(1-firstRatio 25970) *
      sixthConstant (e1CovarianceRatio 25970 (mW 12985) (1/10^6) rowEps))) /
    (712/10000 - 25970*(1+1/10^6)*((995777/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25970 (mW 12985) /
    ((1/10^5) * ((mW 12985 : ℝ)*25970*((mW 12985 : ℝ)+25970+1)))^2 +
  8*(mW 12985 : ℝ)*25970*(25970+2)*(25970+3) /
    ((1/1000)*((mW 12985 : ℝ)*25970*(25970+2)))^2 +
  covarianceVarianceBound 25970 (mW 12985) /
    ((1/1000)*covarianceMeanBound 25970 (mW 12985))^2 +
  normVarianceBound 25970 (mW 12985) / (3*inputVarianceMean 25970 (mW 12985))^2

end BstLean.Part268.WorldRow12985
namespace BstLean.Part268.WorldRow12986
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12986 = 249553631951013 := by
  have hu : mW 12986 ≤ 249553631951013 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12986 ≤ 249553631951012 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12986)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25972 ^ 2)
    ((12500000000000000000/2039836109975852749738571))
    ((25000000000000000000/4079515140319026009802233)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25972) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25972 : ℝ)^2 / (mW 12986 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1991399/1000000000000))/2) * ((1-firstRatio 25972) * √(1-firstRatio 25972) *
      sixthConstant (e1CovarianceRatio 25972 (mW 12986) (1/10^6) rowEps))) /
    (712/10000 - 25972*(1+1/10^6)*((1991399/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25972 (mW 12986) /
    ((1/10^5) * ((mW 12986 : ℝ)*25972*((mW 12986 : ℝ)+25972+1)))^2 +
  8*(mW 12986 : ℝ)*25972*(25972+2)*(25972+3) /
    ((1/1000)*((mW 12986 : ℝ)*25972*(25972+2)))^2 +
  covarianceVarianceBound 25972 (mW 12986) /
    ((1/1000)*covarianceMeanBound 25972 (mW 12986))^2 +
  normVarianceBound 25972 (mW 12986) / (3*inputVarianceMean 25972 (mW 12986))^2

end BstLean.Part268.WorldRow12986
namespace BstLean.Part268.WorldRow12987
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12987 = 249620898375625 := by
  have hu : mW 12987 ≤ 249620898375625 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12987 ≤ 249620898375624 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12987)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25974 ^ 2)
    ((25000000000000000000/4079986379217064478800989))
    ((25000000000000000000/4079829299584384989126079)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25974) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25974 : ℝ)^2 / (mW 12987 : ℝ)) * (1 + 1/10^6)^2 *
    √(((497811/250000000000))/2) * ((1-firstRatio 25974) * √(1-firstRatio 25974) *
      sixthConstant (e1CovarianceRatio 25974 (mW 12987) (1/10^6) rowEps))) /
    (712/10000 - 25974*(1+1/10^6)*((497811/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25974 (mW 12987) /
    ((1/10^5) * ((mW 12987 : ℝ)*25974*((mW 12987 : ℝ)+25974+1)))^2 +
  8*(mW 12987 : ℝ)*25974*(25974+2)*(25974+3) /
    ((1/1000)*((mW 12987 : ℝ)*25974*(25974+2)))^2 +
  covarianceVarianceBound 25974 (mW 12987) /
    ((1/1000)*covarianceMeanBound 25974 (mW 12987))^2 +
  normVarianceBound 25974 (mW 12987) / (3*inputVarianceMean 25974 (mW 12987))^2

end BstLean.Part268.WorldRow12987
namespace BstLean.Part268.WorldRow12988
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12988 = 249688177750282 := by
  have hu : mW 12988 ≤ 249688177750282 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12988 ≤ 249688177750281 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12988)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25976 ^ 2)
    ((6250000000000000000/1020075134620605864531209))
    ((1000000000000000000/163205738353989758737997)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25976) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25976 : ℝ)^2 / (mW 12988 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1991089/1000000000000))/2) * ((1-firstRatio 25976) * √(1-firstRatio 25976) *
      sixthConstant (e1CovarianceRatio 25976 (mW 12988) (1/10^6) rowEps))) /
    (712/10000 - 25976*(1+1/10^6)*((1991089/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25976 (mW 12988) /
    ((1/10^5) * ((mW 12988 : ℝ)*25976*((mW 12988 : ℝ)+25976+1)))^2 +
  8*(mW 12988 : ℝ)*25976*(25976+2)*(25976+3) /
    ((1/1000)*((mW 12988 : ℝ)*25976*(25976+2)))^2 +
  covarianceVarianceBound 25976 (mW 12988) /
    ((1/1000)*covarianceMeanBound 25976 (mW 12988))^2 +
  normVarianceBound 25976 (mW 12988) / (3*inputVarianceMean 25976 (mW 12988))^2

end BstLean.Part268.WorldRow12988
namespace BstLean.Part268.WorldRow12989
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12989 = 249755470076482 := by
  have hu : mW 12989 ≤ 249755470076482 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12989 ≤ 249755470076481 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12989)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25978 ^ 2)
    ((25000000000000000000/4080614697747782437448683))
    ((25000000000000000000/4080457618115102947773771)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25978) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25978 : ℝ)^2 / (mW 12989 : ℝ)) * (1 + 1/10^6)^2 *
    √(((995467/500000000000))/2) * ((1-firstRatio 25978) * √(1-firstRatio 25978) *
      sixthConstant (e1CovarianceRatio 25978 (mW 12989) (1/10^6) rowEps))) /
    (712/10000 - 25978*(1+1/10^6)*((995467/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25978 (mW 12989) /
    ((1/10^5) * ((mW 12989 : ℝ)*25978*((mW 12989 : ℝ)+25978+1)))^2 +
  8*(mW 12989 : ℝ)*25978*(25978+2)*(25978+3) /
    ((1/1000)*((mW 12989 : ℝ)*25978*(25978+2)))^2 +
  covarianceVarianceBound 25978 (mW 12989) /
    ((1/1000)*covarianceMeanBound 25978 (mW 12989))^2 +
  normVarianceBound 25978 (mW 12989) / (3*inputVarianceMean 25978 (mW 12989))^2

end BstLean.Part268.WorldRow12989
namespace BstLean.Part268.WorldRow12990
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12990 = 249822775355719 := by
  have hu : mW 12990 ≤ 249822775355719 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12990 ≤ 249822775355718 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12990)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25980 ^ 2)
    ((2500000000000000000/408092885701314141677253))
    ((25000000000000000000/4080771777380461927097617)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25980) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25980 : ℝ)^2 / (mW 12990 : ℝ)) * (1 + 1/10^6)^2 *
    √(((99539/50000000000))/2) * ((1-firstRatio 25980) * √(1-firstRatio 25980) *
      sixthConstant (e1CovarianceRatio 25980 (mW 12990) (1/10^6) rowEps))) /
    (712/10000 - 25980*(1+1/10^6)*((99539/50000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25980 (mW 12990) /
    ((1/10^5) * ((mW 12990 : ℝ)*25980*((mW 12990 : ℝ)+25980+1)))^2 +
  8*(mW 12990 : ℝ)*25980*(25980+2)*(25980+3) /
    ((1/1000)*((mW 12990 : ℝ)*25980*(25980+2)))^2 +
  covarianceVarianceBound 25980 (mW 12990) /
    ((1/1000)*covarianceMeanBound 25980 (mW 12990))^2 +
  normVarianceBound 25980 (mW 12990) / (3*inputVarianceMean 25980 (mW 12990))^2

end BstLean.Part268.WorldRow12990
namespace BstLean.Part268.WorldRow12991
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12991 = 249890093589489 := by
  have hu : mW 12991 ≤ 249890093589489 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12991 ≤ 249890093589488 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12991)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25982 ^ 2)
    ((25000000000000000000/4081243016278500396096377))
    ((25000000000000000000/4081085936645820906421463)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25982) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25982 : ℝ)^2 / (mW 12991 : ℝ)) * (1 + 1/10^6)^2 *
    √(((637/320000000))/2) * ((1-firstRatio 25982) * √(1-firstRatio 25982) *
      sixthConstant (e1CovarianceRatio 25982 (mW 12991) (1/10^6) rowEps))) /
    (712/10000 - 25982*(1+1/10^6)*((637/320000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25982 (mW 12991) /
    ((1/10^5) * ((mW 12991 : ℝ)*25982*((mW 12991 : ℝ)+25982+1)))^2 +
  8*(mW 12991 : ℝ)*25982*(25982+2)*(25982+3) /
    ((1/1000)*((mW 12991 : ℝ)*25982*(25982+2)))^2 +
  covarianceVarianceBound 25982 (mW 12991) /
    ((1/1000)*covarianceMeanBound 25982 (mW 12991))^2 +
  normVarianceBound 25982 (mW 12991) / (3*inputVarianceMean 25982 (mW 12991))^2

end BstLean.Part268.WorldRow12991
namespace BstLean.Part268.WorldRow12992
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12992 = 249957424779289 := by
  have hu : mW 12992 ≤ 249957424779289 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12992 ≤ 249957424779288 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12992)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25984 ^ 2)
    ((390625000000000000/63774330867872802740941))
    ((25000000000000000000/4081400095911179885745309)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25984) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25984 : ℝ)^2 / (mW 12992 : ℝ)) * (1 + 1/10^6)^2 *
    √(((199047/100000000000))/2) * ((1-firstRatio 25984) * √(1-firstRatio 25984) *
      sixthConstant (e1CovarianceRatio 25984 (mW 12992) (1/10^6) rowEps))) /
    (712/10000 - 25984*(1+1/10^6)*((199047/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25984 (mW 12992) /
    ((1/10^5) * ((mW 12992 : ℝ)*25984*((mW 12992 : ℝ)+25984+1)))^2 +
  8*(mW 12992 : ℝ)*25984*(25984+2)*(25984+3) /
    ((1/1000)*((mW 12992 : ℝ)*25984*(25984+2)))^2 +
  covarianceVarianceBound 25984 (mW 12992) /
    ((1/1000)*covarianceMeanBound 25984 (mW 12992))^2 +
  normVarianceBound 25984 (mW 12992) / (3*inputVarianceMean 25984 (mW 12992))^2

end BstLean.Part268.WorldRow12992
namespace BstLean.Part268.WorldRow12993
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12993 = 250024768926615 := by
  have hu : mW 12993 ≤ 250024768926615 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12993 ≤ 250024768926614 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12993)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25986 ^ 2)
    ((25000000000000000000/4081871334809218354744071))
    ((5000000000000000000/816342851035307773013831)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25986) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25986 : ℝ)^2 / (mW 12993 : ℝ)) * (1 + 1/10^6)^2 *
    √(((398063/200000000000))/2) * ((1-firstRatio 25986) * √(1-firstRatio 25986) *
      sixthConstant (e1CovarianceRatio 25986 (mW 12993) (1/10^6) rowEps))) /
    (712/10000 - 25986*(1+1/10^6)*((398063/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25986 (mW 12993) /
    ((1/10^5) * ((mW 12993 : ℝ)*25986*((mW 12993 : ℝ)+25986+1)))^2 +
  8*(mW 12993 : ℝ)*25986*(25986+2)*(25986+3) /
    ((1/1000)*((mW 12993 : ℝ)*25986*(25986+2)))^2 +
  covarianceVarianceBound 25986 (mW 12993) /
    ((1/1000)*covarianceMeanBound 25986 (mW 12993))^2 +
  normVarianceBound 25986 (mW 12993) / (3*inputVarianceMean 25986 (mW 12993))^2

end BstLean.Part268.WorldRow12993
namespace BstLean.Part268.WorldRow12994
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12994 = 250092126032962 := by
  have hu : mW 12994 ≤ 250092126032962 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12994 ≤ 250092126032961 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12994)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25988 ^ 2)
    ((12500000000000000000/2041092747037288667033959))
    ((25000000000000000000/4082028414441897844393001)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25988) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25988 : ℝ)^2 / (mW 12994 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1990161/1000000000000))/2) * ((1-firstRatio 25988) * √(1-firstRatio 25988) *
      sixthConstant (e1CovarianceRatio 25988 (mW 12994) (1/10^6) rowEps))) /
    (712/10000 - 25988*(1+1/10^6)*((1990161/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25988 (mW 12994) /
    ((1/10^5) * ((mW 12994 : ℝ)*25988*((mW 12994 : ℝ)+25988+1)))^2 +
  8*(mW 12994 : ℝ)*25988*(25988+2)*(25988+3) /
    ((1/1000)*((mW 12994 : ℝ)*25988*(25988+2)))^2 +
  covarianceVarianceBound 25988 (mW 12994) /
    ((1/1000)*covarianceMeanBound 25988 (mW 12994))^2 +
  normVarianceBound 25988 (mW 12994) / (3*inputVarianceMean 25988 (mW 12994))^2

end BstLean.Part268.WorldRow12994
namespace BstLean.Part268.WorldRow12995
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12995 = 250159496099826 := by
  have hu : mW 12995 ≤ 250159496099826 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12995 ≤ 250159496099825 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12995)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25990 ^ 2)
    ((5000000000000000000/816499930667987262678353))
    ((25000000000000000000/4082342573707256823716847)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25990) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25990 : ℝ)^2 / (mW 12995 : ℝ)) * (1 + 1/10^6)^2 *
    √(((995003/500000000000))/2) * ((1-firstRatio 25990) * √(1-firstRatio 25990) *
      sixthConstant (e1CovarianceRatio 25990 (mW 12995) (1/10^6) rowEps))) /
    (712/10000 - 25990*(1+1/10^6)*((995003/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25990 (mW 12995) /
    ((1/10^5) * ((mW 12995 : ℝ)*25990*((mW 12995 : ℝ)+25990+1)))^2 +
  8*(mW 12995 : ℝ)*25990*(25990+2)*(25990+3) /
    ((1/1000)*((mW 12995 : ℝ)*25990*(25990+2)))^2 +
  covarianceVarianceBound 25990 (mW 12995) /
    ((1/1000)*covarianceMeanBound 25990 (mW 12995))^2 +
  normVarianceBound 25990 (mW 12995) / (3*inputVarianceMean 25990 (mW 12995))^2

end BstLean.Part268.WorldRow12995
namespace BstLean.Part268.WorldRow12996
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12996 = 250226879128704 := by
  have hu : mW 12996 ≤ 250226879128704 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12996 ≤ 250226879128703 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12996)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25992 ^ 2)
    ((6250000000000000000/1020703453151323823178903))
    ((25000000000000000000/4082656732972615803040693)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25992) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25992 : ℝ)^2 / (mW 12996 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1989851/1000000000000))/2) * ((1-firstRatio 25992) * √(1-firstRatio 25992) *
      sixthConstant (e1CovarianceRatio 25992 (mW 12996) (1/10^6) rowEps))) /
    (712/10000 - 25992*(1+1/10^6)*((1989851/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25992 (mW 12996) /
    ((1/10^5) * ((mW 12996 : ℝ)*25992*((mW 12996 : ℝ)+25992+1)))^2 +
  8*(mW 12996 : ℝ)*25992*(25992+2)*(25992+3) /
    ((1/1000)*((mW 12996 : ℝ)*25992*(25992+2)))^2 +
  covarianceVarianceBound 25992 (mW 12996) /
    ((1/1000)*covarianceMeanBound 25992 (mW 12996))^2 +
  normVarianceBound 25992 (mW 12996) / (3*inputVarianceMean 25992 (mW 12996))^2

end BstLean.Part268.WorldRow12996
namespace BstLean.Part268.WorldRow12997
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12997 = 250294275121093 := by
  have hu : mW 12997 ≤ 250294275121093 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12997 ≤ 250294275121092 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12997)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25994 ^ 2)
    ((25000000000000000000/4083127971870654272039459))
    ((25000000000000000000/4082970892237974782364539)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25994) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25994 : ℝ)^2 / (mW 12997 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1989697/1000000000000))/2) * ((1-firstRatio 25994) * √(1-firstRatio 25994) *
      sixthConstant (e1CovarianceRatio 25994 (mW 12997) (1/10^6) rowEps))) /
    (712/10000 - 25994*(1+1/10^6)*((1989697/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25994 (mW 12997) /
    ((1/10^5) * ((mW 12997 : ℝ)*25994*((mW 12997 : ℝ)+25994+1)))^2 +
  8*(mW 12997 : ℝ)*25994*(25994+2)*(25994+3) /
    ((1/1000)*((mW 12997 : ℝ)*25994*(25994+2)))^2 +
  covarianceVarianceBound 25994 (mW 12997) /
    ((1/1000)*covarianceMeanBound 25994 (mW 12997))^2 +
  normVarianceBound 25994 (mW 12997) / (3*inputVarianceMean 25994 (mW 12997))^2

end BstLean.Part268.WorldRow12997
namespace BstLean.Part268.WorldRow12998
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12998 = 250361684078488 := by
  have hu : mW 12998 ≤ 250361684078488 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12998 ≤ 250361684078487 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12998)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25996 ^ 2)
    ((12500000000000000000/2041721065568006625681653))
    ((5000000000000000000/816657010300666752337677)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25996) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25996 : ℝ)^2 / (mW 12998 : ℝ)) * (1 + 1/10^6)^2 *
    √(((994771/500000000000))/2) * ((1-firstRatio 25996) * √(1-firstRatio 25996) *
      sixthConstant (e1CovarianceRatio 25996 (mW 12998) (1/10^6) rowEps))) /
    (712/10000 - 25996*(1+1/10^6)*((994771/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25996 (mW 12998) /
    ((1/10^5) * ((mW 12998 : ℝ)*25996*((mW 12998 : ℝ)+25996+1)))^2 +
  8*(mW 12998 : ℝ)*25996*(25996+2)*(25996+3) /
    ((1/1000)*((mW 12998 : ℝ)*25996*(25996+2)))^2 +
  covarianceVarianceBound 25996 (mW 12998) /
    ((1/1000)*covarianceMeanBound 25996 (mW 12998))^2 +
  normVarianceBound 25996 (mW 12998) / (3*inputVarianceMean 25996 (mW 12998))^2

end BstLean.Part268.WorldRow12998
namespace BstLean.Part268.WorldRow12999
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12999 = 250429106002385 := by
  have hu : mW 12999 ≤ 250429106002385 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12999 ≤ 250429106002384 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12999)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25998 ^ 2)
    ((25000000000000000000/4083756290401372230687153))
    ((25000000000000000000/4083599210768692741012231)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25998) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25998 : ℝ)^2 / (mW 12999 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1989387/1000000000000))/2) * ((1-firstRatio 25998) * √(1-firstRatio 25998) *
      sixthConstant (e1CovarianceRatio 25998 (mW 12999) (1/10^6) rowEps))) /
    (712/10000 - 25998*(1+1/10^6)*((1989387/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25998 (mW 12999) /
    ((1/10^5) * ((mW 12999 : ℝ)*25998*((mW 12999 : ℝ)+25998+1)))^2 +
  8*(mW 12999 : ℝ)*25998*(25998+2)*(25998+3) /
    ((1/1000)*((mW 12999 : ℝ)*25998*(25998+2)))^2 +
  covarianceVarianceBound 25998 (mW 12999) /
    ((1/1000)*covarianceMeanBound 25998 (mW 12999))^2 +
  normVarianceBound 25998 (mW 12999) / (3*inputVarianceMean 25998 (mW 12999))^2

end BstLean.Part268.WorldRow12999
