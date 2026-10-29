import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part281Scalar7
namespace BstLean.Part281.WorldRow12034
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12034 = 191176728300969 := by
  have hu : mW 12034 ≤ 191176728300969 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12034 ≤ 191176728300968 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12034)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24068 ^ 2)
    ((12500000000000000000/1890296299664978591587399))
    ((25000000000000000000/3780435519697277693500841)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24068) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24068 : ℝ)^2 / (mW 12034 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2150691/1000000000000))/2) * ((1-firstRatio 24068) * √(1-firstRatio 24068) *
      sixthConstant (e1CovarianceRatio 24068 (mW 12034) (1/10^6) rowEps))) /
    (712/10000 - 24068*(1+1/10^6)*((2150691/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24068 (mW 12034) /
    ((1/10^5) * ((mW 12034 : ℝ)*24068*((mW 12034 : ℝ)+24068+1)))^2 +
  8*(mW 12034 : ℝ)*24068*(24068+2)*(24068+3) /
    ((1/1000)*((mW 12034 : ℝ)*24068*(24068+2)))^2 +
  covarianceVarianceBound 24068 (mW 12034) /
    ((1/1000)*covarianceMeanBound 24068 (mW 12034))^2 +
  normVarianceBound 24068 (mW 12034) / (3*inputVarianceMean 24068 (mW 12034))^2

end BstLean.Part281.WorldRow12034
namespace BstLean.Part281.WorldRow12035
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12035 = 191232336415882 := by
  have hu : mW 12035 ≤ 191232336415882 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12035 ≤ 191232336415881 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12035)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24070 ^ 2)
    ((5000000000000000000/756181351719063232499729))
    ((25000000000000000000/3780749678962636672824687)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24070) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24070 : ℝ)^2 / (mW 12035 : ℝ)) * (1 + 1/10^6)^2 *
    √(((215051/100000000000))/2) * ((1-firstRatio 24070) * √(1-firstRatio 24070) *
      sixthConstant (e1CovarianceRatio 24070 (mW 12035) (1/10^6) rowEps))) /
    (712/10000 - 24070*(1+1/10^6)*((215051/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24070 (mW 12035) /
    ((1/10^5) * ((mW 12035 : ℝ)*24070*((mW 12035 : ℝ)+24070+1)))^2 +
  8*(mW 12035 : ℝ)*24070*(24070+2)*(24070+3) /
    ((1/1000)*((mW 12035 : ℝ)*24070*(24070+2)))^2 +
  covarianceVarianceBound 24070 (mW 12035) /
    ((1/1000)*covarianceMeanBound 24070 (mW 12035))^2 +
  normVarianceBound 24070 (mW 12035) / (3*inputVarianceMean 24070 (mW 12035))^2

end BstLean.Part281.WorldRow12035
namespace BstLean.Part281.WorldRow12036
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12036 = 191287956083327 := by
  have hu : mW 12036 ≤ 191287956083327 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12036 ≤ 191287956083326 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12036)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24072 ^ 2)
    ((6250000000000000000/945305229465168785455623))
    ((25000000000000000000/3781063838227995652148533)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24072) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24072 : ℝ)^2 / (mW 12036 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2150329/1000000000000))/2) * ((1-firstRatio 24072) * √(1-firstRatio 24072) *
      sixthConstant (e1CovarianceRatio 24072 (mW 12036) (1/10^6) rowEps))) /
    (712/10000 - 24072*(1+1/10^6)*((2150329/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24072 (mW 12036) /
    ((1/10^5) * ((mW 12036 : ℝ)*24072*((mW 12036 : ℝ)+24072+1)))^2 +
  8*(mW 12036 : ℝ)*24072*(24072+2)*(24072+3) /
    ((1/1000)*((mW 12036 : ℝ)*24072*(24072+2)))^2 +
  covarianceVarianceBound 24072 (mW 12036) /
    ((1/1000)*covarianceMeanBound 24072 (mW 12036))^2 +
  normVarianceBound 24072 (mW 12036) / (3*inputVarianceMean 24072 (mW 12036))^2

end BstLean.Part281.WorldRow12036
namespace BstLean.Part281.WorldRow12037
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12037 = 191343587304745 := by
  have hu : mW 12037 ≤ 191343587304745 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12037 ≤ 191343587304744 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12037)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24074 ^ 2)
    ((25000000000000000000/3781535077126034121146339))
    ((25000000000000000000/3781377997493354631472379)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24074) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24074 : ℝ)^2 / (mW 12037 : ℝ)) * (1 + 1/10^6)^2 *
    √(((537537/250000000000))/2) * ((1-firstRatio 24074) * √(1-firstRatio 24074) *
      sixthConstant (e1CovarianceRatio 24074 (mW 12037) (1/10^6) rowEps))) /
    (712/10000 - 24074*(1+1/10^6)*((537537/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24074 (mW 12037) /
    ((1/10^5) * ((mW 12037 : ℝ)*24074*((mW 12037 : ℝ)+24074+1)))^2 +
  8*(mW 12037 : ℝ)*24074*(24074+2)*(24074+3) /
    ((1/1000)*((mW 12037 : ℝ)*24074*(24074+2)))^2 +
  covarianceVarianceBound 24074 (mW 12037) /
    ((1/1000)*covarianceMeanBound 24074 (mW 12037))^2 +
  normVarianceBound 24074 (mW 12037) / (3*inputVarianceMean 24074 (mW 12037))^2

end BstLean.Part281.WorldRow12037
namespace BstLean.Part281.WorldRow12038
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12038 = 191399230081575 := by
  have hu : mW 12038 ≤ 191399230081575 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12038 ≤ 191399230081574 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12038)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24076 ^ 2)
    ((12500000000000000000/1890924618195696550235093))
    ((1000000000000000000/151267686270348544431849)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24076) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24076 : ℝ)^2 / (mW 12038 : ℝ)) * (1 + 1/10^6)^2 *
    √(((134373/62500000000))/2) * ((1-firstRatio 24076) * √(1-firstRatio 24076) *
      sixthConstant (e1CovarianceRatio 24076 (mW 12038) (1/10^6) rowEps))) /
    (712/10000 - 24076*(1+1/10^6)*((134373/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24076 (mW 12038) /
    ((1/10^5) * ((mW 12038 : ℝ)*24076*((mW 12038 : ℝ)+24076+1)))^2 +
  8*(mW 12038 : ℝ)*24076*(24076+2)*(24076+3) /
    ((1/1000)*((mW 12038 : ℝ)*24076*(24076+2)))^2 +
  covarianceVarianceBound 24076 (mW 12038) /
    ((1/1000)*covarianceMeanBound 24076 (mW 12038))^2 +
  normVarianceBound 24076 (mW 12038) / (3*inputVarianceMean 24076 (mW 12038))^2

end BstLean.Part281.WorldRow12038
namespace BstLean.Part281.WorldRow12039
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12039 = 191454884415258 := by
  have hu : mW 12039 ≤ 191454884415258 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12039 ≤ 191454884415257 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12039)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24078 ^ 2)
    ((25000000000000000000/3782163395656752079794033))
    ((25000000000000000000/3782006316024072590120071)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24078) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24078 : ℝ)^2 / (mW 12039 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2149787/1000000000000))/2) * ((1-firstRatio 24078) * √(1-firstRatio 24078) *
      sixthConstant (e1CovarianceRatio 24078 (mW 12039) (1/10^6) rowEps))) /
    (712/10000 - 24078*(1+1/10^6)*((2149787/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24078 (mW 12039) /
    ((1/10^5) * ((mW 12039 : ℝ)*24078*((mW 12039 : ℝ)+24078+1)))^2 +
  8*(mW 12039 : ℝ)*24078*(24078+2)*(24078+3) /
    ((1/1000)*((mW 12039 : ℝ)*24078*(24078+2)))^2 +
  covarianceVarianceBound 24078 (mW 12039) /
    ((1/1000)*covarianceMeanBound 24078 (mW 12039))^2 +
  normVarianceBound 24078 (mW 12039) / (3*inputVarianceMean 24078 (mW 12039))^2

end BstLean.Part281.WorldRow12039
namespace BstLean.Part281.WorldRow12040
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12040 = 191510550307232 := by
  have hu : mW 12040 ≤ 191510550307232 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12040 ≤ 191510550307231 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12040)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24080 ^ 2)
    ((625000000000000000/94561938873052776477947))
    ((25000000000000000000/3782320475289431569443917)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24080) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24080 : ℝ)^2 / (mW 12040 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2149607/1000000000000))/2) * ((1-firstRatio 24080) * √(1-firstRatio 24080) *
      sixthConstant (e1CovarianceRatio 24080 (mW 12040) (1/10^6) rowEps))) /
    (712/10000 - 24080*(1+1/10^6)*((2149607/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24080 (mW 12040) /
    ((1/10^5) * ((mW 12040 : ℝ)*24080*((mW 12040 : ℝ)+24080+1)))^2 +
  8*(mW 12040 : ℝ)*24080*(24080+2)*(24080+3) /
    ((1/1000)*((mW 12040 : ℝ)*24080*(24080+2)))^2 +
  covarianceVarianceBound 24080 (mW 12040) /
    ((1/1000)*covarianceMeanBound 24080 (mW 12040))^2 +
  normVarianceBound 24080 (mW 12040) / (3*inputVarianceMean 24080 (mW 12040))^2

end BstLean.Part281.WorldRow12040
namespace BstLean.Part281.WorldRow12041
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12041 = 191566227758940 := by
  have hu : mW 12041 ≤ 191566227758940 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12041 ≤ 191566227758939 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12041)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24082 ^ 2)
    ((25000000000000000000/3782791714187470038441727))
    ((25000000000000000000/3782634634554790548767763)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24082) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24082 : ℝ)^2 / (mW 12041 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1074713/500000000000))/2) * ((1-firstRatio 24082) * √(1-firstRatio 24082) *
      sixthConstant (e1CovarianceRatio 24082 (mW 12041) (1/10^6) rowEps))) /
    (712/10000 - 24082*(1+1/10^6)*((1074713/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24082 (mW 12041) /
    ((1/10^5) * ((mW 12041 : ℝ)*24082*((mW 12041 : ℝ)+24082+1)))^2 +
  8*(mW 12041 : ℝ)*24082*(24082+2)*(24082+3) /
    ((1/1000)*((mW 12041 : ℝ)*24082*(24082+2)))^2 +
  covarianceVarianceBound 24082 (mW 12041) /
    ((1/1000)*covarianceMeanBound 24082 (mW 12041))^2 +
  normVarianceBound 24082 (mW 12041) / (3*inputVarianceMean 24082 (mW 12041))^2

end BstLean.Part281.WorldRow12041
namespace BstLean.Part281.WorldRow12042
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12042 = 191621916771819 := by
  have hu : mW 12042 ≤ 191621916771819 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12042 ≤ 191621916771818 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12042)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24084 ^ 2)
    ((12500000000000000000/1891552936726414508882787))
    ((25000000000000000000/3782948793820149528091609)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24084) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24084 : ℝ)^2 / (mW 12042 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1074623/500000000000))/2) * ((1-firstRatio 24084) * √(1-firstRatio 24084) *
      sixthConstant (e1CovarianceRatio 24084 (mW 12042) (1/10^6) rowEps))) /
    (712/10000 - 24084*(1+1/10^6)*((1074623/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24084 (mW 12042) /
    ((1/10^5) * ((mW 12042 : ℝ)*24084*((mW 12042 : ℝ)+24084+1)))^2 +
  8*(mW 12042 : ℝ)*24084*(24084+2)*(24084+3) /
    ((1/1000)*((mW 12042 : ℝ)*24084*(24084+2)))^2 +
  covarianceVarianceBound 24084 (mW 12042) /
    ((1/1000)*covarianceMeanBound 24084 (mW 12042))^2 +
  normVarianceBound 24084 (mW 12042) / (3*inputVarianceMean 24084 (mW 12042))^2

end BstLean.Part281.WorldRow12042
namespace BstLean.Part281.WorldRow12043
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12043 = 191677617347312 := by
  have hu : mW 12043 ≤ 191677617347312 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12043 ≤ 191677617347311 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12043)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24086 ^ 2)
    ((25000000000000000000/3783420032718187997089421))
    ((5000000000000000000/756652590617101701483091)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24086) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24086 : ℝ)^2 / (mW 12043 : ℝ)) * (1 + 1/10^6)^2 *
    √(((429813/200000000000))/2) * ((1-firstRatio 24086) * √(1-firstRatio 24086) *
      sixthConstant (e1CovarianceRatio 24086 (mW 12043) (1/10^6) rowEps))) /
    (712/10000 - 24086*(1+1/10^6)*((429813/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24086 (mW 12043) /
    ((1/10^5) * ((mW 12043 : ℝ)*24086*((mW 12043 : ℝ)+24086+1)))^2 +
  8*(mW 12043 : ℝ)*24086*(24086+2)*(24086+3) /
    ((1/1000)*((mW 12043 : ℝ)*24086*(24086+2)))^2 +
  covarianceVarianceBound 24086 (mW 12043) /
    ((1/1000)*covarianceMeanBound 24086 (mW 12043))^2 +
  normVarianceBound 24086 (mW 12043) / (3*inputVarianceMean 24086 (mW 12043))^2

end BstLean.Part281.WorldRow12043
namespace BstLean.Part281.WorldRow12044
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12044 = 191733329486858 := by
  have hu : mW 12044 ≤ 191733329486858 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12044 ≤ 191733329486857 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12044)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24088 ^ 2)
    ((6250000000000000000/945933547995886744103317))
    ((25000000000000000000/3783577112350867486739301)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24088) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24088 : ℝ)^2 / (mW 12044 : ℝ)) * (1 + 1/10^6)^2 *
    √(((429777/200000000000))/2) * ((1-firstRatio 24088) * √(1-firstRatio 24088) *
      sixthConstant (e1CovarianceRatio 24088 (mW 12044) (1/10^6) rowEps))) /
    (712/10000 - 24088*(1+1/10^6)*((429777/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24088 (mW 12044) /
    ((1/10^5) * ((mW 12044 : ℝ)*24088*((mW 12044 : ℝ)+24088+1)))^2 +
  8*(mW 12044 : ℝ)*24088*(24088+2)*(24088+3) /
    ((1/1000)*((mW 12044 : ℝ)*24088*(24088+2)))^2 +
  covarianceVarianceBound 24088 (mW 12044) /
    ((1/1000)*covarianceMeanBound 24088 (mW 12044))^2 +
  normVarianceBound 24088 (mW 12044) / (3*inputVarianceMean 24088 (mW 12044))^2

end BstLean.Part281.WorldRow12044
namespace BstLean.Part281.WorldRow12045
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12045 = 191789053191898 := by
  have hu : mW 12045 ≤ 191789053191898 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12045 ≤ 191789053191897 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12045)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24090 ^ 2)
    ((5000000000000000000/756809670249781191147423))
    ((25000000000000000000/3783891271616226466063147)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24090) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24090 : ℝ)^2 / (mW 12045 : ℝ)) * (1 + 1/10^6)^2 *
    √(((67147/31250000000))/2) * ((1-firstRatio 24090) * √(1-firstRatio 24090) *
      sixthConstant (e1CovarianceRatio 24090 (mW 12045) (1/10^6) rowEps))) /
    (712/10000 - 24090*(1+1/10^6)*((67147/31250000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24090 (mW 12045) /
    ((1/10^5) * ((mW 12045 : ℝ)*24090*((mW 12045 : ℝ)+24090+1)))^2 +
  8*(mW 12045 : ℝ)*24090*(24090+2)*(24090+3) /
    ((1/1000)*((mW 12045 : ℝ)*24090*(24090+2)))^2 +
  covarianceVarianceBound 24090 (mW 12045) /
    ((1/1000)*covarianceMeanBound 24090 (mW 12045))^2 +
  normVarianceBound 24090 (mW 12045) / (3*inputVarianceMean 24090 (mW 12045))^2

end BstLean.Part281.WorldRow12045
namespace BstLean.Part281.WorldRow12046
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12046 = 191844788463872 := by
  have hu : mW 12046 ≤ 191844788463872 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12046 ≤ 191844788463871 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12046)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24092 ^ 2)
    ((12500000000000000000/1892181255257132467530481))
    ((25000000000000000000/3784205430881585445386993)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24092) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24092 : ℝ)^2 / (mW 12046 : ℝ)) * (1 + 1/10^6)^2 *
    √(((537131/250000000000))/2) * ((1-firstRatio 24092) * √(1-firstRatio 24092) *
      sixthConstant (e1CovarianceRatio 24092 (mW 12046) (1/10^6) rowEps))) /
    (712/10000 - 24092*(1+1/10^6)*((537131/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24092 (mW 12046) /
    ((1/10^5) * ((mW 12046 : ℝ)*24092*((mW 12046 : ℝ)+24092+1)))^2 +
  8*(mW 12046 : ℝ)*24092*(24092+2)*(24092+3) /
    ((1/1000)*((mW 12046 : ℝ)*24092*(24092+2)))^2 +
  covarianceVarianceBound 24092 (mW 12046) /
    ((1/1000)*covarianceMeanBound 24092 (mW 12046))^2 +
  normVarianceBound 24092 (mW 12046) / (3*inputVarianceMean 24092 (mW 12046))^2

end BstLean.Part281.WorldRow12046
namespace BstLean.Part281.WorldRow12047
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12047 = 191900535304220 := by
  have hu : mW 12047 ≤ 191900535304220 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12047 ≤ 191900535304219 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12047)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24094 ^ 2)
    ((25000000000000000000/3784676669779623914384809))
    ((25000000000000000000/3784519590146944424710839)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24094) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24094 : ℝ)^2 / (mW 12047 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2148343/1000000000000))/2) * ((1-firstRatio 24094) * √(1-firstRatio 24094) *
      sixthConstant (e1CovarianceRatio 24094 (mW 12047) (1/10^6) rowEps))) /
    (712/10000 - 24094*(1+1/10^6)*((2148343/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24094 (mW 12047) /
    ((1/10^5) * ((mW 12047 : ℝ)*24094*((mW 12047 : ℝ)+24094+1)))^2 +
  8*(mW 12047 : ℝ)*24094*(24094+2)*(24094+3) /
    ((1/1000)*((mW 12047 : ℝ)*24094*(24094+2)))^2 +
  covarianceVarianceBound 24094 (mW 12047) /
    ((1/1000)*covarianceMeanBound 24094 (mW 12047))^2 +
  normVarianceBound 24094 (mW 12047) / (3*inputVarianceMean 24094 (mW 12047))^2

end BstLean.Part281.WorldRow12047
namespace BstLean.Part281.WorldRow12048
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12048 = 191956293714384 := by
  have hu : mW 12048 ≤ 191956293714384 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12048 ≤ 191956293714383 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12048)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24096 ^ 2)
    ((1562500000000000000/236561926815311430856791))
    ((5000000000000000000/756966749882460680806937)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24096) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24096 : ℝ)^2 / (mW 12048 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2148163/1000000000000))/2) * ((1-firstRatio 24096) * √(1-firstRatio 24096) *
      sixthConstant (e1CovarianceRatio 24096 (mW 12048) (1/10^6) rowEps))) /
    (712/10000 - 24096*(1+1/10^6)*((2148163/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24096 (mW 12048) /
    ((1/10^5) * ((mW 12048 : ℝ)*24096*((mW 12048 : ℝ)+24096+1)))^2 +
  8*(mW 12048 : ℝ)*24096*(24096+2)*(24096+3) /
    ((1/1000)*((mW 12048 : ℝ)*24096*(24096+2)))^2 +
  covarianceVarianceBound 24096 (mW 12048) /
    ((1/1000)*covarianceMeanBound 24096 (mW 12048))^2 +
  normVarianceBound 24096 (mW 12048) / (3*inputVarianceMean 24096 (mW 12048))^2

end BstLean.Part281.WorldRow12048
namespace BstLean.Part281.WorldRow12049
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12049 = 192012063695803 := by
  have hu : mW 12049 ≤ 192012063695803 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12049 ≤ 192012063695802 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12049)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24098 ^ 2)
    ((25000000000000000000/3785304988310341873032503))
    ((25000000000000000000/3785147908677662383358531)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24098) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24098 : ℝ)^2 / (mW 12049 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2147983/1000000000000))/2) * ((1-firstRatio 24098) * √(1-firstRatio 24098) *
      sixthConstant (e1CovarianceRatio 24098 (mW 12049) (1/10^6) rowEps))) /
    (712/10000 - 24098*(1+1/10^6)*((2147983/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24098 (mW 12049) /
    ((1/10^5) * ((mW 12049 : ℝ)*24098*((mW 12049 : ℝ)+24098+1)))^2 +
  8*(mW 12049 : ℝ)*24098*(24098+2)*(24098+3) /
    ((1/1000)*((mW 12049 : ℝ)*24098*(24098+2)))^2 +
  covarianceVarianceBound 24098 (mW 12049) /
    ((1/1000)*covarianceMeanBound 24098 (mW 12049))^2 +
  normVarianceBound 24098 (mW 12049) / (3*inputVarianceMean 24098 (mW 12049))^2

end BstLean.Part281.WorldRow12049
namespace BstLean.Part281.WorldRow12050
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12050 = 192067845249918 := by
  have hu : mW 12050 ≤ 192067845249918 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12050 ≤ 192067845249917 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12050)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24100 ^ 2)
    ((500000000000000000/75712382951514017047127))
    ((25000000000000000000/3785462067943021362682377)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24100) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24100 : ℝ)^2 / (mW 12050 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1073901/500000000000))/2) * ((1-firstRatio 24100) * √(1-firstRatio 24100) *
      sixthConstant (e1CovarianceRatio 24100 (mW 12050) (1/10^6) rowEps))) /
    (712/10000 - 24100*(1+1/10^6)*((1073901/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24100 (mW 12050) /
    ((1/10^5) * ((mW 12050 : ℝ)*24100*((mW 12050 : ℝ)+24100+1)))^2 +
  8*(mW 12050 : ℝ)*24100*(24100+2)*(24100+3) /
    ((1/1000)*((mW 12050 : ℝ)*24100*(24100+2)))^2 +
  covarianceVarianceBound 24100 (mW 12050) /
    ((1/1000)*covarianceMeanBound 24100 (mW 12050))^2 +
  normVarianceBound 24100 (mW 12050) / (3*inputVarianceMean 24100 (mW 12050))^2

end BstLean.Part281.WorldRow12050
namespace BstLean.Part281.WorldRow12051
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12051 = 192123638378171 := by
  have hu : mW 12051 ≤ 192123638378171 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12051 ≤ 192123638378170 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12051)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24102 ^ 2)
    ((25000000000000000000/3785933306841059831680197))
    ((25000000000000000000/3785776227208380342006223)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24102) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24102 : ℝ)^2 / (mW 12051 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1073811/500000000000))/2) * ((1-firstRatio 24102) * √(1-firstRatio 24102) *
      sixthConstant (e1CovarianceRatio 24102 (mW 12051) (1/10^6) rowEps))) /
    (712/10000 - 24102*(1+1/10^6)*((1073811/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24102 (mW 12051) /
    ((1/10^5) * ((mW 12051 : ℝ)*24102*((mW 12051 : ℝ)+24102+1)))^2 +
  8*(mW 12051 : ℝ)*24102*(24102+2)*(24102+3) /
    ((1/1000)*((mW 12051 : ℝ)*24102*(24102+2)))^2 +
  covarianceVarianceBound 24102 (mW 12051) /
    ((1/1000)*covarianceMeanBound 24102 (mW 12051))^2 +
  normVarianceBound 24102 (mW 12051) / (3*inputVarianceMean 24102 (mW 12051))^2

end BstLean.Part281.WorldRow12051
namespace BstLean.Part281.WorldRow12052
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12052 = 192179443082001 := by
  have hu : mW 12052 ≤ 192179443082001 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12052 ≤ 192179443082000 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12052)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24104 ^ 2)
    ((6250000000000000000/946561866526604702751011))
    ((25000000000000000000/3786090386473739321330069)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24104) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24104 : ℝ)^2 / (mW 12052 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1073721/500000000000))/2) * ((1-firstRatio 24104) * √(1-firstRatio 24104) *
      sixthConstant (e1CovarianceRatio 24104 (mW 12052) (1/10^6) rowEps))) /
    (712/10000 - 24104*(1+1/10^6)*((1073721/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24104 (mW 12052) /
    ((1/10^5) * ((mW 12052 : ℝ)*24104*((mW 12052 : ℝ)+24104+1)))^2 +
  8*(mW 12052 : ℝ)*24104*(24104+2)*(24104+3) /
    ((1/1000)*((mW 12052 : ℝ)*24104*(24104+2)))^2 +
  covarianceVarianceBound 24104 (mW 12052) /
    ((1/1000)*covarianceMeanBound 24104 (mW 12052))^2 +
  normVarianceBound 24104 (mW 12052) / (3*inputVarianceMean 24104 (mW 12052))^2

end BstLean.Part281.WorldRow12052
namespace BstLean.Part281.WorldRow12053
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12053 = 192235259362851 := by
  have hu : mW 12053 ≤ 192235259362851 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12053 ≤ 192235259362850 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12053)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24106 ^ 2)
    ((25000000000000000000/3786561625371777790327891))
    ((5000000000000000000/757280909147819660130783)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24106) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24106 : ℝ)^2 / (mW 12053 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1073631/500000000000))/2) * ((1-firstRatio 24106) * √(1-firstRatio 24106) *
      sixthConstant (e1CovarianceRatio 24106 (mW 12053) (1/10^6) rowEps))) /
    (712/10000 - 24106*(1+1/10^6)*((1073631/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24106 (mW 12053) /
    ((1/10^5) * ((mW 12053 : ℝ)*24106*((mW 12053 : ℝ)+24106+1)))^2 +
  8*(mW 12053 : ℝ)*24106*(24106+2)*(24106+3) /
    ((1/1000)*((mW 12053 : ℝ)*24106*(24106+2)))^2 +
  covarianceVarianceBound 24106 (mW 12053) /
    ((1/1000)*covarianceMeanBound 24106 (mW 12053))^2 +
  normVarianceBound 24106 (mW 12053) / (3*inputVarianceMean 24106 (mW 12053))^2

end BstLean.Part281.WorldRow12053
namespace BstLean.Part281.WorldRow12054
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12054 = 192291087222160 := by
  have hu : mW 12054 ≤ 192291087222160 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12054 ≤ 192291087222159 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12054)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24108 ^ 2)
    ((12500000000000000000/1893437892318568384825869))
    ((25000000000000000000/3786718705004457279977761)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24108) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24108 : ℝ)^2 / (mW 12054 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1073541/500000000000))/2) * ((1-firstRatio 24108) * √(1-firstRatio 24108) *
      sixthConstant (e1CovarianceRatio 24108 (mW 12054) (1/10^6) rowEps))) /
    (712/10000 - 24108*(1+1/10^6)*((1073541/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24108 (mW 12054) /
    ((1/10^5) * ((mW 12054 : ℝ)*24108*((mW 12054 : ℝ)+24108+1)))^2 +
  8*(mW 12054 : ℝ)*24108*(24108+2)*(24108+3) /
    ((1/1000)*((mW 12054 : ℝ)*24108*(24108+2)))^2 +
  covarianceVarianceBound 24108 (mW 12054) /
    ((1/1000)*covarianceMeanBound 24108 (mW 12054))^2 +
  normVarianceBound 24108 (mW 12054) / (3*inputVarianceMean 24108 (mW 12054))^2

end BstLean.Part281.WorldRow12054
namespace BstLean.Part281.WorldRow12055
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12055 = 192346926661369 := by
  have hu : mW 12055 ≤ 192346926661369 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12055 ≤ 192346926661368 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12055)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24110 ^ 2)
    ((5000000000000000000/757437988780499149795117))
    ((25000000000000000000/3787032864269816259301607)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24110) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24110 : ℝ)^2 / (mW 12055 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1073451/500000000000))/2) * ((1-firstRatio 24110) * √(1-firstRatio 24110) *
      sixthConstant (e1CovarianceRatio 24110 (mW 12055) (1/10^6) rowEps))) /
    (712/10000 - 24110*(1+1/10^6)*((1073451/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24110 (mW 12055) /
    ((1/10^5) * ((mW 12055 : ℝ)*24110*((mW 12055 : ℝ)+24110+1)))^2 +
  8*(mW 12055 : ℝ)*24110*(24110+2)*(24110+3) /
    ((1/1000)*((mW 12055 : ℝ)*24110*(24110+2)))^2 +
  covarianceVarianceBound 24110 (mW 12055) /
    ((1/1000)*covarianceMeanBound 24110 (mW 12055))^2 +
  normVarianceBound 24110 (mW 12055) / (3*inputVarianceMean 24110 (mW 12055))^2

end BstLean.Part281.WorldRow12055
namespace BstLean.Part281.WorldRow12056
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12056 = 192402777681921 := by
  have hu : mW 12056 ≤ 192402777681921 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12056 ≤ 192402777681920 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12056)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24112 ^ 2)
    ((3125000000000000000/473438012895981841037429))
    ((25000000000000000000/3787347023535175238625453)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24112) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24112 : ℝ)^2 / (mW 12056 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2146721/1000000000000))/2) * ((1-firstRatio 24112) * √(1-firstRatio 24112) *
      sixthConstant (e1CovarianceRatio 24112 (mW 12056) (1/10^6) rowEps))) /
    (712/10000 - 24112*(1+1/10^6)*((2146721/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24112 (mW 12056) /
    ((1/10^5) * ((mW 12056 : ℝ)*24112*((mW 12056 : ℝ)+24112+1)))^2 +
  8*(mW 12056 : ℝ)*24112*(24112+2)*(24112+3) /
    ((1/1000)*((mW 12056 : ℝ)*24112*(24112+2)))^2 +
  covarianceVarianceBound 24112 (mW 12056) /
    ((1/1000)*covarianceMeanBound 24112 (mW 12056))^2 +
  normVarianceBound 24112 (mW 12056) / (3*inputVarianceMean 24112 (mW 12056))^2

end BstLean.Part281.WorldRow12056
namespace BstLean.Part281.WorldRow12057
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12057 = 192458640285255 := by
  have hu : mW 12057 ≤ 192458640285255 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12057 ≤ 192458640285254 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12057)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24114 ^ 2)
    ((25000000000000000000/3787818262433213707623279))
    ((25000000000000000000/3787661182800534217949299)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24114) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24114 : ℝ)^2 / (mW 12057 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2146541/1000000000000))/2) * ((1-firstRatio 24114) * √(1-firstRatio 24114) *
      sixthConstant (e1CovarianceRatio 24114 (mW 12057) (1/10^6) rowEps))) /
    (712/10000 - 24114*(1+1/10^6)*((2146541/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24114 (mW 12057) /
    ((1/10^5) * ((mW 12057 : ℝ)*24114*((mW 12057 : ℝ)+24114+1)))^2 +
  8*(mW 12057 : ℝ)*24114*(24114+2)*(24114+3) /
    ((1/1000)*((mW 12057 : ℝ)*24114*(24114+2)))^2 +
  covarianceVarianceBound 24114 (mW 12057) /
    ((1/1000)*covarianceMeanBound 24114 (mW 12057))^2 +
  normVarianceBound 24114 (mW 12057) / (3*inputVarianceMean 24114 (mW 12057))^2

end BstLean.Part281.WorldRow12057
namespace BstLean.Part281.WorldRow12058
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12058 = 192514514472813 := by
  have hu : mW 12058 ≤ 192514514472813 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12058 ≤ 192514514472812 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12058)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24116 ^ 2)
    ((12500000000000000000/1894066210849286343473563))
    ((5000000000000000000/757595068413178639454629)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24116) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24116 : ℝ)^2 / (mW 12058 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2146361/1000000000000))/2) * ((1-firstRatio 24116) * √(1-firstRatio 24116) *
      sixthConstant (e1CovarianceRatio 24116 (mW 12058) (1/10^6) rowEps))) /
    (712/10000 - 24116*(1+1/10^6)*((2146361/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24116 (mW 12058) /
    ((1/10^5) * ((mW 12058 : ℝ)*24116*((mW 12058 : ℝ)+24116+1)))^2 +
  8*(mW 12058 : ℝ)*24116*(24116+2)*(24116+3) /
    ((1/1000)*((mW 12058 : ℝ)*24116*(24116+2)))^2 +
  covarianceVarianceBound 24116 (mW 12058) /
    ((1/1000)*covarianceMeanBound 24116 (mW 12058))^2 +
  normVarianceBound 24116 (mW 12058) / (3*inputVarianceMean 24116 (mW 12058))^2

end BstLean.Part281.WorldRow12058
