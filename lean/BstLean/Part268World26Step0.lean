import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar26
namespace BstLean.Part268.WorldRow13000
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13000 = 250496540894281 := by
  have hu : mW 13000 ≤ 250496540894281 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13000 ≤ 250496540894280 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13000)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26000 ^ 2)
    ((25000000000000000/4084070449666731210011))
    ((25000000000000000000/4083913370034051720336077)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26000) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26000 : ℝ)^2 / (mW 13000 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1989233/1000000000000))/2) * ((1-firstRatio 26000) * √(1-firstRatio 26000) *
      sixthConstant (e1CovarianceRatio 26000 (mW 13000) (1/10^6) rowEps))) /
    (712/10000 - 26000*(1+1/10^6)*((1989233/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26000 (mW 13000) /
    ((1/10^5) * ((mW 13000 : ℝ)*26000*((mW 13000 : ℝ)+26000+1)))^2 +
  8*(mW 13000 : ℝ)*26000*(26000+2)*(26000+3) /
    ((1/1000)*((mW 13000 : ℝ)*26000*(26000+2)))^2 +
  covarianceVarianceBound 26000 (mW 13000) /
    ((1/1000)*covarianceMeanBound 26000 (mW 13000))^2 +
  normVarianceBound 26000 (mW 13000) / (3*inputVarianceMean 26000 (mW 13000))^2

end BstLean.Part268.WorldRow13000
namespace BstLean.Part268.WorldRow13001
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13001 = 250563988755673 := by
  have hu : mW 13001 ≤ 250563988755673 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13001 ≤ 250563988755672 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13001)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26002 ^ 2)
    ((25000000000000000000/4084384608932090189334847))
    ((25000000000000000000/4084227529299410699659923)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26002) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26002 : ℝ)^2 / (mW 13001 : ℝ)) * (1 + 1/10^6)^2 *
    √(((994539/500000000000))/2) * ((1-firstRatio 26002) * √(1-firstRatio 26002) *
      sixthConstant (e1CovarianceRatio 26002 (mW 13001) (1/10^6) rowEps))) /
    (712/10000 - 26002*(1+1/10^6)*((994539/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26002 (mW 13001) /
    ((1/10^5) * ((mW 13001 : ℝ)*26002*((mW 13001 : ℝ)+26002+1)))^2 +
  8*(mW 13001 : ℝ)*26002*(26002+2)*(26002+3) /
    ((1/1000)*((mW 13001 : ℝ)*26002*(26002+2)))^2 +
  covarianceVarianceBound 26002 (mW 13001) /
    ((1/1000)*covarianceMeanBound 26002 (mW 13001))^2 +
  normVarianceBound 26002 (mW 13001) / (3*inputVarianceMean 26002 (mW 13001))^2

end BstLean.Part268.WorldRow13001
namespace BstLean.Part268.WorldRow13002
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13002 = 250631449588057 := by
  have hu : mW 13002 ≤ 250631449588057 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13002 ≤ 250631449588056 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13002)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26004 ^ 2)
    ((12500000000000000000/2042349384098724584329347))
    ((25000000000000000000/4084541688564769678983769)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26004) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26004 : ℝ)^2 / (mW 13002 : ℝ)) * (1 + 1/10^6)^2 *
    √(((497231/250000000000))/2) * ((1-firstRatio 26004) * √(1-firstRatio 26004) *
      sixthConstant (e1CovarianceRatio 26004 (mW 13002) (1/10^6) rowEps))) /
    (712/10000 - 26004*(1+1/10^6)*((497231/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26004 (mW 13002) /
    ((1/10^5) * ((mW 13002 : ℝ)*26004*((mW 13002 : ℝ)+26004+1)))^2 +
  8*(mW 13002 : ℝ)*26004*(26004+2)*(26004+3) /
    ((1/1000)*((mW 13002 : ℝ)*26004*(26004+2)))^2 +
  covarianceVarianceBound 26004 (mW 13002) /
    ((1/1000)*covarianceMeanBound 26004 (mW 13002))^2 +
  normVarianceBound 26004 (mW 13002) / (3*inputVarianceMean 26004 (mW 13002))^2

end BstLean.Part268.WorldRow13002
namespace BstLean.Part268.WorldRow13003
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13003 = 250698923392929 := by
  have hu : mW 13003 ≤ 250698923392929 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13003 ≤ 250698923392928 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13003)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26006 ^ 2)
    ((25000000000000000000/4085012927462808147982541))
    ((5000000000000000000/816971169566025731661523)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26006) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26006 : ℝ)^2 / (mW 13003 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1988769/1000000000000))/2) * ((1-firstRatio 26006) * √(1-firstRatio 26006) *
      sixthConstant (e1CovarianceRatio 26006 (mW 13003) (1/10^6) rowEps))) /
    (712/10000 - 26006*(1+1/10^6)*((1988769/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26006 (mW 13003) /
    ((1/10^5) * ((mW 13003 : ℝ)*26006*((mW 13003 : ℝ)+26006+1)))^2 +
  8*(mW 13003 : ℝ)*26006*(26006+2)*(26006+3) /
    ((1/1000)*((mW 13003 : ℝ)*26006*(26006+2)))^2 +
  covarianceVarianceBound 26006 (mW 13003) /
    ((1/1000)*covarianceMeanBound 26006 (mW 13003))^2 +
  normVarianceBound 26006 (mW 13003) / (3*inputVarianceMean 26006 (mW 13003))^2

end BstLean.Part268.WorldRow13003
namespace BstLean.Part268.WorldRow13004
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13004 = 250766410171786 := by
  have hu : mW 13004 ≤ 250766410171786 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13004 ≤ 250766410171785 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13004)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26008 ^ 2)
    ((6250000000000000000/1021331771682041781826597))
    ((25000000000000000000/4085170007095487637631461)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26008) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26008 : ℝ)^2 / (mW 13004 : ℝ)) * (1 + 1/10^6)^2 *
    √(((397723/200000000000))/2) * ((1-firstRatio 26008) * √(1-firstRatio 26008) *
      sixthConstant (e1CovarianceRatio 26008 (mW 13004) (1/10^6) rowEps))) /
    (712/10000 - 26008*(1+1/10^6)*((397723/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26008 (mW 13004) /
    ((1/10^5) * ((mW 13004 : ℝ)*26008*((mW 13004 : ℝ)+26008+1)))^2 +
  8*(mW 13004 : ℝ)*26008*(26008+2)*(26008+3) /
    ((1/1000)*((mW 13004 : ℝ)*26008*(26008+2)))^2 +
  covarianceVarianceBound 26008 (mW 13004) /
    ((1/1000)*covarianceMeanBound 26008 (mW 13004))^2 +
  normVarianceBound 26008 (mW 13004) / (3*inputVarianceMean 26008 (mW 13004))^2

end BstLean.Part268.WorldRow13004
namespace BstLean.Part268.WorldRow13005
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13005 = 250833909926126 := by
  have hu : mW 13005 ≤ 250833909926126 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13005 ≤ 250833909926125 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13005)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26010 ^ 2)
    ((5000000000000000000/817128249198705221326047))
    ((25000000000000000000/4085484166360846616955307)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26010) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26010 : ℝ)^2 / (mW 13005 : ℝ)) * (1 + 1/10^6)^2 *
    √(((99423/50000000000))/2) * ((1-firstRatio 26010) * √(1-firstRatio 26010) *
      sixthConstant (e1CovarianceRatio 26010 (mW 13005) (1/10^6) rowEps))) /
    (712/10000 - 26010*(1+1/10^6)*((99423/50000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26010 (mW 13005) /
    ((1/10^5) * ((mW 13005 : ℝ)*26010*((mW 13005 : ℝ)+26010+1)))^2 +
  8*(mW 13005 : ℝ)*26010*(26010+2)*(26010+3) /
    ((1/1000)*((mW 13005 : ℝ)*26010*(26010+2)))^2 +
  covarianceVarianceBound 26010 (mW 13005) /
    ((1/1000)*covarianceMeanBound 26010 (mW 13005))^2 +
  normVarianceBound 26010 (mW 13005) / (3*inputVarianceMean 26010 (mW 13005))^2

end BstLean.Part268.WorldRow13005
namespace BstLean.Part268.WorldRow13006
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13006 = 250901422657443 := by
  have hu : mW 13006 ≤ 250901422657443 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13006 ≤ 250901422657442 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13006)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26012 ^ 2)
    ((12500000000000000000/2042977702629442542977041))
    ((25000000000000000000/4085798325626205596279153)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26012) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26012 : ℝ)^2 / (mW 13006 : ℝ)) * (1 + 1/10^6)^2 *
    √(((994153/500000000000))/2) * ((1-firstRatio 26012) * √(1-firstRatio 26012) *
      sixthConstant (e1CovarianceRatio 26012 (mW 13006) (1/10^6) rowEps))) /
    (712/10000 - 26012*(1+1/10^6)*((994153/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26012 (mW 13006) /
    ((1/10^5) * ((mW 13006 : ℝ)*26012*((mW 13006 : ℝ)+26012+1)))^2 +
  8*(mW 13006 : ℝ)*26012*(26012+2)*(26012+3) /
    ((1/1000)*((mW 13006 : ℝ)*26012*(26012+2)))^2 +
  covarianceVarianceBound 26012 (mW 13006) /
    ((1/1000)*covarianceMeanBound 26012 (mW 13006))^2 +
  normVarianceBound 26012 (mW 13006) / (3*inputVarianceMean 26012 (mW 13006))^2

end BstLean.Part268.WorldRow13006
namespace BstLean.Part268.WorldRow13007
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13007 = 250968948367237 := by
  have hu : mW 13007 ≤ 250968948367237 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13007 ≤ 250968948367236 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13007)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26014 ^ 2)
    ((25000000000000000000/4086269564524244065277929))
    ((25000000000000000000/4086112484891564575602999)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26014) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26014 : ℝ)^2 / (mW 13007 : ℝ)) * (1 + 1/10^6)^2 *
    √(((248519/125000000000))/2) * ((1-firstRatio 26014) * √(1-firstRatio 26014) *
      sixthConstant (e1CovarianceRatio 26014 (mW 13007) (1/10^6) rowEps))) /
    (712/10000 - 26014*(1+1/10^6)*((248519/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26014 (mW 13007) /
    ((1/10^5) * ((mW 13007 : ℝ)*26014*((mW 13007 : ℝ)+26014+1)))^2 +
  8*(mW 13007 : ℝ)*26014*(26014+2)*(26014+3) /
    ((1/1000)*((mW 13007 : ℝ)*26014*(26014+2)))^2 +
  covarianceVarianceBound 26014 (mW 13007) /
    ((1/1000)*covarianceMeanBound 26014 (mW 13007))^2 +
  normVarianceBound 26014 (mW 13007) / (3*inputVarianceMean 26014 (mW 13007))^2

end BstLean.Part268.WorldRow13007
namespace BstLean.Part268.WorldRow13008
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13008 = 251036487057002 := by
  have hu : mW 13008 ≤ 251036487057002 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13008 ≤ 251036487057001 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13008)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26016 ^ 2)
    ((1562500000000000000/255411482736850190287611))
    ((5000000000000000000/817285328831384710985369)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26016) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26016 : ℝ)^2 / (mW 13008 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1987997/1000000000000))/2) * ((1-firstRatio 26016) * √(1-firstRatio 26016) *
      sixthConstant (e1CovarianceRatio 26016 (mW 13008) (1/10^6) rowEps))) /
    (712/10000 - 26016*(1+1/10^6)*((1987997/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26016 (mW 13008) /
    ((1/10^5) * ((mW 13008 : ℝ)*26016*((mW 13008 : ℝ)+26016+1)))^2 +
  8*(mW 13008 : ℝ)*26016*(26016+2)*(26016+3) /
    ((1/1000)*((mW 13008 : ℝ)*26016*(26016+2)))^2 +
  covarianceVarianceBound 26016 (mW 13008) /
    ((1/1000)*covarianceMeanBound 26016 (mW 13008))^2 +
  normVarianceBound 26016 (mW 13008) / (3*inputVarianceMean 26016 (mW 13008))^2

end BstLean.Part268.WorldRow13008
namespace BstLean.Part268.WorldRow13009
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13009 = 251104038728237 := by
  have hu : mW 13009 ≤ 251104038728237 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13009 ≤ 251104038728236 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13009)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26018 ^ 2)
    ((25000000000000000000/4086897883054962023925623))
    ((25000000000000000000/4086740803422282534250691)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26018) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26018 : ℝ)^2 / (mW 13009 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1987843/1000000000000))/2) * ((1-firstRatio 26018) * √(1-firstRatio 26018) *
      sixthConstant (e1CovarianceRatio 26018 (mW 13009) (1/10^6) rowEps))) /
    (712/10000 - 26018*(1+1/10^6)*((1987843/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26018 (mW 13009) /
    ((1/10^5) * ((mW 13009 : ℝ)*26018*((mW 13009 : ℝ)+26018+1)))^2 +
  8*(mW 13009 : ℝ)*26018*(26018+2)*(26018+3) /
    ((1/1000)*((mW 13009 : ℝ)*26018*(26018+2)))^2 +
  covarianceVarianceBound 26018 (mW 13009) /
    ((1/1000)*covarianceMeanBound 26018 (mW 13009))^2 +
  normVarianceBound 26018 (mW 13009) / (3*inputVarianceMean 26018 (mW 13009))^2

end BstLean.Part268.WorldRow13009
namespace BstLean.Part268.WorldRow13010
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13010 = 251171603382438 := by
  have hu : mW 13010 ≤ 251171603382438 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13010 ≤ 251171603382437 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13010)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26020 ^ 2)
    ((2500000000000000000/408721204232032100324947))
    ((25000000000000000000/4087054962687641513574537)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26020) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26020 : ℝ)^2 / (mW 13010 : ℝ)) * (1 + 1/10^6)^2 *
    √(((248461/125000000000))/2) * ((1-firstRatio 26020) * √(1-firstRatio 26020) *
      sixthConstant (e1CovarianceRatio 26020 (mW 13010) (1/10^6) rowEps))) /
    (712/10000 - 26020*(1+1/10^6)*((248461/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26020 (mW 13010) /
    ((1/10^5) * ((mW 13010 : ℝ)*26020*((mW 13010 : ℝ)+26020+1)))^2 +
  8*(mW 13010 : ℝ)*26020*(26020+2)*(26020+3) /
    ((1/1000)*((mW 13010 : ℝ)*26020*(26020+2)))^2 +
  covarianceVarianceBound 26020 (mW 13010) /
    ((1/1000)*covarianceMeanBound 26020 (mW 13010))^2 +
  normVarianceBound 26020 (mW 13010) / (3*inputVarianceMean 26020 (mW 13010))^2

end BstLean.Part268.WorldRow13010
namespace BstLean.Part268.WorldRow13011
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13011 = 251239181021102 := by
  have hu : mW 13011 ≤ 251239181021102 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13011 ≤ 251239181021101 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13011)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26022 ^ 2)
    ((25000000000000000000/4087526201585679982573317))
    ((25000000000000000000/4087369121953000492898383)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26022) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26022 : ℝ)^2 / (mW 13011 : ℝ)) * (1 + 1/10^6)^2 *
    √(((993767/500000000000))/2) * ((1-firstRatio 26022) * √(1-firstRatio 26022) *
      sixthConstant (e1CovarianceRatio 26022 (mW 13011) (1/10^6) rowEps))) /
    (712/10000 - 26022*(1+1/10^6)*((993767/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26022 (mW 13011) /
    ((1/10^5) * ((mW 13011 : ℝ)*26022*((mW 13011 : ℝ)+26022+1)))^2 +
  8*(mW 13011 : ℝ)*26022*(26022+2)*(26022+3) /
    ((1/1000)*((mW 13011 : ℝ)*26022*(26022+2)))^2 +
  covarianceVarianceBound 26022 (mW 13011) /
    ((1/1000)*covarianceMeanBound 26022 (mW 13011))^2 +
  normVarianceBound 26022 (mW 13011) / (3*inputVarianceMean 26022 (mW 13011))^2

end BstLean.Part268.WorldRow13011
namespace BstLean.Part268.WorldRow13012
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13012 = 251306771645726 := by
  have hu : mW 13012 ≤ 251306771645726 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13012 ≤ 251306771645725 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13012)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26024 ^ 2)
    ((6250000000000000000/1021960090212759740474291))
    ((25000000000000000000/4087683281218359472222229)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26024) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26024 : ℝ)^2 / (mW 13012 : ℝ)) * (1 + 1/10^6)^2 *
    √(((99369/50000000000))/2) * ((1-firstRatio 26024) * √(1-firstRatio 26024) *
      sixthConstant (e1CovarianceRatio 26024 (mW 13012) (1/10^6) rowEps))) /
    (712/10000 - 26024*(1+1/10^6)*((99369/50000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26024 (mW 13012) /
    ((1/10^5) * ((mW 13012 : ℝ)*26024*((mW 13012 : ℝ)+26024+1)))^2 +
  8*(mW 13012 : ℝ)*26024*(26024+2)*(26024+3) /
    ((1/1000)*((mW 13012 : ℝ)*26024*(26024+2)))^2 +
  covarianceVarianceBound 26024 (mW 13012) /
    ((1/1000)*covarianceMeanBound 26024 (mW 13012))^2 +
  normVarianceBound 26024 (mW 13012) / (3*inputVarianceMean 26024 (mW 13012))^2

end BstLean.Part268.WorldRow13012
namespace BstLean.Part268.WorldRow13013
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13013 = 251374375257807 := by
  have hu : mW 13013 ≤ 251374375257807 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13013 ≤ 251374375257806 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13013)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26026 ^ 2)
    ((25000000000000000000/4088154520116397941221011))
    ((1000000000000000000/163519897619348738061843)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26026) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26026 : ℝ)^2 / (mW 13013 : ℝ)) * (1 + 1/10^6)^2 *
    √(((993613/500000000000))/2) * ((1-firstRatio 26026) * √(1-firstRatio 26026) *
      sixthConstant (e1CovarianceRatio 26026 (mW 13013) (1/10^6) rowEps))) /
    (712/10000 - 26026*(1+1/10^6)*((993613/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26026 (mW 13013) /
    ((1/10^5) * ((mW 13013 : ℝ)*26026*((mW 13013 : ℝ)+26026+1)))^2 +
  8*(mW 13013 : ℝ)*26026*(26026+2)*(26026+3) /
    ((1/1000)*((mW 13013 : ℝ)*26026*(26026+2)))^2 +
  covarianceVarianceBound 26026 (mW 13013) /
    ((1/1000)*covarianceMeanBound 26026 (mW 13013))^2 +
  normVarianceBound 26026 (mW 13013) / (3*inputVarianceMean 26026 (mW 13013))^2

end BstLean.Part268.WorldRow13013
namespace BstLean.Part268.WorldRow13014
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13014 = 251441991858843 := by
  have hu : mW 13014 ≤ 251441991858843 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13014 ≤ 251441991858842 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13014)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26028 ^ 2)
    ((12500000000000000000/2044234339690878460272429))
    ((25000000000000000000/4088311599749077430869921)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26028) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26028 : ℝ)^2 / (mW 13014 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1987071/1000000000000))/2) * ((1-firstRatio 26028) * √(1-firstRatio 26028) *
      sixthConstant (e1CovarianceRatio 26028 (mW 13014) (1/10^6) rowEps))) /
    (712/10000 - 26028*(1+1/10^6)*((1987071/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26028 (mW 13014) /
    ((1/10^5) * ((mW 13014 : ℝ)*26028*((mW 13014 : ℝ)+26028+1)))^2 +
  8*(mW 13014 : ℝ)*26028*(26028+2)*(26028+3) /
    ((1/1000)*((mW 13014 : ℝ)*26028*(26028+2)))^2 +
  covarianceVarianceBound 26028 (mW 13014) /
    ((1/1000)*covarianceMeanBound 26028 (mW 13014))^2 +
  normVarianceBound 26028 (mW 13014) / (3*inputVarianceMean 26028 (mW 13014))^2

end BstLean.Part268.WorldRow13014
namespace BstLean.Part268.WorldRow13015
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13015 = 251509621450331 := by
  have hu : mW 13015 ≤ 251509621450331 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13015 ≤ 251509621450330 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13015)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26030 ^ 2)
    ((5000000000000000000/817756567729423179973741))
    ((25000000000000000000/4088625759014436410193767)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26030) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26030 : ℝ)^2 / (mW 13015 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1986917/1000000000000))/2) * ((1-firstRatio 26030) * √(1-firstRatio 26030) *
      sixthConstant (e1CovarianceRatio 26030 (mW 13015) (1/10^6) rowEps))) /
    (712/10000 - 26030*(1+1/10^6)*((1986917/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26030 (mW 13015) /
    ((1/10^5) * ((mW 13015 : ℝ)*26030*((mW 13015 : ℝ)+26030+1)))^2 +
  8*(mW 13015 : ℝ)*26030*(26030+2)*(26030+3) /
    ((1/1000)*((mW 13015 : ℝ)*26030*(26030+2)))^2 +
  covarianceVarianceBound 26030 (mW 13015) /
    ((1/1000)*covarianceMeanBound 26030 (mW 13015))^2 +
  normVarianceBound 26030 (mW 13015) / (3*inputVarianceMean 26030 (mW 13015))^2

end BstLean.Part268.WorldRow13015
namespace BstLean.Part268.WorldRow13016
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13016 = 251577264033768 := by
  have hu : mW 13016 ≤ 251577264033768 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13016 ≤ 251577264033767 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13016)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26032 ^ 2)
    ((3125000000000000000/511137124739059359899069))
    ((25000000000000000000/4088939918279795389517613)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26032) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26032 : ℝ)^2 / (mW 13016 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1986763/1000000000000))/2) * ((1-firstRatio 26032) * √(1-firstRatio 26032) *
      sixthConstant (e1CovarianceRatio 26032 (mW 13016) (1/10^6) rowEps))) /
    (712/10000 - 26032*(1+1/10^6)*((1986763/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26032 (mW 13016) /
    ((1/10^5) * ((mW 13016 : ℝ)*26032*((mW 13016 : ℝ)+26032+1)))^2 +
  8*(mW 13016 : ℝ)*26032*(26032+2)*(26032+3) /
    ((1/1000)*((mW 13016 : ℝ)*26032*(26032+2)))^2 +
  covarianceVarianceBound 26032 (mW 13016) /
    ((1/1000)*covarianceMeanBound 26032 (mW 13016))^2 +
  normVarianceBound 26032 (mW 13016) / (3*inputVarianceMean 26032 (mW 13016))^2

end BstLean.Part268.WorldRow13016
namespace BstLean.Part268.WorldRow13017
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13017 = 251644919610652 := by
  have hu : mW 13017 ≤ 251644919610652 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13017 ≤ 251644919610651 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13017)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26034 ^ 2)
    ((25000000000000000000/4089411157177833858516399))
    ((25000000000000000000/4089254077545154368841459)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26034) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26034 : ℝ)^2 / (mW 13017 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1986609/1000000000000))/2) * ((1-firstRatio 26034) * √(1-firstRatio 26034) *
      sixthConstant (e1CovarianceRatio 26034 (mW 13017) (1/10^6) rowEps))) /
    (712/10000 - 26034*(1+1/10^6)*((1986609/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26034 (mW 13017) /
    ((1/10^5) * ((mW 13017 : ℝ)*26034*((mW 13017 : ℝ)+26034+1)))^2 +
  8*(mW 13017 : ℝ)*26034*(26034+2)*(26034+3) /
    ((1/1000)*((mW 13017 : ℝ)*26034*(26034+2)))^2 +
  covarianceVarianceBound 26034 (mW 13017) /
    ((1/1000)*covarianceMeanBound 26034 (mW 13017))^2 +
  normVarianceBound 26034 (mW 13017) / (3*inputVarianceMean 26034 (mW 13017))^2

end BstLean.Part268.WorldRow13017
namespace BstLean.Part268.WorldRow13018
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13018 = 251712588182479 := by
  have hu : mW 13018 ≤ 251712588182479 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13018 ≤ 251712588182478 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13018)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26036 ^ 2)
    ((12500000000000000000/2044862658221596418920123))
    ((5000000000000000000/817913647362102669633061)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26036) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26036 : ℝ)^2 / (mW 13018 : ℝ)) * (1 + 1/10^6)^2 *
    √(((397291/200000000000))/2) * ((1-firstRatio 26036) * √(1-firstRatio 26036) *
      sixthConstant (e1CovarianceRatio 26036 (mW 13018) (1/10^6) rowEps))) /
    (712/10000 - 26036*(1+1/10^6)*((397291/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26036 (mW 13018) /
    ((1/10^5) * ((mW 13018 : ℝ)*26036*((mW 13018 : ℝ)+26036+1)))^2 +
  8*(mW 13018 : ℝ)*26036*(26036+2)*(26036+3) /
    ((1/1000)*((mW 13018 : ℝ)*26036*(26036+2)))^2 +
  covarianceVarianceBound 26036 (mW 13018) /
    ((1/1000)*covarianceMeanBound 26036 (mW 13018))^2 +
  normVarianceBound 26036 (mW 13018) / (3*inputVarianceMean 26036 (mW 13018))^2

end BstLean.Part268.WorldRow13018
namespace BstLean.Part268.WorldRow13019
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13019 = 251780269750748 := by
  have hu : mW 13019 ≤ 251780269750748 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13019 ≤ 251780269750747 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13019)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26038 ^ 2)
    ((25000000000000000000/4090039475708551817164093))
    ((25000000000000000000/4089882396075872327489151)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26038) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26038 : ℝ)^2 / (mW 13019 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1986301/1000000000000))/2) * ((1-firstRatio 26038) * √(1-firstRatio 26038) *
      sixthConstant (e1CovarianceRatio 26038 (mW 13019) (1/10^6) rowEps))) /
    (712/10000 - 26038*(1+1/10^6)*((1986301/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26038 (mW 13019) /
    ((1/10^5) * ((mW 13019 : ℝ)*26038*((mW 13019 : ℝ)+26038+1)))^2 +
  8*(mW 13019 : ℝ)*26038*(26038+2)*(26038+3) /
    ((1/1000)*((mW 13019 : ℝ)*26038*(26038+2)))^2 +
  covarianceVarianceBound 26038 (mW 13019) /
    ((1/1000)*covarianceMeanBound 26038 (mW 13019))^2 +
  normVarianceBound 26038 (mW 13019) / (3*inputVarianceMean 26038 (mW 13019))^2

end BstLean.Part268.WorldRow13019
namespace BstLean.Part268.WorldRow13020
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13020 = 251847964316956 := by
  have hu : mW 13020 ≤ 251847964316956 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13020 ≤ 251847964316955 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13020)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26040 ^ 2)
    ((1250000000000000000/204517681748695539824397))
    ((25000000000000000000/4090196555341231306812997)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26040) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26040 : ℝ)^2 / (mW 13020 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1986147/1000000000000))/2) * ((1-firstRatio 26040) * √(1-firstRatio 26040) *
      sixthConstant (e1CovarianceRatio 26040 (mW 13020) (1/10^6) rowEps))) /
    (712/10000 - 26040*(1+1/10^6)*((1986147/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26040 (mW 13020) /
    ((1/10^5) * ((mW 13020 : ℝ)*26040*((mW 13020 : ℝ)+26040+1)))^2 +
  8*(mW 13020 : ℝ)*26040*(26040+2)*(26040+3) /
    ((1/1000)*((mW 13020 : ℝ)*26040*(26040+2)))^2 +
  covarianceVarianceBound 26040 (mW 13020) /
    ((1/1000)*covarianceMeanBound 26040 (mW 13020))^2 +
  normVarianceBound 26040 (mW 13020) / (3*inputVarianceMean 26040 (mW 13020))^2

end BstLean.Part268.WorldRow13020
namespace BstLean.Part268.WorldRow13021
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13021 = 251915671882601 := by
  have hu : mW 13021 ≤ 251915671882601 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13021 ≤ 251915671882600 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13021)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26042 ^ 2)
    ((25000000000000000000/4090667794239269775811787))
    ((25000000000000000000/4090510714606590286136843)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26042) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26042 : ℝ)^2 / (mW 13021 : ℝ)) * (1 + 1/10^6)^2 *
    √(((248249/125000000000))/2) * ((1-firstRatio 26042) * √(1-firstRatio 26042) *
      sixthConstant (e1CovarianceRatio 26042 (mW 13021) (1/10^6) rowEps))) /
    (712/10000 - 26042*(1+1/10^6)*((248249/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26042 (mW 13021) /
    ((1/10^5) * ((mW 13021 : ℝ)*26042*((mW 13021 : ℝ)+26042+1)))^2 +
  8*(mW 13021 : ℝ)*26042*(26042+2)*(26042+3) /
    ((1/1000)*((mW 13021 : ℝ)*26042*(26042+2)))^2 +
  covarianceVarianceBound 26042 (mW 13021) /
    ((1/1000)*covarianceMeanBound 26042 (mW 13021))^2 +
  normVarianceBound 26042 (mW 13021) / (3*inputVarianceMean 26042 (mW 13021))^2

end BstLean.Part268.WorldRow13021
namespace BstLean.Part268.WorldRow13022
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13022 = 251983392449179 := by
  have hu : mW 13022 ≤ 251983392449179 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13022 ≤ 251983392449178 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13022)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26044 ^ 2)
    ((12500000000000000000/2045490976752314377567817))
    ((25000000000000000000/4090824873871949265460689)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26044) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26044 : ℝ)^2 / (mW 13022 : ℝ)) * (1 + 1/10^6)^2 *
    √(((992919/500000000000))/2) * ((1-firstRatio 26044) * √(1-firstRatio 26044) *
      sixthConstant (e1CovarianceRatio 26044 (mW 13022) (1/10^6) rowEps))) /
    (712/10000 - 26044*(1+1/10^6)*((992919/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26044 (mW 13022) /
    ((1/10^5) * ((mW 13022 : ℝ)*26044*((mW 13022 : ℝ)+26044+1)))^2 +
  8*(mW 13022 : ℝ)*26044*(26044+2)*(26044+3) /
    ((1/1000)*((mW 13022 : ℝ)*26044*(26044+2)))^2 +
  covarianceVarianceBound 26044 (mW 13022) /
    ((1/1000)*covarianceMeanBound 26044 (mW 13022))^2 +
  normVarianceBound 26044 (mW 13022) / (3*inputVarianceMean 26044 (mW 13022))^2

end BstLean.Part268.WorldRow13022
namespace BstLean.Part268.WorldRow13023
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13023 = 252051126018190 := by
  have hu : mW 13023 ≤ 252051126018190 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13023 ≤ 252051126018189 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13023)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26046 ^ 2)
    ((25000000000000000000/4091296112769987734459481))
    ((5000000000000000000/818227806627461648956907)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26046) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26046 : ℝ)^2 / (mW 13023 : ℝ)) * (1 + 1/10^6)^2 *
    √(((496421/250000000000))/2) * ((1-firstRatio 26046) * √(1-firstRatio 26046) *
      sixthConstant (e1CovarianceRatio 26046 (mW 13023) (1/10^6) rowEps))) /
    (712/10000 - 26046*(1+1/10^6)*((496421/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26046 (mW 13023) /
    ((1/10^5) * ((mW 13023 : ℝ)*26046*((mW 13023 : ℝ)+26046+1)))^2 +
  8*(mW 13023 : ℝ)*26046*(26046+2)*(26046+3) /
    ((1/1000)*((mW 13023 : ℝ)*26046*(26046+2)))^2 +
  covarianceVarianceBound 26046 (mW 13023) /
    ((1/1000)*covarianceMeanBound 26046 (mW 13023))^2 +
  normVarianceBound 26046 (mW 13023) / (3*inputVarianceMean 26046 (mW 13023))^2

end BstLean.Part268.WorldRow13023
namespace BstLean.Part268.WorldRow13024
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 13024 = 252118872591130 := by
  have hu : mW 13024 ≤ 252118872591130 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 13024 ≤ 252118872591129 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*13024)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 26048 ^ 2)
    ((781250000000000000/127862821001104584805729))
    ((25000000000000000000/4091453192402667224108381)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 26048) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (26048 : ℝ)^2 / (mW 13024 : ℝ)) * (1 + 1/10^6)^2 *
    √(((198553/100000000000))/2) * ((1-firstRatio 26048) * √(1-firstRatio 26048) *
      sixthConstant (e1CovarianceRatio 26048 (mW 13024) (1/10^6) rowEps))) /
    (712/10000 - 26048*(1+1/10^6)*((198553/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 26048 (mW 13024) /
    ((1/10^5) * ((mW 13024 : ℝ)*26048*((mW 13024 : ℝ)+26048+1)))^2 +
  8*(mW 13024 : ℝ)*26048*(26048+2)*(26048+3) /
    ((1/1000)*((mW 13024 : ℝ)*26048*(26048+2)))^2 +
  covarianceVarianceBound 26048 (mW 13024) /
    ((1/1000)*covarianceMeanBound 26048 (mW 13024))^2 +
  normVarianceBound 26048 (mW 13024) / (3*inputVarianceMean 26048 (mW 13024))^2

end BstLean.Part268.WorldRow13024
