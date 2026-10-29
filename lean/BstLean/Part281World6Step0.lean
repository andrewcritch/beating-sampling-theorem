import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part281Scalar6
namespace BstLean.Part281.WorldRow12009
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12009 = 189790275790695 := by
  have hu : mW 12009 ≤ 189790275790695 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12009 ≤ 189790275790694 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12009)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24018 ^ 2)
    ((25000000000000000000/3772738617695982700078623))
    ((25000000000000000000/3772581538063303210404691)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24018) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24018 : ℝ)^2 / (mW 12009 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2155219/1000000000000))/2) * ((1-firstRatio 24018) * √(1-firstRatio 24018) *
      sixthConstant (e1CovarianceRatio 24018 (mW 12009) (1/10^6) rowEps))) /
    (712/10000 - 24018*(1+1/10^6)*((2155219/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24018 (mW 12009) /
    ((1/10^5) * ((mW 12009 : ℝ)*24018*((mW 12009 : ℝ)+24018+1)))^2 +
  8*(mW 12009 : ℝ)*24018*(24018+2)*(24018+3) /
    ((1/1000)*((mW 12009 : ℝ)*24018*(24018+2)))^2 +
  covarianceVarianceBound 24018 (mW 12009) /
    ((1/1000)*covarianceMeanBound 24018 (mW 12009))^2 +
  normVarianceBound 24018 (mW 12009) / (3*inputVarianceMean 24018 (mW 12009))^2

end BstLean.Part281.WorldRow12009
namespace BstLean.Part281.WorldRow12010
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12010 = 189845595560090 := by
  have hu : mW 12010 ≤ 189845595560090 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12010 ≤ 189845595560089 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12010)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24020 ^ 2)
    ((2500000000000000000/377305277696134167940247))
    ((25000000000000000000/3772895697328662189728537)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24020) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24020 : ℝ)^2 / (mW 12010 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2155037/1000000000000))/2) * ((1-firstRatio 24020) * √(1-firstRatio 24020) *
      sixthConstant (e1CovarianceRatio 24020 (mW 12010) (1/10^6) rowEps))) /
    (712/10000 - 24020*(1+1/10^6)*((2155037/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24020 (mW 12010) /
    ((1/10^5) * ((mW 12010 : ℝ)*24020*((mW 12010 : ℝ)+24020+1)))^2 +
  8*(mW 12010 : ℝ)*24020*(24020+2)*(24020+3) /
    ((1/1000)*((mW 12010 : ℝ)*24020*(24020+2)))^2 +
  covarianceVarianceBound 24020 (mW 12010) /
    ((1/1000)*covarianceMeanBound 24020 (mW 12010))^2 +
  normVarianceBound 24020 (mW 12010) / (3*inputVarianceMean 24020 (mW 12010))^2

end BstLean.Part281.WorldRow12010
namespace BstLean.Part281.WorldRow12011
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12011 = 189900926846039 := by
  have hu : mW 12011 ≤ 189900926846039 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12011 ≤ 189900926846038 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12011)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24022 ^ 2)
    ((25000000000000000000/3773366936226700658726317))
    ((25000000000000000000/3773209856594021169052383)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24022) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24022 : ℝ)^2 / (mW 12011 : ℝ)) * (1 + 1/10^6)^2 *
    √(((269357/125000000000))/2) * ((1-firstRatio 24022) * √(1-firstRatio 24022) *
      sixthConstant (e1CovarianceRatio 24022 (mW 12011) (1/10^6) rowEps))) /
    (712/10000 - 24022*(1+1/10^6)*((269357/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24022 (mW 12011) /
    ((1/10^5) * ((mW 12011 : ℝ)*24022*((mW 12011 : ℝ)+24022+1)))^2 +
  8*(mW 12011 : ℝ)*24022*(24022+2)*(24022+3) /
    ((1/1000)*((mW 12011 : ℝ)*24022*(24022+2)))^2 +
  covarianceVarianceBound 24022 (mW 12011) /
    ((1/1000)*covarianceMeanBound 24022 (mW 12011))^2 +
  normVarianceBound 24022 (mW 12011) / (3*inputVarianceMean 24022 (mW 12011))^2

end BstLean.Part281.WorldRow12011
namespace BstLean.Part281.WorldRow12012
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12012 = 189956269649981 := by
  have hu : mW 12012 ≤ 189956269649981 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12012 ≤ 189956269649980 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12012)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24024 ^ 2)
    ((6250000000000000000/943420273873014909512541))
    ((25000000000000000000/3773524015859380148376229)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24024) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24024 : ℝ)^2 / (mW 12012 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1077337/500000000000))/2) * ((1-firstRatio 24024) * √(1-firstRatio 24024) *
      sixthConstant (e1CovarianceRatio 24024 (mW 12012) (1/10^6) rowEps))) /
    (712/10000 - 24024*(1+1/10^6)*((1077337/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24024 (mW 12012) /
    ((1/10^5) * ((mW 12012 : ℝ)*24024*((mW 12012 : ℝ)+24024+1)))^2 +
  8*(mW 12012 : ℝ)*24024*(24024+2)*(24024+3) /
    ((1/1000)*((mW 12012 : ℝ)*24024*(24024+2)))^2 +
  covarianceVarianceBound 24024 (mW 12012) /
    ((1/1000)*covarianceMeanBound 24024 (mW 12012))^2 +
  normVarianceBound 24024 (mW 12012) / (3*inputVarianceMean 24024 (mW 12012))^2

end BstLean.Part281.WorldRow12012
namespace BstLean.Part281.WorldRow12013
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12013 = 190011623973354 := by
  have hu : mW 12013 ≤ 190011623973354 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12013 ≤ 190011623973353 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12013)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24026 ^ 2)
    ((25000000000000000000/3773995254757418617374011))
    ((1000000000000000000/150953527004989565108003)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24026) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24026 : ℝ)^2 / (mW 12013 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2154493/1000000000000))/2) * ((1-firstRatio 24026) * √(1-firstRatio 24026) *
      sixthConstant (e1CovarianceRatio 24026 (mW 12013) (1/10^6) rowEps))) /
    (712/10000 - 24026*(1+1/10^6)*((2154493/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24026 (mW 12013) /
    ((1/10^5) * ((mW 12013 : ℝ)*24026*((mW 12013 : ℝ)+24026+1)))^2 +
  8*(mW 12013 : ℝ)*24026*(24026+2)*(24026+3) /
    ((1/1000)*((mW 12013 : ℝ)*24026*(24026+2)))^2 +
  covarianceVarianceBound 24026 (mW 12013) /
    ((1/1000)*covarianceMeanBound 24026 (mW 12013))^2 +
  normVarianceBound 24026 (mW 12013) / (3*inputVarianceMean 24026 (mW 12013))^2

end BstLean.Part281.WorldRow12013
namespace BstLean.Part281.WorldRow12014
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12014 = 190066989817597 := by
  have hu : mW 12014 ≤ 190066989817597 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12014 ≤ 190066989817596 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12014)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24028 ^ 2)
    ((12500000000000000000/1887154707011388798348929))
    ((25000000000000000000/3774152334390098107023921)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24028) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24028 : ℝ)^2 / (mW 12014 : ℝ)) * (1 + 1/10^6)^2 *
    √(((269289/125000000000))/2) * ((1-firstRatio 24028) * √(1-firstRatio 24028) *
      sixthConstant (e1CovarianceRatio 24028 (mW 12014) (1/10^6) rowEps))) /
    (712/10000 - 24028*(1+1/10^6)*((269289/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24028 (mW 12014) /
    ((1/10^5) * ((mW 12014 : ℝ)*24028*((mW 12014 : ℝ)+24028+1)))^2 +
  8*(mW 12014 : ℝ)*24028*(24028+2)*(24028+3) /
    ((1/1000)*((mW 12014 : ℝ)*24028*(24028+2)))^2 +
  covarianceVarianceBound 24028 (mW 12014) /
    ((1/1000)*covarianceMeanBound 24028 (mW 12014))^2 +
  normVarianceBound 24028 (mW 12014) / (3*inputVarianceMean 24028 (mW 12014))^2

end BstLean.Part281.WorldRow12014
namespace BstLean.Part281.WorldRow12015
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12015 = 190122367184149 := by
  have hu : mW 12015 ≤ 190122367184149 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12015 ≤ 190122367184148 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12015)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24030 ^ 2)
    ((5000000000000000000/754924714657627315204341))
    ((25000000000000000000/3774466493655457086347767)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24030) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24030 : ℝ)^2 / (mW 12015 : ℝ)) * (1 + 1/10^6)^2 *
    √(((215413/100000000000))/2) * ((1-firstRatio 24030) * √(1-firstRatio 24030) *
      sixthConstant (e1CovarianceRatio 24030 (mW 12015) (1/10^6) rowEps))) /
    (712/10000 - 24030*(1+1/10^6)*((215413/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24030 (mW 12015) /
    ((1/10^5) * ((mW 12015 : ℝ)*24030*((mW 12015 : ℝ)+24030+1)))^2 +
  8*(mW 12015 : ℝ)*24030*(24030+2)*(24030+3) /
    ((1/1000)*((mW 12015 : ℝ)*24030*(24030+2)))^2 +
  covarianceVarianceBound 24030 (mW 12015) /
    ((1/1000)*covarianceMeanBound 24030 (mW 12015))^2 +
  normVarianceBound 24030 (mW 12015) / (3*inputVarianceMean 24030 (mW 12015))^2

end BstLean.Part281.WorldRow12015
namespace BstLean.Part281.WorldRow12016
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12016 = 190177756074447 := by
  have hu : mW 12016 ≤ 190177756074447 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12016 ≤ 190177756074446 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12016)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24032 ^ 2)
    ((1562500000000000000/235933608284593472209097))
    ((25000000000000000000/3774780652920816065671613)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24032) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24032 : ℝ)^2 / (mW 12016 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2153949/1000000000000))/2) * ((1-firstRatio 24032) * √(1-firstRatio 24032) *
      sixthConstant (e1CovarianceRatio 24032 (mW 12016) (1/10^6) rowEps))) /
    (712/10000 - 24032*(1+1/10^6)*((2153949/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24032 (mW 12016) /
    ((1/10^5) * ((mW 12016 : ℝ)*24032*((mW 12016 : ℝ)+24032+1)))^2 +
  8*(mW 12016 : ℝ)*24032*(24032+2)*(24032+3) /
    ((1/1000)*((mW 12016 : ℝ)*24032*(24032+2)))^2 +
  covarianceVarianceBound 24032 (mW 12016) /
    ((1/1000)*covarianceMeanBound 24032 (mW 12016))^2 +
  normVarianceBound 24032 (mW 12016) / (3*inputVarianceMean 24032 (mW 12016))^2

end BstLean.Part281.WorldRow12016
namespace BstLean.Part281.WorldRow12017
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12017 = 190233156489931 := by
  have hu : mW 12017 ≤ 190233156489931 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12017 ≤ 190233156489930 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12017)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24034 ^ 2)
    ((25000000000000000000/3775251891818854534669399))
    ((25000000000000000000/3775094812186175044995459)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24034) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24034 : ℝ)^2 / (mW 12017 : ℝ)) * (1 + 1/10^6)^2 *
    √(((269221/125000000000))/2) * ((1-firstRatio 24034) * √(1-firstRatio 24034) *
      sixthConstant (e1CovarianceRatio 24034 (mW 12017) (1/10^6) rowEps))) /
    (712/10000 - 24034*(1+1/10^6)*((269221/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24034 (mW 12017) /
    ((1/10^5) * ((mW 12017 : ℝ)*24034*((mW 12017 : ℝ)+24034+1)))^2 +
  8*(mW 12017 : ℝ)*24034*(24034+2)*(24034+3) /
    ((1/1000)*((mW 12017 : ℝ)*24034*(24034+2)))^2 +
  covarianceVarianceBound 24034 (mW 12017) /
    ((1/1000)*covarianceMeanBound 24034 (mW 12017))^2 +
  normVarianceBound 24034 (mW 12017) / (3*inputVarianceMean 24034 (mW 12017))^2

end BstLean.Part281.WorldRow12017
namespace BstLean.Part281.WorldRow12018
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12018 = 190288568432040 := by
  have hu : mW 12018 ≤ 190288568432040 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12018 ≤ 190288568432039 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12018)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24036 ^ 2)
    ((12500000000000000000/1887783025542106756996623))
    ((5000000000000000000/755081794290306804863861)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24036) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24036 : ℝ)^2 / (mW 12018 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2153587/1000000000000))/2) * ((1-firstRatio 24036) * √(1-firstRatio 24036) *
      sixthConstant (e1CovarianceRatio 24036 (mW 12018) (1/10^6) rowEps))) /
    (712/10000 - 24036*(1+1/10^6)*((2153587/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24036 (mW 12018) /
    ((1/10^5) * ((mW 12018 : ℝ)*24036*((mW 12018 : ℝ)+24036+1)))^2 +
  8*(mW 12018 : ℝ)*24036*(24036+2)*(24036+3) /
    ((1/1000)*((mW 12018 : ℝ)*24036*(24036+2)))^2 +
  covarianceVarianceBound 24036 (mW 12018) /
    ((1/1000)*covarianceMeanBound 24036 (mW 12018))^2 +
  normVarianceBound 24036 (mW 12018) / (3*inputVarianceMean 24036 (mW 12018))^2

end BstLean.Part281.WorldRow12018
namespace BstLean.Part281.WorldRow12019
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12019 = 190343991902212 := by
  have hu : mW 12019 ≤ 190343991902212 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12019 ≤ 190343991902211 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12019)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24038 ^ 2)
    ((25000000000000000000/3775880210349572493317093))
    ((25000000000000000000/3775723130716893003643151)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24038) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24038 : ℝ)^2 / (mW 12019 : ℝ)) * (1 + 1/10^6)^2 *
    √(((430681/200000000000))/2) * ((1-firstRatio 24038) * √(1-firstRatio 24038) *
      sixthConstant (e1CovarianceRatio 24038 (mW 12019) (1/10^6) rowEps))) /
    (712/10000 - 24038*(1+1/10^6)*((430681/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24038 (mW 12019) /
    ((1/10^5) * ((mW 12019 : ℝ)*24038*((mW 12019 : ℝ)+24038+1)))^2 +
  8*(mW 12019 : ℝ)*24038*(24038+2)*(24038+3) /
    ((1/1000)*((mW 12019 : ℝ)*24038*(24038+2)))^2 +
  covarianceVarianceBound 24038 (mW 12019) /
    ((1/1000)*covarianceMeanBound 24038 (mW 12019))^2 +
  normVarianceBound 24038 (mW 12019) / (3*inputVarianceMean 24038 (mW 12019))^2

end BstLean.Part281.WorldRow12019
namespace BstLean.Part281.WorldRow12020
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12020 = 190399426901886 := by
  have hu : mW 12020 ≤ 190399426901886 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12020 ≤ 190399426901885 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12020)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24040 ^ 2)
    ((1250000000000000000/188809718480746573632047))
    ((25000000000000000000/3776037289982251982966997)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24040) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24040 : ℝ)^2 / (mW 12020 : ℝ)) * (1 + 1/10^6)^2 *
    √(((269153/125000000000))/2) * ((1-firstRatio 24040) * √(1-firstRatio 24040) *
      sixthConstant (e1CovarianceRatio 24040 (mW 12020) (1/10^6) rowEps))) /
    (712/10000 - 24040*(1+1/10^6)*((269153/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24040 (mW 12020) /
    ((1/10^5) * ((mW 12020 : ℝ)*24040*((mW 12020 : ℝ)+24040+1)))^2 +
  8*(mW 12020 : ℝ)*24040*(24040+2)*(24040+3) /
    ((1/1000)*((mW 12020 : ℝ)*24040*(24040+2)))^2 +
  covarianceVarianceBound 24040 (mW 12020) /
    ((1/1000)*covarianceMeanBound 24040 (mW 12020))^2 +
  normVarianceBound 24040 (mW 12020) / (3*inputVarianceMean 24040 (mW 12020))^2

end BstLean.Part281.WorldRow12020
namespace BstLean.Part281.WorldRow12021
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12021 = 190454873432501 := by
  have hu : mW 12021 ≤ 190454873432501 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12021 ≤ 190454873432500 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12021)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24042 ^ 2)
    ((25000000000000000000/3776508528880290451964787))
    ((25000000000000000000/3776351449247610962290843)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24042) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24042 : ℝ)^2 / (mW 12021 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2153043/1000000000000))/2) * ((1-firstRatio 24042) * √(1-firstRatio 24042) *
      sixthConstant (e1CovarianceRatio 24042 (mW 12021) (1/10^6) rowEps))) /
    (712/10000 - 24042*(1+1/10^6)*((2153043/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24042 (mW 12021) /
    ((1/10^5) * ((mW 12021 : ℝ)*24042*((mW 12021 : ℝ)+24042+1)))^2 +
  8*(mW 12021 : ℝ)*24042*(24042+2)*(24042+3) /
    ((1/1000)*((mW 12021 : ℝ)*24042*(24042+2)))^2 +
  covarianceVarianceBound 24042 (mW 12021) /
    ((1/1000)*covarianceMeanBound 24042 (mW 12021))^2 +
  normVarianceBound 24042 (mW 12021) / (3*inputVarianceMean 24042 (mW 12021))^2

end BstLean.Part281.WorldRow12021
namespace BstLean.Part281.WorldRow12022
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12022 = 190510331495497 := by
  have hu : mW 12022 ≤ 190510331495497 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12022 ≤ 190510331495496 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12022)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24044 ^ 2)
    ((12500000000000000000/1888411344072824715644317))
    ((25000000000000000000/3776665608512969941614689)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24044) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24044 : ℝ)^2 / (mW 12022 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1076431/500000000000))/2) * ((1-firstRatio 24044) * √(1-firstRatio 24044) *
      sixthConstant (e1CovarianceRatio 24044 (mW 12022) (1/10^6) rowEps))) /
    (712/10000 - 24044*(1+1/10^6)*((1076431/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24044 (mW 12022) /
    ((1/10^5) * ((mW 12022 : ℝ)*24044*((mW 12022 : ℝ)+24044+1)))^2 +
  8*(mW 12022 : ℝ)*24044*(24044+2)*(24044+3) /
    ((1/1000)*((mW 12022 : ℝ)*24044*(24044+2)))^2 +
  covarianceVarianceBound 24044 (mW 12022) /
    ((1/1000)*covarianceMeanBound 24044 (mW 12022))^2 +
  normVarianceBound 24044 (mW 12022) / (3*inputVarianceMean 24044 (mW 12022))^2

end BstLean.Part281.WorldRow12022
namespace BstLean.Part281.WorldRow12023
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12023 = 190565801092311 := by
  have hu : mW 12023 ≤ 190565801092311 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12023 ≤ 190565801092310 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12023)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24046 ^ 2)
    ((25000000000000000000/3777136847411008410612481))
    ((5000000000000000000/755395953555665784187707)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24046) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24046 : ℝ)^2 / (mW 12023 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2152681/1000000000000))/2) * ((1-firstRatio 24046) * √(1-firstRatio 24046) *
      sixthConstant (e1CovarianceRatio 24046 (mW 12023) (1/10^6) rowEps))) /
    (712/10000 - 24046*(1+1/10^6)*((2152681/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24046 (mW 12023) /
    ((1/10^5) * ((mW 12023 : ℝ)*24046*((mW 12023 : ℝ)+24046+1)))^2 +
  8*(mW 12023 : ℝ)*24046*(24046+2)*(24046+3) /
    ((1/1000)*((mW 12023 : ℝ)*24046*(24046+2)))^2 +
  covarianceVarianceBound 24046 (mW 12023) /
    ((1/1000)*covarianceMeanBound 24046 (mW 12023))^2 +
  normVarianceBound 24046 (mW 12023) / (3*inputVarianceMean 24046 (mW 12023))^2

end BstLean.Part281.WorldRow12023
namespace BstLean.Part281.WorldRow12024
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12024 = 190621282224384 := by
  have hu : mW 12024 ≤ 190621282224384 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12024 ≤ 190621282224383 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12024)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24048 ^ 2)
    ((3125000000000000000/472181375834545923742041))
    ((25000000000000000000/3777293927043687900262381)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24048) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24048 : ℝ)^2 / (mW 12024 : ℝ)) * (1 + 1/10^6)^2 *
    √(((861/400000000))/2) * ((1-firstRatio 24048) * √(1-firstRatio 24048) *
      sixthConstant (e1CovarianceRatio 24048 (mW 12024) (1/10^6) rowEps))) /
    (712/10000 - 24048*(1+1/10^6)*((861/400000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24048 (mW 12024) /
    ((1/10^5) * ((mW 12024 : ℝ)*24048*((mW 12024 : ℝ)+24048+1)))^2 +
  8*(mW 12024 : ℝ)*24048*(24048+2)*(24048+3) /
    ((1/1000)*((mW 12024 : ℝ)*24048*(24048+2)))^2 +
  covarianceVarianceBound 24048 (mW 12024) /
    ((1/1000)*covarianceMeanBound 24048 (mW 12024))^2 +
  normVarianceBound 24048 (mW 12024) / (3*inputVarianceMean 24048 (mW 12024))^2

end BstLean.Part281.WorldRow12024
namespace BstLean.Part281.WorldRow12025
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12025 = 190676774893155 := by
  have hu : mW 12025 ≤ 190676774893155 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12025 ≤ 190676774893154 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12025)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24050 ^ 2)
    ((1000000000000000000/151110606637669054770407))
    ((25000000000000000000/3777608086309046879586227)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24050) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24050 : ℝ)^2 / (mW 12025 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2152319/1000000000000))/2) * ((1-firstRatio 24050) * √(1-firstRatio 24050) *
      sixthConstant (e1CovarianceRatio 24050 (mW 12025) (1/10^6) rowEps))) /
    (712/10000 - 24050*(1+1/10^6)*((2152319/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24050 (mW 12025) /
    ((1/10^5) * ((mW 12025 : ℝ)*24050*((mW 12025 : ℝ)+24050+1)))^2 +
  8*(mW 12025 : ℝ)*24050*(24050+2)*(24050+3) /
    ((1/1000)*((mW 12025 : ℝ)*24050*(24050+2)))^2 +
  covarianceVarianceBound 24050 (mW 12025) /
    ((1/1000)*covarianceMeanBound 24050 (mW 12025))^2 +
  normVarianceBound 24050 (mW 12025) / (3*inputVarianceMean 24050 (mW 12025))^2

end BstLean.Part281.WorldRow12025
namespace BstLean.Part281.WorldRow12026
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12026 = 190732279100062 := by
  have hu : mW 12026 ≤ 190732279100062 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12026 ≤ 190732279100061 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12026)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24052 ^ 2)
    ((12500000000000000000/1889039662603542674292011))
    ((25000000000000000000/3777922245574405858910073)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24052) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24052 : ℝ)^2 / (mW 12026 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1076069/500000000000))/2) * ((1-firstRatio 24052) * √(1-firstRatio 24052) *
      sixthConstant (e1CovarianceRatio 24052 (mW 12026) (1/10^6) rowEps))) /
    (712/10000 - 24052*(1+1/10^6)*((1076069/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24052 (mW 12026) /
    ((1/10^5) * ((mW 12026 : ℝ)*24052*((mW 12026 : ℝ)+24052+1)))^2 +
  8*(mW 12026 : ℝ)*24052*(24052+2)*(24052+3) /
    ((1/1000)*((mW 12026 : ℝ)*24052*(24052+2)))^2 +
  covarianceVarianceBound 24052 (mW 12026) /
    ((1/1000)*covarianceMeanBound 24052 (mW 12026))^2 +
  normVarianceBound 24052 (mW 12026) / (3*inputVarianceMean 24052 (mW 12026))^2

end BstLean.Part281.WorldRow12026
namespace BstLean.Part281.WorldRow12027
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12027 = 190787794846545 := by
  have hu : mW 12027 ≤ 190787794846545 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12027 ≤ 190787794846544 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12027)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24054 ^ 2)
    ((25000000000000000000/3778393484472444327907869))
    ((25000000000000000000/3778236404839764838233919)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24054) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24054 : ℝ)^2 / (mW 12027 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2151957/1000000000000))/2) * ((1-firstRatio 24054) * √(1-firstRatio 24054) *
      sixthConstant (e1CovarianceRatio 24054 (mW 12027) (1/10^6) rowEps))) /
    (712/10000 - 24054*(1+1/10^6)*((2151957/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24054 (mW 12027) /
    ((1/10^5) * ((mW 12027 : ℝ)*24054*((mW 12027 : ℝ)+24054+1)))^2 +
  8*(mW 12027 : ℝ)*24054*(24054+2)*(24054+3) /
    ((1/1000)*((mW 12027 : ℝ)*24054*(24054+2)))^2 +
  covarianceVarianceBound 24054 (mW 12027) /
    ((1/1000)*covarianceMeanBound 24054 (mW 12027))^2 +
  normVarianceBound 24054 (mW 12027) / (3*inputVarianceMean 24054 (mW 12027))^2

end BstLean.Part281.WorldRow12027
namespace BstLean.Part281.WorldRow12028
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12028 = 190843322134043 := by
  have hu : mW 12028 ≤ 190843322134043 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12028 ≤ 190843322134042 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12028)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24056 ^ 2)
    ((6250000000000000000/944676910934450826807929))
    ((5000000000000000000/755710112821024763511553)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24056) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24056 : ℝ)^2 / (mW 12028 : ℝ)) * (1 + 1/10^6)^2 *
    √(((67243/31250000000))/2) * ((1-firstRatio 24056) * √(1-firstRatio 24056) *
      sixthConstant (e1CovarianceRatio 24056 (mW 12028) (1/10^6) rowEps))) /
    (712/10000 - 24056*(1+1/10^6)*((67243/31250000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24056 (mW 12028) /
    ((1/10^5) * ((mW 12028 : ℝ)*24056*((mW 12028 : ℝ)+24056+1)))^2 +
  8*(mW 12028 : ℝ)*24056*(24056+2)*(24056+3) /
    ((1/1000)*((mW 12028 : ℝ)*24056*(24056+2)))^2 +
  covarianceVarianceBound 24056 (mW 12028) /
    ((1/1000)*covarianceMeanBound 24056 (mW 12028))^2 +
  normVarianceBound 24056 (mW 12028) / (3*inputVarianceMean 24056 (mW 12028))^2

end BstLean.Part281.WorldRow12028
namespace BstLean.Part281.WorldRow12029
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12029 = 190898860963996 := by
  have hu : mW 12029 ≤ 190898860963996 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12029 ≤ 190898860963995 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12029)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24058 ^ 2)
    ((25000000000000000000/3779021803003162286555563))
    ((25000000000000000000/3778864723370482796881611)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24058) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24058 : ℝ)^2 / (mW 12029 : ℝ)) * (1 + 1/10^6)^2 *
    √(((430319/200000000000))/2) * ((1-firstRatio 24058) * √(1-firstRatio 24058) *
      sixthConstant (e1CovarianceRatio 24058 (mW 12029) (1/10^6) rowEps))) /
    (712/10000 - 24058*(1+1/10^6)*((430319/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24058 (mW 12029) /
    ((1/10^5) * ((mW 12029 : ℝ)*24058*((mW 12029 : ℝ)+24058+1)))^2 +
  8*(mW 12029 : ℝ)*24058*(24058+2)*(24058+3) /
    ((1/1000)*((mW 12029 : ℝ)*24058*(24058+2)))^2 +
  covarianceVarianceBound 24058 (mW 12029) /
    ((1/1000)*covarianceMeanBound 24058 (mW 12029))^2 +
  normVarianceBound 24058 (mW 12029) / (3*inputVarianceMean 24058 (mW 12029))^2

end BstLean.Part281.WorldRow12029
namespace BstLean.Part281.WorldRow12030
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12030 = 190954411337844 := by
  have hu : mW 12030 ≤ 190954411337844 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12030 ≤ 190954411337843 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12030)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24060 ^ 2)
    ((2500000000000000000/377933596226852126587941))
    ((25000000000000000000/3779178882635841776205457)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24060) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24060 : ℝ)^2 / (mW 12030 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1075707/500000000000))/2) * ((1-firstRatio 24060) * √(1-firstRatio 24060) *
      sixthConstant (e1CovarianceRatio 24060 (mW 12030) (1/10^6) rowEps))) /
    (712/10000 - 24060*(1+1/10^6)*((1075707/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24060 (mW 12030) /
    ((1/10^5) * ((mW 12030 : ℝ)*24060*((mW 12030 : ℝ)+24060+1)))^2 +
  8*(mW 12030 : ℝ)*24060*(24060+2)*(24060+3) /
    ((1/1000)*((mW 12030 : ℝ)*24060*(24060+2)))^2 +
  covarianceVarianceBound 24060 (mW 12030) /
    ((1/1000)*covarianceMeanBound 24060 (mW 12030))^2 +
  normVarianceBound 24060 (mW 12030) / (3*inputVarianceMean 24060 (mW 12030))^2

end BstLean.Part281.WorldRow12030
namespace BstLean.Part281.WorldRow12031
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12031 = 191009973257025 := by
  have hu : mW 12031 ≤ 191009973257025 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12031 ≤ 191009973257024 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12031)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24062 ^ 2)
    ((25000000000000000000/3779650121533880245203257))
    ((25000000000000000000/3779493041901200755529303)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24062) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24062 : ℝ)^2 / (mW 12031 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2151233/1000000000000))/2) * ((1-firstRatio 24062) * √(1-firstRatio 24062) *
      sixthConstant (e1CovarianceRatio 24062 (mW 12031) (1/10^6) rowEps))) /
    (712/10000 - 24062*(1+1/10^6)*((2151233/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24062 (mW 12031) /
    ((1/10^5) * ((mW 12031 : ℝ)*24062*((mW 12031 : ℝ)+24062+1)))^2 +
  8*(mW 12031 : ℝ)*24062*(24062+2)*(24062+3) /
    ((1/1000)*((mW 12031 : ℝ)*24062*(24062+2)))^2 +
  covarianceVarianceBound 24062 (mW 12031) /
    ((1/1000)*covarianceMeanBound 24062 (mW 12031))^2 +
  normVarianceBound 24062 (mW 12031) / (3*inputVarianceMean 24062 (mW 12031))^2

end BstLean.Part281.WorldRow12031
namespace BstLean.Part281.WorldRow12032
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12032 = 191065546722980 := by
  have hu : mW 12032 ≤ 191065546722980 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12032 ≤ 191065546722979 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12032)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24064 ^ 2)
    ((97656250000000000/14765485471872028220809))
    ((25000000000000000000/3779807201166559734853149)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24064) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24064 : ℝ)^2 / (mW 12032 : ℝ)) * (1 + 1/10^6)^2 *
    √(((537763/250000000000))/2) * ((1-firstRatio 24064) * √(1-firstRatio 24064) *
      sixthConstant (e1CovarianceRatio 24064 (mW 12032) (1/10^6) rowEps))) /
    (712/10000 - 24064*(1+1/10^6)*((537763/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24064 (mW 12032) /
    ((1/10^5) * ((mW 12032 : ℝ)*24064*((mW 12032 : ℝ)+24064+1)))^2 +
  8*(mW 12032 : ℝ)*24064*(24064+2)*(24064+3) /
    ((1/1000)*((mW 12032 : ℝ)*24064*(24064+2)))^2 +
  covarianceVarianceBound 24064 (mW 12032) /
    ((1/1000)*covarianceMeanBound 24064 (mW 12032))^2 +
  normVarianceBound 24064 (mW 12032) / (3*inputVarianceMean 24064 (mW 12032))^2

end BstLean.Part281.WorldRow12032
namespace BstLean.Part281.WorldRow12033
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12033 = 191121131737148 := by
  have hu : mW 12033 ≤ 191121131737148 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12033 ≤ 191121131737147 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12033)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24066 ^ 2)
    ((25000000000000000000/3780278440064598203850951))
    ((5000000000000000000/756024272086383742835399)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24066) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24066 : ℝ)^2 / (mW 12033 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2150871/1000000000000))/2) * ((1-firstRatio 24066) * √(1-firstRatio 24066) *
      sixthConstant (e1CovarianceRatio 24066 (mW 12033) (1/10^6) rowEps))) /
    (712/10000 - 24066*(1+1/10^6)*((2150871/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24066 (mW 12033) /
    ((1/10^5) * ((mW 12033 : ℝ)*24066*((mW 12033 : ℝ)+24066+1)))^2 +
  8*(mW 12033 : ℝ)*24066*(24066+2)*(24066+3) /
    ((1/1000)*((mW 12033 : ℝ)*24066*(24066+2)))^2 +
  covarianceVarianceBound 24066 (mW 12033) /
    ((1/1000)*covarianceMeanBound 24066 (mW 12033))^2 +
  normVarianceBound 24066 (mW 12033) / (3*inputVarianceMean 24066 (mW 12033))^2

end BstLean.Part281.WorldRow12033
