import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar24
namespace BstLean.Part268.WorldRow12950
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12950 = 247140652782199 := by
  have hu : mW 12950 ≤ 247140652782199 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12950 ≤ 247140652782198 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12950)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25900 ^ 2)
    ((500000000000000000/81367249727975644876373))
    ((25000000000000000000/4068205406766102754143777)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25900) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25900 : ℝ)^2 / (mW 12950 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1996991/1000000000000))/2) * ((1-firstRatio 25900) * √(1-firstRatio 25900) *
      sixthConstant (e1CovarianceRatio 25900 (mW 12950) (1/10^6) rowEps))) /
    (712/10000 - 25900*(1+1/10^6)*((1996991/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25900 (mW 12950) /
    ((1/10^5) * ((mW 12950 : ℝ)*25900*((mW 12950 : ℝ)+25900+1)))^2 +
  8*(mW 12950 : ℝ)*25900*(25900+2)*(25900+3) /
    ((1/1000)*((mW 12950 : ℝ)*25900*(25900+2)))^2 +
  covarianceVarianceBound 25900 (mW 12950) /
    ((1/1000)*covarianceMeanBound 25900 (mW 12950))^2 +
  normVarianceBound 25900 (mW 12950) / (3*inputVarianceMean 25900 (mW 12950))^2

end BstLean.Part268.WorldRow12950
namespace BstLean.Part268.WorldRow12951
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12951 = 247207454000842 := by
  have hu : mW 12951 ≤ 247207454000842 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12951 ≤ 247207454000841 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12951)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25902 ^ 2)
    ((25000000000000000000/4068676645664141223142497))
    ((25000000000000000000/4068519566031461733467623)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25902) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25902 : ℝ)^2 / (mW 12951 : ℝ)) * (1 + 1/10^6)^2 *
    √(((399367/200000000000))/2) * ((1-firstRatio 25902) * √(1-firstRatio 25902) *
      sixthConstant (e1CovarianceRatio 25902 (mW 12951) (1/10^6) rowEps))) /
    (712/10000 - 25902*(1+1/10^6)*((399367/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25902 (mW 12951) /
    ((1/10^5) * ((mW 12951 : ℝ)*25902*((mW 12951 : ℝ)+25902+1)))^2 +
  8*(mW 12951 : ℝ)*25902*(25902+2)*(25902+3) /
    ((1/1000)*((mW 12951 : ℝ)*25902*(25902+2)))^2 +
  covarianceVarianceBound 25902 (mW 12951) /
    ((1/1000)*covarianceMeanBound 25902 (mW 12951))^2 +
  normVarianceBound 25902 (mW 12951) / (3*inputVarianceMean 25902 (mW 12951))^2

end BstLean.Part268.WorldRow12951
namespace BstLean.Part268.WorldRow12952
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12952 = 247274268115722 := by
  have hu : mW 12952 ≤ 247274268115722 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12952 ≤ 247274268115721 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12952)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25904 ^ 2)
    ((3125000000000000000/508623850616187525308293))
    ((25000000000000000000/4068833725296820712791469)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25904) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25904 : ℝ)^2 / (mW 12952 : ℝ)) * (1 + 1/10^6)^2 *
    √(((49917/25000000000))/2) * ((1-firstRatio 25904) * √(1-firstRatio 25904) *
      sixthConstant (e1CovarianceRatio 25904 (mW 12952) (1/10^6) rowEps))) /
    (712/10000 - 25904*(1+1/10^6)*((49917/25000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25904 (mW 12952) /
    ((1/10^5) * ((mW 12952 : ℝ)*25904*((mW 12952 : ℝ)+25904+1)))^2 +
  8*(mW 12952 : ℝ)*25904*(25904+2)*(25904+3) /
    ((1/1000)*((mW 12952 : ℝ)*25904*(25904+2)))^2 +
  covarianceVarianceBound 25904 (mW 12952) /
    ((1/1000)*covarianceMeanBound 25904 (mW 12952))^2 +
  normVarianceBound 25904 (mW 12952) / (3*inputVarianceMean 25904 (mW 12952))^2

end BstLean.Part268.WorldRow12952
namespace BstLean.Part268.WorldRow12953
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12953 = 247341095128332 := by
  have hu : mW 12953 ≤ 247341095128332 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12953 ≤ 247341095128331 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12953)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25906 ^ 2)
    ((25000000000000000000/4069304964194859181790191))
    ((5000000000000000000/813829576912435938423063)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25906) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25906 : ℝ)^2 / (mW 12953 : ℝ)) * (1 + 1/10^6)^2 *
    √(((499131/250000000000))/2) * ((1-firstRatio 25906) * √(1-firstRatio 25906) *
      sixthConstant (e1CovarianceRatio 25906 (mW 12953) (1/10^6) rowEps))) /
    (712/10000 - 25906*(1+1/10^6)*((499131/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25906 (mW 12953) /
    ((1/10^5) * ((mW 12953 : ℝ)*25906*((mW 12953 : ℝ)+25906+1)))^2 +
  8*(mW 12953 : ℝ)*25906*(25906+2)*(25906+3) /
    ((1/1000)*((mW 12953 : ℝ)*25906*(25906+2)))^2 +
  covarianceVarianceBound 25906 (mW 12953) /
    ((1/1000)*covarianceMeanBound 25906 (mW 12953))^2 +
  normVarianceBound 25906 (mW 12953) / (3*inputVarianceMean 25906 (mW 12953))^2

end BstLean.Part268.WorldRow12953
namespace BstLean.Part268.WorldRow12954
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12954 = 247407935040168 := by
  have hu : mW 12954 ≤ 247407935040168 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12954 ≤ 247407935040167 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12954)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25908 ^ 2)
    ((12500000000000000000/2034809561730109080557019))
    ((25000000000000000000/4069462043827538671439161)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25908) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25908 : ℝ)^2 / (mW 12954 : ℝ)) * (1 + 1/10^6)^2 *
    √(((124773/62500000000))/2) * ((1-firstRatio 25908) * √(1-firstRatio 25908) *
      sixthConstant (e1CovarianceRatio 25908 (mW 12954) (1/10^6) rowEps))) /
    (712/10000 - 25908*(1+1/10^6)*((124773/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25908 (mW 12954) /
    ((1/10^5) * ((mW 12954 : ℝ)*25908*((mW 12954 : ℝ)+25908+1)))^2 +
  8*(mW 12954 : ℝ)*25908*(25908+2)*(25908+3) /
    ((1/1000)*((mW 12954 : ℝ)*25908*(25908+2)))^2 +
  covarianceVarianceBound 25908 (mW 12954) /
    ((1/1000)*covarianceMeanBound 25908 (mW 12954))^2 +
  normVarianceBound 25908 (mW 12954) / (3*inputVarianceMean 25908 (mW 12954))^2

end BstLean.Part268.WorldRow12954
namespace BstLean.Part268.WorldRow12955
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12955 = 247474787852721 := by
  have hu : mW 12955 ≤ 247474787852721 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12955 ≤ 247474787852720 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12955)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25910 ^ 2)
    ((5000000000000000000/813986656545115428087577))
    ((25000000000000000000/4069776203092897650763007)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25910) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25910 : ℝ)^2 / (mW 12955 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1996213/1000000000000))/2) * ((1-firstRatio 25910) * √(1-firstRatio 25910) *
      sixthConstant (e1CovarianceRatio 25910 (mW 12955) (1/10^6) rowEps))) /
    (712/10000 - 25910*(1+1/10^6)*((1996213/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25910 (mW 12955) /
    ((1/10^5) * ((mW 12955 : ℝ)*25910*((mW 12955 : ℝ)+25910+1)))^2 +
  8*(mW 12955 : ℝ)*25910*(25910+2)*(25910+3) /
    ((1/1000)*((mW 12955 : ℝ)*25910*(25910+2)))^2 +
  covarianceVarianceBound 25910 (mW 12955) /
    ((1/1000)*covarianceMeanBound 25910 (mW 12955))^2 +
  normVarianceBound 25910 (mW 12955) / (3*inputVarianceMean 25910 (mW 12955))^2

end BstLean.Part268.WorldRow12955
namespace BstLean.Part268.WorldRow12956
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12956 = 247541653567487 := by
  have hu : mW 12956 ≤ 247541653567487 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12956 ≤ 247541653567486 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12956)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25912 ^ 2)
    ((6250000000000000000/1017561860497734029940433))
    ((25000000000000000000/4070090362358256630086853)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25912) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25912 : ℝ)^2 / (mW 12956 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1996057/1000000000000))/2) * ((1-firstRatio 25912) * √(1-firstRatio 25912) *
      sixthConstant (e1CovarianceRatio 25912 (mW 12956) (1/10^6) rowEps))) /
    (712/10000 - 25912*(1+1/10^6)*((1996057/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25912 (mW 12956) /
    ((1/10^5) * ((mW 12956 : ℝ)*25912*((mW 12956 : ℝ)+25912+1)))^2 +
  8*(mW 12956 : ℝ)*25912*(25912+2)*(25912+3) /
    ((1/1000)*((mW 12956 : ℝ)*25912*(25912+2)))^2 +
  covarianceVarianceBound 25912 (mW 12956) /
    ((1/1000)*covarianceMeanBound 25912 (mW 12956))^2 +
  normVarianceBound 25912 (mW 12956) / (3*inputVarianceMean 25912 (mW 12956))^2

end BstLean.Part268.WorldRow12956
namespace BstLean.Part268.WorldRow12957
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12957 = 247608532185959 := by
  have hu : mW 12957 ≤ 247608532185959 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12957 ≤ 247608532185958 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12957)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25914 ^ 2)
    ((25000000000000000000/4070561601256295099085579))
    ((25000000000000000000/4070404521623615609410699)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25914) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25914 : ℝ)^2 / (mW 12957 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1995901/1000000000000))/2) * ((1-firstRatio 25914) * √(1-firstRatio 25914) *
      sixthConstant (e1CovarianceRatio 25914 (mW 12957) (1/10^6) rowEps))) /
    (712/10000 - 25914*(1+1/10^6)*((1995901/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25914 (mW 12957) /
    ((1/10^5) * ((mW 12957 : ℝ)*25914*((mW 12957 : ℝ)+25914+1)))^2 +
  8*(mW 12957 : ℝ)*25914*(25914+2)*(25914+3) /
    ((1/1000)*((mW 12957 : ℝ)*25914*(25914+2)))^2 +
  covarianceVarianceBound 25914 (mW 12957) /
    ((1/1000)*covarianceMeanBound 25914 (mW 12957))^2 +
  normVarianceBound 25914 (mW 12957) / (3*inputVarianceMean 25914 (mW 12957))^2

end BstLean.Part268.WorldRow12957
namespace BstLean.Part268.WorldRow12958
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12958 = 247675423709630 := by
  have hu : mW 12958 ≤ 247675423709630 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12958 ≤ 247675423709629 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12958)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25916 ^ 2)
    ((12500000000000000000/2035437880260827039204713))
    ((5000000000000000000/814143736177794917746909)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25916) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25916 : ℝ)^2 / (mW 12958 : ℝ)) * (1 + 1/10^6)^2 *
    √(((997873/500000000000))/2) * ((1-firstRatio 25916) * √(1-firstRatio 25916) *
      sixthConstant (e1CovarianceRatio 25916 (mW 12958) (1/10^6) rowEps))) /
    (712/10000 - 25916*(1+1/10^6)*((997873/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25916 (mW 12958) /
    ((1/10^5) * ((mW 12958 : ℝ)*25916*((mW 12958 : ℝ)+25916+1)))^2 +
  8*(mW 12958 : ℝ)*25916*(25916+2)*(25916+3) /
    ((1/1000)*((mW 12958 : ℝ)*25916*(25916+2)))^2 +
  covarianceVarianceBound 25916 (mW 12958) /
    ((1/1000)*covarianceMeanBound 25916 (mW 12958))^2 +
  normVarianceBound 25916 (mW 12958) / (3*inputVarianceMean 25916 (mW 12958))^2

end BstLean.Part268.WorldRow12958
namespace BstLean.Part268.WorldRow12959
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12959 = 247742328139996 := by
  have hu : mW 12959 ≤ 247742328139996 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12959 ≤ 247742328139995 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12959)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25918 ^ 2)
    ((25000000000000000000/4071189919787013057733273))
    ((25000000000000000000/4071032840154333568058391)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25918) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25918 : ℝ)^2 / (mW 12959 : ℝ)) * (1 + 1/10^6)^2 *
    √(((199559/100000000000))/2) * ((1-firstRatio 25918) * √(1-firstRatio 25918) *
      sixthConstant (e1CovarianceRatio 25918 (mW 12959) (1/10^6) rowEps))) /
    (712/10000 - 25918*(1+1/10^6)*((199559/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25918 (mW 12959) /
    ((1/10^5) * ((mW 12959 : ℝ)*25918*((mW 12959 : ℝ)+25918+1)))^2 +
  8*(mW 12959 : ℝ)*25918*(25918+2)*(25918+3) /
    ((1/1000)*((mW 12959 : ℝ)*25918*(25918+2)))^2 +
  covarianceVarianceBound 25918 (mW 12959) /
    ((1/1000)*covarianceMeanBound 25918 (mW 12959))^2 +
  normVarianceBound 25918 (mW 12959) / (3*inputVarianceMean 25918 (mW 12959))^2

end BstLean.Part268.WorldRow12959
namespace BstLean.Part268.WorldRow12960
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12960 = 247809245478550 := by
  have hu : mW 12960 ≤ 247809245478550 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12960 ≤ 247809245478549 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12960)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25920 ^ 2)
    ((156250000000000000/25446900494077325231607))
    ((25000000000000000000/4071346999419692547382237)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25920) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25920 : ℝ)^2 / (mW 12960 : ℝ)) * (1 + 1/10^6)^2 *
    √(((399087/200000000000))/2) * ((1-firstRatio 25920) * √(1-firstRatio 25920) *
      sixthConstant (e1CovarianceRatio 25920 (mW 12960) (1/10^6) rowEps))) /
    (712/10000 - 25920*(1+1/10^6)*((399087/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25920 (mW 12960) /
    ((1/10^5) * ((mW 12960 : ℝ)*25920*((mW 12960 : ℝ)+25920+1)))^2 +
  8*(mW 12960 : ℝ)*25920*(25920+2)*(25920+3) /
    ((1/1000)*((mW 12960 : ℝ)*25920*(25920+2)))^2 +
  covarianceVarianceBound 25920 (mW 12960) /
    ((1/1000)*covarianceMeanBound 25920 (mW 12960))^2 +
  normVarianceBound 25920 (mW 12960) / (3*inputVarianceMean 25920 (mW 12960))^2

end BstLean.Part268.WorldRow12960
namespace BstLean.Part268.WorldRow12961
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12961 = 247876175726787 := by
  have hu : mW 12961 ≤ 247876175726787 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12961 ≤ 247876175726786 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12961)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25922 ^ 2)
    ((25000000000000000000/4071818238317731016380967))
    ((25000000000000000000/4071661158685051526706083)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25922) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25922 : ℝ)^2 / (mW 12961 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1995279/1000000000000))/2) * ((1-firstRatio 25922) * √(1-firstRatio 25922) *
      sixthConstant (e1CovarianceRatio 25922 (mW 12961) (1/10^6) rowEps))) /
    (712/10000 - 25922*(1+1/10^6)*((1995279/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25922 (mW 12961) /
    ((1/10^5) * ((mW 12961 : ℝ)*25922*((mW 12961 : ℝ)+25922+1)))^2 +
  8*(mW 12961 : ℝ)*25922*(25922+2)*(25922+3) /
    ((1/1000)*((mW 12961 : ℝ)*25922*(25922+2)))^2 +
  covarianceVarianceBound 25922 (mW 12961) /
    ((1/1000)*covarianceMeanBound 25922 (mW 12961))^2 +
  normVarianceBound 25922 (mW 12961) / (3*inputVarianceMean 25922 (mW 12961))^2

end BstLean.Part268.WorldRow12961
namespace BstLean.Part268.WorldRow12962
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12962 = 247943118886200 := by
  have hu : mW 12962 ≤ 247943118886200 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12962 ≤ 247943118886199 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12962)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25924 ^ 2)
    ((12500000000000000000/2036066198791544997852407))
    ((25000000000000000000/4071975317950410506029929)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25924) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25924 : ℝ)^2 / (mW 12962 : ℝ)) * (1 + 1/10^6)^2 *
    √(((498781/250000000000))/2) * ((1-firstRatio 25924) * √(1-firstRatio 25924) *
      sixthConstant (e1CovarianceRatio 25924 (mW 12962) (1/10^6) rowEps))) /
    (712/10000 - 25924*(1+1/10^6)*((498781/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25924 (mW 12962) /
    ((1/10^5) * ((mW 12962 : ℝ)*25924*((mW 12962 : ℝ)+25924+1)))^2 +
  8*(mW 12962 : ℝ)*25924*(25924+2)*(25924+3) /
    ((1/1000)*((mW 12962 : ℝ)*25924*(25924+2)))^2 +
  covarianceVarianceBound 25924 (mW 12962) /
    ((1/1000)*covarianceMeanBound 25924 (mW 12962))^2 +
  normVarianceBound 25924 (mW 12962) / (3*inputVarianceMean 25924 (mW 12962))^2

end BstLean.Part268.WorldRow12962
namespace BstLean.Part268.WorldRow12963
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12963 = 248010074958283 := by
  have hu : mW 12963 ≤ 248010074958283 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12963 ≤ 248010074958282 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12963)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25926 ^ 2)
    ((25000000000000000000/4072446556848448975028661))
    ((1000000000000000000/162891579088630779414151)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25926) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25926 : ℝ)^2 / (mW 12963 : ℝ)) * (1 + 1/10^6)^2 *
    √(((249371/125000000000))/2) * ((1-firstRatio 25926) * √(1-firstRatio 25926) *
      sixthConstant (e1CovarianceRatio 25926 (mW 12963) (1/10^6) rowEps))) /
    (712/10000 - 25926*(1+1/10^6)*((249371/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25926 (mW 12963) /
    ((1/10^5) * ((mW 12963 : ℝ)*25926*((mW 12963 : ℝ)+25926+1)))^2 +
  8*(mW 12963 : ℝ)*25926*(25926+2)*(25926+3) /
    ((1/1000)*((mW 12963 : ℝ)*25926*(25926+2)))^2 +
  covarianceVarianceBound 25926 (mW 12963) /
    ((1/1000)*covarianceMeanBound 25926 (mW 12963))^2 +
  normVarianceBound 25926 (mW 12963) / (3*inputVarianceMean 25926 (mW 12963))^2

end BstLean.Part268.WorldRow12963
namespace BstLean.Part268.WorldRow12964
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12964 = 248077043944532 := by
  have hu : mW 12964 ≤ 248077043944532 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12964 ≤ 248077043944531 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12964)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25928 ^ 2)
    ((6250000000000000000/1018190179028451988588127))
    ((25000000000000000000/4072603636481128464677621)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25928) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25928 : ℝ)^2 / (mW 12964 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1994813/1000000000000))/2) * ((1-firstRatio 25928) * √(1-firstRatio 25928) *
      sixthConstant (e1CovarianceRatio 25928 (mW 12964) (1/10^6) rowEps))) /
    (712/10000 - 25928*(1+1/10^6)*((1994813/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25928 (mW 12964) /
    ((1/10^5) * ((mW 12964 : ℝ)*25928*((mW 12964 : ℝ)+25928+1)))^2 +
  8*(mW 12964 : ℝ)*25928*(25928+2)*(25928+3) /
    ((1/1000)*((mW 12964 : ℝ)*25928*(25928+2)))^2 +
  covarianceVarianceBound 25928 (mW 12964) /
    ((1/1000)*covarianceMeanBound 25928 (mW 12964))^2 +
  normVarianceBound 25928 (mW 12964) / (3*inputVarianceMean 25928 (mW 12964))^2

end BstLean.Part268.WorldRow12964
namespace BstLean.Part268.WorldRow12965
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12965 = 248144025846441 := by
  have hu : mW 12965 ≤ 248144025846441 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12965 ≤ 248144025846440 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12965)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25930 ^ 2)
    ((5000000000000000000/814614975075833386735271))
    ((25000000000000000000/4072917795746487444001467)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25930) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25930 : ℝ)^2 / (mW 12965 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1994657/1000000000000))/2) * ((1-firstRatio 25930) * √(1-firstRatio 25930) *
      sixthConstant (e1CovarianceRatio 25930 (mW 12965) (1/10^6) rowEps))) /
    (712/10000 - 25930*(1+1/10^6)*((1994657/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25930 (mW 12965) /
    ((1/10^5) * ((mW 12965 : ℝ)*25930*((mW 12965 : ℝ)+25930+1)))^2 +
  8*(mW 12965 : ℝ)*25930*(25930+2)*(25930+3) /
    ((1/1000)*((mW 12965 : ℝ)*25930*(25930+2)))^2 +
  covarianceVarianceBound 25930 (mW 12965) /
    ((1/1000)*covarianceMeanBound 25930 (mW 12965))^2 +
  normVarianceBound 25930 (mW 12965) / (3*inputVarianceMean 25930 (mW 12965))^2

end BstLean.Part268.WorldRow12965
namespace BstLean.Part268.WorldRow12966
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12966 = 248211020665503 := by
  have hu : mW 12966 ≤ 248211020665503 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12966 ≤ 248211020665502 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12966)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25932 ^ 2)
    ((12500000000000000000/2036694517322262956500101))
    ((25000000000000000000/4073231955011846423325313)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25932) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25932 : ℝ)^2 / (mW 12966 : ℝ)) * (1 + 1/10^6)^2 *
    √(((997251/500000000000))/2) * ((1-firstRatio 25932) * √(1-firstRatio 25932) *
      sixthConstant (e1CovarianceRatio 25932 (mW 12966) (1/10^6) rowEps))) /
    (712/10000 - 25932*(1+1/10^6)*((997251/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25932 (mW 12966) /
    ((1/10^5) * ((mW 12966 : ℝ)*25932*((mW 12966 : ℝ)+25932+1)))^2 +
  8*(mW 12966 : ℝ)*25932*(25932+2)*(25932+3) /
    ((1/1000)*((mW 12966 : ℝ)*25932*(25932+2)))^2 +
  covarianceVarianceBound 25932 (mW 12966) /
    ((1/1000)*covarianceMeanBound 25932 (mW 12966))^2 +
  normVarianceBound 25932 (mW 12966) / (3*inputVarianceMean 25932 (mW 12966))^2

end BstLean.Part268.WorldRow12966
namespace BstLean.Part268.WorldRow12967
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12967 = 248278028403213 := by
  have hu : mW 12967 ≤ 248278028403213 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12967 ≤ 248278028403212 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12967)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25934 ^ 2)
    ((25000000000000000000/4073703193909884892324049))
    ((25000000000000000000/4073546114277205402649159)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25934) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25934 : ℝ)^2 / (mW 12967 : ℝ)) * (1 + 1/10^6)^2 *
    √(((997173/500000000000))/2) * ((1-firstRatio 25934) * √(1-firstRatio 25934) *
      sixthConstant (e1CovarianceRatio 25934 (mW 12967) (1/10^6) rowEps))) /
    (712/10000 - 25934*(1+1/10^6)*((997173/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25934 (mW 12967) /
    ((1/10^5) * ((mW 12967 : ℝ)*25934*((mW 12967 : ℝ)+25934+1)))^2 +
  8*(mW 12967 : ℝ)*25934*(25934+2)*(25934+3) /
    ((1/1000)*((mW 12967 : ℝ)*25934*(25934+2)))^2 +
  covarianceVarianceBound 25934 (mW 12967) /
    ((1/1000)*covarianceMeanBound 25934 (mW 12967))^2 +
  normVarianceBound 25934 (mW 12967) / (3*inputVarianceMean 25934 (mW 12967))^2

end BstLean.Part268.WorldRow12967
namespace BstLean.Part268.WorldRow12968
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12968 = 248345049061067 := by
  have hu : mW 12968 ≤ 248345049061067 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12968 ≤ 248345049061066 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12968)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25936 ^ 2)
    ((3125000000000000000/509252169146905483955987))
    ((5000000000000000000/814772054708512876394601)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25936) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25936 : ℝ)^2 / (mW 12968 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1994191/1000000000000))/2) * ((1-firstRatio 25936) * √(1-firstRatio 25936) *
      sixthConstant (e1CovarianceRatio 25936 (mW 12968) (1/10^6) rowEps))) /
    (712/10000 - 25936*(1+1/10^6)*((1994191/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25936 (mW 12968) /
    ((1/10^5) * ((mW 12968 : ℝ)*25936*((mW 12968 : ℝ)+25936+1)))^2 +
  8*(mW 12968 : ℝ)*25936*(25936+2)*(25936+3) /
    ((1/1000)*((mW 12968 : ℝ)*25936*(25936+2)))^2 +
  covarianceVarianceBound 25936 (mW 12968) /
    ((1/1000)*covarianceMeanBound 25936 (mW 12968))^2 +
  normVarianceBound 25936 (mW 12968) / (3*inputVarianceMean 25936 (mW 12968))^2

end BstLean.Part268.WorldRow12968
namespace BstLean.Part268.WorldRow12969
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12969 = 248412082640558 := by
  have hu : mW 12969 ≤ 248412082640558 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12969 ≤ 248412082640557 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12969)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25938 ^ 2)
    ((25000000000000000000/4074331512440602850971743))
    ((25000000000000000000/4074174432807923361296851)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25938) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25938 : ℝ)^2 / (mW 12969 : ℝ)) * (1 + 1/10^6)^2 *
    √(((498509/250000000000))/2) * ((1-firstRatio 25938) * √(1-firstRatio 25938) *
      sixthConstant (e1CovarianceRatio 25938 (mW 12969) (1/10^6) rowEps))) /
    (712/10000 - 25938*(1+1/10^6)*((498509/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25938 (mW 12969) /
    ((1/10^5) * ((mW 12969 : ℝ)*25938*((mW 12969 : ℝ)+25938+1)))^2 +
  8*(mW 12969 : ℝ)*25938*(25938+2)*(25938+3) /
    ((1/1000)*((mW 12969 : ℝ)*25938*(25938+2)))^2 +
  covarianceVarianceBound 25938 (mW 12969) /
    ((1/1000)*covarianceMeanBound 25938 (mW 12969))^2 +
  normVarianceBound 25938 (mW 12969) / (3*inputVarianceMean 25938 (mW 12969))^2

end BstLean.Part268.WorldRow12969
namespace BstLean.Part268.WorldRow12970
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12970 = 248479129143182 := by
  have hu : mW 12970 ≤ 248479129143182 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12970 ≤ 248479129143181 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12970)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25940 ^ 2)
    ((2500000000000000000/407464567170596183029559))
    ((25000000000000000000/4074488592073282340620697)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25940) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25940 : ℝ)^2 / (mW 12970 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1993881/1000000000000))/2) * ((1-firstRatio 25940) * √(1-firstRatio 25940) *
      sixthConstant (e1CovarianceRatio 25940 (mW 12970) (1/10^6) rowEps))) /
    (712/10000 - 25940*(1+1/10^6)*((1993881/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25940 (mW 12970) /
    ((1/10^5) * ((mW 12970 : ℝ)*25940*((mW 12970 : ℝ)+25940+1)))^2 +
  8*(mW 12970 : ℝ)*25940*(25940+2)*(25940+3) /
    ((1/1000)*((mW 12970 : ℝ)*25940*(25940+2)))^2 +
  covarianceVarianceBound 25940 (mW 12970) /
    ((1/1000)*covarianceMeanBound 25940 (mW 12970))^2 +
  normVarianceBound 25940 (mW 12970) / (3*inputVarianceMean 25940 (mW 12970))^2

end BstLean.Part268.WorldRow12970
namespace BstLean.Part268.WorldRow12971
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12971 = 248546188570432 := by
  have hu : mW 12971 ≤ 248546188570432 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12971 ≤ 248546188570431 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12971)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25942 ^ 2)
    ((25000000000000000000/4074959830971320809619437))
    ((25000000000000000000/4074802751338641319944543)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25942) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25942 : ℝ)^2 / (mW 12971 : ℝ)) * (1 + 1/10^6)^2 *
    √(((79749/40000000000))/2) * ((1-firstRatio 25942) * √(1-firstRatio 25942) *
      sixthConstant (e1CovarianceRatio 25942 (mW 12971) (1/10^6) rowEps))) /
    (712/10000 - 25942*(1+1/10^6)*((79749/40000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25942 (mW 12971) /
    ((1/10^5) * ((mW 12971 : ℝ)*25942*((mW 12971 : ℝ)+25942+1)))^2 +
  8*(mW 12971 : ℝ)*25942*(25942+2)*(25942+3) /
    ((1/1000)*((mW 12971 : ℝ)*25942*(25942+2)))^2 +
  covarianceVarianceBound 25942 (mW 12971) /
    ((1/1000)*covarianceMeanBound 25942 (mW 12971))^2 +
  normVarianceBound 25942 (mW 12971) / (3*inputVarianceMean 25942 (mW 12971))^2

end BstLean.Part268.WorldRow12971
namespace BstLean.Part268.WorldRow12972
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12972 = 248613260923804 := by
  have hu : mW 12972 ≤ 248613260923804 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12972 ≤ 248613260923803 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12972)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25944 ^ 2)
    ((6250000000000000000/1018818497559169947235821))
    ((25000000000000000000/4075116910604000299268389)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25944) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25944 : ℝ)^2 / (mW 12972 : ℝ)) * (1 + 1/10^6)^2 *
    √(((199357/100000000000))/2) * ((1-firstRatio 25944) * √(1-firstRatio 25944) *
      sixthConstant (e1CovarianceRatio 25944 (mW 12972) (1/10^6) rowEps))) /
    (712/10000 - 25944*(1+1/10^6)*((199357/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25944 (mW 12972) /
    ((1/10^5) * ((mW 12972 : ℝ)*25944*((mW 12972 : ℝ)+25944+1)))^2 +
  8*(mW 12972 : ℝ)*25944*(25944+2)*(25944+3) /
    ((1/1000)*((mW 12972 : ℝ)*25944*(25944+2)))^2 +
  covarianceVarianceBound 25944 (mW 12972) /
    ((1/1000)*covarianceMeanBound 25944 (mW 12972))^2 +
  normVarianceBound 25944 (mW 12972) / (3*inputVarianceMean 25944 (mW 12972))^2

end BstLean.Part268.WorldRow12972
namespace BstLean.Part268.WorldRow12973
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12973 = 248680346204793 := by
  have hu : mW 12973 ≤ 248680346204793 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12973 ≤ 248680346204792 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12973)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25946 ^ 2)
    ((25000000000000000000/4075588149502038768267131))
    ((5000000000000000000/815086213973871855718447)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25946) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25946 : ℝ)^2 / (mW 12973 : ℝ)) * (1 + 1/10^6)^2 *
    √(((398683/200000000000))/2) * ((1-firstRatio 25946) * √(1-firstRatio 25946) *
      sixthConstant (e1CovarianceRatio 25946 (mW 12973) (1/10^6) rowEps))) /
    (712/10000 - 25946*(1+1/10^6)*((398683/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25946 (mW 12973) /
    ((1/10^5) * ((mW 12973 : ℝ)*25946*((mW 12973 : ℝ)+25946+1)))^2 +
  8*(mW 12973 : ℝ)*25946*(25946+2)*(25946+3) /
    ((1/1000)*((mW 12973 : ℝ)*25946*(25946+2)))^2 +
  covarianceVarianceBound 25946 (mW 12973) /
    ((1/1000)*covarianceMeanBound 25946 (mW 12973))^2 +
  normVarianceBound 25946 (mW 12973) / (3*inputVarianceMean 25946 (mW 12973))^2

end BstLean.Part268.WorldRow12973
namespace BstLean.Part268.WorldRow12974
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12974 = 248747444414893 := by
  have hu : mW 12974 ≤ 248747444414893 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12974 ≤ 248747444414892 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12974)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25948 ^ 2)
    ((12500000000000000000/2037951154383698873795489))
    ((25000000000000000000/4075745229134718257916081)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25948) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25948 : ℝ)^2 / (mW 12974 : ℝ)) * (1 + 1/10^6)^2 *
    √(((99663/50000000000))/2) * ((1-firstRatio 25948) * √(1-firstRatio 25948) *
      sixthConstant (e1CovarianceRatio 25948 (mW 12974) (1/10^6) rowEps))) /
    (712/10000 - 25948*(1+1/10^6)*((99663/50000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25948 (mW 12974) /
    ((1/10^5) * ((mW 12974 : ℝ)*25948*((mW 12974 : ℝ)+25948+1)))^2 +
  8*(mW 12974 : ℝ)*25948*(25948+2)*(25948+3) /
    ((1/1000)*((mW 12974 : ℝ)*25948*(25948+2)))^2 +
  covarianceVarianceBound 25948 (mW 12974) /
    ((1/1000)*covarianceMeanBound 25948 (mW 12974))^2 +
  normVarianceBound 25948 (mW 12974) / (3*inputVarianceMean 25948 (mW 12974))^2

end BstLean.Part268.WorldRow12974
