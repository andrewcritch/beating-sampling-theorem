import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part281Scalar2
namespace BstLean.Part281.WorldRow11909
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11909 = 184316210742663 := by
  have hu : mW 11909 ≤ 184316210742663 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11909 ≤ 184316210742662 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11909)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23818 ^ 2)
    ((25000000000000000000/3741322691160084767693923))
    ((25000000000000000000/3741165611527405278020091)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23818) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23818 : ℝ)^2 / (mW 11909 : ℝ)) * (1 + 1/10^6)^2 *
    √(((86941/40000000000))/2) * ((1-firstRatio 23818) * √(1-firstRatio 23818) *
      sixthConstant (e1CovarianceRatio 23818 (mW 11909) (1/10^6) rowEps))) /
    (712/10000 - 23818*(1+1/10^6)*((86941/40000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23818 (mW 11909) /
    ((1/10^5) * ((mW 11909 : ℝ)*23818*((mW 11909 : ℝ)+23818+1)))^2 +
  8*(mW 11909 : ℝ)*23818*(23818+2)*(23818+3) /
    ((1/1000)*((mW 11909 : ℝ)*23818*(23818+2)))^2 +
  covarianceVarianceBound 23818 (mW 11909) /
    ((1/1000)*covarianceMeanBound 23818 (mW 11909))^2 +
  normVarianceBound 23818 (mW 11909) / (3*inputVarianceMean 23818 (mW 11909))^2

end BstLean.Part281.WorldRow11909
namespace BstLean.Part281.WorldRow11910
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11910 = 184370386110246 := by
  have hu : mW 11910 ≤ 184370386110246 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11910 ≤ 184370386110245 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11910)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23820 ^ 2)
    ((2500000000000000000/374163685042544374701777))
    ((25000000000000000000/3741479770792764257343937)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23820) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23820 : ℝ)^2 / (mW 11910 : ℝ)) * (1 + 1/10^6)^2 *
    √(((108667/50000000000))/2) * ((1-firstRatio 23820) * √(1-firstRatio 23820) *
      sixthConstant (e1CovarianceRatio 23820 (mW 11910) (1/10^6) rowEps))) /
    (712/10000 - 23820*(1+1/10^6)*((108667/50000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23820 (mW 11910) /
    ((1/10^5) * ((mW 11910 : ℝ)*23820*((mW 11910 : ℝ)+23820+1)))^2 +
  8*(mW 11910 : ℝ)*23820*(23820+2)*(23820+3) /
    ((1/1000)*((mW 11910 : ℝ)*23820*(23820+2)))^2 +
  covarianceVarianceBound 23820 (mW 11910) /
    ((1/1000)*covarianceMeanBound 23820 (mW 11910))^2 +
  normVarianceBound 23820 (mW 11910) / (3*inputVarianceMean 23820 (mW 11910))^2

end BstLean.Part281.WorldRow11910
namespace BstLean.Part281.WorldRow11911
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11911 = 184424572850846 := by
  have hu : mW 11911 ≤ 184424572850846 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11911 ≤ 184424572850845 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11911)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23822 ^ 2)
    ((25000000000000000000/3741951009690802726341617))
    ((25000000000000000000/3741793930058123236667783)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23822) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23822 : ℝ)^2 / (mW 11911 : ℝ)) * (1 + 1/10^6)^2 *
    √(((543289/250000000000))/2) * ((1-firstRatio 23822) * √(1-firstRatio 23822) *
      sixthConstant (e1CovarianceRatio 23822 (mW 11911) (1/10^6) rowEps))) /
    (712/10000 - 23822*(1+1/10^6)*((543289/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23822 (mW 11911) /
    ((1/10^5) * ((mW 11911 : ℝ)*23822*((mW 11911 : ℝ)+23822+1)))^2 +
  8*(mW 11911 : ℝ)*23822*(23822+2)*(23822+3) /
    ((1/1000)*((mW 11911 : ℝ)*23822*(23822+2)))^2 +
  covarianceVarianceBound 23822 (mW 11911) /
    ((1/1000)*covarianceMeanBound 23822 (mW 11911))^2 +
  normVarianceBound 23822 (mW 11911) / (3*inputVarianceMean 23822 (mW 11911))^2

end BstLean.Part281.WorldRow11911
namespace BstLean.Part281.WorldRow11912
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11912 = 184478770965896 := by
  have hu : mW 11912 ≤ 184478770965896 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11912 ≤ 184478770965895 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11912)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23824 ^ 2)
    ((3125000000000000000/467783146119520213208183))
    ((25000000000000000000/3742108089323482215991629)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23824) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23824 : ℝ)^2 / (mW 11912 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2172971/1000000000000))/2) * ((1-firstRatio 23824) * √(1-firstRatio 23824) *
      sixthConstant (e1CovarianceRatio 23824 (mW 11912) (1/10^6) rowEps))) /
    (712/10000 - 23824*(1+1/10^6)*((2172971/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23824 (mW 11912) /
    ((1/10^5) * ((mW 11912 : ℝ)*23824*((mW 11912 : ℝ)+23824+1)))^2 +
  8*(mW 11912 : ℝ)*23824*(23824+2)*(23824+3) /
    ((1/1000)*((mW 11912 : ℝ)*23824*(23824+2)))^2 +
  covarianceVarianceBound 23824 (mW 11912) /
    ((1/1000)*covarianceMeanBound 23824 (mW 11912))^2 +
  normVarianceBound 23824 (mW 11912) / (3*inputVarianceMean 23824 (mW 11912))^2

end BstLean.Part281.WorldRow11912
namespace BstLean.Part281.WorldRow11913
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11913 = 184532980456827 := by
  have hu : mW 11913 ≤ 184532980456827 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11913 ≤ 184532980456826 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11913)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23826 ^ 2)
    ((25000000000000000000/3742579328221520684989311))
    ((1000000000000000000/149696889943553647812619)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23826) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23826 : ℝ)^2 / (mW 11913 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2172787/1000000000000))/2) * ((1-firstRatio 23826) * √(1-firstRatio 23826) *
      sixthConstant (e1CovarianceRatio 23826 (mW 11913) (1/10^6) rowEps))) /
    (712/10000 - 23826*(1+1/10^6)*((2172787/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23826 (mW 11913) /
    ((1/10^5) * ((mW 11913 : ℝ)*23826*((mW 11913 : ℝ)+23826+1)))^2 +
  8*(mW 11913 : ℝ)*23826*(23826+2)*(23826+3) /
    ((1/1000)*((mW 11913 : ℝ)*23826*(23826+2)))^2 +
  covarianceVarianceBound 23826 (mW 11913) /
    ((1/1000)*covarianceMeanBound 23826 (mW 11913))^2 +
  normVarianceBound 23826 (mW 11913) / (3*inputVarianceMean 23826 (mW 11913))^2

end BstLean.Part281.WorldRow11913
namespace BstLean.Part281.WorldRow11914
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11914 = 184587201325073 := by
  have hu : mW 11914 ≤ 184587201325073 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11914 ≤ 184587201325072 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11914)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23828 ^ 2)
    ((12500000000000000000/1871446743743439832156579))
    ((25000000000000000000/3742736407854200174639321)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23828) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23828 : ℝ)^2 / (mW 11914 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1086301/500000000000))/2) * ((1-firstRatio 23828) * √(1-firstRatio 23828) *
      sixthConstant (e1CovarianceRatio 23828 (mW 11914) (1/10^6) rowEps))) /
    (712/10000 - 23828*(1+1/10^6)*((1086301/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23828 (mW 11914) /
    ((1/10^5) * ((mW 11914 : ℝ)*23828*((mW 11914 : ℝ)+23828+1)))^2 +
  8*(mW 11914 : ℝ)*23828*(23828+2)*(23828+3) /
    ((1/1000)*((mW 11914 : ℝ)*23828*(23828+2)))^2 +
  covarianceVarianceBound 23828 (mW 11914) /
    ((1/1000)*covarianceMeanBound 23828 (mW 11914))^2 +
  normVarianceBound 23828 (mW 11914) / (3*inputVarianceMean 23828 (mW 11914))^2

end BstLean.Part281.WorldRow11914
namespace BstLean.Part281.WorldRow11915
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11915 = 184641433572067 := by
  have hu : mW 11915 ≤ 184641433572067 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11915 ≤ 184641433572066 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11915)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23830 ^ 2)
    ((5000000000000000000/748641529350447728727401))
    ((25000000000000000000/3743050567119559153963167)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23830) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23830 : ℝ)^2 / (mW 11915 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1086209/500000000000))/2) * ((1-firstRatio 23830) * √(1-firstRatio 23830) *
      sixthConstant (e1CovarianceRatio 23830 (mW 11915) (1/10^6) rowEps))) /
    (712/10000 - 23830*(1+1/10^6)*((1086209/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23830 (mW 11915) /
    ((1/10^5) * ((mW 11915 : ℝ)*23830*((mW 11915 : ℝ)+23830+1)))^2 +
  8*(mW 11915 : ℝ)*23830*(23830+2)*(23830+3) /
    ((1/1000)*((mW 11915 : ℝ)*23830*(23830+2)))^2 +
  covarianceVarianceBound 23830 (mW 11915) /
    ((1/1000)*covarianceMeanBound 23830 (mW 11915))^2 +
  normVarianceBound 23830 (mW 11915) / (3*inputVarianceMean 23830 (mW 11915))^2

end BstLean.Part281.WorldRow11915
namespace BstLean.Part281.WorldRow11916
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11916 = 184695677199240 := by
  have hu : mW 11916 ≤ 184695677199240 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11916 ≤ 184695677199239 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11916)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23832 ^ 2)
    ((6250000000000000000/935880451504399405740213))
    ((25000000000000000000/3743364726384918133287013)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23832) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23832 : ℝ)^2 / (mW 11916 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2172233/1000000000000))/2) * ((1-firstRatio 23832) * √(1-firstRatio 23832) *
      sixthConstant (e1CovarianceRatio 23832 (mW 11916) (1/10^6) rowEps))) /
    (712/10000 - 23832*(1+1/10^6)*((2172233/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23832 (mW 11916) /
    ((1/10^5) * ((mW 11916 : ℝ)*23832*((mW 11916 : ℝ)+23832+1)))^2 +
  8*(mW 11916 : ℝ)*23832*(23832+2)*(23832+3) /
    ((1/1000)*((mW 11916 : ℝ)*23832*(23832+2)))^2 +
  covarianceVarianceBound 23832 (mW 11916) /
    ((1/1000)*covarianceMeanBound 23832 (mW 11916))^2 +
  normVarianceBound 23832 (mW 11916) / (3*inputVarianceMean 23832 (mW 11916))^2

end BstLean.Part281.WorldRow11916
namespace BstLean.Part281.WorldRow11917
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11917 = 184749932208026 := by
  have hu : mW 11917 ≤ 184749932208026 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11917 ≤ 184749932208025 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11917)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23834 ^ 2)
    ((25000000000000000000/3743835965282956602284699))
    ((25000000000000000000/3743678885650277112610859)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23834) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23834 : ℝ)^2 / (mW 11917 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2172049/1000000000000))/2) * ((1-firstRatio 23834) * √(1-firstRatio 23834) *
      sixthConstant (e1CovarianceRatio 23834 (mW 11917) (1/10^6) rowEps))) /
    (712/10000 - 23834*(1+1/10^6)*((2172049/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23834 (mW 11917) /
    ((1/10^5) * ((mW 11917 : ℝ)*23834*((mW 11917 : ℝ)+23834+1)))^2 +
  8*(mW 11917 : ℝ)*23834*(23834+2)*(23834+3) /
    ((1/1000)*((mW 11917 : ℝ)*23834*(23834+2)))^2 +
  covarianceVarianceBound 23834 (mW 11917) /
    ((1/1000)*covarianceMeanBound 23834 (mW 11917))^2 +
  normVarianceBound 23834 (mW 11917) / (3*inputVarianceMean 23834 (mW 11917))^2

end BstLean.Part281.WorldRow11917
namespace BstLean.Part281.WorldRow11918
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11918 = 184804198599857 := by
  have hu : mW 11918 ≤ 184804198599857 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11918 ≤ 184804198599856 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11918)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23836 ^ 2)
    ((12500000000000000000/1872075062274157790804273))
    ((5000000000000000000/748798608983127218386941)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23836) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23836 : ℝ)^2 / (mW 11918 : ℝ)) * (1 + 1/10^6)^2 *
    √(((434373/200000000000))/2) * ((1-firstRatio 23836) * √(1-firstRatio 23836) *
      sixthConstant (e1CovarianceRatio 23836 (mW 11918) (1/10^6) rowEps))) /
    (712/10000 - 23836*(1+1/10^6)*((434373/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23836 (mW 11918) /
    ((1/10^5) * ((mW 11918 : ℝ)*23836*((mW 11918 : ℝ)+23836+1)))^2 +
  8*(mW 11918 : ℝ)*23836*(23836+2)*(23836+3) /
    ((1/1000)*((mW 11918 : ℝ)*23836*(23836+2)))^2 +
  covarianceVarianceBound 23836 (mW 11918) /
    ((1/1000)*covarianceMeanBound 23836 (mW 11918))^2 +
  normVarianceBound 23836 (mW 11918) / (3*inputVarianceMean 23836 (mW 11918))^2

end BstLean.Part281.WorldRow11918
namespace BstLean.Part281.WorldRow11919
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11919 = 184858476376166 := by
  have hu : mW 11919 ≤ 184858476376166 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11919 ≤ 184858476376165 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11919)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23838 ^ 2)
    ((25000000000000000000/3744464283813674560932393))
    ((25000000000000000000/3744307204180995071258551)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23838) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23838 : ℝ)^2 / (mW 11919 : ℝ)) * (1 + 1/10^6)^2 *
    √(((13573/6250000000))/2) * ((1-firstRatio 23838) * √(1-firstRatio 23838) *
      sixthConstant (e1CovarianceRatio 23838 (mW 11919) (1/10^6) rowEps))) /
    (712/10000 - 23838*(1+1/10^6)*((13573/6250000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23838 (mW 11919) /
    ((1/10^5) * ((mW 11919 : ℝ)*23838*((mW 11919 : ℝ)+23838+1)))^2 +
  8*(mW 11919 : ℝ)*23838*(23838+2)*(23838+3) /
    ((1/1000)*((mW 11919 : ℝ)*23838*(23838+2)))^2 +
  covarianceVarianceBound 23838 (mW 11919) /
    ((1/1000)*covarianceMeanBound 23838 (mW 11919))^2 +
  normVarianceBound 23838 (mW 11919) / (3*inputVarianceMean 23838 (mW 11919))^2

end BstLean.Part281.WorldRow11919
namespace BstLean.Part281.WorldRow11920
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11920 = 184912765538386 := by
  have hu : mW 11920 ≤ 184912765538386 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11920 ≤ 184912765538385 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11920)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23840 ^ 2)
    ((312500000000000000/46809730538487919253203))
    ((25000000000000000000/3744621363446354050582397)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23840) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23840 : ℝ)^2 / (mW 11920 : ℝ)) * (1 + 1/10^6)^2 *
    √(((271437/125000000000))/2) * ((1-firstRatio 23840) * √(1-firstRatio 23840) *
      sixthConstant (e1CovarianceRatio 23840 (mW 11920) (1/10^6) rowEps))) /
    (712/10000 - 23840*(1+1/10^6)*((271437/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23840 (mW 11920) /
    ((1/10^5) * ((mW 11920 : ℝ)*23840*((mW 11920 : ℝ)+23840+1)))^2 +
  8*(mW 11920 : ℝ)*23840*(23840+2)*(23840+3) /
    ((1/1000)*((mW 11920 : ℝ)*23840*(23840+2)))^2 +
  covarianceVarianceBound 23840 (mW 11920) /
    ((1/1000)*covarianceMeanBound 23840 (mW 11920))^2 +
  normVarianceBound 23840 (mW 11920) / (3*inputVarianceMean 23840 (mW 11920))^2

end BstLean.Part281.WorldRow11920
namespace BstLean.Part281.WorldRow11921
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11921 = 184967066087949 := by
  have hu : mW 11921 ≤ 184967066087949 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11921 ≤ 184967066087948 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11921)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23842 ^ 2)
    ((25000000000000000000/3745092602344392519580087))
    ((25000000000000000000/3744935522711713029906243)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23842) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23842 : ℝ)^2 / (mW 11921 : ℝ)) * (1 + 1/10^6)^2 *
    √(((135707/62500000000))/2) * ((1-firstRatio 23842) * √(1-firstRatio 23842) *
      sixthConstant (e1CovarianceRatio 23842 (mW 11921) (1/10^6) rowEps))) /
    (712/10000 - 23842*(1+1/10^6)*((135707/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23842 (mW 11921) /
    ((1/10^5) * ((mW 11921 : ℝ)*23842*((mW 11921 : ℝ)+23842+1)))^2 +
  8*(mW 11921 : ℝ)*23842*(23842+2)*(23842+3) /
    ((1/1000)*((mW 11921 : ℝ)*23842*(23842+2)))^2 +
  covarianceVarianceBound 23842 (mW 11921) /
    ((1/1000)*covarianceMeanBound 23842 (mW 11921))^2 +
  normVarianceBound 23842 (mW 11921) / (3*inputVarianceMean 23842 (mW 11921))^2

end BstLean.Part281.WorldRow11921
namespace BstLean.Part281.WorldRow11922
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11922 = 185021378026290 := by
  have hu : mW 11922 ≤ 185021378026290 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11922 ≤ 185021378026289 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11922)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23844 ^ 2)
    ((12500000000000000000/1872703380804875749451967))
    ((25000000000000000000/3745249681977072009230089)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23844) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23844 : ℝ)^2 / (mW 11922 : ℝ)) * (1 + 1/10^6)^2 *
    √(((271391/125000000000))/2) * ((1-firstRatio 23844) * √(1-firstRatio 23844) *
      sixthConstant (e1CovarianceRatio 23844 (mW 11922) (1/10^6) rowEps))) /
    (712/10000 - 23844*(1+1/10^6)*((271391/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23844 (mW 11922) /
    ((1/10^5) * ((mW 11922 : ℝ)*23844*((mW 11922 : ℝ)+23844+1)))^2 +
  8*(mW 11922 : ℝ)*23844*(23844+2)*(23844+3) /
    ((1/1000)*((mW 11922 : ℝ)*23844*(23844+2)))^2 +
  covarianceVarianceBound 23844 (mW 11922) /
    ((1/1000)*covarianceMeanBound 23844 (mW 11922))^2 +
  normVarianceBound 23844 (mW 11922) / (3*inputVarianceMean 23844 (mW 11922))^2

end BstLean.Part281.WorldRow11922
namespace BstLean.Part281.WorldRow11923
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11923 = 185075701354841 := by
  have hu : mW 11923 ≤ 185075701354841 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11923 ≤ 185075701354840 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11923)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23846 ^ 2)
    ((25000000000000000000/3745720920875110478227781))
    ((5000000000000000000/749112768248486197710787)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23846) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23846 : ℝ)^2 / (mW 11923 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2170943/1000000000000))/2) * ((1-firstRatio 23846) * √(1-firstRatio 23846) *
      sixthConstant (e1CovarianceRatio 23846 (mW 11923) (1/10^6) rowEps))) /
    (712/10000 - 23846*(1+1/10^6)*((2170943/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23846 (mW 11923) /
    ((1/10^5) * ((mW 11923 : ℝ)*23846*((mW 11923 : ℝ)+23846+1)))^2 +
  8*(mW 11923 : ℝ)*23846*(23846+2)*(23846+3) /
    ((1/1000)*((mW 11923 : ℝ)*23846*(23846+2)))^2 +
  covarianceVarianceBound 23846 (mW 11923) /
    ((1/1000)*covarianceMeanBound 23846 (mW 11923))^2 +
  normVarianceBound 23846 (mW 11923) / (3*inputVarianceMean 23846 (mW 11923))^2

end BstLean.Part281.WorldRow11923
namespace BstLean.Part281.WorldRow11924
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11924 = 185130036075034 := by
  have hu : mW 11924 ≤ 185130036075034 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11924 ≤ 185130036075033 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11924)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23848 ^ 2)
    ((6250000000000000000/936508770035117364387907))
    ((25000000000000000000/3745878000507789967877781)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23848) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23848 : ℝ)^2 / (mW 11924 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2170759/1000000000000))/2) * ((1-firstRatio 23848) * √(1-firstRatio 23848) *
      sixthConstant (e1CovarianceRatio 23848 (mW 11924) (1/10^6) rowEps))) /
    (712/10000 - 23848*(1+1/10^6)*((2170759/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23848 (mW 11924) /
    ((1/10^5) * ((mW 11924 : ℝ)*23848*((mW 11924 : ℝ)+23848+1)))^2 +
  8*(mW 11924 : ℝ)*23848*(23848+2)*(23848+3) /
    ((1/1000)*((mW 11924 : ℝ)*23848*(23848+2)))^2 +
  covarianceVarianceBound 23848 (mW 11924) /
    ((1/1000)*covarianceMeanBound 23848 (mW 11924))^2 +
  normVarianceBound 23848 (mW 11924) / (3*inputVarianceMean 23848 (mW 11924))^2

end BstLean.Part281.WorldRow11924
namespace BstLean.Part281.WorldRow11925
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11925 = 185184382188304 := by
  have hu : mW 11925 ≤ 185184382188304 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11925 ≤ 185184382188303 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11925)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23850 ^ 2)
    ((1000000000000000000/149853969576233137475019))
    ((25000000000000000000/3746192159773148947201627)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23850) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23850 : ℝ)^2 / (mW 11925 : ℝ)) * (1 + 1/10^6)^2 *
    √(((86823/40000000000))/2) * ((1-firstRatio 23850) * √(1-firstRatio 23850) *
      sixthConstant (e1CovarianceRatio 23850 (mW 11925) (1/10^6) rowEps))) /
    (712/10000 - 23850*(1+1/10^6)*((86823/40000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23850 (mW 11925) /
    ((1/10^5) * ((mW 11925 : ℝ)*23850*((mW 11925 : ℝ)+23850+1)))^2 +
  8*(mW 11925 : ℝ)*23850*(23850+2)*(23850+3) /
    ((1/1000)*((mW 11925 : ℝ)*23850*(23850+2)))^2 +
  covarianceVarianceBound 23850 (mW 11925) /
    ((1/1000)*covarianceMeanBound 23850 (mW 11925))^2 +
  normVarianceBound 23850 (mW 11925) / (3*inputVarianceMean 23850 (mW 11925))^2

end BstLean.Part281.WorldRow11925
namespace BstLean.Part281.WorldRow11926
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11926 = 185238739696084 := by
  have hu : mW 11926 ≤ 185238739696084 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11926 ≤ 185238739696083 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11926)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23852 ^ 2)
    ((12500000000000000000/1873331699335593708099661))
    ((25000000000000000000/3746506319038507926525473)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23852) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23852 : ℝ)^2 / (mW 11926 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2170391/1000000000000))/2) * ((1-firstRatio 23852) * √(1-firstRatio 23852) *
      sixthConstant (e1CovarianceRatio 23852 (mW 11926) (1/10^6) rowEps))) /
    (712/10000 - 23852*(1+1/10^6)*((2170391/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23852 (mW 11926) /
    ((1/10^5) * ((mW 11926 : ℝ)*23852*((mW 11926 : ℝ)+23852+1)))^2 +
  8*(mW 11926 : ℝ)*23852*(23852+2)*(23852+3) /
    ((1/1000)*((mW 11926 : ℝ)*23852*(23852+2)))^2 +
  covarianceVarianceBound 23852 (mW 11926) /
    ((1/1000)*covarianceMeanBound 23852 (mW 11926))^2 +
  normVarianceBound 23852 (mW 11926) / (3*inputVarianceMean 23852 (mW 11926))^2

end BstLean.Part281.WorldRow11926
namespace BstLean.Part281.WorldRow11927
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11927 = 185293108599806 := by
  have hu : mW 11927 ≤ 185293108599806 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11927 ≤ 185293108599805 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11927)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23854 ^ 2)
    ((25000000000000000000/3746977557936546395523169))
    ((25000000000000000000/3746820478303866905849319)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23854) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23854 : ℝ)^2 / (mW 11927 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2170207/1000000000000))/2) * ((1-firstRatio 23854) * √(1-firstRatio 23854) *
      sixthConstant (e1CovarianceRatio 23854 (mW 11927) (1/10^6) rowEps))) /
    (712/10000 - 23854*(1+1/10^6)*((2170207/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23854 (mW 11927) /
    ((1/10^5) * ((mW 11927 : ℝ)*23854*((mW 11927 : ℝ)+23854+1)))^2 +
  8*(mW 11927 : ℝ)*23854*(23854+2)*(23854+3) /
    ((1/1000)*((mW 11927 : ℝ)*23854*(23854+2)))^2 +
  covarianceVarianceBound 23854 (mW 11927) /
    ((1/1000)*covarianceMeanBound 23854 (mW 11927))^2 +
  normVarianceBound 23854 (mW 11927) / (3*inputVarianceMean 23854 (mW 11927))^2

end BstLean.Part281.WorldRow11927
namespace BstLean.Part281.WorldRow11928
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11928 = 185347488900905 := by
  have hu : mW 11928 ≤ 185347488900905 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11928 ≤ 185347488900904 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11928)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23856 ^ 2)
    ((3125000000000000000/468411464650238171855877))
    ((5000000000000000000/749426927513845177034633)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23856) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23856 : ℝ)^2 / (mW 11928 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2170023/1000000000000))/2) * ((1-firstRatio 23856) * √(1-firstRatio 23856) *
      sixthConstant (e1CovarianceRatio 23856 (mW 11928) (1/10^6) rowEps))) /
    (712/10000 - 23856*(1+1/10^6)*((2170023/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23856 (mW 11928) /
    ((1/10^5) * ((mW 11928 : ℝ)*23856*((mW 11928 : ℝ)+23856+1)))^2 +
  8*(mW 11928 : ℝ)*23856*(23856+2)*(23856+3) /
    ((1/1000)*((mW 11928 : ℝ)*23856*(23856+2)))^2 +
  covarianceVarianceBound 23856 (mW 11928) /
    ((1/1000)*covarianceMeanBound 23856 (mW 11928))^2 +
  normVarianceBound 23856 (mW 11928) / (3*inputVarianceMean 23856 (mW 11928))^2

end BstLean.Part281.WorldRow11928
namespace BstLean.Part281.WorldRow11929
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11929 = 185401880600813 := by
  have hu : mW 11929 ≤ 185401880600813 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11929 ≤ 185401880600812 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11929)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23858 ^ 2)
    ((25000000000000000000/3747605876467264354170863))
    ((25000000000000000000/3747448796834584864497011)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23858) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23858 : ℝ)^2 / (mW 11929 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2169839/1000000000000))/2) * ((1-firstRatio 23858) * √(1-firstRatio 23858) *
      sixthConstant (e1CovarianceRatio 23858 (mW 11929) (1/10^6) rowEps))) /
    (712/10000 - 23858*(1+1/10^6)*((2169839/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23858 (mW 11929) /
    ((1/10^5) * ((mW 11929 : ℝ)*23858*((mW 11929 : ℝ)+23858+1)))^2 +
  8*(mW 11929 : ℝ)*23858*(23858+2)*(23858+3) /
    ((1/1000)*((mW 11929 : ℝ)*23858*(23858+2)))^2 +
  covarianceVarianceBound 23858 (mW 11929) /
    ((1/1000)*covarianceMeanBound 23858 (mW 11929))^2 +
  normVarianceBound 23858 (mW 11929) / (3*inputVarianceMean 23858 (mW 11929))^2

end BstLean.Part281.WorldRow11929
namespace BstLean.Part281.WorldRow11930
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11930 = 185456283700964 := by
  have hu : mW 11930 ≤ 185456283700964 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11930 ≤ 185456283700963 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11930)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23860 ^ 2)
    ((2500000000000000000/374792003573262333349471))
    ((25000000000000000000/3747762956099943843820857)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23860) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23860 : ℝ)^2 / (mW 11930 : ℝ)) * (1 + 1/10^6)^2 *
    √(((433931/200000000000))/2) * ((1-firstRatio 23860) * √(1-firstRatio 23860) *
      sixthConstant (e1CovarianceRatio 23860 (mW 11930) (1/10^6) rowEps))) /
    (712/10000 - 23860*(1+1/10^6)*((433931/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23860 (mW 11930) /
    ((1/10^5) * ((mW 11930 : ℝ)*23860*((mW 11930 : ℝ)+23860+1)))^2 +
  8*(mW 11930 : ℝ)*23860*(23860+2)*(23860+3) /
    ((1/1000)*((mW 11930 : ℝ)*23860*(23860+2)))^2 +
  covarianceVarianceBound 23860 (mW 11930) /
    ((1/1000)*covarianceMeanBound 23860 (mW 11930))^2 +
  normVarianceBound 23860 (mW 11930) / (3*inputVarianceMean 23860 (mW 11930))^2

end BstLean.Part281.WorldRow11930
namespace BstLean.Part281.WorldRow11931
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11931 = 185510698202792 := by
  have hu : mW 11931 ≤ 185510698202792 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11931 ≤ 185510698202791 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11931)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23862 ^ 2)
    ((25000000000000000000/3748234194997982312818557))
    ((25000000000000000000/3748077115365302823144703)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23862) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23862 : ℝ)^2 / (mW 11931 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2169471/1000000000000))/2) * ((1-firstRatio 23862) * √(1-firstRatio 23862) *
      sixthConstant (e1CovarianceRatio 23862 (mW 11931) (1/10^6) rowEps))) /
    (712/10000 - 23862*(1+1/10^6)*((2169471/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23862 (mW 11931) /
    ((1/10^5) * ((mW 11931 : ℝ)*23862*((mW 11931 : ℝ)+23862+1)))^2 +
  8*(mW 11931 : ℝ)*23862*(23862+2)*(23862+3) /
    ((1/1000)*((mW 11931 : ℝ)*23862*(23862+2)))^2 +
  covarianceVarianceBound 23862 (mW 11931) /
    ((1/1000)*covarianceMeanBound 23862 (mW 11931))^2 +
  normVarianceBound 23862 (mW 11931) / (3*inputVarianceMean 23862 (mW 11931))^2

end BstLean.Part281.WorldRow11931
namespace BstLean.Part281.WorldRow11932
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11932 = 185565124107730 := by
  have hu : mW 11932 ≤ 185565124107730 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11932 ≤ 185565124107729 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11932)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23864 ^ 2)
    ((6250000000000000000/937137088565835323035601))
    ((25000000000000000000/3748391274630661802468549)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23864) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23864 : ℝ)^2 / (mW 11932 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2169287/1000000000000))/2) * ((1-firstRatio 23864) * √(1-firstRatio 23864) *
      sixthConstant (e1CovarianceRatio 23864 (mW 11932) (1/10^6) rowEps))) /
    (712/10000 - 23864*(1+1/10^6)*((2169287/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23864 (mW 11932) /
    ((1/10^5) * ((mW 11932 : ℝ)*23864*((mW 11932 : ℝ)+23864+1)))^2 +
  8*(mW 11932 : ℝ)*23864*(23864+2)*(23864+3) /
    ((1/1000)*((mW 11932 : ℝ)*23864*(23864+2)))^2 +
  covarianceVarianceBound 23864 (mW 11932) /
    ((1/1000)*covarianceMeanBound 23864 (mW 11932))^2 +
  normVarianceBound 23864 (mW 11932) / (3*inputVarianceMean 23864 (mW 11932))^2

end BstLean.Part281.WorldRow11932
namespace BstLean.Part281.WorldRow11933
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11933 = 185619561417211 := by
  have hu : mW 11933 ≤ 185619561417211 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11933 ≤ 185619561417210 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11933)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23866 ^ 2)
    ((25000000000000000000/3748862513528700271466251))
    ((5000000000000000000/749741086779204156358479)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23866) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23866 : ℝ)^2 / (mW 11933 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2169103/1000000000000))/2) * ((1-firstRatio 23866) * √(1-firstRatio 23866) *
      sixthConstant (e1CovarianceRatio 23866 (mW 11933) (1/10^6) rowEps))) /
    (712/10000 - 23866*(1+1/10^6)*((2169103/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23866 (mW 11933) /
    ((1/10^5) * ((mW 11933 : ℝ)*23866*((mW 11933 : ℝ)+23866+1)))^2 +
  8*(mW 11933 : ℝ)*23866*(23866+2)*(23866+3) /
    ((1/1000)*((mW 11933 : ℝ)*23866*(23866+2)))^2 +
  covarianceVarianceBound 23866 (mW 11933) /
    ((1/1000)*covarianceMeanBound 23866 (mW 11933))^2 +
  normVarianceBound 23866 (mW 11933) / (3*inputVarianceMean 23866 (mW 11933))^2

end BstLean.Part281.WorldRow11933
