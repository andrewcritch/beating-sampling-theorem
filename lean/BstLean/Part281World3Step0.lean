import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part281Scalar3
namespace BstLean.Part281.WorldRow11934
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11934 = 185674010132671 := by
  have hu : mW 11934 ≤ 185674010132671 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11934 ≤ 185674010132670 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11934)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23868 ^ 2)
    ((12500000000000000000/1874588336397029625395049))
    ((25000000000000000000/3749019593161379761116241)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23868) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23868 : ℝ)^2 / (mW 11934 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2168919/1000000000000))/2) * ((1-firstRatio 23868) * √(1-firstRatio 23868) *
      sixthConstant (e1CovarianceRatio 23868 (mW 11934) (1/10^6) rowEps))) /
    (712/10000 - 23868*(1+1/10^6)*((2168919/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23868 (mW 11934) /
    ((1/10^5) * ((mW 11934 : ℝ)*23868*((mW 11934 : ℝ)+23868+1)))^2 +
  8*(mW 11934 : ℝ)*23868*(23868+2)*(23868+3) /
    ((1/1000)*((mW 11934 : ℝ)*23868*(23868+2)))^2 +
  covarianceVarianceBound 23868 (mW 11934) /
    ((1/1000)*covarianceMeanBound 23868 (mW 11934))^2 +
  normVarianceBound 23868 (mW 11934) / (3*inputVarianceMean 23868 (mW 11934))^2

end BstLean.Part281.WorldRow11934
namespace BstLean.Part281.WorldRow11935
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11935 = 185728470255542 := by
  have hu : mW 11935 ≤ 185728470255542 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11935 ≤ 185728470255541 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11935)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23870 ^ 2)
    ((5000000000000000000/749898166411883646022789))
    ((25000000000000000000/3749333752426738740440087)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23870) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23870 : ℝ)^2 / (mW 11935 : ℝ)) * (1 + 1/10^6)^2 *
    √(((67773/31250000000))/2) * ((1-firstRatio 23870) * √(1-firstRatio 23870) *
      sixthConstant (e1CovarianceRatio 23870 (mW 11935) (1/10^6) rowEps))) /
    (712/10000 - 23870*(1+1/10^6)*((67773/31250000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23870 (mW 11935) /
    ((1/10^5) * ((mW 11935 : ℝ)*23870*((mW 11935 : ℝ)+23870+1)))^2 +
  8*(mW 11935 : ℝ)*23870*(23870+2)*(23870+3) /
    ((1/1000)*((mW 11935 : ℝ)*23870*(23870+2)))^2 +
  covarianceVarianceBound 23870 (mW 11935) /
    ((1/1000)*covarianceMeanBound 23870 (mW 11935))^2 +
  normVarianceBound 23870 (mW 11935) / (3*inputVarianceMean 23870 (mW 11935))^2

end BstLean.Part281.WorldRow11935
namespace BstLean.Part281.WorldRow11936
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11936 = 185782941787258 := by
  have hu : mW 11936 ≤ 185782941787258 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11936 ≤ 185782941787257 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11936)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23872 ^ 2)
    ((781250000000000000/117181405978899287794931))
    ((25000000000000000000/3749647911692097719763933)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23872) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23872 : ℝ)^2 / (mW 11936 : ℝ)) * (1 + 1/10^6)^2 *
    √(((271069/125000000000))/2) * ((1-firstRatio 23872) * √(1-firstRatio 23872) *
      sixthConstant (e1CovarianceRatio 23872 (mW 11936) (1/10^6) rowEps))) /
    (712/10000 - 23872*(1+1/10^6)*((271069/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23872 (mW 11936) /
    ((1/10^5) * ((mW 11936 : ℝ)*23872*((mW 11936 : ℝ)+23872+1)))^2 +
  8*(mW 11936 : ℝ)*23872*(23872+2)*(23872+3) /
    ((1/1000)*((mW 11936 : ℝ)*23872*(23872+2)))^2 +
  covarianceVarianceBound 23872 (mW 11936) /
    ((1/1000)*covarianceMeanBound 23872 (mW 11936))^2 +
  normVarianceBound 23872 (mW 11936) / (3*inputVarianceMean 23872 (mW 11936))^2

end BstLean.Part281.WorldRow11936
namespace BstLean.Part281.WorldRow11937
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11937 = 185837424729253 := by
  have hu : mW 11937 ≤ 185837424729253 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11937 ≤ 185837424729252 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11937)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23874 ^ 2)
    ((25000000000000000000/3750119150590136188761639))
    ((25000000000000000000/3749962070957456699087779)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23874) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23874 : ℝ)^2 / (mW 11937 : ℝ)) * (1 + 1/10^6)^2 *
    √(((135523/62500000000))/2) * ((1-firstRatio 23874) * √(1-firstRatio 23874) *
      sixthConstant (e1CovarianceRatio 23874 (mW 11937) (1/10^6) rowEps))) /
    (712/10000 - 23874*(1+1/10^6)*((135523/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23874 (mW 11937) /
    ((1/10^5) * ((mW 11937 : ℝ)*23874*((mW 11937 : ℝ)+23874+1)))^2 +
  8*(mW 11937 : ℝ)*23874*(23874+2)*(23874+3) /
    ((1/1000)*((mW 11937 : ℝ)*23874*(23874+2)))^2 +
  covarianceVarianceBound 23874 (mW 11937) /
    ((1/1000)*covarianceMeanBound 23874 (mW 11937))^2 +
  normVarianceBound 23874 (mW 11937) / (3*inputVarianceMean 23874 (mW 11937))^2

end BstLean.Part281.WorldRow11937
namespace BstLean.Part281.WorldRow11938
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11938 = 185891919082961 := by
  have hu : mW 11938 ≤ 185891919082961 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11938 ≤ 185891919082960 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11938)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23876 ^ 2)
    ((12500000000000000000/1875216654927747584042743))
    ((200000000000000000/30002209841782525427293)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23876) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23876 : ℝ)^2 / (mW 11938 : ℝ)) * (1 + 1/10^6)^2 *
    √(((271023/125000000000))/2) * ((1-firstRatio 23876) * √(1-firstRatio 23876) *
      sixthConstant (e1CovarianceRatio 23876 (mW 11938) (1/10^6) rowEps))) /
    (712/10000 - 23876*(1+1/10^6)*((271023/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23876 (mW 11938) /
    ((1/10^5) * ((mW 11938 : ℝ)*23876*((mW 11938 : ℝ)+23876+1)))^2 +
  8*(mW 11938 : ℝ)*23876*(23876+2)*(23876+3) /
    ((1/1000)*((mW 11938 : ℝ)*23876*(23876+2)))^2 +
  covarianceVarianceBound 23876 (mW 11938) /
    ((1/1000)*covarianceMeanBound 23876 (mW 11938))^2 +
  normVarianceBound 23876 (mW 11938) / (3*inputVarianceMean 23876 (mW 11938))^2

end BstLean.Part281.WorldRow11938
namespace BstLean.Part281.WorldRow11939
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11939 = 185946424849816 := by
  have hu : mW 11939 ≤ 185946424849816 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11939 ≤ 185946424849815 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11939)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23878 ^ 2)
    ((25000000000000000000/3750747469120854147409333))
    ((25000000000000000000/3750590389488174657735471)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23878) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23878 : ℝ)^2 / (mW 11939 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2168001/1000000000000))/2) * ((1-firstRatio 23878) * √(1-firstRatio 23878) *
      sixthConstant (e1CovarianceRatio 23878 (mW 11939) (1/10^6) rowEps))) /
    (712/10000 - 23878*(1+1/10^6)*((2168001/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23878 (mW 11939) /
    ((1/10^5) * ((mW 11939 : ℝ)*23878*((mW 11939 : ℝ)+23878+1)))^2 +
  8*(mW 11939 : ℝ)*23878*(23878+2)*(23878+3) /
    ((1/1000)*((mW 11939 : ℝ)*23878*(23878+2)))^2 +
  covarianceVarianceBound 23878 (mW 11939) /
    ((1/1000)*covarianceMeanBound 23878 (mW 11939))^2 +
  normVarianceBound 23878 (mW 11939) / (3*inputVarianceMean 23878 (mW 11939))^2

end BstLean.Part281.WorldRow11939
namespace BstLean.Part281.WorldRow11940
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11940 = 186000942031253 := by
  have hu : mW 11940 ≤ 186000942031253 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11940 ≤ 186000942031252 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11940)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23880 ^ 2)
    ((1250000000000000000/187553081419310656336659))
    ((25000000000000000000/3750904548753533637059317)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23880) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23880 : ℝ)^2 / (mW 11940 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2167817/1000000000000))/2) * ((1-firstRatio 23880) * √(1-firstRatio 23880) *
      sixthConstant (e1CovarianceRatio 23880 (mW 11940) (1/10^6) rowEps))) /
    (712/10000 - 23880*(1+1/10^6)*((2167817/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23880 (mW 11940) /
    ((1/10^5) * ((mW 11940 : ℝ)*23880*((mW 11940 : ℝ)+23880+1)))^2 +
  8*(mW 11940 : ℝ)*23880*(23880+2)*(23880+3) /
    ((1/1000)*((mW 11940 : ℝ)*23880*(23880+2)))^2 +
  covarianceVarianceBound 23880 (mW 11940) /
    ((1/1000)*covarianceMeanBound 23880 (mW 11940))^2 +
  normVarianceBound 23880 (mW 11940) / (3*inputVarianceMean 23880 (mW 11940))^2

end BstLean.Part281.WorldRow11940
namespace BstLean.Part281.WorldRow11941
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11941 = 186055470628705 := by
  have hu : mW 11941 ≤ 186055470628705 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11941 ≤ 186055470628704 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11941)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23882 ^ 2)
    ((25000000000000000000/3751375787651572106057027))
    ((25000000000000000000/3751218708018892616383163)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23882) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23882 : ℝ)^2 / (mW 11941 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2167633/1000000000000))/2) * ((1-firstRatio 23882) * √(1-firstRatio 23882) *
      sixthConstant (e1CovarianceRatio 23882 (mW 11941) (1/10^6) rowEps))) /
    (712/10000 - 23882*(1+1/10^6)*((2167633/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23882 (mW 11941) /
    ((1/10^5) * ((mW 11941 : ℝ)*23882*((mW 11941 : ℝ)+23882+1)))^2 +
  8*(mW 11941 : ℝ)*23882*(23882+2)*(23882+3) /
    ((1/1000)*((mW 11941 : ℝ)*23882*(23882+2)))^2 +
  covarianceVarianceBound 23882 (mW 11941) /
    ((1/1000)*covarianceMeanBound 23882 (mW 11941))^2 +
  normVarianceBound 23882 (mW 11941) / (3*inputVarianceMean 23882 (mW 11941))^2

end BstLean.Part281.WorldRow11941
namespace BstLean.Part281.WorldRow11942
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11942 = 186110010643606 := by
  have hu : mW 11942 ≤ 186110010643606 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11942 ≤ 186110010643605 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11942)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23884 ^ 2)
    ((12500000000000000000/1875844973458465542690437))
    ((25000000000000000000/3751532867284251595707009)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23884) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23884 : ℝ)^2 / (mW 11942 : ℝ)) * (1 + 1/10^6)^2 *
    √(((43349/20000000000))/2) * ((1-firstRatio 23884) * √(1-firstRatio 23884) *
      sixthConstant (e1CovarianceRatio 23884 (mW 11942) (1/10^6) rowEps))) /
    (712/10000 - 23884*(1+1/10^6)*((43349/20000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23884 (mW 11942) /
    ((1/10^5) * ((mW 11942 : ℝ)*23884*((mW 11942 : ℝ)+23884+1)))^2 +
  8*(mW 11942 : ℝ)*23884*(23884+2)*(23884+3) /
    ((1/1000)*((mW 11942 : ℝ)*23884*(23884+2)))^2 +
  covarianceVarianceBound 23884 (mW 11942) /
    ((1/1000)*covarianceMeanBound 23884 (mW 11942))^2 +
  normVarianceBound 23884 (mW 11942) / (3*inputVarianceMean 23884 (mW 11942))^2

end BstLean.Part281.WorldRow11942
namespace BstLean.Part281.WorldRow11943
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11943 = 186164562077391 := by
  have hu : mW 11943 ≤ 186164562077391 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11943 ≤ 186164562077390 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11943)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23886 ^ 2)
    ((25000000000000000000/3752004106182290064704721))
    ((5000000000000000000/750369405309922115006171)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23886) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23886 : ℝ)^2 / (mW 11943 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1083633/500000000000))/2) * ((1-firstRatio 23886) * √(1-firstRatio 23886) *
      sixthConstant (e1CovarianceRatio 23886 (mW 11943) (1/10^6) rowEps))) /
    (712/10000 - 23886*(1+1/10^6)*((1083633/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23886 (mW 11943) /
    ((1/10^5) * ((mW 11943 : ℝ)*23886*((mW 11943 : ℝ)+23886+1)))^2 +
  8*(mW 11943 : ℝ)*23886*(23886+2)*(23886+3) /
    ((1/1000)*((mW 11943 : ℝ)*23886*(23886+2)))^2 +
  covarianceVarianceBound 23886 (mW 11943) /
    ((1/1000)*covarianceMeanBound 23886 (mW 11943))^2 +
  normVarianceBound 23886 (mW 11943) / (3*inputVarianceMean 23886 (mW 11943))^2

end BstLean.Part281.WorldRow11943
namespace BstLean.Part281.WorldRow11944
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11944 = 186219124931494 := by
  have hu : mW 11944 ≤ 186219124931494 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11944 ≤ 186219124931493 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11944)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23888 ^ 2)
    ((3125000000000000000/469039783180956130503571))
    ((25000000000000000000/3752161185814969554354701)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23888) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23888 : ℝ)^2 / (mW 11944 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2167083/1000000000000))/2) * ((1-firstRatio 23888) * √(1-firstRatio 23888) *
      sixthConstant (e1CovarianceRatio 23888 (mW 11944) (1/10^6) rowEps))) /
    (712/10000 - 23888*(1+1/10^6)*((2167083/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23888 (mW 11944) /
    ((1/10^5) * ((mW 11944 : ℝ)*23888*((mW 11944 : ℝ)+23888+1)))^2 +
  8*(mW 11944 : ℝ)*23888*(23888+2)*(23888+3) /
    ((1/1000)*((mW 11944 : ℝ)*23888*(23888+2)))^2 +
  covarianceVarianceBound 23888 (mW 11944) /
    ((1/1000)*covarianceMeanBound 23888 (mW 11944))^2 +
  normVarianceBound 23888 (mW 11944) / (3*inputVarianceMean 23888 (mW 11944))^2

end BstLean.Part281.WorldRow11944
namespace BstLean.Part281.WorldRow11945
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11945 = 186273699207350 := by
  have hu : mW 11945 ≤ 186273699207350 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11945 ≤ 186273699207349 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11945)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23890 ^ 2)
    ((5000000000000000000/750526484942601604670483))
    ((25000000000000000000/3752475345080328533678547)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23890) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23890 : ℝ)^2 / (mW 11945 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2166899/1000000000000))/2) * ((1-firstRatio 23890) * √(1-firstRatio 23890) *
      sixthConstant (e1CovarianceRatio 23890 (mW 11945) (1/10^6) rowEps))) /
    (712/10000 - 23890*(1+1/10^6)*((2166899/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23890 (mW 11945) /
    ((1/10^5) * ((mW 11945 : ℝ)*23890*((mW 11945 : ℝ)+23890+1)))^2 +
  8*(mW 11945 : ℝ)*23890*(23890+2)*(23890+3) /
    ((1/1000)*((mW 11945 : ℝ)*23890*(23890+2)))^2 +
  covarianceVarianceBound 23890 (mW 11945) /
    ((1/1000)*covarianceMeanBound 23890 (mW 11945))^2 +
  normVarianceBound 23890 (mW 11945) / (3*inputVarianceMean 23890 (mW 11945))^2

end BstLean.Part281.WorldRow11945
namespace BstLean.Part281.WorldRow11946
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11946 = 186328284906393 := by
  have hu : mW 11946 ≤ 186328284906393 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11946 ≤ 186328284906392 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11946)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23892 ^ 2)
    ((12500000000000000000/1876473291989183501338131))
    ((25000000000000000000/3752789504345687513002393)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23892) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23892 : ℝ)^2 / (mW 11946 : ℝ)) * (1 + 1/10^6)^2 *
    √(((541679/250000000000))/2) * ((1-firstRatio 23892) * √(1-firstRatio 23892) *
      sixthConstant (e1CovarianceRatio 23892 (mW 11946) (1/10^6) rowEps))) /
    (712/10000 - 23892*(1+1/10^6)*((541679/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23892 (mW 11946) /
    ((1/10^5) * ((mW 11946 : ℝ)*23892*((mW 11946 : ℝ)+23892+1)))^2 +
  8*(mW 11946 : ℝ)*23892*(23892+2)*(23892+3) /
    ((1/1000)*((mW 11946 : ℝ)*23892*(23892+2)))^2 +
  covarianceVarianceBound 23892 (mW 11946) /
    ((1/1000)*covarianceMeanBound 23892 (mW 11946))^2 +
  normVarianceBound 23892 (mW 11946) / (3*inputVarianceMean 23892 (mW 11946))^2

end BstLean.Part281.WorldRow11946
namespace BstLean.Part281.WorldRow11947
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11947 = 186382882030057 := by
  have hu : mW 11947 ≤ 186382882030057 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11947 ≤ 186382882030056 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11947)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23894 ^ 2)
    ((25000000000000000000/3753260743243725982000109))
    ((25000000000000000000/3753103663611046492326239)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23894) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23894 : ℝ)^2 / (mW 11947 : ℝ)) * (1 + 1/10^6)^2 *
    √(((541633/250000000000))/2) * ((1-firstRatio 23894) * √(1-firstRatio 23894) *
      sixthConstant (e1CovarianceRatio 23894 (mW 11947) (1/10^6) rowEps))) /
    (712/10000 - 23894*(1+1/10^6)*((541633/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23894 (mW 11947) /
    ((1/10^5) * ((mW 11947 : ℝ)*23894*((mW 11947 : ℝ)+23894+1)))^2 +
  8*(mW 11947 : ℝ)*23894*(23894+2)*(23894+3) /
    ((1/1000)*((mW 11947 : ℝ)*23894*(23894+2)))^2 +
  covarianceVarianceBound 23894 (mW 11947) /
    ((1/1000)*covarianceMeanBound 23894 (mW 11947))^2 +
  normVarianceBound 23894 (mW 11947) / (3*inputVarianceMean 23894 (mW 11947))^2

end BstLean.Part281.WorldRow11947
namespace BstLean.Part281.WorldRow11948
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11948 = 186437490579777 := by
  have hu : mW 11948 ≤ 186437490579777 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11948 ≤ 186437490579776 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11948)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23896 ^ 2)
    ((6250000000000000000/938393725627271240330989))
    ((5000000000000000000/750683564575281094330017)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23896) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23896 : ℝ)^2 / (mW 11948 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2166349/1000000000000))/2) * ((1-firstRatio 23896) * √(1-firstRatio 23896) *
      sixthConstant (e1CovarianceRatio 23896 (mW 11948) (1/10^6) rowEps))) /
    (712/10000 - 23896*(1+1/10^6)*((2166349/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23896 (mW 11948) /
    ((1/10^5) * ((mW 11948 : ℝ)*23896*((mW 11948 : ℝ)+23896+1)))^2 +
  8*(mW 11948 : ℝ)*23896*(23896+2)*(23896+3) /
    ((1/1000)*((mW 11948 : ℝ)*23896*(23896+2)))^2 +
  covarianceVarianceBound 23896 (mW 11948) /
    ((1/1000)*covarianceMeanBound 23896 (mW 11948))^2 +
  normVarianceBound 23896 (mW 11948) / (3*inputVarianceMean 23896 (mW 11948))^2

end BstLean.Part281.WorldRow11948
namespace BstLean.Part281.WorldRow11949
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11949 = 186492110556988 := by
  have hu : mW 11949 ≤ 186492110556988 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11949 ≤ 186492110556987 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11949)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23898 ^ 2)
    ((25000000000000000000/3753889061774443940647803))
    ((25000000000000000000/3753731982141764450973931)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23898) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23898 : ℝ)^2 / (mW 11949 : ℝ)) * (1 + 1/10^6)^2 *
    √(((433233/200000000000))/2) * ((1-firstRatio 23898) * √(1-firstRatio 23898) *
      sixthConstant (e1CovarianceRatio 23898 (mW 11949) (1/10^6) rowEps))) /
    (712/10000 - 23898*(1+1/10^6)*((433233/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23898 (mW 11949) /
    ((1/10^5) * ((mW 11949 : ℝ)*23898*((mW 11949 : ℝ)+23898+1)))^2 +
  8*(mW 11949 : ℝ)*23898*(23898+2)*(23898+3) /
    ((1/1000)*((mW 11949 : ℝ)*23898*(23898+2)))^2 +
  covarianceVarianceBound 23898 (mW 11949) /
    ((1/1000)*covarianceMeanBound 23898 (mW 11949))^2 +
  normVarianceBound 23898 (mW 11949) / (3*inputVarianceMean 23898 (mW 11949))^2

end BstLean.Part281.WorldRow11949
namespace BstLean.Part281.WorldRow11950
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11950 = 186546741963124 := by
  have hu : mW 11950 ≤ 186546741963124 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11950 ≤ 186546741963123 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11950)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23900 ^ 2)
    ((500000000000000000/75084064420796058399433))
    ((25000000000000000000/3754046141407123430297777)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23900) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23900 : ℝ)^2 / (mW 11950 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1082991/500000000000))/2) * ((1-firstRatio 23900) * √(1-firstRatio 23900) *
      sixthConstant (e1CovarianceRatio 23900 (mW 11950) (1/10^6) rowEps))) /
    (712/10000 - 23900*(1+1/10^6)*((1082991/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23900 (mW 11950) /
    ((1/10^5) * ((mW 11950 : ℝ)*23900*((mW 11950 : ℝ)+23900+1)))^2 +
  8*(mW 11950 : ℝ)*23900*(23900+2)*(23900+3) /
    ((1/1000)*((mW 11950 : ℝ)*23900*(23900+2)))^2 +
  covarianceVarianceBound 23900 (mW 11950) /
    ((1/1000)*covarianceMeanBound 23900 (mW 11950))^2 +
  normVarianceBound 23900 (mW 11950) / (3*inputVarianceMean 23900 (mW 11950))^2

end BstLean.Part281.WorldRow11950
namespace BstLean.Part281.WorldRow11951
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11951 = 186601384799621 := by
  have hu : mW 11951 ≤ 186601384799621 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11951 ≤ 186601384799620 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11951)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23902 ^ 2)
    ((25000000000000000000/3754517380305161899295497))
    ((25000000000000000000/3754360300672482409621623)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23902) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23902 : ℝ)^2 / (mW 11951 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2165799/1000000000000))/2) * ((1-firstRatio 23902) * √(1-firstRatio 23902) *
      sixthConstant (e1CovarianceRatio 23902 (mW 11951) (1/10^6) rowEps))) /
    (712/10000 - 23902*(1+1/10^6)*((2165799/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23902 (mW 11951) /
    ((1/10^5) * ((mW 11951 : ℝ)*23902*((mW 11951 : ℝ)+23902+1)))^2 +
  8*(mW 11951 : ℝ)*23902*(23902+2)*(23902+3) /
    ((1/1000)*((mW 11951 : ℝ)*23902*(23902+2)))^2 +
  covarianceVarianceBound 23902 (mW 11951) /
    ((1/1000)*covarianceMeanBound 23902 (mW 11951))^2 +
  normVarianceBound 23902 (mW 11951) / (3*inputVarianceMean 23902 (mW 11951))^2

end BstLean.Part281.WorldRow11951
namespace BstLean.Part281.WorldRow11952
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11952 = 186656039067912 := by
  have hu : mW 11952 ≤ 186656039067912 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11952 ≤ 186656039067911 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11952)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23904 ^ 2)
    ((1562500000000000000/234676971223157554913709))
    ((25000000000000000000/3754674459937841388945469)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23904) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23904 : ℝ)^2 / (mW 11952 : ℝ)) * (1 + 1/10^6)^2 *
    √(((433123/200000000000))/2) * ((1-firstRatio 23904) * √(1-firstRatio 23904) *
      sixthConstant (e1CovarianceRatio 23904 (mW 11952) (1/10^6) rowEps))) /
    (712/10000 - 23904*(1+1/10^6)*((433123/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23904 (mW 11952) /
    ((1/10^5) * ((mW 11952 : ℝ)*23904*((mW 11952 : ℝ)+23904+1)))^2 +
  8*(mW 11952 : ℝ)*23904*(23904+2)*(23904+3) /
    ((1/1000)*((mW 11952 : ℝ)*23904*(23904+2)))^2 +
  covarianceVarianceBound 23904 (mW 11952) /
    ((1/1000)*covarianceMeanBound 23904 (mW 11952))^2 +
  normVarianceBound 23904 (mW 11952) / (3*inputVarianceMean 23904 (mW 11952))^2

end BstLean.Part281.WorldRow11952
namespace BstLean.Part281.WorldRow11953
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11953 = 186710704769432 := by
  have hu : mW 11953 ≤ 186710704769432 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11953 ≤ 186710704769431 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11953)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23906 ^ 2)
    ((25000000000000000000/3755145698835879857943191))
    ((5000000000000000000/750997723840640073653863)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23906) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23906 : ℝ)^2 / (mW 11953 : ℝ)) * (1 + 1/10^6)^2 *
    √(((270679/125000000000))/2) * ((1-firstRatio 23906) * √(1-firstRatio 23906) *
      sixthConstant (e1CovarianceRatio 23906 (mW 11953) (1/10^6) rowEps))) /
    (712/10000 - 23906*(1+1/10^6)*((270679/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23906 (mW 11953) /
    ((1/10^5) * ((mW 11953 : ℝ)*23906*((mW 11953 : ℝ)+23906+1)))^2 +
  8*(mW 11953 : ℝ)*23906*(23906+2)*(23906+3) /
    ((1/1000)*((mW 11953 : ℝ)*23906*(23906+2)))^2 +
  covarianceVarianceBound 23906 (mW 11953) /
    ((1/1000)*covarianceMeanBound 23906 (mW 11953))^2 +
  normVarianceBound 23906 (mW 11953) / (3*inputVarianceMean 23906 (mW 11953))^2

end BstLean.Part281.WorldRow11953
namespace BstLean.Part281.WorldRow11954
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11954 = 186765381905618 := by
  have hu : mW 11954 ≤ 186765381905618 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11954 ≤ 186765381905617 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11954)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23908 ^ 2)
    ((12500000000000000000/1877729929050619418633519))
    ((25000000000000000000/3755302778468559347593161)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23908) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23908 : ℝ)^2 / (mW 11954 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2165249/1000000000000))/2) * ((1-firstRatio 23908) * √(1-firstRatio 23908) *
      sixthConstant (e1CovarianceRatio 23908 (mW 11954) (1/10^6) rowEps))) /
    (712/10000 - 23908*(1+1/10^6)*((2165249/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23908 (mW 11954) /
    ((1/10^5) * ((mW 11954 : ℝ)*23908*((mW 11954 : ℝ)+23908+1)))^2 +
  8*(mW 11954 : ℝ)*23908*(23908+2)*(23908+3) /
    ((1/1000)*((mW 11954 : ℝ)*23908*(23908+2)))^2 +
  covarianceVarianceBound 23908 (mW 11954) /
    ((1/1000)*covarianceMeanBound 23908 (mW 11954))^2 +
  normVarianceBound 23908 (mW 11954) / (3*inputVarianceMean 23908 (mW 11954))^2

end BstLean.Part281.WorldRow11954
namespace BstLean.Part281.WorldRow11955
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11955 = 186820070477903 := by
  have hu : mW 11955 ≤ 186820070477903 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11955 ≤ 186820070477902 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11955)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23910 ^ 2)
    ((5000000000000000000/751154803473319563318177))
    ((25000000000000000000/3755616937733918326917007)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23910) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23910 : ℝ)^2 / (mW 11955 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1082533/500000000000))/2) * ((1-firstRatio 23910) * √(1-firstRatio 23910) *
      sixthConstant (e1CovarianceRatio 23910 (mW 11955) (1/10^6) rowEps))) /
    (712/10000 - 23910*(1+1/10^6)*((1082533/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23910 (mW 11955) /
    ((1/10^5) * ((mW 11955 : ℝ)*23910*((mW 11955 : ℝ)+23910+1)))^2 +
  8*(mW 11955 : ℝ)*23910*(23910+2)*(23910+3) /
    ((1/1000)*((mW 11955 : ℝ)*23910*(23910+2)))^2 +
  covarianceVarianceBound 23910 (mW 11955) /
    ((1/1000)*covarianceMeanBound 23910 (mW 11955))^2 +
  normVarianceBound 23910 (mW 11955) / (3*inputVarianceMean 23910 (mW 11955))^2

end BstLean.Part281.WorldRow11955
namespace BstLean.Part281.WorldRow11956
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11956 = 186874770487723 := by
  have hu : mW 11956 ≤ 186874770487723 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11956 ≤ 186874770487722 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11956)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23912 ^ 2)
    ((6250000000000000000/939022044157989198978683))
    ((25000000000000000000/3755931096999277306240853)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23912) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23912 : ℝ)^2 / (mW 11956 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1082441/500000000000))/2) * ((1-firstRatio 23912) * √(1-firstRatio 23912) *
      sixthConstant (e1CovarianceRatio 23912 (mW 11956) (1/10^6) rowEps))) /
    (712/10000 - 23912*(1+1/10^6)*((1082441/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23912 (mW 11956) /
    ((1/10^5) * ((mW 11956 : ℝ)*23912*((mW 11956 : ℝ)+23912+1)))^2 +
  8*(mW 11956 : ℝ)*23912*(23912+2)*(23912+3) /
    ((1/1000)*((mW 11956 : ℝ)*23912*(23912+2)))^2 +
  covarianceVarianceBound 23912 (mW 11956) /
    ((1/1000)*covarianceMeanBound 23912 (mW 11956))^2 +
  normVarianceBound 23912 (mW 11956) / (3*inputVarianceMean 23912 (mW 11956))^2

end BstLean.Part281.WorldRow11956
namespace BstLean.Part281.WorldRow11957
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11957 = 186929481936512 := by
  have hu : mW 11957 ≤ 186929481936512 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11957 ≤ 186929481936511 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11957)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23914 ^ 2)
    ((25000000000000000000/3756402335897315775238579))
    ((25000000000000000000/3756245256264636285564699)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23914) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23914 : ℝ)^2 / (mW 11957 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2164699/1000000000000))/2) * ((1-firstRatio 23914) * √(1-firstRatio 23914) *
      sixthConstant (e1CovarianceRatio 23914 (mW 11957) (1/10^6) rowEps))) /
    (712/10000 - 23914*(1+1/10^6)*((2164699/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23914 (mW 11957) /
    ((1/10^5) * ((mW 11957 : ℝ)*23914*((mW 11957 : ℝ)+23914+1)))^2 +
  8*(mW 11957 : ℝ)*23914*(23914+2)*(23914+3) /
    ((1/1000)*((mW 11957 : ℝ)*23914*(23914+2)))^2 +
  covarianceVarianceBound 23914 (mW 11957) /
    ((1/1000)*covarianceMeanBound 23914 (mW 11957))^2 +
  normVarianceBound 23914 (mW 11957) / (3*inputVarianceMean 23914 (mW 11957))^2

end BstLean.Part281.WorldRow11957
namespace BstLean.Part281.WorldRow11958
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11958 = 186984204825707 := by
  have hu : mW 11958 ≤ 186984204825707 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11958 ≤ 186984204825706 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11958)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23916 ^ 2)
    ((12500000000000000000/1878358247581337377281213))
    ((5000000000000000000/751311883105999052977709)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23916) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23916 : ℝ)^2 / (mW 11958 : ℝ)) * (1 + 1/10^6)^2 *
    √(((541129/250000000000))/2) * ((1-firstRatio 23916) * √(1-firstRatio 23916) *
      sixthConstant (e1CovarianceRatio 23916 (mW 11958) (1/10^6) rowEps))) /
    (712/10000 - 23916*(1+1/10^6)*((541129/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23916 (mW 11958) /
    ((1/10^5) * ((mW 11958 : ℝ)*23916*((mW 11958 : ℝ)+23916+1)))^2 +
  8*(mW 11958 : ℝ)*23916*(23916+2)*(23916+3) /
    ((1/1000)*((mW 11958 : ℝ)*23916*(23916+2)))^2 +
  covarianceVarianceBound 23916 (mW 11958) /
    ((1/1000)*covarianceMeanBound 23916 (mW 11958))^2 +
  normVarianceBound 23916 (mW 11958) / (3*inputVarianceMean 23916 (mW 11958))^2

end BstLean.Part281.WorldRow11958
