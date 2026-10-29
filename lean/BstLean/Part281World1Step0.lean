import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part281Scalar1
namespace BstLean.Part281.WorldRow11884
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11884 = 182965518595139 := by
  have hu : mW 11884 ≤ 182965518595139 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11884 ≤ 182965518595138 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11884)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23768 ^ 2)
    ((6250000000000000000/933367177381527571149437))
    ((25000000000000000000/3733311629893430794923941)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23768) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23768 : ℝ)^2 / (mW 11884 : ℝ)) * (1 + 1/10^6)^2 *
    √(((43563/20000000000))/2) * ((1-firstRatio 23768) * √(1-firstRatio 23768) *
      sixthConstant (e1CovarianceRatio 23768 (mW 11884) (1/10^6) rowEps))) /
    (712/10000 - 23768*(1+1/10^6)*((43563/20000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23768 (mW 11884) /
    ((1/10^5) * ((mW 11884 : ℝ)*23768*((mW 11884 : ℝ)+23768+1)))^2 +
  8*(mW 11884 : ℝ)*23768*(23768+2)*(23768+3) /
    ((1/1000)*((mW 11884 : ℝ)*23768*(23768+2)))^2 +
  covarianceVarianceBound 23768 (mW 11884) /
    ((1/1000)*covarianceMeanBound 23768 (mW 11884))^2 +
  normVarianceBound 23768 (mW 11884) / (3*inputVarianceMean 23768 (mW 11884))^2

end BstLean.Part281.WorldRow11884
namespace BstLean.Part281.WorldRow11885
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11885 = 183019410102646 := by
  have hu : mW 11885 ≤ 183019410102646 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11885 ≤ 183019410102645 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11885)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23770 ^ 2)
    ((5000000000000000000/746756573758293852784319))
    ((25000000000000000000/3733625789158789774247787)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23770) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23770 : ℝ)^2 / (mW 11885 : ℝ)) * (1 + 1/10^6)^2 *
    √(((435593/200000000000))/2) * ((1-firstRatio 23770) * √(1-firstRatio 23770) *
      sixthConstant (e1CovarianceRatio 23770 (mW 11885) (1/10^6) rowEps))) /
    (712/10000 - 23770*(1+1/10^6)*((435593/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23770 (mW 11885) /
    ((1/10^5) * ((mW 11885 : ℝ)*23770*((mW 11885 : ℝ)+23770+1)))^2 +
  8*(mW 11885 : ℝ)*23770*(23770+2)*(23770+3) /
    ((1/1000)*((mW 11885 : ℝ)*23770*(23770+2)))^2 +
  covarianceVarianceBound 23770 (mW 11885) /
    ((1/1000)*covarianceMeanBound 23770 (mW 11885))^2 +
  normVarianceBound 23770 (mW 11885) / (3*inputVarianceMean 23770 (mW 11885))^2

end BstLean.Part281.WorldRow11885
namespace BstLean.Part281.WorldRow11886
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11886 = 183073312947380 := by
  have hu : mW 11886 ≤ 183073312947380 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11886 ≤ 183073312947379 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11886)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23772 ^ 2)
    ((12500000000000000000/1867048514028414121622721))
    ((25000000000000000000/3733939948424148753571633)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23772) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23772 : ℝ)^2 / (mW 11886 : ℝ)) * (1 + 1/10^6)^2 *
    √(((108889/50000000000))/2) * ((1-firstRatio 23772) * √(1-firstRatio 23772) *
      sixthConstant (e1CovarianceRatio 23772 (mW 11886) (1/10^6) rowEps))) /
    (712/10000 - 23772*(1+1/10^6)*((108889/50000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23772 (mW 11886) /
    ((1/10^5) * ((mW 11886 : ℝ)*23772*((mW 11886 : ℝ)+23772+1)))^2 +
  8*(mW 11886 : ℝ)*23772*(23772+2)*(23772+3) /
    ((1/1000)*((mW 11886 : ℝ)*23772*(23772+2)))^2 +
  covarianceVarianceBound 23772 (mW 11886) /
    ((1/1000)*covarianceMeanBound 23772 (mW 11886))^2 +
  normVarianceBound 23772 (mW 11886) / (3*inputVarianceMean 23772 (mW 11886))^2

end BstLean.Part281.WorldRow11886
namespace BstLean.Part281.WorldRow11887
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11887 = 183127227130772 := by
  have hu : mW 11887 ≤ 183127227130772 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11887 ≤ 183127227130771 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11887)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23774 ^ 2)
    ((25000000000000000000/3734411187322187222569289))
    ((25000000000000000000/3734254107689507732895479)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23774) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23774 : ℝ)^2 / (mW 11887 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1088797/500000000000))/2) * ((1-firstRatio 23774) * √(1-firstRatio 23774) *
      sixthConstant (e1CovarianceRatio 23774 (mW 11887) (1/10^6) rowEps))) /
    (712/10000 - 23774*(1+1/10^6)*((1088797/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23774 (mW 11887) /
    ((1/10^5) * ((mW 11887 : ℝ)*23774*((mW 11887 : ℝ)+23774+1)))^2 +
  8*(mW 11887 : ℝ)*23774*(23774+2)*(23774+3) /
    ((1/1000)*((mW 11887 : ℝ)*23774*(23774+2)))^2 +
  covarianceVarianceBound 23774 (mW 11887) /
    ((1/1000)*covarianceMeanBound 23774 (mW 11887))^2 +
  normVarianceBound 23774 (mW 11887) / (3*inputVarianceMean 23774 (mW 11887))^2

end BstLean.Part281.WorldRow11887
namespace BstLean.Part281.WorldRow11888
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11888 = 183181152654252 := by
  have hu : mW 11888 ≤ 183181152654252 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11888 ≤ 183181152654251 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11888)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23776 ^ 2)
    ((1562500000000000000/233420334161721637618321))
    ((1000000000000000000/149382730678194668488773)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23776) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23776 : ℝ)^2 / (mW 11888 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2177409/1000000000000))/2) * ((1-firstRatio 23776) * √(1-firstRatio 23776) *
      sixthConstant (e1CovarianceRatio 23776 (mW 11888) (1/10^6) rowEps))) /
    (712/10000 - 23776*(1+1/10^6)*((2177409/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23776 (mW 11888) /
    ((1/10^5) * ((mW 11888 : ℝ)*23776*((mW 11888 : ℝ)+23776+1)))^2 +
  8*(mW 11888 : ℝ)*23776*(23776+2)*(23776+3) /
    ((1/1000)*((mW 11888 : ℝ)*23776*(23776+2)))^2 +
  covarianceVarianceBound 23776 (mW 11888) /
    ((1/1000)*covarianceMeanBound 23776 (mW 11888))^2 +
  normVarianceBound 23776 (mW 11888) / (3*inputVarianceMean 23776 (mW 11888))^2

end BstLean.Part281.WorldRow11888
namespace BstLean.Part281.WorldRow11889
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11889 = 183235089519252 := by
  have hu : mW 11889 ≤ 183235089519252 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11889 ≤ 183235089519251 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11889)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23778 ^ 2)
    ((25000000000000000000/3735039505852905181216983))
    ((25000000000000000000/3734882426220225691543171)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23778) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23778 : ℝ)^2 / (mW 11889 : ℝ)) * (1 + 1/10^6)^2 *
    √(((272153/125000000000))/2) * ((1-firstRatio 23778) * √(1-firstRatio 23778) *
      sixthConstant (e1CovarianceRatio 23778 (mW 11889) (1/10^6) rowEps))) /
    (712/10000 - 23778*(1+1/10^6)*((272153/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23778 (mW 11889) /
    ((1/10^5) * ((mW 11889 : ℝ)*23778*((mW 11889 : ℝ)+23778+1)))^2 +
  8*(mW 11889 : ℝ)*23778*(23778+2)*(23778+3) /
    ((1/1000)*((mW 11889 : ℝ)*23778*(23778+2)))^2 +
  covarianceVarianceBound 23778 (mW 11889) /
    ((1/1000)*covarianceMeanBound 23778 (mW 11889))^2 +
  normVarianceBound 23778 (mW 11889) / (3*inputVarianceMean 23778 (mW 11889))^2

end BstLean.Part281.WorldRow11889
namespace BstLean.Part281.WorldRow11890
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11890 = 183289037727202 := by
  have hu : mW 11890 ≤ 183289037727202 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11890 ≤ 183289037727201 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11890)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23780 ^ 2)
    ((2500000000000000000/373535366511826416054083))
    ((25000000000000000000/3735196585485584670867017)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23780) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23780 : ℝ)^2 / (mW 11890 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2177039/1000000000000))/2) * ((1-firstRatio 23780) * √(1-firstRatio 23780) *
      sixthConstant (e1CovarianceRatio 23780 (mW 11890) (1/10^6) rowEps))) /
    (712/10000 - 23780*(1+1/10^6)*((2177039/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23780 (mW 11890) /
    ((1/10^5) * ((mW 11890 : ℝ)*23780*((mW 11890 : ℝ)+23780+1)))^2 +
  8*(mW 11890 : ℝ)*23780*(23780+2)*(23780+3) /
    ((1/1000)*((mW 11890 : ℝ)*23780*(23780+2)))^2 +
  covarianceVarianceBound 23780 (mW 11890) /
    ((1/1000)*covarianceMeanBound 23780 (mW 11890))^2 +
  normVarianceBound 23780 (mW 11890) / (3*inputVarianceMean 23780 (mW 11890))^2

end BstLean.Part281.WorldRow11890
namespace BstLean.Part281.WorldRow11891
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11891 = 183342997279535 := by
  have hu : mW 11891 ≤ 183342997279535 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11891 ≤ 183342997279534 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11891)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23782 ^ 2)
    ((25000000000000000000/3735667824383623139864677))
    ((25000000000000000000/3735510744750943650190863)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23782) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23782 : ℝ)^2 / (mW 11891 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2176853/1000000000000))/2) * ((1-firstRatio 23782) * √(1-firstRatio 23782) *
      sixthConstant (e1CovarianceRatio 23782 (mW 11891) (1/10^6) rowEps))) /
    (712/10000 - 23782*(1+1/10^6)*((2176853/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23782 (mW 11891) /
    ((1/10^5) * ((mW 11891 : ℝ)*23782*((mW 11891 : ℝ)+23782+1)))^2 +
  8*(mW 11891 : ℝ)*23782*(23782+2)*(23782+3) /
    ((1/1000)*((mW 11891 : ℝ)*23782*(23782+2)))^2 +
  covarianceVarianceBound 23782 (mW 11891) /
    ((1/1000)*covarianceMeanBound 23782 (mW 11891))^2 +
  normVarianceBound 23782 (mW 11891) / (3*inputVarianceMean 23782 (mW 11891))^2

end BstLean.Part281.WorldRow11891
namespace BstLean.Part281.WorldRow11892
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11892 = 183396968177680 := by
  have hu : mW 11892 ≤ 183396968177680 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11892 ≤ 183396968177679 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11892)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23784 ^ 2)
    ((6250000000000000000/933995495912245529797131))
    ((25000000000000000000/3735824904016302629514709)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23784) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23784 : ℝ)^2 / (mW 11892 : ℝ)) * (1 + 1/10^6)^2 *
    √(((544167/250000000000))/2) * ((1-firstRatio 23784) * √(1-firstRatio 23784) *
      sixthConstant (e1CovarianceRatio 23784 (mW 11892) (1/10^6) rowEps))) /
    (712/10000 - 23784*(1+1/10^6)*((544167/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23784 (mW 11892) /
    ((1/10^5) * ((mW 11892 : ℝ)*23784*((mW 11892 : ℝ)+23784+1)))^2 +
  8*(mW 11892 : ℝ)*23784*(23784+2)*(23784+3) /
    ((1/1000)*((mW 11892 : ℝ)*23784*(23784+2)))^2 +
  covarianceVarianceBound 23784 (mW 11892) /
    ((1/1000)*covarianceMeanBound 23784 (mW 11892))^2 +
  normVarianceBound 23784 (mW 11892) / (3*inputVarianceMean 23784 (mW 11892))^2

end BstLean.Part281.WorldRow11892
namespace BstLean.Part281.WorldRow11893
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11893 = 183450950423070 := by
  have hu : mW 11893 ≤ 183450950423070 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11893 ≤ 183450950423069 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11893)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23786 ^ 2)
    ((25000000000000000000/3736296142914341098512371))
    ((5000000000000000000/747227812656332321767711)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23786) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23786 : ℝ)^2 / (mW 11893 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2176483/1000000000000))/2) * ((1-firstRatio 23786) * √(1-firstRatio 23786) *
      sixthConstant (e1CovarianceRatio 23786 (mW 11893) (1/10^6) rowEps))) /
    (712/10000 - 23786*(1+1/10^6)*((2176483/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23786 (mW 11893) /
    ((1/10^5) * ((mW 11893 : ℝ)*23786*((mW 11893 : ℝ)+23786+1)))^2 +
  8*(mW 11893 : ℝ)*23786*(23786+2)*(23786+3) /
    ((1/1000)*((mW 11893 : ℝ)*23786*(23786+2)))^2 +
  covarianceVarianceBound 23786 (mW 11893) /
    ((1/1000)*covarianceMeanBound 23786 (mW 11893))^2 +
  normVarianceBound 23786 (mW 11893) / (3*inputVarianceMean 23786 (mW 11893))^2

end BstLean.Part281.WorldRow11893
namespace BstLean.Part281.WorldRow11894
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11894 = 183504944017135 := by
  have hu : mW 11894 ≤ 183504944017135 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11894 ≤ 183504944017134 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11894)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23788 ^ 2)
    ((12500000000000000000/1868305151089850038918109))
    ((25000000000000000000/3736453222547020588162401)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23788) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23788 : ℝ)^2 / (mW 11894 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1088149/500000000000))/2) * ((1-firstRatio 23788) * √(1-firstRatio 23788) *
      sixthConstant (e1CovarianceRatio 23788 (mW 11894) (1/10^6) rowEps))) /
    (712/10000 - 23788*(1+1/10^6)*((1088149/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23788 (mW 11894) /
    ((1/10^5) * ((mW 11894 : ℝ)*23788*((mW 11894 : ℝ)+23788+1)))^2 +
  8*(mW 11894 : ℝ)*23788*(23788+2)*(23788+3) /
    ((1/1000)*((mW 11894 : ℝ)*23788*(23788+2)))^2 +
  covarianceVarianceBound 23788 (mW 11894) /
    ((1/1000)*covarianceMeanBound 23788 (mW 11894))^2 +
  normVarianceBound 23788 (mW 11894) / (3*inputVarianceMean 23788 (mW 11894))^2

end BstLean.Part281.WorldRow11894
namespace BstLean.Part281.WorldRow11895
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11895 = 183558948961307 := by
  have hu : mW 11895 ≤ 183558948961307 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11895 ≤ 183558948961306 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11895)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23790 ^ 2)
    ((5000000000000000000/747384892289011811432013))
    ((25000000000000000000/3736767381812379567486247)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23790) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23790 : ℝ)^2 / (mW 11895 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2176113/1000000000000))/2) * ((1-firstRatio 23790) * √(1-firstRatio 23790) *
      sixthConstant (e1CovarianceRatio 23790 (mW 11895) (1/10^6) rowEps))) /
    (712/10000 - 23790*(1+1/10^6)*((2176113/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23790 (mW 11895) /
    ((1/10^5) * ((mW 11895 : ℝ)*23790*((mW 11895 : ℝ)+23790+1)))^2 +
  8*(mW 11895 : ℝ)*23790*(23790+2)*(23790+3) /
    ((1/1000)*((mW 11895 : ℝ)*23790*(23790+2)))^2 +
  covarianceVarianceBound 23790 (mW 11895) /
    ((1/1000)*covarianceMeanBound 23790 (mW 11895))^2 +
  normVarianceBound 23790 (mW 11895) / (3*inputVarianceMean 23790 (mW 11895))^2

end BstLean.Part281.WorldRow11895
namespace BstLean.Part281.WorldRow11896
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11896 = 183612965257017 := by
  have hu : mW 11896 ≤ 183612965257017 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11896 ≤ 183612965257016 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11896)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23792 ^ 2)
    ((3125000000000000000/467154827588802254560489))
    ((25000000000000000000/3737081541077738546810093)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23792) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23792 : ℝ)^2 / (mW 11896 : ℝ)) * (1 + 1/10^6)^2 *
    √(((271991/125000000000))/2) * ((1-firstRatio 23792) * √(1-firstRatio 23792) *
      sixthConstant (e1CovarianceRatio 23792 (mW 11896) (1/10^6) rowEps))) /
    (712/10000 - 23792*(1+1/10^6)*((271991/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23792 (mW 11896) /
    ((1/10^5) * ((mW 11896 : ℝ)*23792*((mW 11896 : ℝ)+23792+1)))^2 +
  8*(mW 11896 : ℝ)*23792*(23792+2)*(23792+3) /
    ((1/1000)*((mW 11896 : ℝ)*23792*(23792+2)))^2 +
  covarianceVarianceBound 23792 (mW 11896) /
    ((1/1000)*covarianceMeanBound 23792 (mW 11896))^2 +
  normVarianceBound 23792 (mW 11896) / (3*inputVarianceMean 23792 (mW 11896))^2

end BstLean.Part281.WorldRow11896
namespace BstLean.Part281.WorldRow11897
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11897 = 183666992905698 := by
  have hu : mW 11897 ≤ 183666992905698 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11897 ≤ 183666992905697 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11897)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23794 ^ 2)
    ((25000000000000000000/3737552779975777015807759))
    ((25000000000000000000/3737395700343097526133939)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23794) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23794 : ℝ)^2 / (mW 11897 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2175743/1000000000000))/2) * ((1-firstRatio 23794) * √(1-firstRatio 23794) *
      sixthConstant (e1CovarianceRatio 23794 (mW 11897) (1/10^6) rowEps))) /
    (712/10000 - 23794*(1+1/10^6)*((2175743/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23794 (mW 11897) /
    ((1/10^5) * ((mW 11897 : ℝ)*23794*((mW 11897 : ℝ)+23794+1)))^2 +
  8*(mW 11897 : ℝ)*23794*(23794+2)*(23794+3) /
    ((1/1000)*((mW 11897 : ℝ)*23794*(23794+2)))^2 +
  covarianceVarianceBound 23794 (mW 11897) /
    ((1/1000)*covarianceMeanBound 23794 (mW 11897))^2 +
  normVarianceBound 23794 (mW 11897) / (3*inputVarianceMean 23794 (mW 11897))^2

end BstLean.Part281.WorldRow11897
namespace BstLean.Part281.WorldRow11898
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11898 = 183721031908780 := by
  have hu : mW 11898 ≤ 183721031908780 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11898 ≤ 183721031908779 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11898)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23796 ^ 2)
    ((12500000000000000000/1868933469620567997565803))
    ((5000000000000000000/747541971921691301091557)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23796) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23796 : ℝ)^2 / (mW 11898 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1087779/500000000000))/2) * ((1-firstRatio 23796) * √(1-firstRatio 23796) *
      sixthConstant (e1CovarianceRatio 23796 (mW 11898) (1/10^6) rowEps))) /
    (712/10000 - 23796*(1+1/10^6)*((1087779/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23796 (mW 11898) /
    ((1/10^5) * ((mW 11898 : ℝ)*23796*((mW 11898 : ℝ)+23796+1)))^2 +
  8*(mW 11898 : ℝ)*23796*(23796+2)*(23796+3) /
    ((1/1000)*((mW 11898 : ℝ)*23796*(23796+2)))^2 +
  covarianceVarianceBound 23796 (mW 11898) /
    ((1/1000)*covarianceMeanBound 23796 (mW 11898))^2 +
  normVarianceBound 23796 (mW 11898) / (3*inputVarianceMean 23796 (mW 11898))^2

end BstLean.Part281.WorldRow11898
namespace BstLean.Part281.WorldRow11899
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11899 = 183775082267695 := by
  have hu : mW 11899 ≤ 183775082267695 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11899 ≤ 183775082267694 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11899)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23798 ^ 2)
    ((25000000000000000000/3738181098506494974455453))
    ((25000000000000000000/3738024018873815484781631)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23798) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23798 : ℝ)^2 / (mW 11899 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2175373/1000000000000))/2) * ((1-firstRatio 23798) * √(1-firstRatio 23798) *
      sixthConstant (e1CovarianceRatio 23798 (mW 11899) (1/10^6) rowEps))) /
    (712/10000 - 23798*(1+1/10^6)*((2175373/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23798 (mW 11899) /
    ((1/10^5) * ((mW 11899 : ℝ)*23798*((mW 11899 : ℝ)+23798+1)))^2 +
  8*(mW 11899 : ℝ)*23798*(23798+2)*(23798+3) /
    ((1/1000)*((mW 11899 : ℝ)*23798*(23798+2)))^2 +
  covarianceVarianceBound 23798 (mW 11899) /
    ((1/1000)*covarianceMeanBound 23798 (mW 11899))^2 +
  normVarianceBound 23798 (mW 11899) / (3*inputVarianceMean 23798 (mW 11899))^2

end BstLean.Part281.WorldRow11899
namespace BstLean.Part281.WorldRow11900
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11900 = 183829143983875 := by
  have hu : mW 11900 ≤ 183829143983875 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11900 ≤ 183829143983874 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11900)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23800 ^ 2)
    ((250000000000000000/37384952577718539537793))
    ((25000000000000000000/3738338178139174464105477)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23800) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23800 : ℝ)^2 / (mW 11900 : ℝ)) * (1 + 1/10^6)^2 *
    √(((543797/250000000000))/2) * ((1-firstRatio 23800) * √(1-firstRatio 23800) *
      sixthConstant (e1CovarianceRatio 23800 (mW 11900) (1/10^6) rowEps))) /
    (712/10000 - 23800*(1+1/10^6)*((543797/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23800 (mW 11900) /
    ((1/10^5) * ((mW 11900 : ℝ)*23800*((mW 11900 : ℝ)+23800+1)))^2 +
  8*(mW 11900 : ℝ)*23800*(23800+2)*(23800+3) /
    ((1/1000)*((mW 11900 : ℝ)*23800*(23800+2)))^2 +
  covarianceVarianceBound 23800 (mW 11900) /
    ((1/1000)*covarianceMeanBound 23800 (mW 11900))^2 +
  normVarianceBound 23800 (mW 11900) / (3*inputVarianceMean 23800 (mW 11900))^2

end BstLean.Part281.WorldRow11900
namespace BstLean.Part281.WorldRow11901
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11901 = 183883217058751 := by
  have hu : mW 11901 ≤ 183883217058751 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11901 ≤ 183883217058750 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11901)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23802 ^ 2)
    ((25000000000000000000/3738809417037212933103147))
    ((25000000000000000000/3738652337404533443429323)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23802) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23802 : ℝ)^2 / (mW 11901 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2175003/1000000000000))/2) * ((1-firstRatio 23802) * √(1-firstRatio 23802) *
      sixthConstant (e1CovarianceRatio 23802 (mW 11901) (1/10^6) rowEps))) /
    (712/10000 - 23802*(1+1/10^6)*((2175003/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23802 (mW 11901) /
    ((1/10^5) * ((mW 11901 : ℝ)*23802*((mW 11901 : ℝ)+23802+1)))^2 +
  8*(mW 11901 : ℝ)*23802*(23802+2)*(23802+3) /
    ((1/1000)*((mW 11901 : ℝ)*23802*(23802+2)))^2 +
  covarianceVarianceBound 23802 (mW 11901) /
    ((1/1000)*covarianceMeanBound 23802 (mW 11901))^2 +
  normVarianceBound 23802 (mW 11901) / (3*inputVarianceMean 23802 (mW 11901))^2

end BstLean.Part281.WorldRow11901
namespace BstLean.Part281.WorldRow11902
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11902 = 183937301493755 := by
  have hu : mW 11902 ≤ 183937301493755 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11902 ≤ 183937301493754 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11902)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23804 ^ 2)
    ((12500000000000000000/1869561788151285956213497))
    ((25000000000000000000/3738966496669892422753169)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23804) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23804 : ℝ)^2 / (mW 11902 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1087409/500000000000))/2) * ((1-firstRatio 23804) * √(1-firstRatio 23804) *
      sixthConstant (e1CovarianceRatio 23804 (mW 11902) (1/10^6) rowEps))) /
    (712/10000 - 23804*(1+1/10^6)*((1087409/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23804 (mW 11902) /
    ((1/10^5) * ((mW 11902 : ℝ)*23804*((mW 11902 : ℝ)+23804+1)))^2 +
  8*(mW 11902 : ℝ)*23804*(23804+2)*(23804+3) /
    ((1/1000)*((mW 11902 : ℝ)*23804*(23804+2)))^2 +
  covarianceVarianceBound 23804 (mW 11902) /
    ((1/1000)*covarianceMeanBound 23804 (mW 11902))^2 +
  normVarianceBound 23804 (mW 11902) / (3*inputVarianceMean 23804 (mW 11902))^2

end BstLean.Part281.WorldRow11902
namespace BstLean.Part281.WorldRow11903
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11903 = 183991397290320 := by
  have hu : mW 11903 ≤ 183991397290320 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11903 ≤ 183991397290319 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11903)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23806 ^ 2)
    ((25000000000000000000/3739437735567930891750841))
    ((5000000000000000000/747856131187050280415403)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23806) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23806 : ℝ)^2 / (mW 11903 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2174633/1000000000000))/2) * ((1-firstRatio 23806) * √(1-firstRatio 23806) *
      sixthConstant (e1CovarianceRatio 23806 (mW 11903) (1/10^6) rowEps))) /
    (712/10000 - 23806*(1+1/10^6)*((2174633/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23806 (mW 11903) /
    ((1/10^5) * ((mW 11903 : ℝ)*23806*((mW 11903 : ℝ)+23806+1)))^2 +
  8*(mW 11903 : ℝ)*23806*(23806+2)*(23806+3) /
    ((1/1000)*((mW 11903 : ℝ)*23806*(23806+2)))^2 +
  covarianceVarianceBound 23806 (mW 11903) /
    ((1/1000)*covarianceMeanBound 23806 (mW 11903))^2 +
  normVarianceBound 23806 (mW 11903) / (3*inputVarianceMean 23806 (mW 11903))^2

end BstLean.Part281.WorldRow11903
namespace BstLean.Part281.WorldRow11904
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11904 = 184045504449877 := by
  have hu : mW 11904 ≤ 184045504449877 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11904 ≤ 184045504449876 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11904)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23808 ^ 2)
    ((195312500000000000/29216811678385077117771))
    ((25000000000000000000/3739594815200610381400861)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23808) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23808 : ℝ)^2 / (mW 11904 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2174449/1000000000000))/2) * ((1-firstRatio 23808) * √(1-firstRatio 23808) *
      sixthConstant (e1CovarianceRatio 23808 (mW 11904) (1/10^6) rowEps))) /
    (712/10000 - 23808*(1+1/10^6)*((2174449/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23808 (mW 11904) /
    ((1/10^5) * ((mW 11904 : ℝ)*23808*((mW 11904 : ℝ)+23808+1)))^2 +
  8*(mW 11904 : ℝ)*23808*(23808+2)*(23808+3) /
    ((1/1000)*((mW 11904 : ℝ)*23808*(23808+2)))^2 +
  covarianceVarianceBound 23808 (mW 11904) /
    ((1/1000)*covarianceMeanBound 23808 (mW 11904))^2 +
  normVarianceBound 23808 (mW 11904) / (3*inputVarianceMean 23808 (mW 11904))^2

end BstLean.Part281.WorldRow11904
namespace BstLean.Part281.WorldRow11905
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11905 = 184099622973858 := by
  have hu : mW 11905 ≤ 184099622973858 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11905 ≤ 184099622973857 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11905)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23810 ^ 2)
    ((5000000000000000000/748013210819729770079707))
    ((25000000000000000000/3739908974465969360724707)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23810) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23810 : ℝ)^2 / (mW 11905 : ℝ)) * (1 + 1/10^6)^2 *
    √(((271783/125000000000))/2) * ((1-firstRatio 23810) * √(1-firstRatio 23810) *
      sixthConstant (e1CovarianceRatio 23810 (mW 11905) (1/10^6) rowEps))) /
    (712/10000 - 23810*(1+1/10^6)*((271783/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23810 (mW 11905) /
    ((1/10^5) * ((mW 11905 : ℝ)*23810*((mW 11905 : ℝ)+23810+1)))^2 +
  8*(mW 11905 : ℝ)*23810*(23810+2)*(23810+3) /
    ((1/1000)*((mW 11905 : ℝ)*23810*(23810+2)))^2 +
  covarianceVarianceBound 23810 (mW 11905) /
    ((1/1000)*covarianceMeanBound 23810 (mW 11905))^2 +
  normVarianceBound 23810 (mW 11905) / (3*inputVarianceMean 23810 (mW 11905))^2

end BstLean.Part281.WorldRow11905
namespace BstLean.Part281.WorldRow11906
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11906 = 184153752863695 := by
  have hu : mW 11906 ≤ 184153752863695 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11906 ≤ 184153752863694 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11906)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23812 ^ 2)
    ((12500000000000000000/1870190106682003914861191))
    ((25000000000000000000/3740223133731328340048553)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23812) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23812 : ℝ)^2 / (mW 11906 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2174079/1000000000000))/2) * ((1-firstRatio 23812) * √(1-firstRatio 23812) *
      sixthConstant (e1CovarianceRatio 23812 (mW 11906) (1/10^6) rowEps))) /
    (712/10000 - 23812*(1+1/10^6)*((2174079/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23812 (mW 11906) /
    ((1/10^5) * ((mW 11906 : ℝ)*23812*((mW 11906 : ℝ)+23812+1)))^2 +
  8*(mW 11906 : ℝ)*23812*(23812+2)*(23812+3) /
    ((1/1000)*((mW 11906 : ℝ)*23812*(23812+2)))^2 +
  covarianceVarianceBound 23812 (mW 11906) /
    ((1/1000)*covarianceMeanBound 23812 (mW 11906))^2 +
  normVarianceBound 23812 (mW 11906) / (3*inputVarianceMean 23812 (mW 11906))^2

end BstLean.Part281.WorldRow11906
namespace BstLean.Part281.WorldRow11907
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11907 = 184207894120820 := by
  have hu : mW 11907 ≤ 184207894120820 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11907 ≤ 184207894120819 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11907)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23814 ^ 2)
    ((25000000000000000000/3740694372629366809046229))
    ((25000000000000000000/3740537292996687319372399)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23814) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23814 : ℝ)^2 / (mW 11907 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1086947/500000000000))/2) * ((1-firstRatio 23814) * √(1-firstRatio 23814) *
      sixthConstant (e1CovarianceRatio 23814 (mW 11907) (1/10^6) rowEps))) /
    (712/10000 - 23814*(1+1/10^6)*((1086947/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23814 (mW 11907) /
    ((1/10^5) * ((mW 11907 : ℝ)*23814*((mW 11907 : ℝ)+23814+1)))^2 +
  8*(mW 11907 : ℝ)*23814*(23814+2)*(23814+3) /
    ((1/1000)*((mW 11907 : ℝ)*23814*(23814+2)))^2 +
  covarianceVarianceBound 23814 (mW 11907) /
    ((1/1000)*covarianceMeanBound 23814 (mW 11907))^2 +
  normVarianceBound 23814 (mW 11907) / (3*inputVarianceMean 23814 (mW 11907))^2

end BstLean.Part281.WorldRow11907
namespace BstLean.Part281.WorldRow11908
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11908 = 184262046746665 := by
  have hu : mW 11908 ≤ 184262046746665 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11908 ≤ 184262046746664 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11908)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23816 ^ 2)
    ((6250000000000000000/935252132973681447092519))
    ((5000000000000000000/748170290452409259739249)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23816) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23816 : ℝ)^2 / (mW 11908 : ℝ)) * (1 + 1/10^6)^2 *
    √(((217371/100000000000))/2) * ((1-firstRatio 23816) * √(1-firstRatio 23816) *
      sixthConstant (e1CovarianceRatio 23816 (mW 11908) (1/10^6) rowEps))) /
    (712/10000 - 23816*(1+1/10^6)*((217371/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23816 (mW 11908) /
    ((1/10^5) * ((mW 11908 : ℝ)*23816*((mW 11908 : ℝ)+23816+1)))^2 +
  8*(mW 11908 : ℝ)*23816*(23816+2)*(23816+3) /
    ((1/1000)*((mW 11908 : ℝ)*23816*(23816+2)))^2 +
  covarianceVarianceBound 23816 (mW 11908) /
    ((1/1000)*covarianceMeanBound 23816 (mW 11908))^2 +
  normVarianceBound 23816 (mW 11908) / (3*inputVarianceMean 23816 (mW 11908))^2

end BstLean.Part281.WorldRow11908
