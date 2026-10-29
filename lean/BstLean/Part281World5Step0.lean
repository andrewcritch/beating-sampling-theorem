import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part281Scalar5
namespace BstLean.Part281.WorldRow11984
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11984 = 188411020229921 := by
  have hu : mW 11984 ≤ 188411020229921 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11984 ≤ 188411020229920 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11984)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23968 ^ 2)
    ((1562500000000000000/235305289753875513561403))
    ((25000000000000000000/3764727556429328727308541)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23968) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23968 : ℝ)^2 / (mW 11984 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1079883/500000000000))/2) * ((1-firstRatio 23968) * √(1-firstRatio 23968) *
      sixthConstant (e1CovarianceRatio 23968 (mW 11984) (1/10^6) rowEps))) /
    (712/10000 - 23968*(1+1/10^6)*((1079883/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23968 (mW 11984) /
    ((1/10^5) * ((mW 11984 : ℝ)*23968*((mW 11984 : ℝ)+23968+1)))^2 +
  8*(mW 11984 : ℝ)*23968*(23968+2)*(23968+3) /
    ((1/1000)*((mW 11984 : ℝ)*23968*(23968+2)))^2 +
  covarianceVarianceBound 23968 (mW 11984) /
    ((1/1000)*covarianceMeanBound 23968 (mW 11984))^2 +
  normVarianceBound 23968 (mW 11984) / (3*inputVarianceMean 23968 (mW 11984))^2

end BstLean.Part281.WorldRow11984
namespace BstLean.Part281.WorldRow11985
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11985 = 188466052552760 := by
  have hu : mW 11985 ≤ 188466052552760 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11985 ≤ 188466052552759 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11985)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23970 ^ 2)
    ((5000000000000000000/753039759065473439261259))
    ((25000000000000000000/3765041715694687706632387)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23970) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23970 : ℝ)^2 / (mW 11985 : ℝ)) * (1 + 1/10^6)^2 *
    √(((67487/31250000000))/2) * ((1-firstRatio 23970) * √(1-firstRatio 23970) *
      sixthConstant (e1CovarianceRatio 23970 (mW 11985) (1/10^6) rowEps))) /
    (712/10000 - 23970*(1+1/10^6)*((67487/31250000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23970 (mW 11985) /
    ((1/10^5) * ((mW 11985 : ℝ)*23970*((mW 11985 : ℝ)+23970+1)))^2 +
  8*(mW 11985 : ℝ)*23970*(23970+2)*(23970+3) /
    ((1/1000)*((mW 11985 : ℝ)*23970*(23970+2)))^2 +
  covarianceVarianceBound 23970 (mW 11985) /
    ((1/1000)*covarianceMeanBound 23970 (mW 11985))^2 +
  normVarianceBound 23970 (mW 11985) / (3*inputVarianceMean 23970 (mW 11985))^2

end BstLean.Part281.WorldRow11985
namespace BstLean.Part281.WorldRow11986
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11986 = 188521096356213 := by
  have hu : mW 11986 ≤ 188521096356213 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11986 ≤ 188521096356212 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11986)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23972 ^ 2)
    ((12500000000000000000/1882756477296363087815071))
    ((25000000000000000000/3765355874960046685956233)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23972) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23972 : ℝ)^2 / (mW 11986 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1079701/500000000000))/2) * ((1-firstRatio 23972) * √(1-firstRatio 23972) *
      sixthConstant (e1CovarianceRatio 23972 (mW 11986) (1/10^6) rowEps))) /
    (712/10000 - 23972*(1+1/10^6)*((1079701/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23972 (mW 11986) /
    ((1/10^5) * ((mW 11986 : ℝ)*23972*((mW 11986 : ℝ)+23972+1)))^2 +
  8*(mW 11986 : ℝ)*23972*(23972+2)*(23972+3) /
    ((1/1000)*((mW 11986 : ℝ)*23972*(23972+2)))^2 +
  covarianceVarianceBound 23972 (mW 11986) /
    ((1/1000)*covarianceMeanBound 23972 (mW 11986))^2 +
  normVarianceBound 23972 (mW 11986) / (3*inputVarianceMean 23972 (mW 11986))^2

end BstLean.Part281.WorldRow11986
namespace BstLean.Part281.WorldRow11987
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11987 = 188576151641717 := by
  have hu : mW 11987 ≤ 188576151641717 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11987 ≤ 188576151641716 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11987)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23974 ^ 2)
    ((25000000000000000000/3765827113858085154953989))
    ((25000000000000000000/3765670034225405665280079)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23974) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23974 : ℝ)^2 / (mW 11987 : ℝ)) * (1 + 1/10^6)^2 *
    √(((107961/50000000000))/2) * ((1-firstRatio 23974) * √(1-firstRatio 23974) *
      sixthConstant (e1CovarianceRatio 23974 (mW 11987) (1/10^6) rowEps))) /
    (712/10000 - 23974*(1+1/10^6)*((107961/50000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23974 (mW 11987) /
    ((1/10^5) * ((mW 11987 : ℝ)*23974*((mW 11987 : ℝ)+23974+1)))^2 +
  8*(mW 11987 : ℝ)*23974*(23974+2)*(23974+3) /
    ((1/1000)*((mW 11987 : ℝ)*23974*(23974+2)))^2 +
  covarianceVarianceBound 23974 (mW 11987) /
    ((1/1000)*covarianceMeanBound 23974 (mW 11987))^2 +
  normVarianceBound 23974 (mW 11987) / (3*inputVarianceMean 23974 (mW 11987))^2

end BstLean.Part281.WorldRow11987
namespace BstLean.Part281.WorldRow11988
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11988 = 188631218410708 := by
  have hu : mW 11988 ≤ 188631218410708 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11988 ≤ 188631218410707 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11988)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23976 ^ 2)
    ((6250000000000000000/941535318280861033569459))
    ((1000000000000000000/150639367739630585784157)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23976) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23976 : ℝ)^2 / (mW 11988 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2159037/1000000000000))/2) * ((1-firstRatio 23976) * √(1-firstRatio 23976) *
      sixthConstant (e1CovarianceRatio 23976 (mW 11988) (1/10^6) rowEps))) /
    (712/10000 - 23976*(1+1/10^6)*((2159037/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23976 (mW 11988) /
    ((1/10^5) * ((mW 11988 : ℝ)*23976*((mW 11988 : ℝ)+23976+1)))^2 +
  8*(mW 11988 : ℝ)*23976*(23976+2)*(23976+3) /
    ((1/1000)*((mW 11988 : ℝ)*23976*(23976+2)))^2 +
  covarianceVarianceBound 23976 (mW 11988) /
    ((1/1000)*covarianceMeanBound 23976 (mW 11988))^2 +
  normVarianceBound 23976 (mW 11988) / (3*inputVarianceMean 23976 (mW 11988))^2

end BstLean.Part281.WorldRow11988
namespace BstLean.Part281.WorldRow11989
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11989 = 188686296664624 := by
  have hu : mW 11989 ≤ 188686296664624 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11989 ≤ 188686296664623 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11989)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23978 ^ 2)
    ((25000000000000000000/3766455432388803113601683))
    ((25000000000000000000/3766298352756123623927771)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23978) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23978 : ℝ)^2 / (mW 11989 : ℝ)) * (1 + 1/10^6)^2 *
    √(((431771/200000000000))/2) * ((1-firstRatio 23978) * √(1-firstRatio 23978) *
      sixthConstant (e1CovarianceRatio 23978 (mW 11989) (1/10^6) rowEps))) /
    (712/10000 - 23978*(1+1/10^6)*((431771/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23978 (mW 11989) /
    ((1/10^5) * ((mW 11989 : ℝ)*23978*((mW 11989 : ℝ)+23978+1)))^2 +
  8*(mW 11989 : ℝ)*23978*(23978+2)*(23978+3) /
    ((1/1000)*((mW 11989 : ℝ)*23978*(23978+2)))^2 +
  covarianceVarianceBound 23978 (mW 11989) /
    ((1/1000)*covarianceMeanBound 23978 (mW 11989))^2 +
  normVarianceBound 23978 (mW 11989) / (3*inputVarianceMean 23978 (mW 11989))^2

end BstLean.Part281.WorldRow11989
namespace BstLean.Part281.WorldRow11990
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11990 = 188741386404902 := by
  have hu : mW 11990 ≤ 188741386404902 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11990 ≤ 188741386404901 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11990)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23980 ^ 2)
    ((2500000000000000000/376676959165416209292553))
    ((25000000000000000000/3766612512021482603251617)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23980) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23980 : ℝ)^2 / (mW 11990 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2158673/1000000000000))/2) * ((1-firstRatio 23980) * √(1-firstRatio 23980) *
      sixthConstant (e1CovarianceRatio 23980 (mW 11990) (1/10^6) rowEps))) /
    (712/10000 - 23980*(1+1/10^6)*((2158673/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23980 (mW 11990) /
    ((1/10^5) * ((mW 11990 : ℝ)*23980*((mW 11990 : ℝ)+23980+1)))^2 +
  8*(mW 11990 : ℝ)*23980*(23980+2)*(23980+3) /
    ((1/1000)*((mW 11990 : ℝ)*23980*(23980+2)))^2 +
  covarianceVarianceBound 23980 (mW 11990) /
    ((1/1000)*covarianceMeanBound 23980 (mW 11990))^2 +
  normVarianceBound 23980 (mW 11990) / (3*inputVarianceMean 23980 (mW 11990))^2

end BstLean.Part281.WorldRow11990
namespace BstLean.Part281.WorldRow11991
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11991 = 188796487632979 := by
  have hu : mW 11991 ≤ 188796487632979 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11991 ≤ 188796487632978 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11991)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23982 ^ 2)
    ((25000000000000000000/3767083750919521072249377))
    ((25000000000000000000/3766926671286841582575463)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23982) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23982 : ℝ)^2 / (mW 11991 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2158491/1000000000000))/2) * ((1-firstRatio 23982) * √(1-firstRatio 23982) *
      sixthConstant (e1CovarianceRatio 23982 (mW 11991) (1/10^6) rowEps))) /
    (712/10000 - 23982*(1+1/10^6)*((2158491/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23982 (mW 11991) /
    ((1/10^5) * ((mW 11991 : ℝ)*23982*((mW 11991 : ℝ)+23982+1)))^2 +
  8*(mW 11991 : ℝ)*23982*(23982+2)*(23982+3) /
    ((1/1000)*((mW 11991 : ℝ)*23982*(23982+2)))^2 +
  covarianceVarianceBound 23982 (mW 11991) /
    ((1/1000)*covarianceMeanBound 23982 (mW 11991))^2 +
  normVarianceBound 23982 (mW 11991) / (3*inputVarianceMean 23982 (mW 11991))^2

end BstLean.Part281.WorldRow11991
namespace BstLean.Part281.WorldRow11992
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11992 = 188851600350293 := by
  have hu : mW 11992 ≤ 188851600350293 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11992 ≤ 188851600350292 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11992)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23984 ^ 2)
    ((3125000000000000000/470924738773110006446653))
    ((25000000000000000000/3767240830552200561899309)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23984) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23984 : ℝ)^2 / (mW 11992 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2158309/1000000000000))/2) * ((1-firstRatio 23984) * √(1-firstRatio 23984) *
      sixthConstant (e1CovarianceRatio 23984 (mW 11992) (1/10^6) rowEps))) /
    (712/10000 - 23984*(1+1/10^6)*((2158309/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23984 (mW 11992) /
    ((1/10^5) * ((mW 11992 : ℝ)*23984*((mW 11992 : ℝ)+23984+1)))^2 +
  8*(mW 11992 : ℝ)*23984*(23984+2)*(23984+3) /
    ((1/1000)*((mW 11992 : ℝ)*23984*(23984+2)))^2 +
  covarianceVarianceBound 23984 (mW 11992) /
    ((1/1000)*covarianceMeanBound 23984 (mW 11992))^2 +
  normVarianceBound 23984 (mW 11992) / (3*inputVarianceMean 23984 (mW 11992))^2

end BstLean.Part281.WorldRow11992
namespace BstLean.Part281.WorldRow11993
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11993 = 188906724558279 := by
  have hu : mW 11993 ≤ 188906724558279 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11993 ≤ 188906724558278 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11993)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23986 ^ 2)
    ((25000000000000000000/3767712069450239030897071))
    ((5000000000000000000/753510997963511908244631)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23986) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23986 : ℝ)^2 / (mW 11993 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2158127/1000000000000))/2) * ((1-firstRatio 23986) * √(1-firstRatio 23986) *
      sixthConstant (e1CovarianceRatio 23986 (mW 11993) (1/10^6) rowEps))) /
    (712/10000 - 23986*(1+1/10^6)*((2158127/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23986 (mW 11993) /
    ((1/10^5) * ((mW 11993 : ℝ)*23986*((mW 11993 : ℝ)+23986+1)))^2 +
  8*(mW 11993 : ℝ)*23986*(23986+2)*(23986+3) /
    ((1/1000)*((mW 11993 : ℝ)*23986*(23986+2)))^2 +
  covarianceVarianceBound 23986 (mW 11993) /
    ((1/1000)*covarianceMeanBound 23986 (mW 11993))^2 +
  normVarianceBound 23986 (mW 11993) / (3*inputVarianceMean 23986 (mW 11993))^2

end BstLean.Part281.WorldRow11993
namespace BstLean.Part281.WorldRow11994
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11994 = 188961860258377 := by
  have hu : mW 11994 ≤ 188961860258377 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11994 ≤ 188961860258376 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11994)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23988 ^ 2)
    ((12500000000000000000/1884013114357799005110459))
    ((25000000000000000000/3767869149082918520547001)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23988) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23988 : ℝ)^2 / (mW 11994 : ℝ)) * (1 + 1/10^6)^2 *
    √(((431589/200000000000))/2) * ((1-firstRatio 23988) * √(1-firstRatio 23988) *
      sixthConstant (e1CovarianceRatio 23988 (mW 11994) (1/10^6) rowEps))) /
    (712/10000 - 23988*(1+1/10^6)*((431589/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23988 (mW 11994) /
    ((1/10^5) * ((mW 11994 : ℝ)*23988*((mW 11994 : ℝ)+23988+1)))^2 +
  8*(mW 11994 : ℝ)*23988*(23988+2)*(23988+3) /
    ((1/1000)*((mW 11994 : ℝ)*23988*(23988+2)))^2 +
  covarianceVarianceBound 23988 (mW 11994) /
    ((1/1000)*covarianceMeanBound 23988 (mW 11994))^2 +
  normVarianceBound 23988 (mW 11994) / (3*inputVarianceMean 23988 (mW 11994))^2

end BstLean.Part281.WorldRow11994
namespace BstLean.Part281.WorldRow11995
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11995 = 189017007452023 := by
  have hu : mW 11995 ≤ 189017007452023 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11995 ≤ 189017007452022 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11995)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23990 ^ 2)
    ((5000000000000000000/753668077596191397908953))
    ((25000000000000000000/3768183308348277499870847)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23990) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23990 : ℝ)^2 / (mW 11995 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2157763/1000000000000))/2) * ((1-firstRatio 23990) * √(1-firstRatio 23990) *
      sixthConstant (e1CovarianceRatio 23990 (mW 11995) (1/10^6) rowEps))) /
    (712/10000 - 23990*(1+1/10^6)*((2157763/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23990 (mW 11995) /
    ((1/10^5) * ((mW 11995 : ℝ)*23990*((mW 11995 : ℝ)+23990+1)))^2 +
  8*(mW 11995 : ℝ)*23990*(23990+2)*(23990+3) /
    ((1/1000)*((mW 11995 : ℝ)*23990*(23990+2)))^2 +
  covarianceVarianceBound 23990 (mW 11995) /
    ((1/1000)*covarianceMeanBound 23990 (mW 11995))^2 +
  normVarianceBound 23990 (mW 11995) / (3*inputVarianceMean 23990 (mW 11995))^2

end BstLean.Part281.WorldRow11995
namespace BstLean.Part281.WorldRow11996
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11996 = 189072166140654 := by
  have hu : mW 11996 ≤ 189072166140654 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11996 ≤ 189072166140653 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11996)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23992 ^ 2)
    ((6250000000000000000/942163636811578992217153))
    ((25000000000000000000/3768497467613636479194693)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23992) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23992 : ℝ)^2 / (mW 11996 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2157581/1000000000000))/2) * ((1-firstRatio 23992) * √(1-firstRatio 23992) *
      sixthConstant (e1CovarianceRatio 23992 (mW 11996) (1/10^6) rowEps))) /
    (712/10000 - 23992*(1+1/10^6)*((2157581/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23992 (mW 11996) /
    ((1/10^5) * ((mW 11996 : ℝ)*23992*((mW 11996 : ℝ)+23992+1)))^2 +
  8*(mW 11996 : ℝ)*23992*(23992+2)*(23992+3) /
    ((1/1000)*((mW 11996 : ℝ)*23992*(23992+2)))^2 +
  covarianceVarianceBound 23992 (mW 11996) /
    ((1/1000)*covarianceMeanBound 23992 (mW 11996))^2 +
  normVarianceBound 23992 (mW 11996) / (3*inputVarianceMean 23992 (mW 11996))^2

end BstLean.Part281.WorldRow11996
namespace BstLean.Part281.WorldRow11997
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11997 = 189127336325708 := by
  have hu : mW 11997 ≤ 189127336325708 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11997 ≤ 189127336325707 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11997)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23994 ^ 2)
    ((25000000000000000000/3768968706511674948192459))
    ((25000000000000000000/3768811626878995458518539)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23994) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23994 : ℝ)^2 / (mW 11997 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2157399/1000000000000))/2) * ((1-firstRatio 23994) * √(1-firstRatio 23994) *
      sixthConstant (e1CovarianceRatio 23994 (mW 11997) (1/10^6) rowEps))) /
    (712/10000 - 23994*(1+1/10^6)*((2157399/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23994 (mW 11997) /
    ((1/10^5) * ((mW 11997 : ℝ)*23994*((mW 11997 : ℝ)+23994+1)))^2 +
  8*(mW 11997 : ℝ)*23994*(23994+2)*(23994+3) /
    ((1/1000)*((mW 11997 : ℝ)*23994*(23994+2)))^2 +
  covarianceVarianceBound 23994 (mW 11997) /
    ((1/1000)*covarianceMeanBound 23994 (mW 11997))^2 +
  normVarianceBound 23994 (mW 11997) / (3*inputVarianceMean 23994 (mW 11997))^2

end BstLean.Part281.WorldRow11997
namespace BstLean.Part281.WorldRow11998
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11998 = 189182518008623 := by
  have hu : mW 11998 ≤ 189182518008623 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11998 ≤ 189182518008622 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11998)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23996 ^ 2)
    ((12500000000000000000/1884641432888516963758153))
    ((5000000000000000000/753825157228870887568477)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23996) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23996 : ℝ)^2 / (mW 11998 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2157217/1000000000000))/2) * ((1-firstRatio 23996) * √(1-firstRatio 23996) *
      sixthConstant (e1CovarianceRatio 23996 (mW 11998) (1/10^6) rowEps))) /
    (712/10000 - 23996*(1+1/10^6)*((2157217/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23996 (mW 11998) /
    ((1/10^5) * ((mW 11998 : ℝ)*23996*((mW 11998 : ℝ)+23996+1)))^2 +
  8*(mW 11998 : ℝ)*23996*(23996+2)*(23996+3) /
    ((1/1000)*((mW 11998 : ℝ)*23996*(23996+2)))^2 +
  covarianceVarianceBound 23996 (mW 11998) /
    ((1/1000)*covarianceMeanBound 23996 (mW 11998))^2 +
  normVarianceBound 23996 (mW 11998) / (3*inputVarianceMean 23996 (mW 11998))^2

end BstLean.Part281.WorldRow11998
namespace BstLean.Part281.WorldRow11999
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11999 = 189237711190837 := by
  have hu : mW 11999 ≤ 189237711190837 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11999 ≤ 189237711190836 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11999)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23998 ^ 2)
    ((25000000000000000000/3769597025042392906840153))
    ((25000000000000000000/3769439945409713417166231)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23998) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23998 : ℝ)^2 / (mW 11999 : ℝ)) * (1 + 1/10^6)^2 *
    √(((539259/250000000000))/2) * ((1-firstRatio 23998) * √(1-firstRatio 23998) *
      sixthConstant (e1CovarianceRatio 23998 (mW 11999) (1/10^6) rowEps))) /
    (712/10000 - 23998*(1+1/10^6)*((539259/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23998 (mW 11999) /
    ((1/10^5) * ((mW 11999 : ℝ)*23998*((mW 11999 : ℝ)+23998+1)))^2 +
  8*(mW 11999 : ℝ)*23998*(23998+2)*(23998+3) /
    ((1/1000)*((mW 11999 : ℝ)*23998*(23998+2)))^2 +
  covarianceVarianceBound 23998 (mW 11999) /
    ((1/1000)*covarianceMeanBound 23998 (mW 11999))^2 +
  normVarianceBound 23998 (mW 11999) / (3*inputVarianceMean 23998 (mW 11999))^2

end BstLean.Part281.WorldRow11999
namespace BstLean.Part281.WorldRow12000
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12000 = 189292915873786 := by
  have hu : mW 12000 ≤ 189292915873786 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12000 ≤ 189292915873785 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12000)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24000 ^ 2)
    ((6250000000000000/942477796076937971541))
    ((25000000000000000000/3769754104675072396490077)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24000) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24000 : ℝ)^2 / (mW 12000 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1078427/500000000000))/2) * ((1-firstRatio 24000) * √(1-firstRatio 24000) *
      sixthConstant (e1CovarianceRatio 24000 (mW 12000) (1/10^6) rowEps))) /
    (712/10000 - 24000*(1+1/10^6)*((1078427/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24000 (mW 12000) /
    ((1/10^5) * ((mW 12000 : ℝ)*24000*((mW 12000 : ℝ)+24000+1)))^2 +
  8*(mW 12000 : ℝ)*24000*(24000+2)*(24000+3) /
    ((1/1000)*((mW 12000 : ℝ)*24000*(24000+2)))^2 +
  covarianceVarianceBound 24000 (mW 12000) /
    ((1/1000)*covarianceMeanBound 24000 (mW 12000))^2 +
  normVarianceBound 24000 (mW 12000) / (3*inputVarianceMean 24000 (mW 12000))^2

end BstLean.Part281.WorldRow12000
namespace BstLean.Part281.WorldRow12001
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12001 = 189348132058909 := by
  have hu : mW 12001 ≤ 189348132058909 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12001 ≤ 189348132058908 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12001)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24002 ^ 2)
    ((25000000000000000000/3770225343573110865487847))
    ((25000000000000000000/3770068263940431375813923)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24002) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24002 : ℝ)^2 / (mW 12001 : ℝ)) * (1 + 1/10^6)^2 *
    √(((16849/7812500000))/2) * ((1-firstRatio 24002) * √(1-firstRatio 24002) *
      sixthConstant (e1CovarianceRatio 24002 (mW 12001) (1/10^6) rowEps))) /
    (712/10000 - 24002*(1+1/10^6)*((16849/7812500000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24002 (mW 12001) /
    ((1/10^5) * ((mW 12001 : ℝ)*24002*((mW 12001 : ℝ)+24002+1)))^2 +
  8*(mW 12001 : ℝ)*24002*(24002+2)*(24002+3) /
    ((1/1000)*((mW 12001 : ℝ)*24002*(24002+2)))^2 +
  covarianceVarianceBound 24002 (mW 12001) /
    ((1/1000)*covarianceMeanBound 24002 (mW 12001))^2 +
  normVarianceBound 24002 (mW 12001) / (3*inputVarianceMean 24002 (mW 12001))^2

end BstLean.Part281.WorldRow12001
namespace BstLean.Part281.WorldRow12002
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12002 = 189403359747643 := by
  have hu : mW 12002 ≤ 189403359747643 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12002 ≤ 189403359747642 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12002)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24004 ^ 2)
    ((12500000000000000000/1885269751419234922405847))
    ((25000000000000000000/3770382423205790355137769)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24004) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24004 : ℝ)^2 / (mW 12002 : ℝ)) * (1 + 1/10^6)^2 *
    √(((215649/100000000000))/2) * ((1-firstRatio 24004) * √(1-firstRatio 24004) *
      sixthConstant (e1CovarianceRatio 24004 (mW 12002) (1/10^6) rowEps))) /
    (712/10000 - 24004*(1+1/10^6)*((215649/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24004 (mW 12002) /
    ((1/10^5) * ((mW 12002 : ℝ)*24004*((mW 12002 : ℝ)+24004+1)))^2 +
  8*(mW 12002 : ℝ)*24004*(24004+2)*(24004+3) /
    ((1/1000)*((mW 12002 : ℝ)*24004*(24004+2)))^2 +
  covarianceVarianceBound 24004 (mW 12002) /
    ((1/1000)*covarianceMeanBound 24004 (mW 12002))^2 +
  normVarianceBound 24004 (mW 12002) / (3*inputVarianceMean 24004 (mW 12002))^2

end BstLean.Part281.WorldRow12002
namespace BstLean.Part281.WorldRow12003
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12003 = 189458598941427 := by
  have hu : mW 12003 ≤ 189458598941427 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12003 ≤ 189458598941426 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12003)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24006 ^ 2)
    ((25000000000000000000/3770853662103828824135541))
    ((5000000000000000000/754139316494229866892323)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24006) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24006 : ℝ)^2 / (mW 12003 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2156309/1000000000000))/2) * ((1-firstRatio 24006) * √(1-firstRatio 24006) *
      sixthConstant (e1CovarianceRatio 24006 (mW 12003) (1/10^6) rowEps))) /
    (712/10000 - 24006*(1+1/10^6)*((2156309/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24006 (mW 12003) /
    ((1/10^5) * ((mW 12003 : ℝ)*24006*((mW 12003 : ℝ)+24006+1)))^2 +
  8*(mW 12003 : ℝ)*24006*(24006+2)*(24006+3) /
    ((1/1000)*((mW 12003 : ℝ)*24006*(24006+2)))^2 +
  covarianceVarianceBound 24006 (mW 12003) /
    ((1/1000)*covarianceMeanBound 24006 (mW 12003))^2 +
  normVarianceBound 24006 (mW 12003) / (3*inputVarianceMean 24006 (mW 12003))^2

end BstLean.Part281.WorldRow12003
namespace BstLean.Part281.WorldRow12004
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12004 = 189513849641699 := by
  have hu : mW 12004 ≤ 189513849641699 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12004 ≤ 189513849641698 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12004)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24008 ^ 2)
    ((6250000000000000000/942791955342296950864847))
    ((25000000000000000000/3771010741736508313785461)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24008) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24008 : ℝ)^2 / (mW 12004 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2156127/1000000000000))/2) * ((1-firstRatio 24008) * √(1-firstRatio 24008) *
      sixthConstant (e1CovarianceRatio 24008 (mW 12004) (1/10^6) rowEps))) /
    (712/10000 - 24008*(1+1/10^6)*((2156127/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24008 (mW 12004) /
    ((1/10^5) * ((mW 12004 : ℝ)*24008*((mW 12004 : ℝ)+24008+1)))^2 +
  8*(mW 12004 : ℝ)*24008*(24008+2)*(24008+3) /
    ((1/1000)*((mW 12004 : ℝ)*24008*(24008+2)))^2 +
  covarianceVarianceBound 24008 (mW 12004) /
    ((1/1000)*covarianceMeanBound 24008 (mW 12004))^2 +
  normVarianceBound 24008 (mW 12004) / (3*inputVarianceMean 24008 (mW 12004))^2

end BstLean.Part281.WorldRow12004
namespace BstLean.Part281.WorldRow12005
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12005 = 189569111849895 := by
  have hu : mW 12005 ≤ 189569111849895 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12005 ≤ 189569111849894 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12005)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24010 ^ 2)
    ((5000000000000000000/754296396126909356556647))
    ((25000000000000000000/3771324901001867293109307)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24010) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24010 : ℝ)^2 / (mW 12005 : ℝ)) * (1 + 1/10^6)^2 *
    √(((431189/200000000000))/2) * ((1-firstRatio 24010) * √(1-firstRatio 24010) *
      sixthConstant (e1CovarianceRatio 24010 (mW 12005) (1/10^6) rowEps))) /
    (712/10000 - 24010*(1+1/10^6)*((431189/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24010 (mW 12005) /
    ((1/10^5) * ((mW 12005 : ℝ)*24010*((mW 12005 : ℝ)+24010+1)))^2 +
  8*(mW 12005 : ℝ)*24010*(24010+2)*(24010+3) /
    ((1/1000)*((mW 12005 : ℝ)*24010*(24010+2)))^2 +
  covarianceVarianceBound 24010 (mW 12005) /
    ((1/1000)*covarianceMeanBound 24010 (mW 12005))^2 +
  normVarianceBound 24010 (mW 12005) / (3*inputVarianceMean 24010 (mW 12005))^2

end BstLean.Part281.WorldRow12005
namespace BstLean.Part281.WorldRow12006
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12006 = 189624385567455 := by
  have hu : mW 12006 ≤ 189624385567455 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12006 ≤ 189624385567454 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12006)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24012 ^ 2)
    ((12500000000000000000/1885898069949952881053541))
    ((25000000000000000000/3771639060267226272433153)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24012) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24012 : ℝ)^2 / (mW 12006 : ℝ)) * (1 + 1/10^6)^2 *
    √(((538941/250000000000))/2) * ((1-firstRatio 24012) * √(1-firstRatio 24012) *
      sixthConstant (e1CovarianceRatio 24012 (mW 12006) (1/10^6) rowEps))) /
    (712/10000 - 24012*(1+1/10^6)*((538941/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24012 (mW 12006) /
    ((1/10^5) * ((mW 12006 : ℝ)*24012*((mW 12006 : ℝ)+24012+1)))^2 +
  8*(mW 12006 : ℝ)*24012*(24012+2)*(24012+3) /
    ((1/1000)*((mW 12006 : ℝ)*24012*(24012+2)))^2 +
  covarianceVarianceBound 24012 (mW 12006) /
    ((1/1000)*covarianceMeanBound 24012 (mW 12006))^2 +
  normVarianceBound 24012 (mW 12006) / (3*inputVarianceMean 24012 (mW 12006))^2

end BstLean.Part281.WorldRow12006
namespace BstLean.Part281.WorldRow12007
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12007 = 189679670795816 := by
  have hu : mW 12007 ≤ 189679670795816 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12007 ≤ 189679670795815 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12007)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24014 ^ 2)
    ((25000000000000000000/3772110299165264741430929))
    ((25000000000000000000/3771953219532585251756999)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24014) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24014 : ℝ)^2 / (mW 12007 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1077791/500000000000))/2) * ((1-firstRatio 24014) * √(1-firstRatio 24014) *
      sixthConstant (e1CovarianceRatio 24014 (mW 12007) (1/10^6) rowEps))) /
    (712/10000 - 24014*(1+1/10^6)*((1077791/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24014 (mW 12007) /
    ((1/10^5) * ((mW 12007 : ℝ)*24014*((mW 12007 : ℝ)+24014+1)))^2 +
  8*(mW 12007 : ℝ)*24014*(24014+2)*(24014+3) /
    ((1/1000)*((mW 12007 : ℝ)*24014*(24014+2)))^2 +
  covarianceVarianceBound 24014 (mW 12007) /
    ((1/1000)*covarianceMeanBound 24014 (mW 12007))^2 +
  normVarianceBound 24014 (mW 12007) / (3*inputVarianceMean 24014 (mW 12007))^2

end BstLean.Part281.WorldRow12007
namespace BstLean.Part281.WorldRow12008
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12008 = 189734967536417 := by
  have hu : mW 12008 ≤ 189734967536417 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12008 ≤ 189734967536416 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12008)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24016 ^ 2)
    ((3125000000000000000/471553057303827965094347))
    ((5000000000000000000/754453475759588846216169)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24016) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24016 : ℝ)^2 / (mW 12008 : ℝ)) * (1 + 1/10^6)^2 *
    √(((10777/5000000000))/2) * ((1-firstRatio 24016) * √(1-firstRatio 24016) *
      sixthConstant (e1CovarianceRatio 24016 (mW 12008) (1/10^6) rowEps))) /
    (712/10000 - 24016*(1+1/10^6)*((10777/5000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24016 (mW 12008) /
    ((1/10^5) * ((mW 12008 : ℝ)*24016*((mW 12008 : ℝ)+24016+1)))^2 +
  8*(mW 12008 : ℝ)*24016*(24016+2)*(24016+3) /
    ((1/1000)*((mW 12008 : ℝ)*24016*(24016+2)))^2 +
  covarianceVarianceBound 24016 (mW 12008) /
    ((1/1000)*covarianceMeanBound 24016 (mW 12008))^2 +
  normVarianceBound 24016 (mW 12008) / (3*inputVarianceMean 24016 (mW 12008))^2

end BstLean.Part281.WorldRow12008
