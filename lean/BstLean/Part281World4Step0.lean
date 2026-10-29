import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part281Scalar4
namespace BstLean.Part281.WorldRow11959
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11959 = 187038939156742 := by
  have hu : mW 11959 ≤ 187038939156742 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11959 ≤ 187038939156741 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11959)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23918 ^ 2)
    ((25000000000000000000/3757030654428033733886273))
    ((25000000000000000000/3756873574795354244212391)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23918) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23918 : ℝ)^2 / (mW 11959 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2164333/1000000000000))/2) * ((1-firstRatio 23918) * √(1-firstRatio 23918) *
      sixthConstant (e1CovarianceRatio 23918 (mW 11959) (1/10^6) rowEps))) /
    (712/10000 - 23918*(1+1/10^6)*((2164333/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23918 (mW 11959) /
    ((1/10^5) * ((mW 11959 : ℝ)*23918*((mW 11959 : ℝ)+23918+1)))^2 +
  8*(mW 11959 : ℝ)*23918*(23918+2)*(23918+3) /
    ((1/1000)*((mW 11959 : ℝ)*23918*(23918+2)))^2 +
  covarianceVarianceBound 23918 (mW 11959) /
    ((1/1000)*covarianceMeanBound 23918 (mW 11959))^2 +
  normVarianceBound 23918 (mW 11959) / (3*inputVarianceMean 23918 (mW 11959))^2

end BstLean.Part281.WorldRow11959
namespace BstLean.Part281.WorldRow11960
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11960 = 187093684931052 := by
  have hu : mW 11960 ≤ 187093684931052 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11960 ≤ 187093684931051 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11960)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23920 ^ 2)
    ((625000000000000000/93933620342334817830253))
    ((25000000000000000000/3757187734060713223536237)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23920) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23920 : ℝ)^2 / (mW 11960 : ℝ)) * (1 + 1/10^6)^2 *
    √(((43283/20000000000))/2) * ((1-firstRatio 23920) * √(1-firstRatio 23920) *
      sixthConstant (e1CovarianceRatio 23920 (mW 11960) (1/10^6) rowEps))) /
    (712/10000 - 23920*(1+1/10^6)*((43283/20000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23920 (mW 11960) /
    ((1/10^5) * ((mW 11960 : ℝ)*23920*((mW 11960 : ℝ)+23920+1)))^2 +
  8*(mW 11960 : ℝ)*23920*(23920+2)*(23920+3) /
    ((1/1000)*((mW 11960 : ℝ)*23920*(23920+2)))^2 +
  covarianceVarianceBound 23920 (mW 11960) /
    ((1/1000)*covarianceMeanBound 23920 (mW 11960))^2 +
  normVarianceBound 23920 (mW 11960) / (3*inputVarianceMean 23920 (mW 11960))^2

end BstLean.Part281.WorldRow11960
namespace BstLean.Part281.WorldRow11961
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11961 = 187148442150073 := by
  have hu : mW 11961 ≤ 187148442150073 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11961 ≤ 187148442150072 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11961)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23922 ^ 2)
    ((25000000000000000000/3757658972958751692533967))
    ((25000000000000000000/3757501893326072202860083)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23922) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23922 : ℝ)^2 / (mW 11961 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2163967/1000000000000))/2) * ((1-firstRatio 23922) * √(1-firstRatio 23922) *
      sixthConstant (e1CovarianceRatio 23922 (mW 11961) (1/10^6) rowEps))) /
    (712/10000 - 23922*(1+1/10^6)*((2163967/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23922 (mW 11961) /
    ((1/10^5) * ((mW 11961 : ℝ)*23922*((mW 11961 : ℝ)+23922+1)))^2 +
  8*(mW 11961 : ℝ)*23922*(23922+2)*(23922+3) /
    ((1/1000)*((mW 11961 : ℝ)*23922*(23922+2)))^2 +
  covarianceVarianceBound 23922 (mW 11961) /
    ((1/1000)*covarianceMeanBound 23922 (mW 11961))^2 +
  normVarianceBound 23922 (mW 11961) / (3*inputVarianceMean 23922 (mW 11961))^2

end BstLean.Part281.WorldRow11961
namespace BstLean.Part281.WorldRow11962
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11962 = 187203210815240 := by
  have hu : mW 11962 ≤ 187203210815240 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11962 ≤ 187203210815239 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11962)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23924 ^ 2)
    ((12500000000000000000/1878986566112055335928907))
    ((25000000000000000000/3757816052591431182183929)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23924) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23924 : ℝ)^2 / (mW 11962 : ℝ)) * (1 + 1/10^6)^2 *
    √(((270473/125000000000))/2) * ((1-firstRatio 23924) * √(1-firstRatio 23924) *
      sixthConstant (e1CovarianceRatio 23924 (mW 11962) (1/10^6) rowEps))) /
    (712/10000 - 23924*(1+1/10^6)*((270473/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23924 (mW 11962) /
    ((1/10^5) * ((mW 11962 : ℝ)*23924*((mW 11962 : ℝ)+23924+1)))^2 +
  8*(mW 11962 : ℝ)*23924*(23924+2)*(23924+3) /
    ((1/1000)*((mW 11962 : ℝ)*23924*(23924+2)))^2 +
  covarianceVarianceBound 23924 (mW 11962) /
    ((1/1000)*covarianceMeanBound 23924 (mW 11962))^2 +
  normVarianceBound 23924 (mW 11962) / (3*inputVarianceMean 23924 (mW 11962))^2

end BstLean.Part281.WorldRow11962
namespace BstLean.Part281.WorldRow11963
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11963 = 187257990927989 := by
  have hu : mW 11963 ≤ 187257990927989 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11963 ≤ 187257990927988 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11963)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23926 ^ 2)
    ((25000000000000000000/3758287291489469651181661))
    ((1000000000000000000/150325208474271606460311)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23926) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23926 : ℝ)^2 / (mW 11963 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2163601/1000000000000))/2) * ((1-firstRatio 23926) * √(1-firstRatio 23926) *
      sixthConstant (e1CovarianceRatio 23926 (mW 11963) (1/10^6) rowEps))) /
    (712/10000 - 23926*(1+1/10^6)*((2163601/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23926 (mW 11963) /
    ((1/10^5) * ((mW 11963 : ℝ)*23926*((mW 11963 : ℝ)+23926+1)))^2 +
  8*(mW 11963 : ℝ)*23926*(23926+2)*(23926+3) /
    ((1/1000)*((mW 11963 : ℝ)*23926*(23926+2)))^2 +
  covarianceVarianceBound 23926 (mW 11963) /
    ((1/1000)*covarianceMeanBound 23926 (mW 11963))^2 +
  normVarianceBound 23926 (mW 11963) / (3*inputVarianceMean 23926 (mW 11963))^2

end BstLean.Part281.WorldRow11963
namespace BstLean.Part281.WorldRow11964
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11964 = 187312782489755 := by
  have hu : mW 11964 ≤ 187312782489755 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11964 ≤ 187312782489754 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11964)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23928 ^ 2)
    ((6250000000000000000/939650362688707157626377))
    ((25000000000000000000/3758444371122149140831621)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23928) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23928 : ℝ)^2 / (mW 11964 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1081709/500000000000))/2) * ((1-firstRatio 23928) * √(1-firstRatio 23928) *
      sixthConstant (e1CovarianceRatio 23928 (mW 11964) (1/10^6) rowEps))) /
    (712/10000 - 23928*(1+1/10^6)*((1081709/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23928 (mW 11964) /
    ((1/10^5) * ((mW 11964 : ℝ)*23928*((mW 11964 : ℝ)+23928+1)))^2 +
  8*(mW 11964 : ℝ)*23928*(23928+2)*(23928+3) /
    ((1/1000)*((mW 11964 : ℝ)*23928*(23928+2)))^2 +
  covarianceVarianceBound 23928 (mW 11964) /
    ((1/1000)*covarianceMeanBound 23928 (mW 11964))^2 +
  normVarianceBound 23928 (mW 11964) / (3*inputVarianceMean 23928 (mW 11964))^2

end BstLean.Part281.WorldRow11964
namespace BstLean.Part281.WorldRow11965
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11965 = 187367585501973 := by
  have hu : mW 11965 ≤ 187367585501973 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11965 ≤ 187367585501972 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11965)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23930 ^ 2)
    ((5000000000000000000/751783122004037521965871))
    ((25000000000000000000/3758758530387508120155467)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23930) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23930 : ℝ)^2 / (mW 11965 : ℝ)) * (1 + 1/10^6)^2 *
    √(((432647/200000000000))/2) * ((1-firstRatio 23930) * √(1-firstRatio 23930) *
      sixthConstant (e1CovarianceRatio 23930 (mW 11965) (1/10^6) rowEps))) /
    (712/10000 - 23930*(1+1/10^6)*((432647/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23930 (mW 11965) /
    ((1/10^5) * ((mW 11965 : ℝ)*23930*((mW 11965 : ℝ)+23930+1)))^2 +
  8*(mW 11965 : ℝ)*23930*(23930+2)*(23930+3) /
    ((1/1000)*((mW 11965 : ℝ)*23930*(23930+2)))^2 +
  covarianceVarianceBound 23930 (mW 11965) /
    ((1/1000)*covarianceMeanBound 23930 (mW 11965))^2 +
  normVarianceBound 23930 (mW 11965) / (3*inputVarianceMean 23930 (mW 11965))^2

end BstLean.Part281.WorldRow11965
namespace BstLean.Part281.WorldRow11966
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11966 = 187422399966081 := by
  have hu : mW 11966 ≤ 187422399966081 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11966 ≤ 187422399966080 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11966)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23932 ^ 2)
    ((12500000000000000000/1879614884642773294576601))
    ((25000000000000000000/3759072689652867099479313)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23932) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23932 : ℝ)^2 / (mW 11966 : ℝ)) * (1 + 1/10^6)^2 *
    √(((540763/250000000000))/2) * ((1-firstRatio 23932) * √(1-firstRatio 23932) *
      sixthConstant (e1CovarianceRatio 23932 (mW 11966) (1/10^6) rowEps))) /
    (712/10000 - 23932*(1+1/10^6)*((540763/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23932 (mW 11966) /
    ((1/10^5) * ((mW 11966 : ℝ)*23932*((mW 11966 : ℝ)+23932+1)))^2 +
  8*(mW 11966 : ℝ)*23932*(23932+2)*(23932+3) /
    ((1/1000)*((mW 11966 : ℝ)*23932*(23932+2)))^2 +
  covarianceVarianceBound 23932 (mW 11966) /
    ((1/1000)*covarianceMeanBound 23932 (mW 11966))^2 +
  normVarianceBound 23932 (mW 11966) / (3*inputVarianceMean 23932 (mW 11966))^2

end BstLean.Part281.WorldRow11966
namespace BstLean.Part281.WorldRow11967
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11967 = 187477225883512 := by
  have hu : mW 11967 ≤ 187477225883512 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11967 ≤ 187477225883511 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11967)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23934 ^ 2)
    ((25000000000000000000/3759543928550905568477049))
    ((25000000000000000000/3759386848918226078803159)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23934) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23934 : ℝ)^2 / (mW 11967 : ℝ)) * (1 + 1/10^6)^2 *
    √(((216287/100000000000))/2) * ((1-firstRatio 23934) * √(1-firstRatio 23934) *
      sixthConstant (e1CovarianceRatio 23934 (mW 11967) (1/10^6) rowEps))) /
    (712/10000 - 23934*(1+1/10^6)*((216287/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23934 (mW 11967) /
    ((1/10^5) * ((mW 11967 : ℝ)*23934*((mW 11967 : ℝ)+23934+1)))^2 +
  8*(mW 11967 : ℝ)*23934*(23934+2)*(23934+3) /
    ((1/1000)*((mW 11967 : ℝ)*23934*(23934+2)))^2 +
  covarianceVarianceBound 23934 (mW 11967) /
    ((1/1000)*covarianceMeanBound 23934 (mW 11967))^2 +
  normVarianceBound 23934 (mW 11967) / (3*inputVarianceMean 23934 (mW 11967))^2

end BstLean.Part281.WorldRow11967
namespace BstLean.Part281.WorldRow11968
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11968 = 187532063255703 := by
  have hu : mW 11968 ≤ 187532063255703 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11968 ≤ 187532063255702 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11968)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23936 ^ 2)
    ((390625000000000000/58747782622129133559389))
    ((5000000000000000000/751940201636717011625401)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23936) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23936 : ℝ)^2 / (mW 11968 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2162687/1000000000000))/2) * ((1-firstRatio 23936) * √(1-firstRatio 23936) *
      sixthConstant (e1CovarianceRatio 23936 (mW 11968) (1/10^6) rowEps))) /
    (712/10000 - 23936*(1+1/10^6)*((2162687/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23936 (mW 11968) /
    ((1/10^5) * ((mW 11968 : ℝ)*23936*((mW 11968 : ℝ)+23936+1)))^2 +
  8*(mW 11968 : ℝ)*23936*(23936+2)*(23936+3) /
    ((1/1000)*((mW 11968 : ℝ)*23936*(23936+2)))^2 +
  covarianceVarianceBound 23936 (mW 11968) /
    ((1/1000)*covarianceMeanBound 23936 (mW 11968))^2 +
  normVarianceBound 23936 (mW 11968) / (3*inputVarianceMean 23936 (mW 11968))^2

end BstLean.Part281.WorldRow11968
namespace BstLean.Part281.WorldRow11969
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11969 = 187586912084090 := by
  have hu : mW 11969 ≤ 187586912084090 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11969 ≤ 187586912084089 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11969)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23938 ^ 2)
    ((25000000000000000000/3760172247081623527124743))
    ((25000000000000000000/3760015167448944037450851)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23938) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23938 : ℝ)^2 / (mW 11969 : ℝ)) * (1 + 1/10^6)^2 *
    √(((270313/125000000000))/2) * ((1-firstRatio 23938) * √(1-firstRatio 23938) *
      sixthConstant (e1CovarianceRatio 23938 (mW 11969) (1/10^6) rowEps))) /
    (712/10000 - 23938*(1+1/10^6)*((270313/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23938 (mW 11969) /
    ((1/10^5) * ((mW 11969 : ℝ)*23938*((mW 11969 : ℝ)+23938+1)))^2 +
  8*(mW 11969 : ℝ)*23938*(23938+2)*(23938+3) /
    ((1/1000)*((mW 11969 : ℝ)*23938*(23938+2)))^2 +
  covarianceVarianceBound 23938 (mW 11969) /
    ((1/1000)*covarianceMeanBound 23938 (mW 11969))^2 +
  normVarianceBound 23938 (mW 11969) / (3*inputVarianceMean 23938 (mW 11969))^2

end BstLean.Part281.WorldRow11969
namespace BstLean.Part281.WorldRow11970
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11970 = 187641772370108 := by
  have hu : mW 11970 ≤ 187641772370108 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11970 ≤ 187641772370107 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11970)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23940 ^ 2)
    ((2500000000000000000/376048640634698250644859))
    ((25000000000000000000/3760329326714303016774697)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23940) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23940 : ℝ)^2 / (mW 11970 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2162321/1000000000000))/2) * ((1-firstRatio 23940) * √(1-firstRatio 23940) *
      sixthConstant (e1CovarianceRatio 23940 (mW 11970) (1/10^6) rowEps))) /
    (712/10000 - 23940*(1+1/10^6)*((2162321/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23940 (mW 11970) /
    ((1/10^5) * ((mW 11970 : ℝ)*23940*((mW 11970 : ℝ)+23940+1)))^2 +
  8*(mW 11970 : ℝ)*23940*(23940+2)*(23940+3) /
    ((1/1000)*((mW 11970 : ℝ)*23940*(23940+2)))^2 +
  covarianceVarianceBound 23940 (mW 11970) /
    ((1/1000)*covarianceMeanBound 23940 (mW 11970))^2 +
  normVarianceBound 23940 (mW 11970) / (3*inputVarianceMean 23940 (mW 11970))^2

end BstLean.Part281.WorldRow11970
namespace BstLean.Part281.WorldRow11971
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11971 = 187696644115194 := by
  have hu : mW 11971 ≤ 187696644115194 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11971 ≤ 187696644115193 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11971)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23942 ^ 2)
    ((25000000000000000000/3760800565612341485772437))
    ((25000000000000000000/3760643485979661996098543)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23942) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23942 : ℝ)^2 / (mW 11971 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2162139/1000000000000))/2) * ((1-firstRatio 23942) * √(1-firstRatio 23942) *
      sixthConstant (e1CovarianceRatio 23942 (mW 11971) (1/10^6) rowEps))) /
    (712/10000 - 23942*(1+1/10^6)*((2162139/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23942 (mW 11971) /
    ((1/10^5) * ((mW 11971 : ℝ)*23942*((mW 11971 : ℝ)+23942+1)))^2 +
  8*(mW 11971 : ℝ)*23942*(23942+2)*(23942+3) /
    ((1/1000)*((mW 11971 : ℝ)*23942*(23942+2)))^2 +
  covarianceVarianceBound 23942 (mW 11971) /
    ((1/1000)*covarianceMeanBound 23942 (mW 11971))^2 +
  normVarianceBound 23942 (mW 11971) / (3*inputVarianceMean 23942 (mW 11971))^2

end BstLean.Part281.WorldRow11971
namespace BstLean.Part281.WorldRow11972
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11972 = 187751527320784 := by
  have hu : mW 11972 ≤ 187751527320784 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11972 ≤ 187751527320783 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11972)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23944 ^ 2)
    ((6250000000000000000/940278681219425116274071))
    ((25000000000000000000/3760957645245020975422389)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23944) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23944 : ℝ)^2 / (mW 11972 : ℝ)) * (1 + 1/10^6)^2 *
    √(((540489/250000000000))/2) * ((1-firstRatio 23944) * √(1-firstRatio 23944) *
      sixthConstant (e1CovarianceRatio 23944 (mW 11972) (1/10^6) rowEps))) /
    (712/10000 - 23944*(1+1/10^6)*((540489/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23944 (mW 11972) /
    ((1/10^5) * ((mW 11972 : ℝ)*23944*((mW 11972 : ℝ)+23944+1)))^2 +
  8*(mW 11972 : ℝ)*23944*(23944+2)*(23944+3) /
    ((1/1000)*((mW 11972 : ℝ)*23944*(23944+2)))^2 +
  covarianceVarianceBound 23944 (mW 11972) /
    ((1/1000)*covarianceMeanBound 23944 (mW 11972))^2 +
  normVarianceBound 23944 (mW 11972) / (3*inputVarianceMean 23944 (mW 11972))^2

end BstLean.Part281.WorldRow11972
namespace BstLean.Part281.WorldRow11973
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11973 = 187806421988313 := by
  have hu : mW 11973 ≤ 187806421988313 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11973 ≤ 187806421988312 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11973)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23946 ^ 2)
    ((25000000000000000000/3761428884143059444420131))
    ((5000000000000000000/752254360902075990949247)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23946) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23946 : ℝ)^2 / (mW 11973 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2161773/1000000000000))/2) * ((1-firstRatio 23946) * √(1-firstRatio 23946) *
      sixthConstant (e1CovarianceRatio 23946 (mW 11973) (1/10^6) rowEps))) /
    (712/10000 - 23946*(1+1/10^6)*((2161773/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23946 (mW 11973) /
    ((1/10^5) * ((mW 11973 : ℝ)*23946*((mW 11973 : ℝ)+23946+1)))^2 +
  8*(mW 11973 : ℝ)*23946*(23946+2)*(23946+3) /
    ((1/1000)*((mW 11973 : ℝ)*23946*(23946+2)))^2 +
  covarianceVarianceBound 23946 (mW 11973) /
    ((1/1000)*covarianceMeanBound 23946 (mW 11973))^2 +
  normVarianceBound 23946 (mW 11973) / (3*inputVarianceMean 23946 (mW 11973))^2

end BstLean.Part281.WorldRow11973
namespace BstLean.Part281.WorldRow11974
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11974 = 187861328119218 := by
  have hu : mW 11974 ≤ 187861328119218 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11974 ≤ 187861328119217 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11974)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23948 ^ 2)
    ((12500000000000000000/1880871521704209211871989))
    ((25000000000000000000/3761585963775738934070081)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23948) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23948 : ℝ)^2 / (mW 11974 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2161591/1000000000000))/2) * ((1-firstRatio 23948) * √(1-firstRatio 23948) *
      sixthConstant (e1CovarianceRatio 23948 (mW 11974) (1/10^6) rowEps))) /
    (712/10000 - 23948*(1+1/10^6)*((2161591/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23948 (mW 11974) /
    ((1/10^5) * ((mW 11974 : ℝ)*23948*((mW 11974 : ℝ)+23948+1)))^2 +
  8*(mW 11974 : ℝ)*23948*(23948+2)*(23948+3) /
    ((1/1000)*((mW 11974 : ℝ)*23948*(23948+2)))^2 +
  covarianceVarianceBound 23948 (mW 11974) /
    ((1/1000)*covarianceMeanBound 23948 (mW 11974))^2 +
  normVarianceBound 23948 (mW 11974) / (3*inputVarianceMean 23948 (mW 11974))^2

end BstLean.Part281.WorldRow11974
namespace BstLean.Part281.WorldRow11975
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11975 = 187916245714935 := by
  have hu : mW 11975 ≤ 187916245714935 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11975 ≤ 187916245714934 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11975)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23950 ^ 2)
    ((1000000000000000000/150482288106951096122713))
    ((25000000000000000000/3761900123041097913393927)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23950) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23950 : ℝ)^2 / (mW 11975 : ℝ)) * (1 + 1/10^6)^2 *
    √(((8443/3906250000))/2) * ((1-firstRatio 23950) * √(1-firstRatio 23950) *
      sixthConstant (e1CovarianceRatio 23950 (mW 11975) (1/10^6) rowEps))) /
    (712/10000 - 23950*(1+1/10^6)*((8443/3906250000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23950 (mW 11975) /
    ((1/10^5) * ((mW 11975 : ℝ)*23950*((mW 11975 : ℝ)+23950+1)))^2 +
  8*(mW 11975 : ℝ)*23950*(23950+2)*(23950+3) /
    ((1/1000)*((mW 11975 : ℝ)*23950*(23950+2)))^2 +
  covarianceVarianceBound 23950 (mW 11975) /
    ((1/1000)*covarianceMeanBound 23950 (mW 11975))^2 +
  normVarianceBound 23950 (mW 11975) / (3*inputVarianceMean 23950 (mW 11975))^2

end BstLean.Part281.WorldRow11975
namespace BstLean.Part281.WorldRow11976
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11976 = 187971174776899 := by
  have hu : mW 11976 ≤ 187971174776899 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11976 ≤ 187971174776898 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11976)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23952 ^ 2)
    ((3125000000000000000/470296420242392047798959))
    ((25000000000000000000/3762214282306456892717773)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23952) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23952 : ℝ)^2 / (mW 11976 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1080613/500000000000))/2) * ((1-firstRatio 23952) * √(1-firstRatio 23952) *
      sixthConstant (e1CovarianceRatio 23952 (mW 11976) (1/10^6) rowEps))) /
    (712/10000 - 23952*(1+1/10^6)*((1080613/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23952 (mW 11976) /
    ((1/10^5) * ((mW 11976 : ℝ)*23952*((mW 11976 : ℝ)+23952+1)))^2 +
  8*(mW 11976 : ℝ)*23952*(23952+2)*(23952+3) /
    ((1/1000)*((mW 11976 : ℝ)*23952*(23952+2)))^2 +
  covarianceVarianceBound 23952 (mW 11976) /
    ((1/1000)*covarianceMeanBound 23952 (mW 11976))^2 +
  normVarianceBound 23952 (mW 11976) / (3*inputVarianceMean 23952 (mW 11976))^2

end BstLean.Part281.WorldRow11976
namespace BstLean.Part281.WorldRow11977
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11977 = 188026115306549 := by
  have hu : mW 11977 ≤ 188026115306549 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11977 ≤ 188026115306548 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11977)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23954 ^ 2)
    ((25000000000000000000/3762685521204495361715519))
    ((25000000000000000000/3762528441571815872041619)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23954) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23954 : ℝ)^2 / (mW 11977 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2161043/1000000000000))/2) * ((1-firstRatio 23954) * √(1-firstRatio 23954) *
      sixthConstant (e1CovarianceRatio 23954 (mW 11977) (1/10^6) rowEps))) /
    (712/10000 - 23954*(1+1/10^6)*((2161043/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23954 (mW 11977) /
    ((1/10^5) * ((mW 11977 : ℝ)*23954*((mW 11977 : ℝ)+23954+1)))^2 +
  8*(mW 11977 : ℝ)*23954*(23954+2)*(23954+3) /
    ((1/1000)*((mW 11977 : ℝ)*23954*(23954+2)))^2 +
  covarianceVarianceBound 23954 (mW 11977) /
    ((1/1000)*covarianceMeanBound 23954 (mW 11977))^2 +
  normVarianceBound 23954 (mW 11977) / (3*inputVarianceMean 23954 (mW 11977))^2

end BstLean.Part281.WorldRow11977
namespace BstLean.Part281.WorldRow11978
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11978 = 188081067305319 := by
  have hu : mW 11978 ≤ 188081067305319 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11978 ≤ 188081067305318 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11978)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23956 ^ 2)
    ((12500000000000000000/1881499840234927170519683))
    ((5000000000000000000/752568520167434970273093)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23956) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23956 : ℝ)^2 / (mW 11978 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2160861/1000000000000))/2) * ((1-firstRatio 23956) * √(1-firstRatio 23956) *
      sixthConstant (e1CovarianceRatio 23956 (mW 11978) (1/10^6) rowEps))) /
    (712/10000 - 23956*(1+1/10^6)*((2160861/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23956 (mW 11978) /
    ((1/10^5) * ((mW 11978 : ℝ)*23956*((mW 11978 : ℝ)+23956+1)))^2 +
  8*(mW 11978 : ℝ)*23956*(23956+2)*(23956+3) /
    ((1/1000)*((mW 11978 : ℝ)*23956*(23956+2)))^2 +
  covarianceVarianceBound 23956 (mW 11978) /
    ((1/1000)*covarianceMeanBound 23956 (mW 11978))^2 +
  normVarianceBound 23956 (mW 11978) / (3*inputVarianceMean 23956 (mW 11978))^2

end BstLean.Part281.WorldRow11978
namespace BstLean.Part281.WorldRow11979
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11979 = 188136030774646 := by
  have hu : mW 11979 ≤ 188136030774646 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11979 ≤ 188136030774645 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11979)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23958 ^ 2)
    ((25000000000000000000/3763313839735213320363213))
    ((25000000000000000000/3763156760102533830689311)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23958) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23958 : ℝ)^2 / (mW 11979 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1080339/500000000000))/2) * ((1-firstRatio 23958) * √(1-firstRatio 23958) *
      sixthConstant (e1CovarianceRatio 23958 (mW 11979) (1/10^6) rowEps))) /
    (712/10000 - 23958*(1+1/10^6)*((1080339/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23958 (mW 11979) /
    ((1/10^5) * ((mW 11979 : ℝ)*23958*((mW 11979 : ℝ)+23958+1)))^2 +
  8*(mW 11979 : ℝ)*23958*(23958+2)*(23958+3) /
    ((1/1000)*((mW 11979 : ℝ)*23958*(23958+2)))^2 +
  covarianceVarianceBound 23958 (mW 11979) /
    ((1/1000)*covarianceMeanBound 23958 (mW 11979))^2 +
  normVarianceBound 23958 (mW 11979) / (3*inputVarianceMean 23958 (mW 11979))^2

end BstLean.Part281.WorldRow11979
namespace BstLean.Part281.WorldRow11980
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11980 = 188191005715968 := by
  have hu : mW 11980 ≤ 188191005715968 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11980 ≤ 188191005715967 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11980)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23960 ^ 2)
    ((1250000000000000000/188181399950028614984353))
    ((25000000000000000000/3763470919367892810013157)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23960) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23960 : ℝ)^2 / (mW 11980 : ℝ)) * (1 + 1/10^6)^2 *
    √(((135031/62500000000))/2) * ((1-firstRatio 23960) * √(1-firstRatio 23960) *
      sixthConstant (e1CovarianceRatio 23960 (mW 11980) (1/10^6) rowEps))) /
    (712/10000 - 23960*(1+1/10^6)*((135031/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23960 (mW 11980) /
    ((1/10^5) * ((mW 11980 : ℝ)*23960*((mW 11980 : ℝ)+23960+1)))^2 +
  8*(mW 11980 : ℝ)*23960*(23960+2)*(23960+3) /
    ((1/1000)*((mW 11980 : ℝ)*23960*(23960+2)))^2 +
  covarianceVarianceBound 23960 (mW 11980) /
    ((1/1000)*covarianceMeanBound 23960 (mW 11980))^2 +
  normVarianceBound 23960 (mW 11980) / (3*inputVarianceMean 23960 (mW 11980))^2

end BstLean.Part281.WorldRow11980
namespace BstLean.Part281.WorldRow11981
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11981 = 188245992130719 := by
  have hu : mW 11981 ≤ 188245992130719 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11981 ≤ 188245992130718 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11981)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23962 ^ 2)
    ((25000000000000000000/3763942158265931279010907))
    ((25000000000000000000/3763785078633251789337003)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23962) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23962 : ℝ)^2 / (mW 11981 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2160313/1000000000000))/2) * ((1-firstRatio 23962) * √(1-firstRatio 23962) *
      sixthConstant (e1CovarianceRatio 23962 (mW 11981) (1/10^6) rowEps))) /
    (712/10000 - 23962*(1+1/10^6)*((2160313/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23962 (mW 11981) /
    ((1/10^5) * ((mW 11981 : ℝ)*23962*((mW 11981 : ℝ)+23962+1)))^2 +
  8*(mW 11981 : ℝ)*23962*(23962+2)*(23962+3) /
    ((1/1000)*((mW 11981 : ℝ)*23962*(23962+2)))^2 +
  covarianceVarianceBound 23962 (mW 11981) /
    ((1/1000)*covarianceMeanBound 23962 (mW 11981))^2 +
  normVarianceBound 23962 (mW 11981) / (3*inputVarianceMean 23962 (mW 11981))^2

end BstLean.Part281.WorldRow11981
namespace BstLean.Part281.WorldRow11982
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11982 = 188300990020337 := by
  have hu : mW 11982 ≤ 188300990020337 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11982 ≤ 188300990020336 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11982)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23964 ^ 2)
    ((12500000000000000000/1882128158765645129167377))
    ((25000000000000000000/3764099237898610768660849)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23964) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23964 : ℝ)^2 / (mW 11982 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2160131/1000000000000))/2) * ((1-firstRatio 23964) * √(1-firstRatio 23964) *
      sixthConstant (e1CovarianceRatio 23964 (mW 11982) (1/10^6) rowEps))) /
    (712/10000 - 23964*(1+1/10^6)*((2160131/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23964 (mW 11982) /
    ((1/10^5) * ((mW 11982 : ℝ)*23964*((mW 11982 : ℝ)+23964+1)))^2 +
  8*(mW 11982 : ℝ)*23964*(23964+2)*(23964+3) /
    ((1/1000)*((mW 11982 : ℝ)*23964*(23964+2)))^2 +
  covarianceVarianceBound 23964 (mW 11982) /
    ((1/1000)*covarianceMeanBound 23964 (mW 11982))^2 +
  normVarianceBound 23964 (mW 11982) / (3*inputVarianceMean 23964 (mW 11982))^2

end BstLean.Part281.WorldRow11982
namespace BstLean.Part281.WorldRow11983
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 11983 = 188355999386259 := by
  have hu : mW 11983 ≤ 188355999386259 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 11983 ≤ 188355999386258 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*11983)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 23966 ^ 2)
    ((25000000000000000000/3764570476796649237658601))
    ((5000000000000000000/752882679432793949596939)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 23966) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (23966 : ℝ)^2 / (mW 11983 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2159949/1000000000000))/2) * ((1-firstRatio 23966) * √(1-firstRatio 23966) *
      sixthConstant (e1CovarianceRatio 23966 (mW 11983) (1/10^6) rowEps))) /
    (712/10000 - 23966*(1+1/10^6)*((2159949/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 23966 (mW 11983) /
    ((1/10^5) * ((mW 11983 : ℝ)*23966*((mW 11983 : ℝ)+23966+1)))^2 +
  8*(mW 11983 : ℝ)*23966*(23966+2)*(23966+3) /
    ((1/1000)*((mW 11983 : ℝ)*23966*(23966+2)))^2 +
  covarianceVarianceBound 23966 (mW 11983) /
    ((1/1000)*covarianceMeanBound 23966 (mW 11983))^2 +
  normVarianceBound 23966 (mW 11983) / (3*inputVarianceMean 23966 (mW 11983))^2

end BstLean.Part281.WorldRow11983
