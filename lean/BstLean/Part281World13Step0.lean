import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part281Scalar13
namespace BstLean.Part281.WorldRow12184
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12184 = 199647840113075 := by
  have hu : mW 12184 ≤ 199647840113075 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12184 ≤ 199647840113074 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12184)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24368 ^ 2)
    ((3125000000000000000/478464561141725510218981))
    ((25000000000000000000/3827559409501124592077741)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24368) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24368 : ℝ)^2 / (mW 12184 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2123917/1000000000000))/2) * ((1-firstRatio 24368) * √(1-firstRatio 24368) *
      sixthConstant (e1CovarianceRatio 24368 (mW 12184) (1/10^6) rowEps))) /
    (712/10000 - 24368*(1+1/10^6)*((2123917/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24368 (mW 12184) /
    ((1/10^5) * ((mW 12184 : ℝ)*24368*((mW 12184 : ℝ)+24368+1)))^2 +
  8*(mW 12184 : ℝ)*24368*(24368+2)*(24368+3) /
    ((1/1000)*((mW 12184 : ℝ)*24368*(24368+2)))^2 +
  covarianceVarianceBound 24368 (mW 12184) /
    ((1/1000)*covarianceMeanBound 24368 (mW 12184))^2 +
  normVarianceBound 24368 (mW 12184) / (3*inputVarianceMean 24368 (mW 12184))^2

end BstLean.Part281.WorldRow12184
namespace BstLean.Part281.WorldRow12185
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12185 = 199705197231623 := by
  have hu : mW 12185 ≤ 199705197231623 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12185 ≤ 199705197231622 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12185)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24370 ^ 2)
    ((5000000000000000000/765606129679832612215139))
    ((25000000000000000000/3827873568766483571401587)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24370) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24370 : ℝ)^2 / (mW 12185 : ℝ)) * (1 + 1/10^6)^2 *
    √(((106187/50000000000))/2) * ((1-firstRatio 24370) * √(1-firstRatio 24370) *
      sixthConstant (e1CovarianceRatio 24370 (mW 12185) (1/10^6) rowEps))) /
    (712/10000 - 24370*(1+1/10^6)*((106187/50000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24370 (mW 12185) /
    ((1/10^5) * ((mW 12185 : ℝ)*24370*((mW 12185 : ℝ)+24370+1)))^2 +
  8*(mW 12185 : ℝ)*24370*(24370+2)*(24370+3) /
    ((1/1000)*((mW 12185 : ℝ)*24370*(24370+2)))^2 +
  covarianceVarianceBound 24370 (mW 12185) /
    ((1/1000)*covarianceMeanBound 24370 (mW 12185))^2 +
  normVarianceBound 24370 (mW 12185) / (3*inputVarianceMean 24370 (mW 12185))^2

end BstLean.Part281.WorldRow12185
namespace BstLean.Part281.WorldRow12186
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12186 = 199762566119354 := by
  have hu : mW 12186 ≤ 199762566119354 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12186 ≤ 199762566119353 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12186)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24372 ^ 2)
    ((12500000000000000000/1914172403832261020199771))
    ((25000000000000000000/3828187728031842550725433)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24372) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24372 : ℝ)^2 / (mW 12186 : ℝ)) * (1 + 1/10^6)^2 *
    √(((530891/250000000000))/2) * ((1-firstRatio 24372) * √(1-firstRatio 24372) *
      sixthConstant (e1CovarianceRatio 24372 (mW 12186) (1/10^6) rowEps))) /
    (712/10000 - 24372*(1+1/10^6)*((530891/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24372 (mW 12186) /
    ((1/10^5) * ((mW 12186 : ℝ)*24372*((mW 12186 : ℝ)+24372+1)))^2 +
  8*(mW 12186 : ℝ)*24372*(24372+2)*(24372+3) /
    ((1/1000)*((mW 12186 : ℝ)*24372*(24372+2)))^2 +
  covarianceVarianceBound 24372 (mW 12186) /
    ((1/1000)*covarianceMeanBound 24372 (mW 12186))^2 +
  normVarianceBound 24372 (mW 12186) / (3*inputVarianceMean 24372 (mW 12186))^2

end BstLean.Part281.WorldRow12186
namespace BstLean.Part281.WorldRow12187
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12187 = 199819946777718 := by
  have hu : mW 12187 ≤ 199819946777718 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12187 ≤ 199819946777717 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12187)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24374 ^ 2)
    ((25000000000000000000/3828658966929881019723389))
    ((25000000000000000000/3828501887297201530049279)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24374) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24374 : ℝ)^2 / (mW 12187 : ℝ)) * (1 + 1/10^6)^2 *
    √(((530847/250000000000))/2) * ((1-firstRatio 24374) * √(1-firstRatio 24374) *
      sixthConstant (e1CovarianceRatio 24374 (mW 12187) (1/10^6) rowEps))) /
    (712/10000 - 24374*(1+1/10^6)*((530847/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24374 (mW 12187) /
    ((1/10^5) * ((mW 12187 : ℝ)*24374*((mW 12187 : ℝ)+24374+1)))^2 +
  8*(mW 12187 : ℝ)*24374*(24374+2)*(24374+3) /
    ((1/1000)*((mW 12187 : ℝ)*24374*(24374+2)))^2 +
  covarianceVarianceBound 24374 (mW 12187) /
    ((1/1000)*covarianceMeanBound 24374 (mW 12187))^2 +
  normVarianceBound 24374 (mW 12187) / (3*inputVarianceMean 24374 (mW 12187))^2

end BstLean.Part281.WorldRow12187
namespace BstLean.Part281.WorldRow12188
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12188 = 199877339208164 := by
  have hu : mW 12188 ≤ 199877339208164 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12188 ≤ 199877339208163 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12188)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24376 ^ 2)
    ((6250000000000000000/957243281548809999761809))
    ((40000000000000000/6126105674500096814997)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24376) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24376 : ℝ)^2 / (mW 12188 : ℝ)) * (1 + 1/10^6)^2 *
    √(((530803/250000000000))/2) * ((1-firstRatio 24376) * √(1-firstRatio 24376) *
      sixthConstant (e1CovarianceRatio 24376 (mW 12188) (1/10^6) rowEps))) /
    (712/10000 - 24376*(1+1/10^6)*((530803/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24376 (mW 12188) /
    ((1/10^5) * ((mW 12188 : ℝ)*24376*((mW 12188 : ℝ)+24376+1)))^2 +
  8*(mW 12188 : ℝ)*24376*(24376+2)*(24376+3) /
    ((1/1000)*((mW 12188 : ℝ)*24376*(24376+2)))^2 +
  covarianceVarianceBound 24376 (mW 12188) /
    ((1/1000)*covarianceMeanBound 24376 (mW 12188))^2 +
  normVarianceBound 24376 (mW 12188) / (3*inputVarianceMean 24376 (mW 12188))^2

end BstLean.Part281.WorldRow12188
namespace BstLean.Part281.WorldRow12189
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12189 = 199934743412141 := by
  have hu : mW 12189 ≤ 199934743412141 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12189 ≤ 199934743412140 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12189)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24378 ^ 2)
    ((25000000000000000000/3829287285460598978371083))
    ((25000000000000000000/3829130205827919488696971)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24378) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24378 : ℝ)^2 / (mW 12189 : ℝ)) * (1 + 1/10^6)^2 *
    √(((530759/250000000000))/2) * ((1-firstRatio 24378) * √(1-firstRatio 24378) *
      sixthConstant (e1CovarianceRatio 24378 (mW 12189) (1/10^6) rowEps))) /
    (712/10000 - 24378*(1+1/10^6)*((530759/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24378 (mW 12189) /
    ((1/10^5) * ((mW 12189 : ℝ)*24378*((mW 12189 : ℝ)+24378+1)))^2 +
  8*(mW 12189 : ℝ)*24378*(24378+2)*(24378+3) /
    ((1/1000)*((mW 12189 : ℝ)*24378*(24378+2)))^2 +
  covarianceVarianceBound 24378 (mW 12189) /
    ((1/1000)*covarianceMeanBound 24378 (mW 12189))^2 +
  normVarianceBound 24378 (mW 12189) / (3*inputVarianceMean 24378 (mW 12189))^2

end BstLean.Part281.WorldRow12189
namespace BstLean.Part281.WorldRow12190
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12190 = 199992159391097 := by
  have hu : mW 12190 ≤ 199992159391097 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12190 ≤ 199992159391096 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12190)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24380 ^ 2)
    ((2500000000000000000/382960144472595795769493))
    ((25000000000000000000/3829444365093278468020817)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24380) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24380 : ℝ)^2 / (mW 12190 : ℝ)) * (1 + 1/10^6)^2 *
    √(((106143/50000000000))/2) * ((1-firstRatio 24380) * √(1-firstRatio 24380) *
      sixthConstant (e1CovarianceRatio 24380 (mW 12190) (1/10^6) rowEps))) /
    (712/10000 - 24380*(1+1/10^6)*((106143/50000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24380 (mW 12190) /
    ((1/10^5) * ((mW 12190 : ℝ)*24380*((mW 12190 : ℝ)+24380+1)))^2 +
  8*(mW 12190 : ℝ)*24380*(24380+2)*(24380+3) /
    ((1/1000)*((mW 12190 : ℝ)*24380*(24380+2)))^2 +
  covarianceVarianceBound 24380 (mW 12190) /
    ((1/1000)*covarianceMeanBound 24380 (mW 12190))^2 +
  normVarianceBound 24380 (mW 12190) / (3*inputVarianceMean 24380 (mW 12190))^2

end BstLean.Part281.WorldRow12190
namespace BstLean.Part281.WorldRow12191
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12191 = 200049587146483 := by
  have hu : mW 12191 ≤ 200049587146483 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12191 ≤ 200049587146482 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12191)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24382 ^ 2)
    ((25000000000000000000/3829915603991316937018777))
    ((25000000000000000000/3829758524358637447344663)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24382) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24382 : ℝ)^2 / (mW 12191 : ℝ)) * (1 + 1/10^6)^2 *
    √(((530671/250000000000))/2) * ((1-firstRatio 24382) * √(1-firstRatio 24382) *
      sixthConstant (e1CovarianceRatio 24382 (mW 12191) (1/10^6) rowEps))) /
    (712/10000 - 24382*(1+1/10^6)*((530671/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24382 (mW 12191) /
    ((1/10^5) * ((mW 12191 : ℝ)*24382*((mW 12191 : ℝ)+24382+1)))^2 +
  8*(mW 12191 : ℝ)*24382*(24382+2)*(24382+3) /
    ((1/1000)*((mW 12191 : ℝ)*24382*(24382+2)))^2 +
  covarianceVarianceBound 24382 (mW 12191) /
    ((1/1000)*covarianceMeanBound 24382 (mW 12191))^2 +
  normVarianceBound 24382 (mW 12191) / (3*inputVarianceMean 24382 (mW 12191))^2

end BstLean.Part281.WorldRow12191
namespace BstLean.Part281.WorldRow12192
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12192 = 200107026679746 := by
  have hu : mW 12192 ≤ 200107026679746 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12192 ≤ 200107026679745 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12192)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24384 ^ 2)
    ((781250000000000000/119694680101771122385707))
    ((25000000000000000000/3830072683623996426668509)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24384) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24384 : ℝ)^2 / (mW 12192 : ℝ)) * (1 + 1/10^6)^2 *
    √(((530627/250000000000))/2) * ((1-firstRatio 24384) * √(1-firstRatio 24384) *
      sixthConstant (e1CovarianceRatio 24384 (mW 12192) (1/10^6) rowEps))) /
    (712/10000 - 24384*(1+1/10^6)*((530627/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24384 (mW 12192) /
    ((1/10^5) * ((mW 12192 : ℝ)*24384*((mW 12192 : ℝ)+24384+1)))^2 +
  8*(mW 12192 : ℝ)*24384*(24384+2)*(24384+3) /
    ((1/1000)*((mW 12192 : ℝ)*24384*(24384+2)))^2 +
  covarianceVarianceBound 24384 (mW 12192) /
    ((1/1000)*covarianceMeanBound 24384 (mW 12192))^2 +
  normVarianceBound 24384 (mW 12192) / (3*inputVarianceMean 24384 (mW 12192))^2

end BstLean.Part281.WorldRow12192
namespace BstLean.Part281.WorldRow12193
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12193 = 200164477992336 := by
  have hu : mW 12193 ≤ 200164477992336 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12193 ≤ 200164477992335 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12193)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24386 ^ 2)
    ((25000000000000000000/3830543922522034895666471))
    ((5000000000000000000/766077368577871081198471)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24386) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24386 : ℝ)^2 / (mW 12193 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2122331/1000000000000))/2) * ((1-firstRatio 24386) * √(1-firstRatio 24386) *
      sixthConstant (e1CovarianceRatio 24386 (mW 12193) (1/10^6) rowEps))) /
    (712/10000 - 24386*(1+1/10^6)*((2122331/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24386 (mW 12193) /
    ((1/10^5) * ((mW 12193 : ℝ)*24386*((mW 12193 : ℝ)+24386+1)))^2 +
  8*(mW 12193 : ℝ)*24386*(24386+2)*(24386+3) /
    ((1/1000)*((mW 12193 : ℝ)*24386*(24386+2)))^2 +
  covarianceVarianceBound 24386 (mW 12193) /
    ((1/1000)*covarianceMeanBound 24386 (mW 12193))^2 +
  normVarianceBound 24386 (mW 12193) / (3*inputVarianceMean 24386 (mW 12193))^2

end BstLean.Part281.WorldRow12193
namespace BstLean.Part281.WorldRow12194
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12194 = 200221941085703 := by
  have hu : mW 12194 ≤ 200221941085703 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12194 ≤ 200221941085702 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12194)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24388 ^ 2)
    ((12500000000000000000/1915429040893696937495159))
    ((25000000000000000000/3830701002154714385316201)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24388) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24388 : ℝ)^2 / (mW 12194 : ℝ)) * (1 + 1/10^6)^2 *
    √(((530539/250000000000))/2) * ((1-firstRatio 24388) * √(1-firstRatio 24388) *
      sixthConstant (e1CovarianceRatio 24388 (mW 12194) (1/10^6) rowEps))) /
    (712/10000 - 24388*(1+1/10^6)*((530539/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24388 (mW 12194) /
    ((1/10^5) * ((mW 12194 : ℝ)*24388*((mW 12194 : ℝ)+24388+1)))^2 +
  8*(mW 12194 : ℝ)*24388*(24388+2)*(24388+3) /
    ((1/1000)*((mW 12194 : ℝ)*24388*(24388+2)))^2 +
  covarianceVarianceBound 24388 (mW 12194) /
    ((1/1000)*covarianceMeanBound 24388 (mW 12194))^2 +
  normVarianceBound 24388 (mW 12194) / (3*inputVarianceMean 24388 (mW 12194))^2

end BstLean.Part281.WorldRow12194
namespace BstLean.Part281.WorldRow12195
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12195 = 200279415961296 := by
  have hu : mW 12195 ≤ 200279415961296 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12195 ≤ 200279415961295 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12195)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24390 ^ 2)
    ((5000000000000000000/766234448210550570862833))
    ((25000000000000000000/3831015161420073364640047)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24390) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24390 : ℝ)^2 / (mW 12195 : ℝ)) * (1 + 1/10^6)^2 *
    √(((106099/50000000000))/2) * ((1-firstRatio 24390) * √(1-firstRatio 24390) *
      sixthConstant (e1CovarianceRatio 24390 (mW 12195) (1/10^6) rowEps))) /
    (712/10000 - 24390*(1+1/10^6)*((106099/50000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24390 (mW 12195) /
    ((1/10^5) * ((mW 12195 : ℝ)*24390*((mW 12195 : ℝ)+24390+1)))^2 +
  8*(mW 12195 : ℝ)*24390*(24390+2)*(24390+3) /
    ((1/1000)*((mW 12195 : ℝ)*24390*(24390+2)))^2 +
  covarianceVarianceBound 24390 (mW 12195) /
    ((1/1000)*covarianceMeanBound 24390 (mW 12195))^2 +
  normVarianceBound 24390 (mW 12195) / (3*inputVarianceMean 24390 (mW 12195))^2

end BstLean.Part281.WorldRow12195
namespace BstLean.Part281.WorldRow12196
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12196 = 200336902620564 := by
  have hu : mW 12196 ≤ 200336902620564 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12196 ≤ 200336902620563 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12196)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24392 ^ 2)
    ((6250000000000000000/957871600079527958409503))
    ((25000000000000000000/3831329320685432343963893)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24392) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24392 : ℝ)^2 / (mW 12196 : ℝ)) * (1 + 1/10^6)^2 *
    √(((530451/250000000000))/2) * ((1-firstRatio 24392) * √(1-firstRatio 24392) *
      sixthConstant (e1CovarianceRatio 24392 (mW 12196) (1/10^6) rowEps))) /
    (712/10000 - 24392*(1+1/10^6)*((530451/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24392 (mW 12196) /
    ((1/10^5) * ((mW 12196 : ℝ)*24392*((mW 12196 : ℝ)+24392+1)))^2 +
  8*(mW 12196 : ℝ)*24392*(24392+2)*(24392+3) /
    ((1/1000)*((mW 12196 : ℝ)*24392*(24392+2)))^2 +
  covarianceVarianceBound 24392 (mW 12196) /
    ((1/1000)*covarianceMeanBound 24392 (mW 12196))^2 +
  normVarianceBound 24392 (mW 12196) / (3*inputVarianceMean 24392 (mW 12196))^2

end BstLean.Part281.WorldRow12196
namespace BstLean.Part281.WorldRow12197
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12197 = 200394401064956 := by
  have hu : mW 12197 ≤ 200394401064956 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12197 ≤ 200394401064955 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12197)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24394 ^ 2)
    ((25000000000000000000/3831800559583470812961859))
    ((25000000000000000000/3831643479950791323287739)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24394) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24394 : ℝ)^2 / (mW 12197 : ℝ)) * (1 + 1/10^6)^2 *
    √(((530407/250000000000))/2) * ((1-firstRatio 24394) * √(1-firstRatio 24394) *
      sixthConstant (e1CovarianceRatio 24394 (mW 12197) (1/10^6) rowEps))) /
    (712/10000 - 24394*(1+1/10^6)*((530407/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24394 (mW 12197) /
    ((1/10^5) * ((mW 12197 : ℝ)*24394*((mW 12197 : ℝ)+24394+1)))^2 +
  8*(mW 12197 : ℝ)*24394*(24394+2)*(24394+3) /
    ((1/1000)*((mW 12197 : ℝ)*24394*(24394+2)))^2 +
  covarianceVarianceBound 24394 (mW 12197) /
    ((1/1000)*covarianceMeanBound 24394 (mW 12197))^2 +
  normVarianceBound 24394 (mW 12197) / (3*inputVarianceMean 24394 (mW 12197))^2

end BstLean.Part281.WorldRow12197
namespace BstLean.Part281.WorldRow12198
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12198 = 200451911295922 := by
  have hu : mW 12198 ≤ 200451911295922 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12198 ≤ 200451911295921 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12198)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24396 ^ 2)
    ((12500000000000000000/1916057359424414896142853))
    ((5000000000000000000/766391527843230060522317)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24396) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24396 : ℝ)^2 / (mW 12198 : ℝ)) * (1 + 1/10^6)^2 *
    √(((530363/250000000000))/2) * ((1-firstRatio 24396) * √(1-firstRatio 24396) *
      sixthConstant (e1CovarianceRatio 24396 (mW 12198) (1/10^6) rowEps))) /
    (712/10000 - 24396*(1+1/10^6)*((530363/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24396 (mW 12198) /
    ((1/10^5) * ((mW 12198 : ℝ)*24396*((mW 12198 : ℝ)+24396+1)))^2 +
  8*(mW 12198 : ℝ)*24396*(24396+2)*(24396+3) /
    ((1/1000)*((mW 12198 : ℝ)*24396*(24396+2)))^2 +
  covarianceVarianceBound 24396 (mW 12198) /
    ((1/1000)*covarianceMeanBound 24396 (mW 12198))^2 +
  normVarianceBound 24396 (mW 12198) / (3*inputVarianceMean 24396 (mW 12198))^2

end BstLean.Part281.WorldRow12198
namespace BstLean.Part281.WorldRow12199
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12199 = 200509433314912 := by
  have hu : mW 12199 ≤ 200509433314912 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12199 ≤ 200509433314911 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12199)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24398 ^ 2)
    ((25000000000000000000/3832428878114188771609553))
    ((25000000000000000000/3832271798481509281935431)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24398) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24398 : ℝ)^2 / (mW 12199 : ℝ)) * (1 + 1/10^6)^2 *
    √(((530319/250000000000))/2) * ((1-firstRatio 24398) * √(1-firstRatio 24398) *
      sixthConstant (e1CovarianceRatio 24398 (mW 12199) (1/10^6) rowEps))) /
    (712/10000 - 24398*(1+1/10^6)*((530319/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24398 (mW 12199) /
    ((1/10^5) * ((mW 12199 : ℝ)*24398*((mW 12199 : ℝ)+24398+1)))^2 +
  8*(mW 12199 : ℝ)*24398*(24398+2)*(24398+3) /
    ((1/1000)*((mW 12199 : ℝ)*24398*(24398+2)))^2 +
  covarianceVarianceBound 24398 (mW 12199) /
    ((1/1000)*covarianceMeanBound 24398 (mW 12199))^2 +
  normVarianceBound 24398 (mW 12199) / (3*inputVarianceMean 24398 (mW 12199))^2

end BstLean.Part281.WorldRow12199
namespace BstLean.Part281.WorldRow12200
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12200 = 200566967123375 := by
  have hu : mW 12200 ≤ 200566967123375 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12200 ≤ 200566967123374 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12200)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24400 ^ 2)
    ((125000000000000000/19163715186897738754667))
    ((25000000000000000000/3832585957746868261259277)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24400) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24400 : ℝ)^2 / (mW 12200 : ℝ)) * (1 + 1/10^6)^2 *
    √(((21211/10000000000))/2) * ((1-firstRatio 24400) * √(1-firstRatio 24400) *
      sixthConstant (e1CovarianceRatio 24400 (mW 12200) (1/10^6) rowEps))) /
    (712/10000 - 24400*(1+1/10^6)*((21211/10000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24400 (mW 12200) /
    ((1/10^5) * ((mW 12200 : ℝ)*24400*((mW 12200 : ℝ)+24400+1)))^2 +
  8*(mW 12200 : ℝ)*24400*(24400+2)*(24400+3) /
    ((1/1000)*((mW 12200 : ℝ)*24400*(24400+2)))^2 +
  covarianceVarianceBound 24400 (mW 12200) /
    ((1/1000)*covarianceMeanBound 24400 (mW 12200))^2 +
  normVarianceBound 24400 (mW 12200) / (3*inputVarianceMean 24400 (mW 12200))^2

end BstLean.Part281.WorldRow12200
namespace BstLean.Part281.WorldRow12201
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12201 = 200624512722761 := by
  have hu : mW 12201 ≤ 200624512722761 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12201 ≤ 200624512722760 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12201)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24402 ^ 2)
    ((25000000000000000000/3833057196644906730257247))
    ((25000000000000000000/3832900117012227240583123)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24402) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24402 : ℝ)^2 / (mW 12201 : ℝ)) * (1 + 1/10^6)^2 *
    √(((530231/250000000000))/2) * ((1-firstRatio 24402) * √(1-firstRatio 24402) *
      sixthConstant (e1CovarianceRatio 24402 (mW 12201) (1/10^6) rowEps))) /
    (712/10000 - 24402*(1+1/10^6)*((530231/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24402 (mW 12201) /
    ((1/10^5) * ((mW 12201 : ℝ)*24402*((mW 12201 : ℝ)+24402+1)))^2 +
  8*(mW 12201 : ℝ)*24402*(24402+2)*(24402+3) /
    ((1/1000)*((mW 12201 : ℝ)*24402*(24402+2)))^2 +
  covarianceVarianceBound 24402 (mW 12201) /
    ((1/1000)*covarianceMeanBound 24402 (mW 12201))^2 +
  normVarianceBound 24402 (mW 12201) / (3*inputVarianceMean 24402 (mW 12201))^2

end BstLean.Part281.WorldRow12201
namespace BstLean.Part281.WorldRow12202
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12202 = 200682070114520 := by
  have hu : mW 12202 ≤ 200682070114520 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12202 ≤ 200682070114519 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12202)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24404 ^ 2)
    ((12500000000000000000/1916685677955132854790547))
    ((25000000000000000000/3833214276277586219906969)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24404) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24404 : ℝ)^2 / (mW 12202 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2120749/1000000000000))/2) * ((1-firstRatio 24404) * √(1-firstRatio 24404) *
      sixthConstant (e1CovarianceRatio 24404 (mW 12202) (1/10^6) rowEps))) /
    (712/10000 - 24404*(1+1/10^6)*((2120749/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24404 (mW 12202) /
    ((1/10^5) * ((mW 12202 : ℝ)*24404*((mW 12202 : ℝ)+24404+1)))^2 +
  8*(mW 12202 : ℝ)*24404*(24404+2)*(24404+3) /
    ((1/1000)*((mW 12202 : ℝ)*24404*(24404+2)))^2 +
  covarianceVarianceBound 24404 (mW 12202) /
    ((1/1000)*covarianceMeanBound 24404 (mW 12202))^2 +
  normVarianceBound 24404 (mW 12202) / (3*inputVarianceMean 24404 (mW 12202))^2

end BstLean.Part281.WorldRow12202
namespace BstLean.Part281.WorldRow12203
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12203 = 200739639300101 := by
  have hu : mW 12203 ≤ 200739639300101 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12203 ≤ 200739639300100 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12203)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24406 ^ 2)
    ((25000000000000000000/3833685515175624688904941))
    ((5000000000000000000/766705687108589039846163)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24406) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24406 : ℝ)^2 / (mW 12203 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2120573/1000000000000))/2) * ((1-firstRatio 24406) * √(1-firstRatio 24406) *
      sixthConstant (e1CovarianceRatio 24406 (mW 12203) (1/10^6) rowEps))) /
    (712/10000 - 24406*(1+1/10^6)*((2120573/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24406 (mW 12203) /
    ((1/10^5) * ((mW 12203 : ℝ)*24406*((mW 12203 : ℝ)+24406+1)))^2 +
  8*(mW 12203 : ℝ)*24406*(24406+2)*(24406+3) /
    ((1/1000)*((mW 12203 : ℝ)*24406*(24406+2)))^2 +
  covarianceVarianceBound 24406 (mW 12203) /
    ((1/1000)*covarianceMeanBound 24406 (mW 12203))^2 +
  normVarianceBound 24406 (mW 12203) / (3*inputVarianceMean 24406 (mW 12203))^2

end BstLean.Part281.WorldRow12203
namespace BstLean.Part281.WorldRow12204
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12204 = 200797220280954 := by
  have hu : mW 12204 ≤ 200797220280954 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12204 ≤ 200797220280953 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12204)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24408 ^ 2)
    ((6250000000000000000/958499918610245917057197))
    ((25000000000000000000/3833842594808304178554661)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24408) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24408 : ℝ)^2 / (mW 12204 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2120397/1000000000000))/2) * ((1-firstRatio 24408) * √(1-firstRatio 24408) *
      sixthConstant (e1CovarianceRatio 24408 (mW 12204) (1/10^6) rowEps))) /
    (712/10000 - 24408*(1+1/10^6)*((2120397/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24408 (mW 12204) /
    ((1/10^5) * ((mW 12204 : ℝ)*24408*((mW 12204 : ℝ)+24408+1)))^2 +
  8*(mW 12204 : ℝ)*24408*(24408+2)*(24408+3) /
    ((1/1000)*((mW 12204 : ℝ)*24408*(24408+2)))^2 +
  covarianceVarianceBound 24408 (mW 12204) /
    ((1/1000)*covarianceMeanBound 24408 (mW 12204))^2 +
  normVarianceBound 24408 (mW 12204) / (3*inputVarianceMean 24408 (mW 12204))^2

end BstLean.Part281.WorldRow12204
namespace BstLean.Part281.WorldRow12205
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12205 = 200854813058529 := by
  have hu : mW 12205 ≤ 200854813058529 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12205 ≤ 200854813058528 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12205)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24410 ^ 2)
    ((5000000000000000000/766862766741268529510527))
    ((25000000000000000000/3834156754073663157878507)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24410) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24410 : ℝ)^2 / (mW 12205 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1060111/500000000000))/2) * ((1-firstRatio 24410) * √(1-firstRatio 24410) *
      sixthConstant (e1CovarianceRatio 24410 (mW 12205) (1/10^6) rowEps))) /
    (712/10000 - 24410*(1+1/10^6)*((1060111/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24410 (mW 12205) /
    ((1/10^5) * ((mW 12205 : ℝ)*24410*((mW 12205 : ℝ)+24410+1)))^2 +
  8*(mW 12205 : ℝ)*24410*(24410+2)*(24410+3) /
    ((1/1000)*((mW 12205 : ℝ)*24410*(24410+2)))^2 +
  covarianceVarianceBound 24410 (mW 12205) /
    ((1/1000)*covarianceMeanBound 24410 (mW 12205))^2 +
  normVarianceBound 24410 (mW 12205) / (3*inputVarianceMean 24410 (mW 12205))^2

end BstLean.Part281.WorldRow12205
namespace BstLean.Part281.WorldRow12206
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12206 = 200912417634277 := by
  have hu : mW 12206 ≤ 200912417634277 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12206 ≤ 200912417634276 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12206)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24412 ^ 2)
    ((12500000000000000000/1917313996485850813438241))
    ((25000000000000000000/3834470913339022137202353)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24412) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24412 : ℝ)^2 / (mW 12206 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1060023/500000000000))/2) * ((1-firstRatio 24412) * √(1-firstRatio 24412) *
      sixthConstant (e1CovarianceRatio 24412 (mW 12206) (1/10^6) rowEps))) /
    (712/10000 - 24412*(1+1/10^6)*((1060023/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24412 (mW 12206) /
    ((1/10^5) * ((mW 12206 : ℝ)*24412*((mW 12206 : ℝ)+24412+1)))^2 +
  8*(mW 12206 : ℝ)*24412*(24412+2)*(24412+3) /
    ((1/1000)*((mW 12206 : ℝ)*24412*(24412+2)))^2 +
  covarianceVarianceBound 24412 (mW 12206) /
    ((1/1000)*covarianceMeanBound 24412 (mW 12206))^2 +
  normVarianceBound 24412 (mW 12206) / (3*inputVarianceMean 24412 (mW 12206))^2

end BstLean.Part281.WorldRow12206
namespace BstLean.Part281.WorldRow12207
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12207 = 200970034009647 := by
  have hu : mW 12207 ≤ 200970034009647 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12207 ≤ 200970034009646 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12207)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24414 ^ 2)
    ((25000000000000000000/3834942152237060606200329))
    ((25000000000000000000/3834785072604381116526199)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24414) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24414 : ℝ)^2 / (mW 12207 : ℝ)) * (1 + 1/10^6)^2 *
    √(((211987/100000000000))/2) * ((1-firstRatio 24414) * √(1-firstRatio 24414) *
      sixthConstant (e1CovarianceRatio 24414 (mW 12207) (1/10^6) rowEps))) /
    (712/10000 - 24414*(1+1/10^6)*((211987/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24414 (mW 12207) /
    ((1/10^5) * ((mW 12207 : ℝ)*24414*((mW 12207 : ℝ)+24414+1)))^2 +
  8*(mW 12207 : ℝ)*24414*(24414+2)*(24414+3) /
    ((1/1000)*((mW 12207 : ℝ)*24414*(24414+2)))^2 +
  covarianceVarianceBound 24414 (mW 12207) /
    ((1/1000)*covarianceMeanBound 24414 (mW 12207))^2 +
  normVarianceBound 24414 (mW 12207) / (3*inputVarianceMean 24414 (mW 12207))^2

end BstLean.Part281.WorldRow12207
namespace BstLean.Part281.WorldRow12208
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12208 = 201027662186089 := by
  have hu : mW 12208 ≤ 201027662186089 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12208 ≤ 201027662186088 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12208)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24416 ^ 2)
    ((1562500000000000000/239703519468901224095261))
    ((5000000000000000000/767019846373948019170009)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24416) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24416 : ℝ)^2 / (mW 12208 : ℝ)) * (1 + 1/10^6)^2 *
    √(((423939/200000000000))/2) * ((1-firstRatio 24416) * √(1-firstRatio 24416) *
      sixthConstant (e1CovarianceRatio 24416 (mW 12208) (1/10^6) rowEps))) /
    (712/10000 - 24416*(1+1/10^6)*((423939/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24416 (mW 12208) /
    ((1/10^5) * ((mW 12208 : ℝ)*24416*((mW 12208 : ℝ)+24416+1)))^2 +
  8*(mW 12208 : ℝ)*24416*(24416+2)*(24416+3) /
    ((1/1000)*((mW 12208 : ℝ)*24416*(24416+2)))^2 +
  covarianceVarianceBound 24416 (mW 12208) /
    ((1/1000)*covarianceMeanBound 24416 (mW 12208))^2 +
  normVarianceBound 24416 (mW 12208) / (3*inputVarianceMean 24416 (mW 12208))^2

end BstLean.Part281.WorldRow12208
